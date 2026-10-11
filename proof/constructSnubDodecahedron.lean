import Pipeline.FundamentalChart3
import Pipeline.NativeExecutable
import Pipeline.PackedSolutionTree
import SnubDodecahedron.SparseSupport
import SnubDodecahedron

/-!
Native executable that checks the snub dodecahedron's certificate data and, if
it is all valid, establishes `CertificatesValid`, and so
(`isNopert_of_certificatesValid`) that every snub dodecahedron (Wikipedia's coordinates, any similar copy, either
chirality) is a nopert (`SnubDodecahedron.lean`).

Usage:
  constructSnubDodecahedron <tube manifest.txt> <chart directory>
    Checks everything: the view cover, every tube table and all four chart
    tables. On success it prints
      instantiated: IsNopert V for every snub dodecahedron V (none is Rupert)

The arguments: `manifest.txt` lists the tube packs in code order, next to
them; the chart directory holds `chart0.pack` through `chart2.pack`, or
per-code packs `c<chart>/t<t>.pack`. How to produce or obtain the data, and
the running time and memory needed: see `snub-dodecahedron.md` and
`BUILDING.md` at the root of the repository.

The data is untrusted: it is decoded and checked natively, in parallel. The
solution tables exclude every `IModel` (every I-orbit within 6·10⁻¹⁶ of the
rational model); kernel-proved bridges (`Table.Valid.of_withTasksB`) turn
success into `CertificatesValid`.
-/

open Noperts Noperts.Pipeline Noperts.Pipeline.WikipediaSnub
open SnubDodecahedron
open Noperts.Pipeline.AtlasProjectiveSolutionTree
open Noperts.Pipeline.NativeExecutable

/-- A completed local-table audit found 64 chunks materially faster than 512
for these comparatively expensive exact-rational rows. -/
private def localTaskCount : Nat := 64

/-- Global tables are much larger, and chart 0's expensive projective-local
leaves occupy relatively few contiguous ranges.  Finer chunks improve tail
load balancing without imposing the local checker's tiny-chunk overhead. -/
private def globalTaskCount : Nat := 256

private def readArtifact (directory name : String) : IO String :=
  IO.FS.readFile s!"{directory}/{name}"

def main (args : List String) : IO Unit := do
  let (manifestPath, directory) ← match args with
    | [m, d] => pure (m, d)
    | _ => throw (IO.userError (
        "usage: constructSnubDodecahedron <tube manifest.txt> <chart directory>\n" ++
        "(checks everything; see snub-dodecahedron.md)"))
  let packDir := (System.FilePath.mk manifestPath).parent.getD "."
  let mut localTables : SharedLocalTables := #[]
  for line in ← IO.FS.lines manifestPath do
    if let filename :: _ := line.splitOn " " then
      if filename.endsWith ".pack" then
        let data ← IO.FS.readBinFile s!"{packDir}/{filename}"
        localTables := localTables.push (PackedLocalViewTree.decodePackedCodeTriangle data)
  -- Chart data: one pack per chart, or one per code triangle (decoded and
  -- concatenated behind a codeRoot row; decoding is untrusted either way).
  let perCode ← System.FilePath.pathExists s!"{directory}/c0/t0.pack"
  let mut chartData : Array (Array String) := #[]
  for c in [0 : 3] do
    if perCode then
      let mut packs : Array String := #[]
      for t in [0 : localTables.size] do
        packs := packs.push (← readArtifact directory s!"c{c}/t{t}.pack")
      chartData := chartData.push packs
    else
      chartData := chartData.push #[← readArtifact directory s!"chart{c}.pack"]
  IO.println s!"chart data: {if perCode then "per-code packs" else "one pack per chart"}"
  let decode (chart : CayleyAtlas.ChartIndex) (shared : SharedLocalTables)
      (data : Array String) : AtlasProjectiveSolutionTree.Table :=
    let table := if perCode then PackedSolutionTree.decodeCodeTables chart shared data
      else PackedSolutionTree.decodeTable chart shared data[0]!
    { table with chart, sharedLocal := shared }
  let globalTables : SharedLocalTables →
      CayleyAtlas.ChartIndex → AtlasProjectiveSolutionTree.Table :=
    fun shared =>
      ![decode 0 shared chartData[0]!,
        decode 1 shared chartData[1]!,
        decode 2 shared chartData[2]!,
        { FundamentalChart3.table with sharedLocal := shared }]
  let tables := globalTables localTables
  have hchart : ∀ chart, (tables chart).chart = chart := by
    intro chart; fin_cases chart <;> rfl
  have hshared : ∀ chart, (tables chart).sharedLocal = localTables := by
    intro chart; fin_cases chart <;> rfl
  -- The checks of `NativeExecutable.constructProof`, kept here so that the
  -- checked tables give `CertificatesValid`.
  let coverStart ← IO.monoNanosNow
  log "checking the view cover (code triangles cover T)"
  let cover : PLift (SnubDodecahedron.WedgeCover.coverValid = true) ←
    if h : SnubDodecahedron.WedgeCover.coverValid = true then pure ⟨h⟩
    else throw (IO.userError "the view cover is invalid")
  log s!"view cover valid ({(← IO.monoNanosNow) - coverStart} ns)"
  let checkedLocal ← checkLocalAll localTaskCount localTables
  let sharedValid (chart : CayleyAtlas.ChartIndex) :
      AtlasProjectiveSolutionTree.SharedLocalValid (tables chart).sharedLocal := by
    rw [hshared chart]; exact checkedLocal.down
  let valid0 ← checkGlobal "0" globalTaskCount (tables 0) (sharedValid 0)
  let valid1 ← checkGlobal "1" globalTaskCount (tables 1) (sharedValid 1)
  let valid2 ← checkGlobal "2" globalTaskCount (tables 2) (sharedValid 2)
  let valid3 ← checkGlobal "3" globalTaskCount (tables 3) (sharedValid 3)
  have hvalid : ∀ chart, (tables chart).Valid := by
    intro chart
    fin_cases chart
    · exact valid0.down
    · exact valid1.down
    · exact valid2.down
    · exact valid3.down
  have hcv : CertificatesValid := ⟨⟨tables, hchart, hvalid⟩, cover.down⟩
  log "constructed proof: no IModel (I-orbit within 6e-16 of the rational vertices) is Rupert"
  let _snub : ∀ V : Finset ℝ³, IsSnubDodecahedron V → IsNopert V :=
    isNopert_of_certificatesValid hcv
  let _wikipedia : IsNopert snubDodecahedron := isNopert_snubDodecahedron_of_certificatesValid hcv
  IO.println "instantiated: IsNopert V for every snub dodecahedron V (none is Rupert)"
