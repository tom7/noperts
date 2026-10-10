import Nopert231.FundamentalChart3
import Nopert231.NativeExecutable
import Nopert231.PackedSolutionTree
import Nopert231

/-!
Native executable that reads and checks the exact certificate data for
candidate #231, then establishes `CertificatesValid` and so
`isNopert_of_certificatesValid`: every `C5Model` (fivefold-symmetric
polyhedron within 6·10⁻¹⁶ of the rational model), including the exact model
`exactVerts` and idealized #231, is a nopert (`Nopert231.lean`).

The solution tables (tube packs and chart packs) are decoded (untrusted) and
checked natively, in parallel, as in `NativeExecutable.constructProof`. This
is analogous to `constructValidTable`: the expensive Boolean checks run as
parallel native code, while kernel-proved bridge theorems turn success into
`CertificatesValid`.

Usage:
  constructNopert231 <tube manifest.txt> <chart directory>
The manifest lists the identity-tube code packs in code order; the chart
directory holds chart0.pack through chart2.pack, or per-code packs
c<chart>/t<t>.pack (pack5d --per_code).
-/

open Noperts
open Nopert231
open Nopert231.AtlasProjectiveSolutionTree
open Nopert231.NativeExecutable

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
        "usage: constructNopert231 <code-pack manifest.txt> <chart directory>; " ++
        "the manifest lists the identity-tube code packs in code order, and the " ++
        "directory holds chart0.pack through chart2.pack, or per-code packs " ++
        "c<chart>/t<t>.pack (C++ pack5d --per_code)"))
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
  have hcv : CertificatesValid := ⟨tables, hchart, hvalid⟩
  log "constructed proof: no C5Model (fivefold-symmetric polyhedron within 6e-16 of the rational vertices) is Rupert"
  let _all : ∀ P : C5Model, IsNopert P.verts := isNopert_of_certificatesValid hcv
  -- The verified model (exact rotations of the rational seeds) and idealized
  -- #231 (exactly planar quads, `Ideal231.quad_planar`).
  let _exact : IsNopert exactVerts := isNopert_exactVerts_of_certificatesValid hcv
  let _ideal : IsNopert Ideal231.model.verts := isNopert_ideal231_of_certificatesValid hcv
  IO.println ("instantiated: IsNopert P.verts for every C5Model P, including the exact " ++
    "model and idealized #231 (none is Rupert)")
