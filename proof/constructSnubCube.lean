import Pipeline.OctaNativeExecutable
import Pipeline.OctaPackedSolutionTree
import Pipeline.PackedLocalViewTree
import Pipeline.KCapDecode
import SnubCube

/-!
Native executable that checks the snub cube's certificate data and, if it is
all valid, establishes `SnubCube.CertificatesValid`, and so
(`SnubCube.isNopert_of_certificatesValid`) that every snub cube (Wikipedia's
coordinates, any similar copy, either chirality) is a nopert (`SnubCube.lean`).

Usage:
  constructSnubCube <tube manifest.txt> <chart directory> <cap certificate>

    Checks everything: the view cover, every tube table, all four chart
    tables and the cap certificate. On success it prints
      instantiated: IsNopert V for every snub cube V (none is Rupert)

The arguments: `manifest.txt` lists the tube packs in code order, next to
them (`export_codetrees_pack`); the chart directory holds the per-code packs
`c<chart>/t<t>.pack` (`pack5d --per_code`); the cap certificate is
`sccapcert --export`'s output. How to produce or obtain the data, and the
running time and memory needed: see `snub-cube.md` and `BUILDING.md` at the
root of the repository.

The data is untrusted: it is decoded and checked natively, in parallel. The
solution tables exclude every `OModel` (every O-orbit within 6·10⁻¹⁶ of the
rational model) whose hull satisfies the cap claims; the cap certificate
proves the cap claims for the exact solid (`SnubCube.capsHold_snubOModel`).
Kernel-proved bridges (`Table.Valid.of_withTasksB`, `KCert.check_of_par`)
turn success into `CertificatesValid`.

The C++ code that finds the certificates is in `search/sc`. It does not need
to be trusted; a bug there would just result in certificates that Lean
rejects.
-/

open Noperts Noperts.Pipeline Noperts.Pipeline.KCap
open SnubCube
open Noperts.Pipeline.OctaNativeExecutable

private def localTaskCount : Nat := 64
private def globalTaskCount : Nat := 256

private def readArtifact (directory name : String) : IO String :=
  IO.FS.readFile s!"{directory}/{name}"

def main (args : List String) : IO Unit := do
  let (manifestPath, directory, capPath) ← match args with
    | [m, d, c] => pure (m, d, c)
    | _ => throw (IO.userError (
        "usage: constructSnubCube <tube manifest.txt> <chart directory> <cap certificate>\n" ++
        "(checks everything; see snub-cube.md)"))
  let packDir := (System.FilePath.mk manifestPath).parent.getD "."
  -- The cap certificate.
  let cert := decodeKCert (← IO.FS.lines capPath)
  log s!"cap certificate: {cert.V.size} vertices, {cert.charts.length} charts"
  let capStart ← IO.monoNanosNow
  let capOk : PLift (cert.check = true ∧ certMatches cert = true) ←
    if hm : certMatches cert = true then
      if h : cert.checkPar = true then pure ⟨⟨KCert.check_of_par cert h, hm⟩⟩
      else throw (IO.userError "the cap certificate is invalid")
    else throw (IO.userError "the cap certificate's frame, parameters or vertices are not the snub cube's")
  log s!"valid cap certificate ({((← IO.monoNanosNow) - capStart) / 1000000} ms)"
  -- The tube tables.
  let mut localTables : OctaSolutionTree.SharedLocalTables := #[]
  for line in ← IO.FS.lines manifestPath do
    if let filename :: _ := line.splitOn " " then
      if filename.endsWith ".pack" then
        let data ← IO.FS.readBinFile s!"{packDir}/{filename}"
        localTables := localTables.push (PackedLocalViewTree.decodePackedCodeTriangle data)
  -- The chart tables: one pack per code triangle, concatenated behind a codeRoot row.
  let mut chartData : Array (Array String) := #[]
  for c in [0 : 4] do
    let mut packs : Array String := #[]
    for t in [0 : localTables.size] do
      packs := packs.push (← readArtifact directory s!"c{c}/t{t}.pack")
    chartData := chartData.push packs
  let decode (chart : CayleyAtlas.ChartIndex) (shared : OctaSolutionTree.SharedLocalTables)
      (data : Array String) : OctaSolutionTree.Table :=
    { OctaPackedSolutionTree.decodeCodeTables chart shared data with chart, sharedLocal := shared }
  let tables : CayleyAtlas.ChartIndex → OctaSolutionTree.Table :=
    ![decode 0 localTables chartData[0]!, decode 1 localTables chartData[1]!,
      decode 2 localTables chartData[2]!, decode 3 localTables chartData[3]!]
  have hchart : ∀ chart, (tables chart).chart = chart := by
    intro chart; fin_cases chart <;> rfl
  have hshared : ∀ chart, (tables chart).sharedLocal = localTables := by
    intro chart; fin_cases chart <;> rfl
  let coverStart ← IO.monoNanosNow
  log "checking the view cover (code triangles cover the Oh chamber)"
  let cover : PLift (octaCoverValid = true) ←
    if h : octaCoverValid = true then pure ⟨h⟩
    else throw (IO.userError "the view cover is invalid")
  log s!"view cover valid ({(← IO.monoNanosNow) - coverStart} ns)"
  let checkedLocal ← checkLocalAll localTaskCount localTables
  let sharedValid (chart : CayleyAtlas.ChartIndex) :
      OctaSolutionTree.SharedLocalValid (tables chart).sharedLocal := by
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
  have hcv : CertificatesValid :=
    ⟨⟨tables, hchart, hvalid⟩, cover.down, cert, capOk.down.1, capOk.down.2⟩
  log "constructed proof: the exact snub cube's model is not Rupert"
  let _snub : ∀ V : Finset ℝ³, IsSnubCube V → IsNopert V := isNopert_of_certificatesValid hcv
  let _wikipedia : IsNopert snubCube := isNopert_snubCube_of_certificatesValid hcv
  IO.println "instantiated: IsNopert V for every snub cube V (none is Rupert)"
