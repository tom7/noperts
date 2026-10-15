import DeltoidalHexecontahedron.FundamentalChart3
import DeltoidalHexecontahedron.Decode
import DeltoidalHexecontahedron.NativeExecutable
import DeltoidalHexecontahedron.PackedSolutionTree
import DeltoidalHexecontahedron

/-!
Native executable that checks the deltoidal hexecontahedron's certificate
data and, if it is all valid, establishes `CertificatesValid`, and so
(`isNopert_of_certificatesValid`) that every deltoidal hexecontahedron is a
nopert (`DeltoidalHexecontahedron.lean`).

Usage:
  constructDeltoidalHexecontahedron <tube manifest.txt> <chart directory>
      <cap directory> <tie directory>
    Checks everything: the three cap certificates, the tie certificates, the
    view cover, every tube table and all four chart tables. On success it
    prints
      instantiated: IsNopert V for every deltoidal hexecontahedron V (none is Rupert)

The arguments: `manifest.txt` lists the tube packs in code order, next to
them; the chart directory holds `chart0.pack` through `chart2.pack`, or
per-code packs `c<chart>/t<t>.pack`; the cap directory holds `u0.cert`,
`ux.cert` and `u0_wide.cert`; the tie directory holds `dh-tie-data.txt`,
`nodes.txt` and the `n*_t*.cert` tie certificates. How to produce or obtain
the data, and the running time and memory needed: see
`deltoidal-hexecontahedron.md` and `BUILDING.md` at the root of the
repository.

The data is untrusted: it is decoded and checked natively, in parallel. The
solution tables exclude every centrally symmetric `IModel` whose exact
claims hold; the cap certificates give the cap claims for the exact solid
(`capsHold_of_certs`), and the tie certificates the tie nodes' claims
(`tiesHold_of_certs`). Kernel-proved bridges (`capsCheck_of_par`,
`tiesCheck_of_par`, `Table.Valid.of_withTasksB`) turn success into
`CertificatesValid`.
-/

open Noperts Noperts.Pipeline Noperts.Pipeline.Cap
open DeltoidalHexecontahedron
open DeltoidalHexecontahedron.AtlasProjectiveSolutionTree
open DeltoidalHexecontahedron.NativeExecutable
open DeltoidalHexecontahedron.Cap
open DeltoidalHexecontahedron.Tie
open DeltoidalHexecontahedron.DH
open DeltoidalHexecontahedron.Decode

private def localTaskCount : Nat := 64
private def globalTaskCount : Nat := 256

private def readArtifact (directory name : String) : IO String :=
  IO.FS.readFile s!"{directory}/{name}"

def main (args : List String) : IO Unit := do
  let (manifestPath, directory, capDir, tieDir) ← match args with
    | [m, d, c, t] => pure (m, d, c, t)
    | _ => throw (IO.userError (
        "usage: constructDeltoidalHexecontahedron <tube manifest.txt> <chart directory> " ++
        "<cap directory: u0.cert ux.cert u0_wide.cert> <tie directory: dh-tie-data.txt nodes.txt n*_t*.cert>\n" ++
        "(checks everything; see deltoidal-hexecontahedron.md)"))
  -- Caps.
  let mut caps : Array CapCert := #[]
  for name in ["u0.cert", "ux.cert", "u0_wide.cert"] do
    caps := caps.push (decodeCert (← readLines s!"{capDir}/{name}"))
  IO.println s!"caps: {caps.map (·.charts.length)} charts"
  let capsStart ← IO.monoMsNow
  if hcaps : capsCheckPar caps = true then
    IO.println s!"valid caps: {(← IO.monoMsNow) - capsStart} ms"
    -- Ties.
    let mut certFiles : Array (ℕ × ℕ × Array String) := #[]
    for entry in ← System.FilePath.readDir tieDir do
      let name := entry.fileName
      if name.startsWith "n" && name.endsWith ".cert" then
        match (((name.drop 1).dropEnd 5).toString).splitOn "_t" with
        | [n, tt] => certFiles := certFiles.push (n.toNat!, tt.toNat!, ← readLines entry.path.toString)
        | _ => pure ()
    let ties := decodeTies (← readLines s!"{tieDir}/dh-tie-data.txt") (← readLines s!"{tieDir}/nodes.txt") certFiles
    IO.println s!"ties: {ties.normals.size} normals, {certFiles.size} certificate files"
    let tiesStart ← IO.monoMsNow
    if hties : tiesCheckPar ties = true then
      IO.println s!"valid ties: {(← IO.monoMsNow) - tiesStart} ms"
      -- Tables.
      let packDir := (System.FilePath.mk manifestPath).parent.getD "."
      let mut localTables : SharedLocalTables := #[]
      for line in ← IO.FS.lines manifestPath do
        if let filename :: _ := line.splitOn " " then
          if filename.endsWith ".pack" then
            let data ← IO.FS.readBinFile s!"{packDir}/{filename}"
            localTables := localTables.push (PackedLocalViewTree.decodePackedCodeTriangle data)
      let perCode ← System.FilePath.pathExists s!"{directory}/c0/t0.pack"
      let mut chartData : Array (Array String) := #[]
      for c in [0 : 3] do
        if perCode then
          let mut packs : Array String := #[]
          for tt in [0 : localTables.size] do
            packs := packs.push (← readArtifact directory s!"c{c}/t{tt}.pack")
          chartData := chartData.push packs
        else
          chartData := chartData.push #[← readArtifact directory s!"chart{c}.pack"]
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
      -- The checks (`NativeExecutable`); the checked tables give
      -- `CertificatesValid`.
      let coverStart ← IO.monoNanosNow
      log "checking the view cover (code triangles cover T)"
      let cover : PLift (WedgeCover.coverValid = true) ←
        if h : WedgeCover.coverValid = true then pure ⟨h⟩
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
      have hcv : CertificatesValid :=
        ⟨⟨tables, hchart, hvalid⟩, cover.down, ⟨caps, capsCheck_of_par caps hcaps⟩,
          ⟨ties, tiesCheck_of_par ties hties⟩⟩
      let _dh : ∀ V : Finset ℝ³, IsDeltoidalHexecontahedron V → IsNopert V :=
        isNopert_of_certificatesValid hcv
      IO.println "instantiated: IsNopert V for every deltoidal hexecontahedron V (none is Rupert)"
    else
      throw (IO.userError "the tie certificates are not valid")
  else
    throw (IO.userError "the cap certificates are not valid")
