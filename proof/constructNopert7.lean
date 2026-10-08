import Noperthedron.Nopert7.NativeExecutable
import Noperthedron.Nopert7.PackedSolutionTree

/-!
Native executable that reads and checks the 7-vertex solid's certificate data
and constructs `¬ IsRupert Nopert7.verts` (K, `nopert_233`).

Data (decoded untrusted, checked natively in parallel):
- the identity-tube packs (`export_codetrees_pack`; `manifest.txt` lists one
  pack per code triangle, in `ViewCover.codeTriangles` order);
- the chart packs (`pack5d --chart C --per_code DIR`: `DIR/c<C>/t<T>.pack`,
  C = 0..3, T = 0..21), concatenated behind a `codeRoot` row
  (`PackedSolutionTree.decodeCodeTables`);
- the cap certificate (`capcert7.exe --export`, `cap-1_16.cert`).

Usage:
  constructNopert7 <tube manifest.txt> <chart directory> <cap.cert>
  constructNopert7 rows <tube manifest.txt> <chart> <job pack> [locals]
    (smoke test: decode one job pack (row 0 = the job's root) and check every
    row's `ValidAt` natively, reporting failures; with `locals`, also check
    the tube tables the job's tube rows use.)
  constructNopert7 local <tube manifest.txt> <index>   (check one tube table)
-/

open Noperthedron.PentagonalHexecontahedron
open Noperthedron.Nopert7
open Noperthedron.Nopert7.SolutionTree
open Noperthedron.Nopert7.NativeExecutable

private def threads : Nat := 12

def readLocalTables (manifestPath : String) : IO SharedLocalTables := do
  let packDir := (System.FilePath.mk manifestPath).parent.getD "."
  let mut localTables : SharedLocalTables := #[]
  for line in ← IO.FS.lines manifestPath do
    if let filename :: _ := line.splitOn " " then
      if filename.endsWith ".pack" then
        let data ← IO.FS.readBinFile s!"{packDir}/{filename}"
        localTables := localTables.push (PackedLocalViewTree.decodePackedCodeTriangle data)
  pure localTables

def rowKind : Row → String
  | .cayleySplit .. => "cayleySplit" | .viewSplit .. => "viewSplit"
  | .projective .. => "projective" | .projectiveGlobal .. => "projectiveGlobal"
  | .projectiveMixedGlobal .. => "projectiveMixedGlobal" | .symmetryLocal .. => "symmetryLocal"
  | .projectiveLocal .. => "projectiveLocal" | .symmetryTube .. => "symmetryTube"
  | .codeRoot .. => "codeRoot" | .radiusPrune .. => "radiusPrune" | .c3Prune .. => "c3Prune"
  | .regionRelax .. => "regionRelax" | .cayleySplitAt .. => "cayleySplitAt"
  | .mirrorPrune .. => "mirrorPrune" | .capLeaf .. => "capLeaf"

/-- Smoke test: check every row of one decoded job pack. -/
def rowsMode (manifestPath : String) (chart : CayleyAtlas.ChartIndex) (packPath : String)
    (locals : Bool) : IO Unit := do
  let shared ← readLocalTables manifestPath
  log s!"{shared.size} tube tables (roots {shared.map (·.root)})"
  let table := PackedSolutionTree.decodeTable chart shared (← IO.FS.readFile packPath)
  log s!"job pack: {table.size} rows, row 0 {rowKind (table.get 0)}"
  -- What the codeRoot row of `decodeCodeTables` needs of a job's row 0.
  let codes := (List.range ViewCover.codeTriangles.size).filter fun t =>
    decide ((table.get 0).region = .triangle (ViewCover.codeTriangles.getD t defaultCode).1
      (ViewCover.codeTriangles.getD t defaultCode).2)
  log s!"row 0: interval = rootInterval: {decide ((table.get 0).interval = AtlasPose.rootInterval ℚ)}, region = code triangle {codes}"
  let mut counts : Std.HashMap String Nat := {}
  for i in [0:table.size] do
    counts := counts.insert (rowKind (table.get i)) ((counts.getD (rowKind (table.get i)) 0) + 1)
  log s!"row kinds: {counts.toList}"
  let t0 ← IO.monoMsNow
  let chunk := table.size / threads + 1
  let tasks := (List.range threads).map fun k => Task.spawn fun _ =>
    (List.range chunk).filterMap fun j =>
      let i := k * chunk + j
      if validIxAtB table.chart table.get table.size table.sharedLocal i then none else some i
  let bad := (tasks.map Task.get).flatten
  log s!"rows checked in {(← IO.monoMsNow) - t0} ms: {bad.length} invalid"
  for i in bad.take 20 do
    log s!"  invalid row {i}: {rowKind (table.get i)}"
  if locals then
    let mut used : Std.HashSet Nat := {}
    for i in [0:table.size] do
      if let .symmetryTube _ _ s _ _ := table.get i then used := used.insert s
    for s in used.toList do
      if h : s < shared.size then
        let _ ← checkLocal s!"{s}" threads shared[s]
        log s!"tube table {s} valid"
  if bad.isEmpty then log "all rows valid" else throw (IO.userError "invalid rows")

def fullMode (manifestPath directory capPath : String) : IO Unit := do
  let cap := decodeCert (← IO.FS.lines capPath)
  log s!"cap: {cap.charts.length} charts"
  let capOk ← checkCap cap
  let localTables ← readLocalTables manifestPath
  unless localTables.size = ViewCover.codeTriangles.size do
    throw (IO.userError s!"{localTables.size} tube tables for {ViewCover.codeTriangles.size} code triangles")
  let mut chartData : Array (Array String) := #[]
  for c in [0:4] do
    let mut packs : Array String := #[]
    for t in [0:localTables.size] do
      packs := packs.push (← IO.FS.readFile s!"{directory}/c{c}/t{t}.pack")
    chartData := chartData.push packs
  let decode (shared : SharedLocalTables) (chart : CayleyAtlas.ChartIndex) : SolutionTree.Table :=
    { PackedSolutionTree.decodeCodeTables chart shared chartData[chart.val]! with
      chart, sharedLocal := shared }
  let checked ← constructProof threads threads localTables decode
    (by intro shared chart; rfl) (by intro shared chart; rfl)
  let _k : ¬ IsRupert verts := checked.down capOk.down
  IO.println "instantiated: ¬ IsRupert Nopert7.verts (the 7-vertex solid is not Rupert)"

def main (args : List String) : IO Unit := do
  match args with
  | ["rows", m, c, p] => rowsMode m (Fin.ofNat 4 c.toNat!) p false
  | ["rows", m, c, p, "locals"] => rowsMode m (Fin.ofNat 4 c.toNat!) p true
  | ["local", m, i] => do
      let shared ← readLocalTables m
      let k := i.toNat!
      if h : k < shared.size then
        let _ ← checkLocal s!"{k}" threads shared[k]
        log s!"tube table {k} valid"
      else throw (IO.userError "no such table")
  | [m, d, cap] => fullMode m d cap
  | _ => throw (IO.userError
      "usage: constructNopert7 <tube manifest.txt> <chart directory> <cap.cert>\n       constructNopert7 rows <tube manifest.txt> <chart> <job pack> [locals]")
