import Septopert.NativeExecutable
import Septopert.PackedSolutionTree

/-!
Native executable that reads and checks the 7-vertex solid's certificate data
and constructs `¬ IsRupert Septopert.verts`.

Data (decoded untrusted, checked natively in parallel):
- the identity-tube packs (`export_codetrees_pack`; `manifest.txt` lists one
  pack per code triangle, in `ViewCover.codeTriangles` order);
- the chart packs (`pack5d --chart C --per_code DIR`: `DIR/c<C>/t<T>.pack`,
  C = 0..3, T = 0..21), concatenated behind a `codeRoot` row
  (`PackedSolutionTree.decodeCodeTablesLazy`: each pack is kept as bytes with
  a row/interval offset index and rows are decoded on demand; the charts are
  loaded, checked and dropped one at a time);
- the cap certificate (`capcert_septopert.exe --export`, `cap-1_16.cert`).

Worker threads: the runtime's default (hardware threads); set `LEAN_NUM_THREADS`
to use fewer. Each table is checked in 256 row chunks.

Usage:
  constructSeptopert <tube manifest.txt> <chart directory> <cap.cert>
  constructSeptopert rows <tube manifest.txt> <chart> <job pack> [locals]
    (smoke test: decode one job pack (row 0 = the job's root) and check every
    row's `ValidAt` natively, reporting failures; with `locals`, also check
    the tube tables the job's tube rows use.)
  constructSeptopert local <tube manifest.txt> <index>   (check one tube table)
  constructSeptopert chart <tube manifest.txt> <chart directory> <chart>
    (smoke test: load one chart's code packs and check all its rows and its
    root, as the full run does, without checking the tube tables.)
-/

open Noperts.Pipeline
open Septopert
open Septopert.SolutionTree
open Septopert.NativeExecutable

/-- Row chunks per table: many more than worker threads, so that expensive
subtrees (contiguous row ranges) do not leave threads idle. The number of
worker threads is the runtime's (hardware threads, or `LEAN_NUM_THREADS`). -/
private def chunks : Nat := 256

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
  let t0 ← IO.monoMsNow
  let data ← IO.FS.readBinFile packPath
  let table ← IO.lazyPure fun _ => PackedSolutionTree.decodeTableLazy chart shared data
  log s!"job pack: {table.size} rows, row 0 {rowKind (table.get 0)} (read and indexed in {(← IO.monoMsNow) - t0} ms)"
  -- What the codeRoot row of `decodeCodeTables` needs of a job's row 0.
  let codes := (List.range ViewCover.codeTriangles.size).filter fun t =>
    decide ((table.get 0).region = .triangle (ViewCover.codeTriangles.getD t defaultCode).1
      (ViewCover.codeTriangles.getD t defaultCode).2)
  log s!"row 0: interval = rootInterval: {decide ((table.get 0).interval = AtlasPose.rootInterval ℚ)}, region = code triangle {codes}"
  let mut counts : Std.HashMap String Nat := {}
  for i in [0:table.size] do
    let kind := rowKind (table.get i)
    counts := counts.insert kind ((counts.getD kind 0) + 1)
  log s!"row kinds: {counts.toList}"
  let t0 ← IO.monoMsNow
  let chunk := table.size / chunks + 1
  let tasks := (List.range chunks).map fun k => Task.spawn fun _ =>
    (List.range chunk).filterMap fun j =>
      let i := k * chunk + j
      if validIxAtB table.chart table.get table.size table.sharedLocal i then none else some i
  let bad := (← tasks.mapM fun task => (IO.wait task : IO _)).flatten
  log s!"rows checked in {(← IO.monoMsNow) - t0} ms: {bad.length} invalid"
  for i in bad.take 20 do
    log s!"  invalid row {i}: {rowKind (table.get i)}"
  if locals then
    let mut used : Std.HashSet Nat := {}
    for i in [0:table.size] do
      if let .symmetryTube _ _ s _ _ := table.get i then used := used.insert s
    for s in used.toList do
      if h : s < shared.size then
        let _ ← checkLocal s!"{s}" chunks shared[s]
        log s!"tube table {s} valid"
  if bad.isEmpty then log "all rows valid" else throw (IO.userError "invalid rows")

/-- Read chart `chart`'s per-code packs (`DIR/c<C>/t<T>.pack`) as bytes and
index them (in parallel); rows are decoded on demand
(`PackedSolutionTree.decodeCodeTablesLazy`). -/
def loadChart (directory : String) (codes : Nat) (shared : SharedLocalTables)
    (chart : CayleyAtlas.ChartIndex) :
    IO {table : SolutionTree.Table // table.chart = chart ∧ table.sharedLocal = shared} := do
  let t0 ← IO.monoMsNow
  let mut tasks : Array (Task PackedSolutionTree.LazyPack) := #[]
  for t in [0:codes] do
    let data ← IO.FS.readBinFile s!"{directory}/c{chart.val}/t{t}.pack"
    tasks := tasks.push (Task.spawn fun _ => PackedSolutionTree.LazyPack.index chart data)
  let packs ← tasks.mapM fun task => (IO.wait task : IO _)
  let table := PackedSolutionTree.decodeCodeTablesLazy chart shared packs
  log s!"chart {chart}: {codes} packs, {table.size} rows, read and indexed in {(← IO.monoMsNow) - t0} ms"
  pure ⟨table, rfl, rfl⟩

/-- Smoke test: load one chart's code packs and run the chart check of
`checkGlobal` (all rows and the root), without checking the tube tables. -/
def chartMode (manifestPath directory : String) (chart : CayleyAtlas.ChartIndex) : IO Unit := do
  let shared ← readLocalTables manifestPath
  log s!"{shared.size} tube tables"
  let table := (← loadChart directory shared.size shared chart).1
  log s!"checking chart {chart}: {table.size} rows"
  let tasks := tableCoreTasks table chunks
  waitChunks s!"chart {chart}" table.size chunks tasks
  if tableCoreValidWithTasksB table chunks tasks then
    log s!"chart {chart}: all {table.size} rows valid (and the root)"
  else throw (IO.userError "invalid chart table")

def fullMode (manifestPath directory capPath : String) : IO Unit := do
  let cap := decodeCert (← IO.FS.lines capPath)
  log s!"cap: {cap.charts.length} charts"
  let capOk ← checkCap cap
  let localTables ← readLocalTables manifestPath
  unless localTables.size = ViewCover.codeTriangles.size do
    throw (IO.userError s!"{localTables.size} tube tables for {ViewCover.codeTriangles.size} code triangles")
  let checked ← constructProof chunks chunks localTables
    (loadChart directory localTables.size)
  let _k : ¬ IsRupert verts := checked.down capOk.down
  IO.println "instantiated: ¬ IsRupert Septopert.verts (the Septopert is not Rupert)"

def main (args : List String) : IO Unit := do
  match args with
  | ["rows", m, c, p] => rowsMode m (Fin.ofNat 4 c.toNat!) p false
  | ["rows", m, c, p, "locals"] => rowsMode m (Fin.ofNat 4 c.toNat!) p true
  | ["local", m, i] => do
      let shared ← readLocalTables m
      let k := i.toNat!
      if h : k < shared.size then
        let _ ← checkLocal s!"{k}" chunks shared[k]
        log s!"tube table {k} valid"
      else throw (IO.userError "no such table")
  | ["chart", m, d, c] => chartMode m d (Fin.ofNat 4 c.toNat!)
  | [m, d, cap] => fullMode m d cap
  | _ => throw (IO.userError
      "usage: constructSeptopert <tube manifest.txt> <chart directory> <cap.cert>\n       constructSeptopert rows <tube manifest.txt> <chart> <job pack> [locals]")
