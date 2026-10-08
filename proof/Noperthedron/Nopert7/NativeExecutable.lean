module

public import Noperthedron.Nopert7.IsNotRupert
public import Noperthedron.Nopert7.CapsNative
public import Noperthedron.PentagonalHexecontahedron.SparseLocalViewTree

@[expose] public section

/-!
# Native executable proof construction for the 7-vertex solid

The DH's `NativeExecutable` re-targeted to K: a release-mode program checks the
shared identity-tube tables and the four chart tables in parallel (data-only,
untrusted decoders) and keeps the semantic validity proofs in `PLift`;
`constructProof` returns `CapOk → ¬ IsRupert verts`, and the cap certificate
check (`CapsNative.certOkPar`, `certOk_of_par`) supplies `CapOk`. The view
cover needs no native check (`ViewCover.coverValid_eq` is kernel-checked).
-/

namespace Noperthedron.Nopert7.NativeExecutable

open Noperthedron.PentagonalHexecontahedron
open AtlasProjectiveLocalViewTree
open SparseLocalViewTree
open SolutionTree

def log (message : String) : IO Unit := do
  IO.println message
  (← IO.getStdout).flush

/-- Wait for row-chunk tasks, reporting progress; fail on the first invalid chunk. -/
def waitChunks (what : String) (size taskCount : Nat) (tasks : List (Task Bool)) : IO Unit := do
  let start ← IO.monoNanosNow
  let chunkSize := size / taskCount + 1
  let total := tasks.length
  let progressEvery := max 1 (total / 16)
  let mut pending := tasks.zipIdx.map fun (task, index) =>
    task.map (sync := true) fun valid => (index, valid)
  let mut completed := 0
  let mut checkedRows := 0
  while h : 0 < pending.length do
    let ((index, valid), remaining) ← IO.waitAny' pending h
    pending := remaining
    let first := index * chunkSize
    unless valid do
      throw (IO.userError
        s!"{what} is invalid in rows [{first}, {min size (first + chunkSize)})")
    let rowCount := if first < size then min chunkSize (size - first) else 0
    completed := completed + 1
    checkedRows := checkedRows + rowCount
    if completed % progressEvery = 0 || completed = total then
      let now ← IO.monoNanosNow
      log s!"{what}: {checkedRows}/{size} rows in {completed}/{total} tasks ({(now - start) / 1000000} ms)"

/-- Check one sparse shared-local table and return its validity proof. -/
def checkLocal (label : String) (taskCount : Nat)
    (table : AtlasProjectiveLocalViewTree.Table) : IO (PLift table.Valid) := do
  log s!"checking local {label}: {table.size} rows (root {table.root})"
  let tasks := sparseTableTasks table taskCount
  waitChunks s!"local {label}" table.size taskCount tasks
  if h : sparseTableValidWithTasksB table taskCount tasks = true then
    have h' : sparseTableValidWithTasksB table taskCount
        (sparseTableTasks table taskCount) = true := by
      simpa only [tasks] using h
    pure ⟨Table.Valid.of_sparseWithTasksB h'⟩
  else
    throw (IO.userError s!"local table {label} is not valid")

/-- Check the shared-local tables from index `k` on. -/
partial def checkLocalFrom (taskCount : Nat) (tables : SharedLocalTables) (k : Nat)
    (hk : ∀ i (h : i < tables.size), i < k → tables[i].Valid) :
    IO (PLift (SharedLocalValid tables)) := do
  if hlt : k < tables.size then
    let checked ← checkLocal s!"{k}" taskCount tables[k]
    checkLocalFrom taskCount tables (k + 1) (fun i h hik => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hik with h' | h'
      · exact hk i h h'
      · subst h'
        exact checked.down)
  else
    pure ⟨fun i h => hk i h (by omega)⟩

def checkLocalAll (taskCount : Nat) (tables : SharedLocalTables) :
    IO (PLift (SharedLocalValid tables)) :=
  checkLocalFrom taskCount tables 0 (fun _ _ h => absurd h (Nat.not_lt_zero _))

/-- Check one chart table (with the already checked shared-local tables). -/
def checkGlobal (label : String) (taskCount : Nat) (table : SolutionTree.Table)
    (hshared : SharedLocalValid table.sharedLocal) : IO (PLift table.Valid) := do
  log s!"checking chart {label}: {table.size} rows"
  let tasks := tableCoreTasks table taskCount
  waitChunks s!"chart {label}" table.size taskCount tasks
  if h : tableCoreValidWithTasksB table taskCount tasks = true then
    have h' : tableCoreValidWithTasksB table taskCount (tableCoreTasks table taskCount) = true := by
      simpa only [tasks] using h
    pure ⟨Table.Valid.of_withTasksB hshared h'⟩
  else
    throw (IO.userError s!"chart table {label} is not valid (root row or a row past the tasks)")

/-- The checked chart tables. -/
structure CheckedChartTables where
  tables : CayleyAtlas.ChartIndex → SolutionTree.Table
  charts : ∀ chart, (tables chart).chart = chart
  valid : ∀ chart, (tables chart).Valid

theorem CheckedChartTables.notRupert (checked : CheckedChartTables) :
    CapOk → ¬ IsRupert verts :=
  fun hcap => not_rupert_of_valid_tables checked.tables checked.charts checked.valid hcap

/-- Check all tables and construct `CapOk → ¬ IsRupert verts`. The chart
tables are supplied as a function of the checked shared-local tables; the two
equations keep a wrapper from checking rows under the wrong chart or tubes. -/
def constructProof (localTaskCount globalTaskCount : Nat)
    (localTables : SharedLocalTables)
    (globalTables : SharedLocalTables → CayleyAtlas.ChartIndex → SolutionTree.Table)
    (hchart : ∀ shared chart, (globalTables shared chart).chart = chart)
    (hshared : ∀ shared chart, (globalTables shared chart).sharedLocal = shared) :
    IO (PLift (CapOk → ¬ IsRupert verts)) := do
  let checkedLocal ← checkLocalAll localTaskCount localTables
  let shared := localTables
  have sharedValid : SharedLocalValid shared := checkedLocal.down
  have hs : ∀ chart, SharedLocalValid (globalTables shared chart).sharedLocal := by
    intro chart
    rw [hshared shared chart]
    exact sharedValid
  let valid0 ← checkGlobal "0" globalTaskCount (globalTables shared 0) (hs 0)
  let valid1 ← checkGlobal "1" globalTaskCount (globalTables shared 1) (hs 1)
  let valid2 ← checkGlobal "2" globalTaskCount (globalTables shared 2) (hs 2)
  let valid3 ← checkGlobal "3" globalTaskCount (globalTables shared 3) (hs 3)
  let checked : CheckedChartTables := {
    tables := globalTables shared
    charts := hchart shared
    valid := by
      intro chart
      fin_cases chart
      · exact valid0.down
      · exact valid1.down
      · exact valid2.down
      · exact valid3.down }
  log "constructed: CapOk → ¬ IsRupert verts"
  pure ⟨checked.notRupert⟩

/-- Check a cap certificate (`capcert7.exe --export`) natively and return `CapOk`. -/
def checkCap (c : Cap.CapCert) : IO (PLift CapOk) := do
  let t0 ← IO.monoMsNow
  if h : certOkPar c = true then
    log s!"valid cap certificate: {(← IO.monoMsNow) - t0} ms"
    pure ⟨⟨c, certOk_of_par c h⟩⟩
  else
    throw (IO.userError "the cap certificate is not valid")

end Noperthedron.Nopert7.NativeExecutable
