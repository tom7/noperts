module

public import DeltoidalHexecontahedron.IsNotRupert
public import Pipeline.SparseLocalViewTree

@[expose] public section

/-!
# Native checks of the certificate tables

The native checkers that `constructDeltoidalHexecontahedron` runs: a
release-mode program checks the data-only local and global tables in
parallel, then keeps the kernel-proved semantic validity witnesses in
`PLift`, from which it builds `CertificatesValid`.

Keeping the proof witnesses in `PLift` lets ordinary `IO` code sequence checks
and report useful errors. Proof fields are erased by native code generation;
their correctness comes from the specifications of the Boolean checkers.
-/

open Noperts Noperts.Pipeline

namespace DeltoidalHexecontahedron.NativeExecutable

variable {P : CyclicModel}

open AtlasProjectiveLocalViewTree
open SparseLocalViewTree

def log (message : String) : IO Unit := do
  IO.println message
  (← IO.getStdout).flush

/-- Check one sparse shared-local table with native worker tasks and return its
semantic validity proof. -/
def checkLocal (label : String) (taskCount : Nat)
    (table : AtlasProjectiveLocalViewTree.Table) : IO (PLift table.Valid) := do
  let start ← IO.monoNanosNow
  log s!"checking local {label}: {table.size} rows in {taskCount} native tasks"
  let chunkSize := table.size / taskCount + 1
  let tasks := sparseTableTasks table taskCount
  let total := tasks.length
  let progressEvery := max 1 (total / 16)
  let mut pending := tasks.zipIdx.map fun (task, index) =>
    task.map (sync := true) fun valid => (index, valid)
  let mut completed := 0
  let mut checkedRows := 0
  while h : 0 < pending.length do
    let ((index, valid), remaining) ← IO.waitAny' pending h
    pending := remaining
    unless valid do
      let first := index * chunkSize
      let afterLast := min table.size (first + chunkSize)
      throw (IO.userError (s!"local table {label} is invalid in rows " ++
        s!"[{first}, {afterLast})"))
    let first := index * chunkSize
    let rowCount := if first < table.size then
      min chunkSize (table.size - first)
    else 0
    completed := completed + 1
    checkedRows := checkedRows + rowCount
    if completed % progressEvery = 0 || completed = total then
      let now ← IO.monoNanosNow
      log (s!"local {label}: {checkedRows}/{table.size} rows checked " ++
        s!"in {completed}/{total} completed tasks " ++
        s!"({(now - start) / 1000000} ms)")
  if h : sparseTableValidWithTasksB table taskCount tasks = true then
    let finish ← IO.monoNanosNow
    log s!"valid local {label}: {(finish - start) / 1000000} ms"
    have h' : sparseTableValidWithTasksB table taskCount
        (sparseTableTasks table taskCount) = true := by
      simpa only [tasks] using h
    pure ⟨Table.Valid.of_sparseWithTasksB h'⟩
  else
    throw (IO.userError s!"local table {label} is not valid")

/-- Check the shared-local (identity-tube) tables from index `k` on,
threading the validity proofs of the tables already checked. -/
partial def checkLocalFrom (taskCount : Nat)
    (tables : AtlasProjectiveSolutionTree.SharedLocalTables) (k : Nat)
    (hk : ∀ i (h : i < tables.size), i < k → tables[i].Valid) :
    IO (PLift (AtlasProjectiveSolutionTree.SharedLocalValid tables)) := do
  if hlt : k < tables.size then
    let checked ← checkLocal s!"{k}" taskCount tables[k]
    checkLocalFrom taskCount tables (k + 1) (fun i h hik => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hik with h' | h'
      · exact hk i h h'
      · subst h'
        exact checked.down)
  else
    pure ⟨fun i h => hk i h (by omega)⟩

/-- Check every shared-local table (one per code triangle). -/
def checkLocalAll (taskCount : Nat)
    (tables : AtlasProjectiveSolutionTree.SharedLocalTables) :
    IO (PLift (AtlasProjectiveSolutionTree.SharedLocalValid tables)) :=
  checkLocalFrom taskCount tables 0 (fun _ _ h => absurd h (Nat.not_lt_zero _))

/-- Check one data-only global chart table after attaching the already checked
shared-local tables. -/
def checkGlobal (label : String) (taskCount : Nat)
    (table : AtlasProjectiveSolutionTree.Table)
    (hshared : AtlasProjectiveSolutionTree.SharedLocalValid table.sharedLocal) :
    IO (PLift table.Valid) := do
  let start ← IO.monoNanosNow
  log s!"checking chart {label}: {table.size} rows in {taskCount} native tasks"
  let chunkSize := table.size / taskCount + 1
  let tasks := AtlasProjectiveSolutionTree.tableCoreTasks table taskCount
  let total := tasks.length
  let progressEvery := max 1 (total / 16)
  let mut pending := tasks.zipIdx.map fun (task, index) =>
    task.map (sync := true) fun valid => (index, valid)
  let mut completed := 0
  let mut checkedRows := 0
  while h : 0 < pending.length do
    let ((index, valid), remaining) ← IO.waitAny' pending h
    pending := remaining
    unless valid do
      let first := index * chunkSize
      let afterLast := min table.size (first + chunkSize)
      throw (IO.userError (s!"chart {label} is invalid in rows " ++
        s!"[{first}, {afterLast})"))
    let first := index * chunkSize
    let rowCount := if first < table.size then
      min chunkSize (table.size - first)
    else 0
    completed := completed + 1
    checkedRows := checkedRows + rowCount
    if completed % progressEvery = 0 || completed = total then
      let now ← IO.monoNanosNow
      log (s!"chart {label}: {checkedRows}/{table.size} rows checked " ++
        s!"in {completed}/{total} completed tasks " ++
        s!"({(now - start) / 1000000} ms)")
  if h : AtlasProjectiveSolutionTree.tableCoreValidWithTasksB
      table taskCount tasks = true then
    let finish ← IO.monoNanosNow
    log s!"valid chart {label}: {(finish - start) / 1000000} ms"
    have h' : AtlasProjectiveSolutionTree.tableCoreValidWithTasksB
        table taskCount
        (AtlasProjectiveSolutionTree.tableCoreTasks table taskCount) = true := by
      simpa only [tasks] using h
    pure ⟨AtlasProjectiveSolutionTree.Table.Valid.of_withTasksB hshared h'⟩
  else
    throw (IO.userError s!"global chart table {label} is not valid")

end DeltoidalHexecontahedron.NativeExecutable

end
