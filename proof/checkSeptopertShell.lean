import SeptopertShell

/-!
Native executable that checks the certificate of the watertight Rupert shell around the Septopert island and, if it is
valid, instantiates `SeptopertShell.islandEnclosed_of_closureData`: `SeptopertShell.IslandEnclosed`, i.e. every
continuous path in the parameter space (P/A, C/A, E/A) from the Septopert Classic to (1, 0, 0) meets a set of Rupert
shapes.

Usage:
  checkSeptopertShell          (the certificate built into the library: `SeptopertShell.shellText`, data/shell.txt)
  checkSeptopertShell FILE     (another certificate file in the same format, e.g. a regenerated one)

The data is untrusted (`SeptopertShell.parseShell`; format in SeptopertShell/Parse.lean). The slab checks run as 32
parallel tasks (`ClosureData.checkPar`, `check_of_checkPar`).
-/

open SeptopertShell

def main (args : List String) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let text ← match args with
    | [] => pure shellText
    | path :: _ => IO.FS.readFile path
  let C ← match parseShell text with
    | .ok C => pure C
    | .error e => throw (IO.userError s!"bad certificate: {e}")
  let t1 ← IO.monoMsNow
  IO.println s!"read {C.faces.length} faces, {(C.faces.map (·.slabs.length)).foldl (· + ·) 0} slabs in {t1 - t0} ms"
  if hc : C.classicOk = true then
    if h : C.checkPar 32 = true then   -- the slab checks in 32 parallel tasks
      let t2 ← IO.monoMsNow
      let _thm : IslandEnclosed := islandEnclosed_of_closureData C (C.check_of_checkPar h) hc
      IO.println s!"checked in {t2 - t1} ms"
      IO.println "instantiated: IslandEnclosed (every path from the Septopert Classic to (1, 0, 0) in (P/A, C/A, E/A) meets certified Rupert shapes)"
      return 0
    else
      IO.println "CHECK FAILED"; return 1
  else
    IO.println "classicOk FAILED"; return 1
