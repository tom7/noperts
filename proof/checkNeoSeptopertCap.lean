import NeoSeptopert.CapsNative

/-!
Diagnostic: checks only the NeoSeptopert's cap certificate and instantiates the
cap theorem (`NeoSeptopert.capHolds_of_cert`; the region form is
`NeoSeptopert.cap_not_rupert`). The full verification, `constructNeoSeptopert`,
checks the cap certificate too.

Usage: `checkNeoSeptopertCap <cap.cert> [diag]` (`diag`: per-chart results).
-/

open Noperts.Pipeline
open Noperts.Pipeline.Cap
open NeoSeptopert

def main (args : List String) : IO Unit := do
  let (file, diag) ← match args with
    | [f] => pure (f, false)
    | [f, "diag"] => pure (f, true)
    | _ => throw (IO.userError "usage: checkNeoSeptopertCap <cap.cert> [diag]")
  let c := decodeCert (← IO.FS.lines file)
  IO.println s!"cap: {c.charts.length} charts, {c.verts.size} vertices, {c.wits.size} witnesses, mu0 {c.pr.mu0}"
  if diag then
    IO.println s!"frameCheck {Cap.frameCheck c.st}, chartList {c.charts.map (·.1) == chartList c.st c.pr c.zOf} ({(chartList c.st c.pr c.zOf).length}), tieCheck {c.tieCheck}, verts {decide (c.verts = solidVerts)}, frame {decide (c.st.x = capX) && decide (c.st.e1 = capE1) && decide (c.st.e2 = capE2)}"
    let tasks := c.charts.map fun e => Task.spawn fun _ => (e.1, chartCheck c e.1 e.2)
    for task in tasks do
      let (id, ok) := task.get
      IO.println s!"chart {repr id.kind} side {id.side} axis {id.axis} sign {id.sign}: {ok}"
  let t0 ← IO.monoMsNow
  if h : certOkPar c = true then
    IO.println s!"valid cap certificate: {(← IO.monoMsNow) - t0} ms"
    let _holds : CapHolds := capHolds_of_cert c (certOk_of_par c h)
    IO.println "instantiated: CapHolds (NeoSeptopert.capHolds_of_cert)"
  else
    throw (IO.userError s!"the cap certificate is not valid ({(← IO.monoMsNow) - t0} ms)")
