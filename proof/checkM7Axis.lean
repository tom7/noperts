import M7.AxisCap

/-!
Checks the axis cap certificate of M7 (cap 2; exported by `m7cap/exportaxis.sh`) and
instantiates the claim `M7.AxisHolds` (`M7.axisHolds_of_cert`), which `M7.axis_not_rupert`
states.

Usage: `checkM7Axis <cert.txt> [diag]` (`diag`: per-chart results, sequential over the charts).
-/

open Noperts.Pipeline
open Noperts.Pipeline.ArcCap
open M7

def main (args : List String) : IO Unit := do
  let (file, diag) ← match args with
    | [f] => pure (f, false)
    | [f, "diag"] => pure (f, true)
    | _ => throw (IO.userError "usage: checkM7Axis <cert.txt> [diag]")
  let c := decodeCert arcBlends (← IO.FS.lines file)
  IO.println s!"M7 axis cap: {c.length} charts of {axisCharts.length} required"
  if diag then
    let tasks := c.map fun e => Task.spawn fun _ => (e.1, chartCheck axisVerts axisFrame axisParams e.1 e.2)
    for task in tasks do
      let (id, ok) := task.get
      IO.println s!"chart {repr id}: {ok}"
  let t0 ← IO.monoMsNow
  if h : axisCertOkPar c = true then
    IO.println s!"valid M7 axis cap certificate: {(← IO.monoMsNow) - t0} ms"
    let _holds : AxisHolds := axisHolds_of_cert c (axisCertOk_of_par c h)
    IO.println "instantiated: M7.AxisHolds"
  else
    throw (IO.userError s!"the M7 axis cap certificate is not valid ({(← IO.monoMsNow) - t0} ms)")
