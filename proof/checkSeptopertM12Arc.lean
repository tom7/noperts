import SeptopertM12.ArcCap

/-!
Checks the arc cap certificate of SeptopertM12 (cap 1: the U cap and the arc; exported by
`h12cap/exportm12.sh`) and instantiates the claim `SeptopertM12.ArcHolds`
(`SeptopertM12.arcHolds_of_cert`), which `SeptopertM12.arc_not_rupert` states.

Usage: `checkSeptopertM12Arc <cert.txt> [diag]` (`diag`: per-chart results, sequential over the charts).
-/

open Noperts.Pipeline
open Noperts.Pipeline.ArcCap
open SeptopertM12

def main (args : List String) : IO Unit := do
  let (file, diag) ← match args with
    | [f] => pure (f, false)
    | [f, "diag"] => pure (f, true)
    | _ => throw (IO.userError "usage: checkSeptopertM12Arc <cert.txt> [diag]")
  let c := decodeCert arcBlends (← IO.FS.lines file)
  IO.println s!"SeptopertM12 arc cap: {c.length} charts of {requiredCharts.length} required"
  if diag then
    let tasks := c.map fun e => Task.spawn fun _ => (e.1, chartCheck arcVerts apexFrame m12Params e.1 e.2)
    for task in tasks do
      let (id, ok) := task.get
      IO.println s!"chart {repr id}: {ok}"
  let t0 ← IO.monoMsNow
  if h : arcCertOkPar c = true then
    IO.println s!"valid SeptopertM12 arc cap certificate: {(← IO.monoMsNow) - t0} ms"
    let _holds : ArcHolds := arcHolds_of_cert c (arcCertOk_of_par c h)
    IO.println "instantiated: SeptopertM12.ArcHolds"
  else
    throw (IO.userError s!"the SeptopertM12 arc cap certificate is not valid ({(← IO.monoMsNow) - t0} ms)")
