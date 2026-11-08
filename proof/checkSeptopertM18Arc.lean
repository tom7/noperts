import SeptopertM18.ArcCap

/-!
Diagnostic: checks only the SeptopertM18's arc cap certificate (`capcert-neo.cc --export`,
stage `arccert` of `search/septopert/rebuild.sh`) and instantiates the claim
(`SeptopertM18.arcHolds_of_cert`). The full verification, `constructSeptopertM18`, checks it too.

Usage: `checkSeptopertM18Arc <cert.txt> [diag]` (`diag`: per-chart results, sequential
over the charts).
-/

open Noperts.Pipeline
open Noperts.Pipeline.ArcCap
open SeptopertM18

def main (args : List String) : IO Unit := do
  let (file, diag) ← match args with
    | [f] => pure (f, false)
    | [f, "diag"] => pure (f, true)
    | _ => throw (IO.userError "usage: checkSeptopertM18Arc <cert.txt> [diag]")
  let c := decodeCert arcBlends (← IO.FS.lines file)
  IO.println s!"arc cap: {c.length} charts of {requiredCharts.length} required"
  if diag then
    let tasks := c.map fun e => Task.spawn fun _ => (e.1, chartCheck arcVerts apexFrame neoParams e.1 e.2)
    for task in tasks do
      let (id, ok) := task.get
      IO.println s!"chart {repr id}: {ok}"
  let t0 ← IO.monoMsNow
  if h : arcCertOkPar c = true then
    IO.println s!"valid arc cap certificate: {(← IO.monoMsNow) - t0} ms"
    let _holds : ArcHolds := arcHolds_of_cert c (arcCertOk_of_par c h)
    IO.println "instantiated: ArcHolds (SeptopertM18.arcHolds_of_cert)"
  else
    throw (IO.userError s!"the arc cap certificate is not valid ({(← IO.monoMsNow) - t0} ms)")
