import NeoSeptopert.ArcCap

/-!
Checks the NeoSeptopert's arc cap certificate (`capcert-neo.cc --export`, see
`nopert229/out/bottleneck/neo/capwork/exportall.sh`) and instantiates the claim
(`NeoSeptopert.arcHolds_of_cert`).

Usage: `checkNeoSeptopertArc <cert.txt> [diag]` (`diag`: per-chart results, sequential
over the charts).
-/

open Noperts.Pipeline
open Noperts.Pipeline.ArcCap
open NeoSeptopert

def main (args : List String) : IO Unit := do
  let (file, diag) ← match args with
    | [f] => pure (f, false)
    | [f, "diag"] => pure (f, true)
    | _ => throw (IO.userError "usage: checkNeoSeptopertArc <cert.txt> [diag]")
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
    IO.println "instantiated: ArcHolds (NeoSeptopert.arcHolds_of_cert)"
  else
    throw (IO.userError s!"the arc cap certificate is not valid ({(← IO.monoMsNow) - t0} ms)")
