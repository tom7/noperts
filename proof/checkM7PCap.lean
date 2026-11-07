import M7.PCap

/-!
Checks the P cap certificate of M7 (cap 3; the leaf lists of `capcert-m7 --frame P`, converted by
`h12cap/leaf2cert.py`, `m7cap/p3cert.sh`: the wedge's `M7/data/pcap-wp.cert` and the U cap's `M7/data/pcap-u.cert`, 1.5 MB)
and instantiates the claim `M7.PHolds` (`M7.pHolds_of_cert`), which `M7.pcap_not_rupert` states.

Usage: `checkM7PCap <cert.txt>... [diag]` (the files are concatenated; `diag`: per-chart results,
sequential over the charts).
-/

open Noperts.Pipeline
open Noperts.Pipeline.ArcCap
open M7

def main (args : List String) : IO Unit := do
  let (files, diag) := match args.reverse with
    | "diag" :: fs => (fs.reverse, true)
    | _ => (args, false)
  if files.isEmpty then throw (IO.userError "usage: checkM7PCap <cert.txt>... [diag]")
  let mut lines : Array String := #[]
  for f in files do
    lines := lines ++ (← IO.FS.lines f)
  let c := decodeCert arcBlends lines
  IO.println s!"M7 P cap: {c.length} charts of {pCharts.length} required"
  if diag then
    let tasks := c.map fun e => Task.spawn fun _ => (e.1, chartCheck pVerts pFrame pParams e.1 e.2)
    for task in tasks do
      let (id, ok) := task.get
      IO.println s!"chart {repr id}: {ok}"
  let t0 ← IO.monoMsNow
  if h : pcapCertOkPar c = true then
    IO.println s!"valid M7 P cap certificate: {(← IO.monoMsNow) - t0} ms"
    let _holds : PHolds := pHolds_of_cert c (pcapCertOk_of_par c h)
    IO.println "instantiated: M7.PHolds"
  else
    throw (IO.userError s!"the M7 P cap certificate is not valid ({(← IO.monoMsNow) - t0} ms)")
