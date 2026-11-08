import SeptopertM12.PCap

/-!
Checks the P cap certificate of SeptopertM12 (cap 3; the leaf lists of `capcert-m12 --frame P`, converted by
`h12cap/leaf2cert.py`: the wedge's `SeptopertM12/data/pcap-wp.cert` and the U cap's `h12cap/cert-p3-u.txt`, 8 MB)
and instantiates the claim `SeptopertM12.PHolds` (`SeptopertM12.pHolds_of_cert`), which `SeptopertM12.pcap_not_rupert` states.

Usage: `checkSeptopertM12PCap <cert.txt>... [diag]` (the files are concatenated; `diag`: per-chart results,
sequential over the charts).
-/

open Noperts.Pipeline
open Noperts.Pipeline.ArcCap
open SeptopertM12

def main (args : List String) : IO Unit := do
  let (files, diag) := match args.reverse with
    | "diag" :: fs => (fs.reverse, true)
    | _ => (args, false)
  if files.isEmpty then throw (IO.userError "usage: checkSeptopertM12PCap <cert.txt>... [diag]")
  let mut lines : Array String := #[]
  for f in files do
    lines := lines ++ (← IO.FS.lines f)
  let c := decodeCert arcBlends lines
  IO.println s!"SeptopertM12 P cap: {c.length} charts of {pCharts.length} required"
  if diag then
    let tasks := c.map fun e => Task.spawn fun _ => (e.1, chartCheck pVerts pFrame pParams e.1 e.2)
    for task in tasks do
      let (id, ok) := task.get
      IO.println s!"chart {repr id}: {ok}"
  let t0 ← IO.monoMsNow
  if h : pcapCertOkPar c = true then
    IO.println s!"valid SeptopertM12 P cap certificate: {(← IO.monoMsNow) - t0} ms"
    let _holds : PHolds := pHolds_of_cert c (pcapCertOk_of_par c h)
    IO.println "instantiated: SeptopertM12.PHolds"
  else
    throw (IO.userError s!"the SeptopertM12 P cap certificate is not valid ({(← IO.monoMsNow) - t0} ms)")
