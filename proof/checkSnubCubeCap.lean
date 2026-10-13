import Pipeline.KCapDecode

/-!
Diagnostic: decodes and checks the snub cube's cap certificate
(`search/sc/sccapcert.cc --export`) natively, per chart, with timings, then
the parallel check `KCert.checkPar` (which proves `KCert.check`, hence the
cap's claims `KCert.boxClaim` and `KCert.tubeClaim`).

Usage: `checkSnubCubeCap <sc.cert> [diag]` (`diag`: per-chart results).
-/

open Noperts.Pipeline Noperts.Pipeline.KCap

def kindName : Kind → String
  | .fe => "fe" | .face => "face" | .cone => "cone" | .tcone => "tcone"

def main (args : List String) : IO UInt32 := do
  let path := args.headD "sc.cert"
  let lines ← IO.FS.lines path
  let c := decodeKCert lines
  IO.println s!"{c.V.size} vertices, {c.charts.length} charts"
  if args.length > 1 then
    for (id, t) in c.charts do
      let s ← IO.monoMsNow
      let ok := c.chartCheck id t
      let e ← IO.monoMsNow
      IO.println s!"{kindName id.kind}:{id.side}:{id.axis}:{id.sign}: {ok} ({e - s} ms)"
  if h : c.checkPar = true then
    -- The check proves the cap's claims for the hull of the certificate's vertices.
    let _box : BoxClaim c := KCert.boxClaim c (KCert.check_of_par c h)
    let _tube : TubeClaim c := KCert.tubeClaim c (KCert.check_of_par c h)
    IO.println "valid: KCert.check, hence BoxClaim and TubeClaim for the certificate's solid"
    return 0
  else
    IO.println "INVALID"
    return 1
