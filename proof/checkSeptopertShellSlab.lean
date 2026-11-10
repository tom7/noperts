import SeptopertShell

/-!
Native executable that checks slab certificates of the Septopert shell (`SeptopertShell.SlabData.check`) and, for
each valid one, instantiates `SeptopertShell.SlabData.isRupert_of_check`: every shape of the slab is Rupert.

Usage:
  checkSeptopertShellSlab FILE...

Each FILE is the untrusted data written by nopert229 `islandmap/bnd/shellcert4.cc` (environment `SC_LEAN=FILE`): one
item per line (`box`, the polynomials `s y z v0 v1 v2 c0 c1 c2 t0 t1`, `N0`, `m0`, `tri`, `view`, then 22 `cond` lines:
the view condition, then the triangle conditions of the inner vertices 0..6, each `m dc tree`, the tree in preorder
with `S dim point` and `L`).
-/

open SeptopertShell


def readSlab (path : String) : IO SlabData := do
  match parseSlab path (← IO.FS.lines path).toList with
  | .ok D => pure D
  | .error e => throw (IO.userError s!"{path}: {e}")

/-- `--profile FILE`: time the parts of the check (the integer data, the condition polynomials, then the bounds). -/
def profile (path : String) : IO Unit := do
  let D ← readSlab path
  let t0 ← IO.monoMsNow
  let C := D.core
  let w := (List.finRange 7).map fun k => ((List.finRange 3).map fun i => (D.WI C k i).length).foldl (· + ·) 0
  let w := w.foldl (· + ·) 0
  IO.println s!"integer data, WI terms {w}  ({(← IO.monoMsNow) - t0} ms)"
  let t1 ← IO.monoMsNow
  let cs := (List.finRange 7).flatMap fun k =>
    let Wk := D.WI C k
    (List.finRange 3).map fun e => D.condI C Wk k e
  let n := (cs.map List.length).foldl (· + ·) 0
  IO.println s!"21 conditions, {n} terms, built in {(← IO.monoMsNow) - t1} ms"
  let t2 ← IO.monoMsNow
  let ok := D.check
  IO.println s!"full check (rebuild + certify): {ok} in {(← IO.monoMsNow) - t2} ms"
  -- per-certificate timing: the root shift, then the whole certificate
  for k in List.finRange 7 do
    let Wk := D.WI C k
    for e in List.finRange 3 do
      let p := (D.condI C Wk k e).toPoly
      let c := D.tcert k e
      let t3 ← IO.monoMsNow
      let q := (SeptopertShell.Poly.divX2 p c.m).getD []
      let sh := SeptopertShell.Poly.shiftX2 q c.dc
      let n := sh.length
      let t4 ← IO.monoMsNow
      let r := SeptopertShell.checkCert D.H0 D.H1 D.D0 D.D1 p c
      IO.println s!"  cert {k} {e}: {p.length} terms, root shift -> {n} terms in {t4 - t3} ms, whole cert {r} in {(← IO.monoMsNow) - t4} ms"

def main (args : List String) : IO UInt32 := do
  if args.headD "" = "--profile" then profile (args.getD 1 ""); return 0
  let mut bad := 0
  for path in args do
    let t0 ← IO.monoMsNow
    let D ← readSlab path
    let t1 ← IO.monoMsNow
    if h : D.check = true then
      let t2 ← IO.monoMsNow
      let _thm : ∀ x : Fin 3 → ℝ, |x 0| ≤ (D.H0 : ℝ) → |x 1| ≤ (D.H1 : ℝ) → (D.D0 : ℝ) ≤ x 2 → x 2 ≤ (D.D1 : ℝ) →
          IsRupert (shellVerts (D.point x)) := fun x h0 h1 h2 h3 => D.isRupert_of_check h x h0 h1 h2 h3
      IO.println s!"{path}: read in {t1 - t0} ms, checked in {t2 - t1} ms; instantiated: every shape of the slab is Rupert"
    else
      let t2 ← IO.monoMsNow
      IO.println s!"{path}: CHECK FAILED ({t2 - t1} ms)"
      bad := bad + 1
  return if bad = 0 then 0 else 1
