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

instance : Inhabited SplitTree := ⟨.leaf⟩
instance : Inhabited Cert := ⟨{ m := 0, dc := 0, tree := .leaf }⟩

def parseRat (s : String) : IO ℚ :=
  match s.splitOn "/" with
  | [a] => match a.toInt? with
    | some n => pure n
    | none => throw (IO.userError s!"not a rational: {s}")
  | [a, b] => match a.toInt?, b.toNat? with
    | some n, some d => if d = 0 then throw (IO.userError s!"zero denominator: {s}") else pure ((n : ℚ) / d)
    | _, _ => throw (IO.userError s!"not a rational: {s}")
  | _ => throw (IO.userError s!"not a rational: {s}")

def parseNat (s : String) : IO ℕ :=
  match s.toNat? with
  | some n => pure n
  | none => throw (IO.userError s!"not a natural number: {s}")

/-- `nt` then `nt` terms `i j k coef`. -/
def parsePoly (fs : List String) : IO SeptopertShell.Poly := do
  let nt ← parseNat (fs.headD "")
  let mut rest := fs.drop 1
  let mut p : SeptopertShell.Poly := []
  for _ in [0:nt] do
    let i ← parseNat (rest.getD 0 ""); let j ← parseNat (rest.getD 1 ""); let k ← parseNat (rest.getD 2 "")
    let c ← parseRat (rest.getD 3 "")
    p := ((i, j, k), c) :: p
    rest := rest.drop 4
  pure p.reverse

/-- A split tree in preorder: `L` (leaf), `S dim point`, `s dim` (split at the midpoint of the current box) or `g`
(shellcert4's geometric split in the third coordinate e = d - dc: the point 2 e_lo + dc). The points are recomputed
from the box `lo`, `hi` (untrusted parsing: `checkTree` checks every split point lies in its box). -/
partial def parseTree (lo hi : Array ℚ) (dc : ℚ) (fs : List String) : IO (SplitTree × List String) := do
  let sub (dim : ℕ) (mid : ℚ) (rest : List String) : IO (SplitTree × List String) := do
    if h : dim < 3 then
      let (l, r1) ← parseTree lo (hi.set! dim mid) dc rest
      let (r, r2) ← parseTree (lo.set! dim mid) hi dc r1
      pure (.split ⟨dim, h⟩ mid l r, r2)
    else throw (IO.userError s!"bad split dimension {dim}")
  match fs with
  | "L" :: rest => pure (.leaf, rest)
  | "S" :: d :: m :: rest => do let dim ← parseNat d; sub dim (← parseRat m) rest
  | "s" :: d :: rest => do let dim ← parseNat d; sub dim ((lo[dim]! + hi[dim]!) / 2) rest
  | "g" :: rest => sub 2 (2 * lo[2]! + dc) rest
  | _ => throw (IO.userError "bad tree")

def fin3 (n : ℕ) : IO (Fin 3) := if h : n < 3 then pure ⟨n, h⟩ else throw (IO.userError s!"not < 3: {n}")
def fin7 (n : ℕ) : IO (Fin 7) := if h : n < 7 then pure ⟨n, h⟩ else throw (IO.userError s!"not < 7: {n}")

def parseSlab (path : String) : IO SlabData := do
  let mut m : Std.HashMap String (List String) := {}
  let mut conds : Array (List String) := #[]
  for line in ← IO.FS.lines path do
    let fs := (line.splitOn " ").filter (· ≠ "")
    match fs with
    | "cond" :: rest => conds := conds.push rest
    | k :: rest => m := m.insert k rest
    | [] => pure ()
  let get (k : String) : IO (List String) := match m[k]? with
    | some v => pure v
    | none => throw (IO.userError s!"{path}: missing {k}")
  let box ← (← get "box").mapM parseRat
  let poly (k : String) : IO SeptopertShell.Poly := do parsePoly (← get k)
  let n0 ← (← get "N0").mapM parseRat
  let tri ← (← get "tri").mapM parseNat
  let view ← get "view"
  if conds.size ≠ 22 || box.length ≠ 4 || n0.length ≠ 9 || tri.length ≠ 21 then
    throw (IO.userError s!"{path}: bad sizes")
  let certs ← conds.mapM fun fs => do
    let mm ← parseNat (fs.getD 0 ""); let dc ← parseRat (fs.getD 1 "")
    let (t, rest) ← parseTree #[-box[0]!, -box[1]!, box[2]! - dc] #[box[0]!, box[1]!, box[3]! - dc] dc (fs.drop 2)
    unless rest.isEmpty do throw (IO.userError s!"{path}: trailing tree tokens")
    pure ({ m := mm, dc := dc, tree := t } : Cert)
  let triF ← (List.range 7).toArray.mapM fun k => do
    pure (← fin7 tri[3 * k]!, ← fin7 tri[3 * k + 1]!, ← fin7 tri[3 * k + 2]!)
  let n0a := n0.toArray; let ca := certs
  let v0 ← poly "v0"; let v1 ← poly "v1"; let v2 ← poly "v2"
  let c0 ← poly "c0"; let c1 ← poly "c1"; let c2 ← poly "c2"
  let vj ← fin3 (← parseNat (view.getD 0 ""))
  let vs ← parseRat (view.getD 1 "")
  pure {
    H0 := box[0]!, H1 := box[1]!, D0 := box[2]!, D1 := box[3]!
    s := ← poly "s", y := ← poly "y", z := ← poly "z"
    v := ![v0, v1, v2], cay := ![c0, c1, c2], t0 := ← poly "t0", t1 := ← poly "t1"
    N0 := fun i j => n0a[3 * i.val + j.val]!, m0 := ← parseRat ((← get "m0").headD "")
    tri := fun k => triF[k.val]!
    vj := vj, vs := vs
    vcert := ca[0]!, tcert := fun k e => ca[1 + 3 * k.val + e.val]! }

def main (args : List String) : IO UInt32 := do
  let mut bad := 0
  for path in args do
    let t0 ← IO.monoMsNow
    let D ← parseSlab path
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
