import SeptopertShell

/-!
Native executable that checks the certificate of the watertight Rupert shell around the Septopert island and, if it is
valid, instantiates `SeptopertShell.islandEnclosed_of_closureData`: `SeptopertShell.IslandEnclosed`, i.e. every
continuous path in the parameter space (P/A, C/A, E/A) from the Septopert Classic to (1, 0, 0) meets a set of Rupert
shapes.

Usage:
  checkSeptopertShell SeptopertShell/data/shell      (DIR/shell.txt and the slab files it names, written by nopert229
                                islandmap/bnd/closure.py --lean DIR)

The data is untrusted. shell.txt: `B0` (s_lo s_hi y_lo y_hi z_lo z_hi), `dm`, the `g` polynomials (one per face, in
order), then per face `face gi i0 i1 o0 o1 lo0 hi0 lo1 hi1`, three `chart` polynomials, `slab FILE a0 a1` lines and a
`tree` (preorder: `S dim point`, `B j` (slab j), `H k` (h_k > 0)), then six `b0tree` lines (B0 face k = 0..2, side 0..1).
-/

open SeptopertShell

instance : Inhabited SplitTree := ⟨.leaf⟩
instance : Inhabited Cert := ⟨{ m := 0, dc := 0, tree := .leaf }⟩
instance : Inhabited CoverTree := ⟨.pos 0⟩

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

/-- A cover tree in preorder: `B j`, `H k`, `S dim point` or `s dim` (midpoint of the current rectangle `lo`, `hi`). -/
partial def parseCover (lo hi : Array ℚ) (fs : List String) : IO (CoverTree × List String) := do
  let sub (dim : ℕ) (mid : ℚ) (rest : List String) : IO (CoverTree × List String) := do
    if h : dim < 2 then
      let (l, r1) ← parseCover lo (hi.set! dim mid) rest
      let (r, r2) ← parseCover (lo.set! dim mid) hi r1
      pure (.split ⟨dim, h⟩ mid l r, r2)
    else throw (IO.userError s!"bad cover split dimension {dim}")
  match fs with
  | "B" :: j :: rest => pure (.slab (← parseNat j), rest)
  | "H" :: k :: rest => pure (.pos (← parseNat k), rest)
  | "S" :: d :: m :: rest => do let dim ← parseNat d; sub dim (← parseRat m) rest
  | "s" :: d :: rest => do let dim ← parseNat d; sub dim ((lo[dim]! + hi[dim]!) / 2) rest
  | _ => throw (IO.userError "bad cover tree")

def parseCoverLine (lo hi : Array ℚ) (fs : List String) : IO CoverTree := do
  let (t, rest) ← parseCover lo hi fs
  unless rest.isEmpty do throw (IO.userError "trailing cover tree tokens")
  pure t

def parseShell (dir : String) : IO ClosureData := do
  let lines ← IO.FS.lines (dir ++ "/shell.txt")
  let mut b0 : List ℚ := []; let mut dm : ℚ := 0; let mut gs : Array SeptopertShell.Poly := #[]
  let mut faces : Array FaceData := #[]; let mut b0t : Array CoverTree := #[]
  let mut cur : Option FaceData := none; let mut charts : Array SeptopertShell.Poly := #[]
  let mut slabs : Array (SlabData × ℚ × ℚ) := #[]
  for line in lines do
    let fs := (line.splitOn " ").filter (· ≠ "")
    match fs with
    | "B0" :: rest => b0 ← rest.mapM parseRat
    | "dm" :: q :: _ => dm ← parseRat q
    | "g" :: rest => gs := gs.push (← parsePoly rest)
    | "face" :: rest =>
      let r ← rest.mapM parseRat
      if r.length ≠ 9 then throw (IO.userError "bad face line")
      let i0 ← fin3 (r[1]!).num.toNat
      let i1 ← fin3 (r[2]!).num.toNat
      let ra := r.toArray
      let gi := (ra.getD 0 0).num.toNat
      let f : FaceData := { gi := gi, chart := (fun _ => []), i0 := i0, i1 := i1, o0 := (ra.getD 3 0), o1 := (ra.getD 4 0), lo0 := (ra.getD 5 0), hi0 := (ra.getD 6 0), lo1 := (ra.getD 7 0), hi1 := (ra.getD 8 0), slabs := [], tree := CoverTree.pos 0 }
      cur := some f
      charts := #[]; slabs := #[]
    | "chart" :: rest => charts := charts.push (← parsePoly rest)
    | "slab" :: fn :: a0 :: a1 :: _ =>
      let sl ← parseSlab (dir ++ "/" ++ fn)
      slabs := slabs.push (sl, ← parseRat a0, ← parseRat a1)
    | "tree" :: rest =>
      match cur with
      | some f =>
        if charts.size ≠ 3 then throw (IO.userError "face needs 3 chart polynomials")
        let ch := charts
        let t ← parseCoverLine #[f.lo0, f.lo1] #[f.hi0, f.hi1] rest
        let sl := slabs.toList
        let chf : PV := fun k => ch[k.val]!
        faces := faces.push { f with chart := chf, slabs := sl, tree := t }
        cur := none
      | none => throw (IO.userError "tree outside a face")
    | "b0tree" :: rest =>
      let k := b0t.size / 2; let u := (k + 1) % 3; let w := (k + 2) % 3; let b := b0.toArray
      b0t := b0t.push (← parseCoverLine #[b[2 * u]!, b[2 * w]!] #[b[2 * u + 1]!, b[2 * w + 1]!] rest)
    | [] => pure ()
    | _ => throw (IO.userError s!"bad line: {line}")
  if b0.length ≠ 6 || b0t.size ≠ 6 then throw (IO.userError "bad B0 data")
  let b0a := b0.toArray; let b0ta := b0t
  let lo : Fin 3 → ℚ := fun k => b0a[2 * k.val]!
  let hi : Fin 3 → ℚ := fun k => b0a[2 * k.val + 1]!
  let bt : Fin 3 → Fin 2 → CoverTree := fun k s => b0ta[2 * k.val + s.val]!
  pure { B0lo := lo, B0hi := hi, dm := dm, gs := gs.toList, faces := faces.toList, b0trees := bt }

def main (args : List String) : IO UInt32 := do
  let dir := args.headD "."
  let t0 ← IO.monoMsNow
  let C ← parseShell dir
  let t1 ← IO.monoMsNow
  IO.println s!"read {C.faces.length} faces, {(C.faces.map (·.slabs.length)).foldl (· + ·) 0} slabs in {t1 - t0} ms"
  if hc : C.classicOk = true then
    if h : C.checkPar 32 = true then   -- the slab checks in 32 parallel tasks
      let t2 ← IO.monoMsNow
      let _thm : IslandEnclosed := islandEnclosed_of_closureData C (C.check_of_checkPar h) hc
      IO.println s!"checked in {t2 - t1} ms"
      IO.println "instantiated: IslandEnclosed (every path from the Septopert Classic to (1, 0, 0) in (P/A, C/A, E/A) meets certified Rupert shapes)"
      return 0
    else
      IO.println "CHECK FAILED"; return 1
  else
    IO.println "classicOk FAILED"; return 1
