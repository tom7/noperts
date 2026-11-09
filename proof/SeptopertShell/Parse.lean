module

public import SeptopertShell.ClosurePar

/-!
# Parsing the shell certificate

The certificate data is untrusted text (written by nopert229 `islandmap/bnd/closure.py --lean`); these computable
parsers turn it into `ClosureData` (`parseShell`) or one `SlabData` (`parseSlab`). Nothing here needs to be correct for
soundness: the theorems only use `ClosureData.check` on whatever the parser produced. Format: `slabdata K` blocks (one
slab each: `box`, the polynomials `s y z v0 v1 v2 c0 c1 c2 t0 t1`, `N0`, `m0`, `tri`, `view`, 22 `cond` lines
`m dc [C] TREE`, trees in preorder with `L`, `S dim point`, `s dim` (midpoint), `g` (geometric split in e)), then
`shell` and `B0`, `dm`, the `g` polynomials, per face `face ...`, three `chart` lines, `slab K a0 a1` lines and a cover
`tree` (`B j`, `H k`, `S dim point`, `s dim`), then six `b0tree` lines.
-/

@[expose] public section

namespace SeptopertShell

instance : Inhabited SplitTree := ⟨.leaf⟩
instance : Inhabited Cert := ⟨{ m := 0, dc := 0, tree := .leaf }⟩
instance : Inhabited CoverTree := ⟨.pos 0⟩

def parseRat (s : String) : Except String ℚ :=
  match s.splitOn "/" with
  | [a] => match a.toInt? with
    | some n => pure n
    | none => throw (s!"not a rational: {s}")
  | [a, b] => match a.toInt?, b.toNat? with
    | some n, some d => if d = 0 then throw (s!"zero denominator: {s}") else pure ((n : ℚ) / d)
    | _, _ => throw (s!"not a rational: {s}")
  | _ => throw (s!"not a rational: {s}")

def parseNat (s : String) : Except String ℕ :=
  match s.toNat? with
  | some n => pure n
  | none => throw (s!"not a natural number: {s}")

/-- `nt` then `nt` terms `i j k coef`. -/
def parsePoly (fs : List String) : Except String SeptopertShell.Poly := do
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
partial def parseTree (lo hi : Array ℚ) (dc : ℚ) (fs : List String) : Except String (SplitTree × List String) := do
  let sub (dim : ℕ) (mid : ℚ) (rest : List String) : Except String (SplitTree × List String) := do
    if h : dim < 3 then
      let (l, r1) ← parseTree lo (hi.set! dim mid) dc rest
      let (r, r2) ← parseTree (lo.set! dim mid) hi dc r1
      pure (.split ⟨dim, h⟩ mid l r, r2)
    else throw (s!"bad split dimension {dim}")
  match fs with
  | "L" :: rest => pure (.leaf, rest)
  | "S" :: d :: m :: rest => do let dim ← parseNat d; sub dim (← parseRat m) rest
  | "s" :: d :: rest => do let dim ← parseNat d; sub dim ((lo[dim]! + hi[dim]!) / 2) rest
  | "g" :: rest => sub 2 (2 * lo[2]! + dc) rest
  | _ => throw ("bad tree")

def fin3 (n : ℕ) : Except String (Fin 3) := if h : n < 3 then pure ⟨n, h⟩ else throw (s!"not < 3: {n}")
def fin7 (n : ℕ) : Except String (Fin 7) := if h : n < 7 then pure ⟨n, h⟩ else throw (s!"not < 7: {n}")

def parseSlab (path : String) (lines : List String) : Except String SlabData := do
  let mut m : Std.HashMap String (List String) := {}
  let mut conds : Array (List String) := #[]
  for line in lines do
    let fs := (line.splitOn " ").filter (· ≠ "")
    match fs with
    | "cond" :: rest => conds := conds.push rest
    | k :: rest => m := m.insert k rest
    | [] => pure ()
  let get (k : String) : Except String (List String) := match m[k]? with
    | some v => pure v
    | none => throw (s!"{path}: missing {k}")
  let box ← (← get "box").mapM parseRat
  let poly (k : String) : Except String SeptopertShell.Poly := do parsePoly (← get k)
  let n0 ← (← get "N0").mapM parseRat
  let tri ← (← get "tri").mapM parseNat
  let view ← get "view"
  if conds.size ≠ 22 || box.length ≠ 4 || n0.length ≠ 9 || tri.length ≠ 21 then
    throw (s!"{path}: bad sizes")
  let certs ← conds.mapM fun fs => do
    let mm ← parseNat (fs.getD 0 ""); let dc ← parseRat (fs.getD 1 "")
    let cen := fs.getD 2 "" == "C"   -- `cond m dc C TREE`: centred form
    let (t, rest) ← parseTree #[-box[0]!, -box[1]!, box[2]! - dc] #[box[0]!, box[1]!, box[3]! - dc] dc (fs.drop (if cen then 3 else 2))
    unless rest.isEmpty do throw (s!"{path}: trailing tree tokens")
    pure ({ m := mm, dc := dc, tree := t, centred := cen } : Cert)
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
partial def parseCover (lo hi : Array ℚ) (fs : List String) : Except String (CoverTree × List String) := do
  let sub (dim : ℕ) (mid : ℚ) (rest : List String) : Except String (CoverTree × List String) := do
    if h : dim < 2 then
      let (l, r1) ← parseCover lo (hi.set! dim mid) rest
      let (r, r2) ← parseCover (lo.set! dim mid) hi r1
      pure (.split ⟨dim, h⟩ mid l r, r2)
    else throw (s!"bad cover split dimension {dim}")
  match fs with
  | "B" :: j :: rest => pure (.slab (← parseNat j), rest)
  | "H" :: k :: rest => pure (.pos (← parseNat k), rest)
  | "S" :: d :: m :: rest => do let dim ← parseNat d; sub dim (← parseRat m) rest
  | "s" :: d :: rest => do let dim ← parseNat d; sub dim ((lo[dim]! + hi[dim]!) / 2) rest
  | _ => throw ("bad cover tree")

def parseCoverLine (lo hi : Array ℚ) (fs : List String) : Except String CoverTree := do
  let (t, rest) ← parseCover lo hi fs
  unless rest.isEmpty do throw ("trailing cover tree tokens")
  pure t

/-- The slab blocks (`slabdata K` ... ) of the merged certificate text and the shell part (after `shell`). -/
def splitBlocks (text : String) : Array (List String) × List String := Id.run do
  let mut blocks : Array (List String) := #[]; let mut cur : Array String := #[]; let mut inSlab := false
  let mut shell : Array String := #[]; let mut inShell := false
  for line in text.splitOn "\n" do
    let fs := (line.splitOn " ").filter (· ≠ "")
    match fs with
    | "slabdata" :: _ => if inSlab then blocks := blocks.push cur.toList
                         cur := #[]; inSlab := true; inShell := false
    | ["shell"] => if inSlab then blocks := blocks.push cur.toList
                   inSlab := false; inShell := true
    | _ => if inSlab then cur := cur.push line else if inShell then shell := shell.push line
  if inSlab then blocks := blocks.push cur.toList
  return (blocks, shell.toList)

/-- The closure data from the merged certificate text (`slabdata K` blocks, then `shell` and the shell lines; a face
refers to its slabs by `slab K a0 a1`). -/
def parseShell (text : String) : Except String ClosureData := do
  let (blocks, lines) := splitBlocks text
  let slabArr ← (List.range blocks.size).toArray.mapM fun k => parseSlab s!"slab {k}" blocks[k]!
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
      if r.length ≠ 9 then throw ("bad face line")
      let i0 ← fin3 (r[1]!).num.toNat
      let i1 ← fin3 (r[2]!).num.toNat
      let ra := r.toArray
      let gi := (ra.getD 0 0).num.toNat
      let f : FaceData := { gi := gi, chart := (fun _ => []), i0 := i0, i1 := i1, o0 := (ra.getD 3 0), o1 := (ra.getD 4 0), lo0 := (ra.getD 5 0), hi0 := (ra.getD 6 0), lo1 := (ra.getD 7 0), hi1 := (ra.getD 8 0), slabs := [], tree := CoverTree.pos 0 }
      cur := some f
      charts := #[]; slabs := #[]
    | "chart" :: rest => charts := charts.push (← parsePoly rest)
    | "slab" :: k :: a0 :: a1 :: _ =>
      let kk ← parseNat k
      if h : kk < slabArr.size then slabs := slabs.push (slabArr[kk], ← parseRat a0, ← parseRat a1)
      else throw s!"no slab {kk}"
    | "tree" :: rest =>
      match cur with
      | some f =>
        if charts.size ≠ 3 then throw ("face needs 3 chart polynomials")
        let ch := charts
        let t ← parseCoverLine #[f.lo0, f.lo1] #[f.hi0, f.hi1] rest
        let sl := slabs.toList
        let chf : PV := fun k => ch[k.val]!
        faces := faces.push { f with chart := chf, slabs := sl, tree := t }
        cur := none
      | none => throw ("tree outside a face")
    | "b0tree" :: rest =>
      let k := b0t.size / 2; let u := (k + 1) % 3; let w := (k + 2) % 3; let b := b0.toArray
      b0t := b0t.push (← parseCoverLine #[b[2 * u]!, b[2 * w]!] #[b[2 * u + 1]!, b[2 * w + 1]!] rest)
    | [] => pure ()
    | _ => throw (s!"bad line: {line}")
  if b0.length ≠ 6 || b0t.size ≠ 6 then throw ("bad B0 data")
  let b0a := b0.toArray; let b0ta := b0t
  let lo : Fin 3 → ℚ := fun k => b0a[2 * k.val]!
  let hi : Fin 3 → ℚ := fun k => b0a[2 * k.val + 1]!
  let bt : Fin 3 → Fin 2 → CoverTree := fun k s => b0ta[2 * k.val + s.val]!
  pure { B0lo := lo, B0hi := hi, dm := dm, gs := gs.toList, faces := faces.toList, b0trees := bt }


end SeptopertShell

end
