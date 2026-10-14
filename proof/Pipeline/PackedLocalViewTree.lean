module

public import Pipeline.AtlasProjectiveLocalViewTree
public import Atlas.QuadCoverTree

@[expose] public section

/-!
# Packed native certificates for the local view tree

Large generated local certificates contain very little repeated axis data.
Representing every integer in that data as a separate Lean declaration makes
elaboration and code generation dominate the actual certificate check.  This
module provides a deliberately small total decoder for comma-separated natural
numbers, so that a table can be stored as one string literal; the native
checkers that the `construct*` executables run still check the fully decoded
exact rational table.

Signed rational numerators use zig-zag coding: `z >= 0` is encoded as `2*z`,
and `z < 0` as `-2*z-1`.
-/

namespace Noperts.Pipeline.PackedLocalViewTree

variable [SolidModel]

open Noperts.Atlas

open AtlasProjectiveView AtlasProjectiveLocalCertificate
open AtlasProjectiveLocalViewTree
open Noperts.Atlas.ProjectiveView

structure Cursor where
  data : ByteArray
  pos : Nat := 0

def Cursor.readNat (cursor : Cursor) : Nat × Cursor :=
  Id.run do
    let data := cursor.data
    let mut pos := cursor.pos
    let mut acc : Nat := 0
    let size := data.size
    while h : pos < size do
      let byte := data[pos]
      pos := pos + 1
      if byte = 44 then
        break
      let value := byte.toNat
      if 48 ≤ value ∧ value ≤ 57 then
        acc := 10 * acc + value - 48
    (acc, { cursor with pos })


abbrev Decoder := StateM Cursor

def readNat : Decoder Nat := fun cursor => cursor.readNat

def fin3 (n : Nat) : Fin 3 := ⟨n % 3, by omega⟩
def fin4 (n : Nat) : Fin 4 := ⟨n % 4, by omega⟩
def fin5 (n : Nat) : Fin 5 := ⟨n % 5, by omega⟩
def fin8 (n : Nat) : Fin 8 := ⟨n % 8, by omega⟩
/-- `n` reduced into `Fin m`; used for vertex indices, whose count comes from the model. -/
def finMod {m : Nat} [NeZero m] (n : Nat) : Fin m := ⟨n % m, Nat.mod_lt _ (Nat.pos_of_neZero m)⟩
def fin1001 (n : Nat) : Fin 1001 := ⟨n % 1001, by omega⟩

def zigzagInt (n : Nat) : Int :=
  if n % 2 = 0 then Int.ofNat (n / 2) else Int.negSucc (n / 2)

def readRat : Decoder Rat := do
  let numerator ← readNat
  let denominator ← readNat
  pure ((((zigzagInt numerator : Int) : Rat) / (denominator : Rat)) : Rat)

/-- The model slot of the C++ checker's vertex number `n` (for the
Septopert, the first of the slots holding that vertex). -/
def vertexSlot (n : Nat) : VertexIndex := SolidModel.vertexSlot n

def readVertices : Decoder (Fin 3 → VertexIndex) := do
  let a ← readNat
  let b ← readNat
  let c ← readNat
  pure ![vertexSlot a, vertexSlot b, vertexSlot c]

def readMix : Decoder (Fin 3 → Fin 1001) := do
  let a ← readNat
  let b ← readNat
  let c ← readNat
  pure ![fin1001 a, fin1001 b, fin1001 c]

def readAxis : Decoder AxisCertificate := do
  let edgeStart ← readVertices
  let edgeFinish ← readVertices
  let edgeStart₂ ← readVertices
  let edgeFinish₂ ← readVertices
  let mix ← readMix
  let index ← readVertices
  let nonzeroWitness ← readVertices
  let B ← readRat
  pure {
    edgeStart := edgeStart
    edgeFinish := edgeFinish
    edgeStart₂ := edgeStart₂
    edgeFinish₂ := edgeFinish₂
    mix := mix
    index := index
    nonzeroWitness := nonzeroWitness
    B := B }

def readCertificate : Decoder (Fin 4 → AxisCertificate) := do
  let a ← readAxis
  let b ← readAxis
  let c ← readAxis
  let d ← readAxis
  pure (fun
    | 0 => a
    | 1 => b
    | 2 => c
    | 3 => d)

def readAxes (count : Nat) : Decoder (Array AxisCertificate) := fun cursor =>
  Id.run do
    let mut cur := cursor
    let mut axes := Array.mkEmpty count
    for _ in [0:count] do
      let (ax, next) := readAxis cur
      cur := next
      axes := axes.push ax
    (axes, cur)

def readQuadTree (fuel : Nat := 1000) : Decoder QuadCoverTree := fun cursor =>
  match fuel with
  | 0 => (.outside, cursor)
  | fuel + 1 =>
      let (nodeTag, c1) := readNat cursor
      if nodeTag = 0 then
        (.outside, c1)
      else if nodeTag = 1 then
        let (m, c2) := readNat c1
        (.covered m, c2)
      else if nodeTag = 2 then
        let (mid, c2) := readRat c1
        let (left, c3) := readQuadTree fuel c2
        let (right, c4) := readQuadTree fuel c3
        (.splitS mid left right, c4)
      else
        let (mid, c2) := readRat c1
        let (left, c3) := readQuadTree fuel c2
        let (right, c4) := readQuadTree fuel c3
        (.splitT mid left right, c4)

structure PrecomputedTriangle where
  v : Array Rat

def PrecomputedTriangle.toTriangle (pt : PrecomputedTriangle) :
    AtlasProjectiveView.Triangle Rat :=
  fun i c => pt.v[3 * i.val + c.val]!

def PrecomputedTriangle.ofTriangle (t : AtlasProjectiveView.Triangle Rat) :
    PrecomputedTriangle :=
  let arr : Array Rat := #[
    t 0 0, t 0 1, t 0 2,
    t 1 0, t 1 1, t 1 2,
    t 2 0, t 2 1, t 2 2
  ]
  ⟨arr⟩

def stepTriangle (pt : PrecomputedTriangle) (child : Fin 4) :
    PrecomputedTriangle :=
  let s := split pt.toTriangle child
  let arr : Array Rat := #[
    s 0 0, s 0 1, s 0 2,
    s 1 0, s 1 1, s 1 2,
    s 2 0, s 2 1, s 2 2
  ]
  ⟨arr⟩

def readTrianglePath (length : Nat) (pt : PrecomputedTriangle) :
    Decoder PrecomputedTriangle := fun cursor =>
  Id.run do
    let mut curCursor := cursor
    let mut curPt := pt
    for _ in [0:length] do
      let (child, nextCursor) := curCursor.readNat
      curCursor := nextCursor
      curPt := stepTriangle curPt (fin4 child)
    (curPt, curCursor)

def readTriangle (base : AtlasProjectiveView.Triangle Rat) :
    Decoder (AtlasProjectiveView.Triangle Rat) := do
  let length ← readNat
  let pt ← readTrianglePath length (PrecomputedTriangle.ofTriangle base)
  pure pt.toTriangle

/-- A blow-up certificate leaf (`KCap.Leaf`): K, the Cramer sign, per contact the edge
(a, b) and its outer set (n, then n vertices), the tuple count, and per tuple K inner
vertices; vertices as indices of the row's vertex array (C++ vertex numbers). -/
def readKLeaf : Decoder KCap.Leaf := do
  let K ← readNat
  let s ← readRat
  let mut edges : Array (ℕ × ℕ) := #[]
  let mut outer : Array (List ℕ) := #[]
  for _ in [0:K] do
    let a ← readNat
    let b ← readNat
    let n ← readNat
    let mut S : Array ℕ := #[]
    for _ in [0:n] do
      S := S.push (← readNat)
    edges := edges.push (a, b)
    outer := outer.push S.toList
  let nt ← readNat
  let mut inner : Array (List ℕ) := #[]
  for _ in [0:nt] do
    let mut it : Array ℕ := #[]
    for _ in [0:K] do
      it := it.push (← readNat)
    inner := inner.push it.toList
  pure ⟨s, edges.toList, outer.toList, inner.toList, []⟩

/-- Five rationals. -/
def readQ5 : Decoder (Fin 5 → ℚ) := do
  let a ← readRat
  let b ← readRat
  let c ← readRat
  let d ← readRat
  let e ← readRat
  pure ![a, b, c, d, e]

/-- A 5 × 5 rational matrix, row by row. -/
def readM5 : Decoder (Fin 5 → Fin 5 → ℚ) := do
  let r0 ← readQ5
  let r1 ← readQ5
  let r2 ← readQ5
  let r3 ← readQ5
  let r4 ← readQ5
  pure ![r0, r1, r2, r3, r4]

/-- A blow-up face tree in preorder: 0 axis (a split), 1 leaf, 3 an affine node (A, c, B as
rationals, row by row, then the new box as five (lower end, width) pairs), 4 a leaf with
blended inner points (their count, then per blend a, c, t; then the leaf as for 1), 2 (a
failed leaf). The fuel bounds the depth. -/
def readATree : ℕ → Decoder KCap.ATree
  | 0 => pure .fail
  | fuel + 1 => do
    let tag ← readNat
    if tag = 0 then
      let a ← readNat
      let l ← readATree fuel
      let r ← readATree fuel
      pure (.split (fin5 a) l r)
    else if tag = 1 then
      pure (.leaf (← readKLeaf))
    else if tag = 3 then
      let A ← readM5
      let c ← readQ5
      let B ← readM5
      let lo ← readQ5
      let w ← readQ5
      let t ← readATree fuel
      pure (.affine ⟨A, c, B⟩ (fun i => (lo i, w i)) t)
    else if tag = 4 then
      let nb ← readNat
      let mut bl : Array (ℕ × ℕ × ℚ) := #[]
      for _ in [0:nb] do
        let a ← readNat
        let c ← readNat
        let t ← readRat
        bl := bl.push (a, c, t)
      let leaf ← readKLeaf
      pure (.leaf { leaf with blends := bl.toList })
    else
      pure .fail

def readRow (base : AtlasProjectiveView.Triangle Rat) : Decoder Row := do
  let tag ← readNat
  let id ← readNat
  let root ← readNat
  let triangle ← readTriangle base
  if tag = 0 then
    let a ← readNat
    let b ← readNat
    let c ← readNat
    let d ← readNat
    let rLower ← readRat
    pure (.split id ![a, b, c, d] (fin8 root) triangle rLower)
  else if tag = 4 then
    pure (.empty id (fin8 root) triangle)
  else if tag = 5 then
    let rho ← readRat
    -- The vertex array in C++ order: the model vertex of each C++ vertex number (the
    -- row's validity checks that they are the model's vertices).
    let nverts ← readNat
    let V : Array (KCap.KVec ℚ) := Array.ofFn fun n : Fin nverts => rationalVertex (vertexSlot n.val)
    let nfaces ← readNat
    let mut faces : Array ((ℕ × Bool) × KCap.ATree) := #[]
    for _ in [0:nfaces] do
      let axis ← readNat
      let sign ← readNat
      let tree ← readATree 200
      faces := faces.push ((axis, sign = 1), tree)
    pure (.idcap id (fin8 root) triangle rho V faces.toList)
  else if tag = 2 then
    let symmetryIndex ← readNat
    let certificate ← readCertificate
    let c ← readRat
    let δ ← readRat
    let r ← readRat
    let coreAxis ← readAxis
    let d0 ← readRat
    let d1 ← readRat
    let d2 ← readRat
    let defect0 : Fin 3 → ℚ := ![d0, d1, d2]
    let D0 ← readRat
    let r_min ← readRat
    let c_cone ← readRat
    let c_core ← readRat
    let lam ← readRat
    let w0 ← readRat
    let w1 ← readRat
    let w2 ← readRat
    let w : Fin 3 → ℚ := ![w0, w1, w2]
    pure (.decomposed id {
      interval := AtlasPose.rootInterval Rat
      root := fin8 root
      triangle
      chart := 0
      symmetryIndex := finMod symmetryIndex
      certificate
      c
      δ
      r } coreAxis defect0 D0 r_min c_cone c_core lam w)
  else if tag = 3 then
    let symmetryIndex ← readNat
    let certificate ← readCertificate
    let c ← readRat
    let δ ← readRat
    let r ← readRat
    let numFlockAxes ← readNat
    let flockAxes ← readAxes numFlockAxes
    let d0 ← readRat
    let d1 ← readRat
    let d2 ← readRat
    let defect0 : Fin 3 → ℚ := ![d0, d1, d2]
    let D0 ← readRat
    let r_min ← readRat
    let c_cone ← readRat
    let c_core ← readRat
    let S_max ← readRat
    let T_max ← readRat
    let tree ← readQuadTree 1000
    pure (.flockDecomposed id {
      interval := AtlasPose.rootInterval Rat
      root := fin8 root
      triangle
      chart := 0
      symmetryIndex := finMod symmetryIndex
      certificate
      c
      δ
      r } flockAxes defect0 D0 r_min c_cone c_core S_max T_max tree)
  else
    let symmetryIndex ← readNat
    let certificate ← readCertificate
    let c ← readRat
    let δ ← readRat
    let r ← readRat
    pure (.certificate id {
      interval := AtlasPose.rootInterval Rat
      root := fin8 root
      triangle
      chart := 0
      symmetryIndex := finMod symmetryIndex
      certificate
      c
      δ
      r })

def readRows (base : AtlasProjectiveView.Triangle Rat) (count : Nat) :
    Decoder (Array Row) := fun cursor =>
  Id.run do
    let mut cur := cursor
    let mut rows := Array.mkEmpty count
    for _ in [0:count] do
      let (row, next) := readRow base cur
      cur := next
      rows := rows.push row
    (rows, cur)

def decodeRows (base : AtlasProjectiveView.Triangle Rat)
    (count : Nat) (packed : String) : Array Row :=
  (readRows base count { data := packed.toUTF8 }).1

def decodeTable (initialChild symmetryIndex : Nat) (r : Rat)
    (count : Nat) (packed : String) : Table :=
  let base := split upperWedgeTriangle (fin4 initialChild)
  let rows := decodeRows base count packed
  {
    symmetryIndex := finMod symmetryIndex
    r
    root := 0
    triangle := base
    get := fun i => rows[i]!
    size := count
  }

structure Decoded where
  symmetryIndex : Nat
  r : Rat
  count : Nat
  rows : Array Row

def readDecoded (base : AtlasProjectiveView.Triangle Rat) :
    Decoder Decoded := do
  let count ← readNat
  let symmetryIndex ← readNat
  let r ← readRat
  let rows ← readRows base count
  pure { symmetryIndex, r, count, rows }

/-- Decode a self-describing packed local-table artifact from binary bytes. -/
def decodePackedByteArray (initialChild : Nat) (data : ByteArray) : Table :=
  let base := split upperWedgeTriangle (fin4 initialChild)
  let decoded := (readDecoded base { data }).1
  {
    symmetryIndex := finMod decoded.symmetryIndex
    r := decoded.r
    root := 0
    triangle := base
    get := fun i => decoded.rows[i]!
    size := decoded.count
  }

/-- Decode a self-describing packed local-table artifact. The initial projective
root child is supplied by its position in the four-table atlas. -/
def decodePackedTable (initialChild : Nat) (packed : String) : Table :=
  decodePackedByteArray initialChild packed.toUTF8

def readTriangleCorners : Decoder (AtlasProjectiveView.Triangle Rat) := do
  let c00 ← readRat; let c01 ← readRat; let c02 ← readRat
  let c10 ← readRat; let c11 ← readRat; let c12 ← readRat
  let c20 ← readRat; let c21 ← readRat; let c22 ← readRat
  pure ![![c00, c01, c02], ![c10, c11, c12], ![c20, c21, c22]]

structure DecodedCodeTable where
  count : Nat
  symmetryIndex : Nat
  r : Rat
  base : AtlasProjectiveView.Triangle Rat
  rows : Array Row

def readDecodedCodeTable : Decoder DecodedCodeTable := do
  let count ← readNat
  let symmetryIndex ← readNat
  let r ← readRat
  let base ← readTriangleCorners
  let rows ← readRows base count
  pure { count, symmetryIndex, r, base, rows }

/-- Decode a self-describing packed code-triangle artifact from binary bytes.
The table's root is its first row's (the code triangle's projective root). -/
def decodePackedCodeTriangle (data : ByteArray) : Table :=
  let decoded := (readDecodedCodeTable { data }).1
  {
    symmetryIndex := finMod decoded.symmetryIndex
    r := decoded.r
    root := (decoded.rows[0]?.map Row.root).getD 0
    triangle := decoded.base
    get := fun i => decoded.rows[i]!
    size := decoded.count
  }

end Noperts.Pipeline.PackedLocalViewTree

end
