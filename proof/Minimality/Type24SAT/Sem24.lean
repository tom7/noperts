module

public import Minimality.OctaTools

@[expose] public section

/-!
# Type 24, SAT bridge layer 1: the real meaning of every shape literal

The type 24 encoder names 305 shape literals of six kinds; their
polynomials are those of the loop's reference decoder (`value`, `normals`, `convex`), which is the decoding the loop
itself uses (the SMT checks, the frame export, the realizer).  This file gives the same definitions in Lean.

Points `x : Nat → ℝ³` (indices `0..6`), the nine facets `A..I = 0..8` with vertex lists `faces`
(012 016 025 0345 046 126 235 236 346), and the normal of facet `t`
  `nrm x t = sig t • (x b - x a) × (x c - x a)`   (`a b c` the first three vertices of `t`),
where `sig` is the loop's `SIG` (from the labelled reference shape: `nrm` points outward).  The literals:
- `[abcd]`     `br a b c d`   `det (b - a, c - a, d - a)`
- `Labc;de`    `lv a b c d e` `det (b - a, c - a, d - e)`
- `Mab.cd.ef.` `mv a b c d e f` `det (a - b, c - d, e - f)`
- `X:pq`       `fc t p q`     `⟪nrm t, p - q⟫`
- `Nrst`       `nv r s t`     `det (nrm r, nrm s, nrm t)`
- `KXabcd`     `kv t a b c d` `⟪(a - b) × (c - d), nrm t⟫`
and the 35 convexity values `cv x t v = -⟪nrm t, x v - x a_t⟫` (`v` off facet `t`, in the loop's convexity list order).
A literal `(name, s)` of a model says `0 < s * val x lit`.

Everything is also defined over any commutative ring on coordinate triples (`V3`, `val3`), with
`val_eq_val3` (the real definitions are the coordinate ones) and `val3_map` (ring homomorphisms commute),
so that exact signs at a rational shape are computed over `ℚ` by `decide` and moved to `ℝ` by `Rat.cast`.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace

namespace Minimality.T24.SAT

open Minimality

/-! ### Coordinates over a commutative ring -/

/-- A coordinate triple. -/
structure V3 (R : Type) where
  x : R
  y : R
  z : R
  deriving DecidableEq, Repr

namespace V3
variable {R S : Type} [CommRing R] [CommRing S]
/-- Difference. -/
def sub (a b : V3 R) : V3 R := ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩
/-- Scalar multiple. -/
def smul (k : R) (a : V3 R) : V3 R := ⟨k * a.x, k * a.y, k * a.z⟩
/-- Cross product (the convention of `Minimality.cross`). -/
def cr (a b : V3 R) : V3 R := ⟨a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x⟩
/-- Dot product. -/
def dot (a b : V3 R) : R := a.x * b.x + a.y * b.y + a.z * b.z
/-- `det (a, b, c) = (a × b) · c` (the convention of `Minimality.det3`). -/
def det (a b c : V3 R) : R := dot (cr a b) c
/-- Image under a ring homomorphism. -/
def map (f : R →+* S) (a : V3 R) : V3 S := ⟨f a.x, f a.y, f a.z⟩
end V3

/-! ### The facets -/

/-- Vertex lists of the nine facets `A..I` (the loop's face list; the quadrilateral `D = 0345`). -/
def faces : List (List Nat) :=
  [[0, 1, 2], [0, 1, 6], [0, 2, 5], [0, 3, 4, 5], [0, 4, 6], [1, 2, 6], [2, 3, 5], [2, 3, 6], [3, 4, 6]]

/-- First, second, third vertex of facet `t` (the points of the normal's cross product). -/
def fa (t : Nat) : Nat := (faces.getD t []).getD 0 0
/-- Second vertex of facet `t`. -/
def fb (t : Nat) : Nat := (faces.getD t []).getD 1 0
/-- Third vertex of facet `t`. -/
def fc' (t : Nat) : Nat := (faces.getD t []).getD 2 0

/-- the loop's `SIG`: the outward orientation of `(x b - x a) × (x c - x a)` per facet, read off the labelled
reference shape the labelled reference shape. -/
def sigs : List Int := [1, -1, 1, 1, 1, -1, 1, -1, -1]
/-- Orientation sign of facet `t`. -/
def sig (t : Nat) : Int := sigs.getD t 0


/-! ### The literals -/


/-- A shape literal kind with its indices (the encoder's name decoded as the loop's reference decoder does). -/
inductive Lit24 where
  /-- `[abcd]`: `det (b - a, c - a, d - a)`. -/
  | br (a b c d : Nat)
  /-- `Labc;de`: `det (b - a, c - a, d - e)`. -/
  | lv (a b c d e : Nat)
  /-- `Mab.cd.ef.`: `det (a - b, c - d, e - f)`. -/
  | mv (a b c d e f : Nat)
  /-- `X:pq`: `⟪nrm X, p - q⟫`. -/
  | fc (t p q : Nat)
  /-- `Nrst`: `det (nrm r, nrm s, nrm t)`. -/
  | nv (r s t : Nat)
  /-- `KXabcd`: `⟪(a - b) × (c - d), nrm X⟫`. -/
  | kv (t a b c d : Nat)
  deriving DecidableEq, Repr

section Coord
variable {R : Type} [CommRing R]




end Coord

/-! ### The real definitions -/

/-- Outward normal of facet `t` (a positive multiple of the facet function's gradient on a type 24 polytope). -/
noncomputable def nrm (x : Nat → ℝ³) (t : Nat) : ℝ³ :=
  ((sig t : ℝ)) • cross (x (fb t) - x (fa t)) (x (fc' t) - x (fa t))

/-- **The real number whose sign a literal names.** -/
noncomputable def val (x : Nat → ℝ³) : Lit24 → ℝ
  | .br a b c d => det3 (x b - x a) (x c - x a) (x d - x a)
  | .lv a b c d e => det3 (x b - x a) (x c - x a) (x d - x e)
  | .mv a b c d e f => det3 (x a - x b) (x c - x d) (x e - x f)
  | .fc t p q => ⟪nrm x t, x p - x q⟫
  | .nv r s t => det3 (nrm x r) (nrm x s) (nrm x t)
  | .kv t a b c d => ⟪cross (x a - x b) (x c - x d), nrm x t⟫

/-- Convexity value of vertex `v` at facet `t` (positive on a strictly convex shape with these facets). -/
noncomputable def cv (x : Nat → ℝ³) (t v : Nat) : ℝ := -⟪nrm x t, x v - x (fa t)⟫




/-! ### Real = coordinates -/

/-- The coordinate triple of a point. -/
noncomputable def toV3 (a : ℝ³) : V3 ℝ := ⟨a 0, a 1, a 2⟩


theorem toV3_sub (a b : ℝ³) : toV3 (a - b) = V3.sub (toV3 a) (toV3 b) := by
  simp [toV3, V3.sub]

theorem toV3_smul (k : ℝ) (a : ℝ³) : toV3 (k • a) = V3.smul k (toV3 a) := by
  simp [toV3, V3.smul]

theorem toV3_cross (a b : ℝ³) : toV3 (cross a b) = V3.cr (toV3 a) (toV3 b) := by
  simp [toV3, V3.cr, cross_apply_zero, cross_apply_one, cross_apply_two]

theorem inner_eq_dot (a b : ℝ³) : ⟪a, b⟫ = V3.dot (toV3 a) (toV3 b) := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial, toV3, V3.dot]
  ring

theorem det3_eq_det (a b c : ℝ³) : det3 a b c = V3.det (toV3 a) (toV3 b) (toV3 c) := by
  rw [det3_expand]
  simp only [V3.det, V3.dot, V3.cr, toV3]




/-! ### Ring homomorphisms -/

section Map
variable {R S : Type} [CommRing R] [CommRing S]

theorem V3.map_sub (f : R →+* S) (a b : V3 R) : (V3.sub a b).map f = V3.sub (a.map f) (b.map f) := by
  simp [V3.sub, V3.map]

theorem V3.map_cr (f : R →+* S) (a b : V3 R) : (V3.cr a b).map f = V3.cr (a.map f) (b.map f) := by
  simp [V3.cr, V3.map]

theorem V3.map_smul (f : R →+* S) (k : R) (a : V3 R) : (V3.smul k a).map f = V3.smul (f k) (a.map f) := by
  simp [V3.smul, V3.map]

theorem V3.map_dot (f : R →+* S) (a b : V3 R) : f (V3.dot a b) = V3.dot (a.map f) (b.map f) := by
  simp [V3.dot, V3.map]

theorem V3.map_det (f : R →+* S) (a b c : V3 R) :
    f (V3.det a b c) = V3.det (a.map f) (b.map f) (c.map f) := by
  simp only [V3.det, V3.map_dot, V3.map_cr]




end Map

/-! ### Rational shapes -/







end Minimality.T24.SAT
