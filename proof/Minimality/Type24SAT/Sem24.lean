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

/-- The 35 convexity pairs `(t, v)`, `v` not on facet `t`, in the loop's convexity list order (`cvN` = entry `N`). -/
def cvList : List (Nat × Nat) :=
  (List.range 9).flatMap fun t =>
    ((List.range 7).filter fun v => !(faces.getD t []).contains v).map fun v => (t, v)

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

/-- Facet normal in coordinates. -/
def nrm3 (P : Nat → V3 R) (t : Nat) : V3 R :=
  V3.smul ((sig t : R)) (V3.cr (V3.sub (P (fb t)) (P (fa t))) (V3.sub (P (fc' t)) (P (fa t))))

/-- The value of a literal in coordinates. -/
def val3 (P : Nat → V3 R) : Lit24 → R
  | .br a b c d => V3.det (V3.sub (P b) (P a)) (V3.sub (P c) (P a)) (V3.sub (P d) (P a))
  | .lv a b c d e => V3.det (V3.sub (P b) (P a)) (V3.sub (P c) (P a)) (V3.sub (P d) (P e))
  | .mv a b c d e f => V3.det (V3.sub (P a) (P b)) (V3.sub (P c) (P d)) (V3.sub (P e) (P f))
  | .fc t p q => V3.dot (nrm3 P t) (V3.sub (P p) (P q))
  | .nv r s t => V3.det (nrm3 P r) (nrm3 P s) (nrm3 P t)
  | .kv t a b c d => V3.dot (V3.cr (V3.sub (P a) (P b)) (V3.sub (P c) (P d))) (nrm3 P t)

/-- Convexity value in coordinates. -/
def cv3 (P : Nat → V3 R) (t v : Nat) : R := -(V3.dot (nrm3 P t) (V3.sub (P v) (P (fa t))))

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

/-- The 35 strict convexity inequalities of the loop's convexity list. -/
def Convex24 (x : Nat → ℝ³) : Prop := ∀ p ∈ cvList, 0 < cv x p.1 p.2

/-- The planarity of the quadrilateral `D = 0345` (part of the type). -/
def QuadD (x : Nat → ℝ³) : Prop := det3 (x 3 - x 0) (x 4 - x 0) (x 5 - x 0) = 0

/-- A literal of a sign model: `(lit, s)` with `s = ±1` holds when `0 < s * val`. -/
def LitHolds (x : Nat → ℝ³) (l : Lit24) (s : Int) : Prop := 0 < (s : ℝ) * val x l

/-! ### Real = coordinates -/

/-- The coordinate triple of a point. -/
noncomputable def toV3 (a : ℝ³) : V3 ℝ := ⟨a 0, a 1, a 2⟩

/-- The coordinates of a configuration. -/
noncomputable def pt (x : Nat → ℝ³) (i : Nat) : V3 ℝ := toV3 (x i)

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

theorem toV3_nrm (x : Nat → ℝ³) (t : Nat) : toV3 (nrm x t) = nrm3 (pt x) t := by
  simp only [nrm, nrm3, pt, toV3_smul, toV3_cross, toV3_sub]

/-- The real values are the coordinate values. -/
theorem val_eq_val3 (x : Nat → ℝ³) (l : Lit24) : val x l = val3 (pt x) l := by
  cases l <;>
    simp only [val, val3, det3_eq_det, inner_eq_dot, toV3_sub, toV3_cross, toV3_nrm, pt]

theorem cv_eq_cv3 (x : Nat → ℝ³) (t v : Nat) : cv x t v = cv3 (pt x) t v := by
  simp only [cv, cv3, inner_eq_dot, toV3_sub, toV3_nrm, pt]

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

theorem nrm3_map (f : R →+* S) (P : Nat → V3 R) (t : Nat) :
    (nrm3 P t).map f = nrm3 (fun i => (P i).map f) t := by
  simp only [nrm3, V3.map_smul, V3.map_cr, V3.map_sub, map_intCast]

/-- Ring homomorphisms commute with the literal values. -/
theorem val3_map (f : R →+* S) (P : Nat → V3 R) (l : Lit24) :
    val3 (fun i => (P i).map f) l = f (val3 P l) := by
  cases l <;> simp only [val3, V3.map_det, V3.map_dot, V3.map_sub, V3.map_cr, nrm3_map]

theorem cv3_map (f : R →+* S) (P : Nat → V3 R) (t v : Nat) :
    cv3 (fun i => (P i).map f) t v = f (cv3 P t v) := by
  simp only [cv3, map_neg, V3.map_dot, V3.map_sub, nrm3_map]

end Map

/-! ### Rational shapes -/

/-- The real configuration of rational coordinates. -/
noncomputable def ofQ (Q : Nat → V3 ℚ) (i : Nat) : ℝ³ := !₂[((Q i).x : ℝ), ((Q i).y : ℝ), ((Q i).z : ℝ)]

theorem pt_ofQ (Q : Nat → V3 ℚ) : pt (ofQ Q) = fun i => (Q i).map (Rat.castHom ℝ) := by
  funext i
  simp [pt, ofQ, toV3, V3.map]

/-- At a rational shape the value is the cast of the rational value. -/
theorem val_ofQ (Q : Nat → V3 ℚ) (l : Lit24) : val (ofQ Q) l = ((val3 Q l : ℚ) : ℝ) := by
  rw [val_eq_val3, pt_ofQ, val3_map]; rfl

theorem cv_ofQ (Q : Nat → V3 ℚ) (t v : Nat) : cv (ofQ Q) t v = ((cv3 Q t v : ℚ) : ℝ) := by
  rw [cv_eq_cv3, pt_ofQ, cv3_map]; rfl

/-- A sign computed over `ℚ` is the real sign. -/
theorem litHolds_ofQ (Q : Nat → V3 ℚ) (l : Lit24) (s : Int) (h : 0 < (s : ℚ) * val3 Q l) :
    LitHolds (ofQ Q) l s := by
  unfold LitHolds
  rw [val_ofQ]
  exact_mod_cast h

/-- Convexity checked over `ℚ` is real convexity. -/
theorem convex24_ofQ (Q : Nat → V3 ℚ) (h : cvList.all (fun p => decide (0 < cv3 Q p.1 p.2)) = true) :
    Convex24 (ofQ Q) := by
  intro p hp
  have := List.all_eq_true.mp h p hp
  rw [cv_ofQ]
  exact_mod_cast of_decide_eq_true this

end Minimality.T24.SAT
