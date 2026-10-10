module

public import SmallRupert.OctahedronAll
public import SmallRupert.L8T3
public import SmallRupert.L8T4
public import SmallRupert.RightPrism
public import SmallRupert.Witnesses

@[expose] public section

/-!
# Six points in convex position: dependencies, Gale signs, splits, prisms (LEMMAS.md L10)

Setting (S) of L10 (`Six V`): six points, none in the hull of the others,
not coplanar, no five coplanar.  Affine dependencies are functions
`ℝ³ → ℝ` (`IsDepOn V l`); two of them, `l` and `m`, give the Gale vectors
`(l t, m t)` and the determinants `galeD l m s t`.

* §10.1: the vertex lemma, no three collinear points, no three parallel Gale
  vectors, and facets (triangles, quadrilaterals) and independent tetrahedra
  from signs of `galeD`;
* Lemma 10.1 (`exists_split_of_no_partner`): a point without an O-partner
  gives a 2+4 split (a dependency positive at exactly two points);
* Proposition 10.2 (`isRupert_of_all_partners`): three O-pairs form a prism
  (frustum, parallel or translation prism).
-/

namespace SmallRupert

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- `l` is an affine dependency of the points of `V`. -/
def IsDepOn (V : Finset ℝ³) (l : ℝ³ → ℝ) : Prop :=
  ∑ t ∈ V, l t = 0 ∧ ∑ t ∈ V, l t • t = 0

/-- Setting (S) of LEMMAS.md L10. -/
structure Six (V : Finset ℝ³) : Prop where
  card : V.card = 6
  vert : ∀ v ∈ V, v ∉ convexHull ℝ ((V.erase v : Finset ℝ³) : Set ℝ³)
  noncop : ¬ Coplanar ℝ (V : Set ℝ³)
  no5 : ∀ v ∈ V, ¬ Coplanar ℝ ((V.erase v : Finset ℝ³) : Set ℝ³)

/-! ### Sums over six listed points -/

theorem sum_six {M : Type*} [AddCommMonoid M] {a b c d e f : ℝ³}
    (hnd : [a, b, c, d, e, f].Nodup) (g : ℝ³ → M) :
    ∑ t ∈ ({a, b, c, d, e, f} : Finset ℝ³), g t = g a + g b + g c + g d + g e + g f := by
  sorry

/-! ### Dependencies -/

theorem IsDepOn.comb {V : Finset ℝ³} {l m : ℝ³ → ℝ} (hl : IsDepOn V l) (hm : IsDepOn V m)
    (α β : ℝ) : IsDepOn V (fun t => α * l t + β * m t) := by
  sorry

theorem IsDepOn.neg {V : Finset ℝ³} {l : ℝ³ → ℝ} (hl : IsDepOn V l) :
    IsDepOn V (fun t => -l t) := by
  sorry

/-- A dependency applied to an affine function. -/
theorem IsDepOn.apply {V : Finset ℝ³} {l : ℝ³ → ℝ} (hl : IsDepOn V l) (f : ℝ³ →ᵃ[ℝ] ℝ) :
    ∑ t ∈ V, l t * f t = 0 := by
  sorry

theorem IsDepOn.galeD {V : Finset ℝ³} {l m : ℝ³ → ℝ} (hl : IsDepOn V l) (hm : IsDepOn V m)
    (s : ℝ³) : IsDepOn V (galeD l m s) := by
  sorry

/-- The dependency `t ↦ -⟨g_s, g_t⟩`. -/
theorem IsDepOn.nu {V : Finset ℝ³} {l m : ℝ³ → ℝ} (hl : IsDepOn V l) (hm : IsDepOn V m)
    (s : ℝ³) : IsDepOn V (fun t => -(l s * l t + m s * m t)) := by
  sorry

/-! ### §10.1 (a)–(d) -/

/-- **(a) Vertex lemma.**  No dependency is negative at exactly one point and
nonnegative elsewhere. -/
theorem Six.not_single_neg {V : Finset ℝ³} (hS : Six V) {μ : ℝ³ → ℝ} (hμ : IsDepOn V μ)
    {v : ℝ³} (hv : v ∈ V) (hneg : μ v < 0) (hrest : ∀ t ∈ V, t ≠ v → 0 ≤ μ t) : False := by
  sorry

/-- A dependency that is nonnegative (or nonpositive) everywhere vanishes. -/
theorem IsDepOn.eq_zero_of_nonpos {V : Finset ℝ³} {μ : ℝ³ → ℝ} (hμ : IsDepOn V μ)
    (h : ∀ t ∈ V, μ t ≤ 0) : ∀ t ∈ V, μ t = 0 := by
  sorry

/-- **(b)** No three points of `V` are collinear. -/
theorem Six.cross_ne_zero {V : Finset ℝ³} (hS : Six V) {P Q R : ℝ³} (hP : P ∈ V) (hQ : Q ∈ V)
    (hR : R ∈ V) (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) : cross (Q - P) (R - P) ≠ 0 := by
  sorry

/-- A nonzero dependency vanishes at no three points (support at least 4). -/
theorem Six.no_three_zeros {V : Finset ℝ³} (hS : Six V) {μ : ℝ³ → ℝ} (hμ : IsDepOn V μ)
    (hne : ∃ t ∈ V, μ t ≠ 0) {a b c : ℝ³} (ha : a ∈ V) (hb : b ∈ V) (hc : c ∈ V) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (h0a : μ a = 0) (h0b : μ b = 0) (h0c : μ c = 0) : False := by
  sorry

/-- A Gale frame: two dependencies, with nonzero Gale vectors, and two points
where they take the values of barycentric dependencies. -/
structure GaleFrame (V : Finset ℝ³) (l m : ℝ³ → ℝ) : Prop where
  hl : IsDepOn V l
  hm : IsDepOn V m
  ne : ∀ t ∈ V, l t ≠ 0 ∨ m t ≠ 0
  base : ∃ D₀ ∈ V, ∃ E₀ ∈ V, l D₀ = -1 ∧ m D₀ = 0 ∧ l E₀ = 0 ∧ m E₀ = -1

/-- Every six-point set in setting (S) has a Gale frame. -/
theorem Six.exists_galeFrame {V : Finset ℝ³} (hS : Six V) : ∃ l m, GaleFrame V l m := by
  sorry

/-- `galeD l m s ·` is nonzero somewhere. -/
theorem GaleFrame.exists_galeD_ne {V : Finset ℝ³} {l m : ℝ³ → ℝ} (hF : GaleFrame V l m)
    {s : ℝ³} (hs : s ∈ V) : ∃ t ∈ V, galeD l m s t ≠ 0 := by
  sorry

/-- **(d)** No three Gale vectors are pairwise parallel. -/
theorem GaleFrame.no_three_parallel {V : Finset ℝ³} {l m : ℝ³ → ℝ} (hS : Six V)
    (hF : GaleFrame V l m) {s t u : ℝ³} (hs : s ∈ V) (ht : t ∈ V) (hu : u ∈ V) (hst : s ≠ t)
    (hsu : s ≠ u) (htu : t ≠ u) (h1 : galeD l m s t = 0) (h2 : galeD l m s u = 0) : False := by
  sorry

/-! ### §10.1 (e): facets from Gale signs -/

/-- A triangle facet from three negative Gale determinants of its complement. -/
theorem isFacetTriangle_of_gale {V : Finset ℝ³} (hS : Six V) {l m : ℝ³ → ℝ}
    (hl : IsDepOn V l) (hm : IsDepOn V m) {P Q R X Y Z : ℝ³} (hV : V = {P, Q, R, X, Y, Z})
    (hnd : [P, Q, R, X, Y, Z].Nodup) (h₁ : galeD l m X Y < 0) (h₂ : galeD l m Y Z < 0)
    (h₃ : galeD l m Z X < 0) : IsFacetTriangle V P Q R := by
  sorry

/-- A quadrilateral facet from a parallel opposite complementary pair. -/
theorem isFacet_quad_of_gale {V : Finset ℝ³} (hS : Six V) {l m : ℝ³ → ℝ}
    (hl : IsDepOn V l) (hm : IsDepOn V m) {P Q R Z X Y : ℝ³} (hV : V = {P, Q, R, Z, X, Y})
    (hnd : [P, Q, R, Z, X, Y].Nodup) (h₀ : galeD l m X Y = 0)
    (h₁ : galeD l m X Z * galeD l m Y Z < 0) : IsFacet V {P, Q, R, Z} := by
  sorry

/-- The complement of a non-parallel pair is an independent tetrahedron. -/
theorem affineIndependent_of_gale {V : Finset ℝ³} (hS : Six V) {l m : ℝ³ → ℝ}
    (hl : IsDepOn V l) (hm : IsDepOn V m) {A B C T X Y : ℝ³} (hV : V = {A, B, C, T, X, Y})
    (hnd : [A, B, C, T, X, Y].Nodup) (h : galeD l m X Y ≠ 0) :
    AffineIndependent ℝ ![A, B, C, T] := by
  sorry

/-! ### Lemma 10.1: a 2+4 split -/

/-- `s, t` are an O-pair: antiparallel Gale vectors. -/
def IsOPair (l m : ℝ³ → ℝ) (s t : ℝ³) : Prop :=
  s ≠ t ∧ galeD l m s t = 0 ∧ l s * l t + m s * m t < 0

/-- **Lemma 10.1.** A point without an O-partner gives a 2+4 split. -/
theorem exists_split_of_no_partner {V : Finset ℝ³} (hS : Six V) {l m : ℝ³ → ℝ}
    (hF : GaleFrame V l m) {i : ℝ³} (hi : i ∈ V) (hno : ∀ j ∈ V, ¬ IsOPair l m i j) :
    ∃ D ∈ V, ∃ E ∈ V, D ≠ E ∧ ∃ μ : ℝ³ → ℝ, IsDepOn V μ ∧ 0 < μ D ∧ 0 < μ E ∧
      ∀ x ∈ V, x ≠ D → x ≠ E → μ x < 0 := by
  sorry

/-! ### Proposition 10.2: prisms -/

/-- **Proposition 10.2.** If every point has an O-partner, `V` is a prism and
Rupert. -/
theorem isRupert_of_all_partners {V : Finset ℝ³} (hS : Six V) {l m : ℝ³ → ℝ}
    (hF : GaleFrame V l m) (hall : ∀ i ∈ V, ∃ j ∈ V, IsOPair l m i j) : IsRupert V := by
  sorry

end SmallRupert

end
