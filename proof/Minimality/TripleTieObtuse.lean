module

public import Minimality.TripleTie
public import Minimality.SlideDS
public import Minimality.Prism
public import Minimality.L8T3
public import Minimality.L8Shapes
public import Minimality.Octahedron

@[expose] public section

/-!
# The triple tie with a right or obtuse apex (`FEWER-FACES-PROOFS.md` §24, Theorem 24.8)

Case (c) of Theorem 24.5 (the triple tie of two quadrilateral faces `F1`, `F2` meeting only in the
vertex `v`, both faces two-sided) is not settled by a sector tilt when the shadow triangle `T` has
acute far angles.  **Theorem 24.8** settles it when the angle of `T` at `v` is at least `π/2`
(`b ≤ 0` below), by sliding along the face circle of `F1` instead of tilting: the horizontal view
along `a = p - v` has `F1` edge-on with chord ends `M±` (the middles of `F1`), the points `v`, `p`
chord middles, and the rim a cyclic subsequence of `(M+, M-, N-, B, N+)` with depths
`(t1, t2, s2 b, b, s1 b)` (in units of `⟪a, a⟫`); for `b < 0` the cycle has one maximum and one
minimum, for `b = 0` the same holds at small tilts of the right side, and the slide theorem
(`isRupert_of_slideG`, Theorem 18.1) applies.

* `CObt`: the Euclidean model of §24.3 (an orthogonal frame `A, N, E` at the apex `v`, the seven
  points with the coordinates of the paper); `CObt.isRupert_model` is Theorem 24.8 for it, in the
  four regimes (`regime5`, `regime4a`, `regime4b`, `regime3`) according to which of the middles
  `N±` of `F2` are corners of the rim at the horizontal view.  The tie `N+` on the edge `M+ B`
  is a corner after the slide and `N-` on the edge `M- B` is not: `SlideTest` with the derivative.
* `CObt.noBad`: no persistent horizontal double normal (`NoBadNormalR`).  The paper's exceptional
  case (the orthogonal foot on the plane of `F1` of `B`, `N+` or `N-` on the open diagonal
  `M+ M-`) never occurs for `b ≤ 0`, because the feet have depth `≤ 0` along `a` and the diagonal
  has depth `> 0`; the remaining bad directions are excluded by `CObt.key` (the feet of the
  two edges meet only at a common vertex).  So the statement has no exceptional hypothesis.
* `isRupert_of_obtuse_apex`: the facet form (two quadrilateral facets covering `V`, any facet
  functionals, `p`, `q` the far ends), obtaining the model from the facets.
* `TriGenTieO`: `TriGenTieT` with the right or obtuse apex as one more way out at the far ends;
  `isRupert_of_facets_vertex_tieO`: `TriGenTieO` gives Rupert (`TriGenTieT` is `TriGenTieO`
  minus the new clause, `TriGenTieT.toO`).
-/

namespace Minimality

open Finset Filter Topology
open scoped RealInnerProductSpace

/-! ### The orthogonal frame -/

/-- Coordinates `(x, y, z)` in the orthogonal frame `A, N, E` at `v`. -/
noncomputable def cpt (v A N E : ℝ³) (x y z : ℝ) : ℝ³ := v + x • A + y • N + z • E

theorem cpt_sub (v A N E : ℝ³) (x y z x' y' z' : ℝ) :
    cpt v A N E x y z - cpt v A N E x' y' z' =
      (x - x') • A + (y - y') • N + (z - z') • E := by
  simp only [cpt]; module

theorem det3_coord (A N E : ℝ³) (a1 b1 c1 a2 b2 c2 a3 b3 c3 : ℝ) :
    det3 (a1 • A + b1 • N + c1 • E) (a2 • A + b2 • N + c2 • E) (a3 • A + b3 • N + c3 • E) =
      det3 A N E * (a1 * (b2 * c3 - c2 * b3) - b1 * (a2 * c3 - c2 * a3) +
        c1 * (a2 * b3 - b2 * a3)) := by
  simp only [det3, cross, PiLp.inner_apply, Fin.sum_univ_three, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, RCLike.inner_apply, conj_trivial]
  simp
  ring

/-- **The case-(c) shape at the apex** (§24.3, Euclidean model): `v` the apex, `A = p - v`
(the far end `p` of the face `F1`), `E` the line direction (`F1` and `F2` contain the line
`v + R E`), `N` the part of `q - v` perpendicular to `A` and `E`.  The seven points are
`v`, `p = v + A`, `M± ` (the middles of `F1`), `B = q`, `N±` (the middles of `F2`); in the
frame `(A, N, E)` they have the coordinates `(1,0,0)`, `(t1, 0, h1)`, `(t2, 0, -h2)`,
`(b, 1, 0)`, `(s1 b, s1, k1)`, `(s2 b, s2, -k2)`.  The apex angle is `≥ π/2` iff `b ≤ 0`. -/
structure CObt where
  v : ℝ³
  A : ℝ³
  N : ℝ³
  E : ℝ³
  b : ℝ
  t1 : ℝ
  t2 : ℝ
  h1 : ℝ
  h2 : ℝ
  s1 : ℝ
  s2 : ℝ
  k1 : ℝ
  k2 : ℝ
  hAN : ⟪A, N⟫ = 0
  hAE : ⟪A, E⟫ = 0
  hNE : ⟪N, E⟫ = 0
  hA : A ≠ 0
  hN : N ≠ 0
  hE : E ≠ 0
  hb : b ≤ 0
  ht1 : 0 < t1
  ht1' : t1 < 1
  ht2 : 0 < t2
  ht2' : t2 < 1
  hh1 : 0 < h1
  hh2 : 0 < h2
  hs1 : 0 < s1
  hs1' : s1 < 1
  hs2 : 0 < s2
  hs2' : s2 < 1
  hk1 : 0 < k1
  hk2 : 0 < k2

namespace CObt

variable (c : CObt)

theorem hNA : ⟪c.N, c.A⟫ = 0 := by rw [real_inner_comm]; exact c.hAN
theorem hEA : ⟪c.E, c.A⟫ = 0 := by rw [real_inner_comm]; exact c.hAE
theorem hEN : ⟪c.E, c.N⟫ = 0 := by rw [real_inner_comm]; exact c.hNE

theorem a2_pos : 0 < ⟪c.A, c.A⟫ := real_inner_self_pos.mpr c.hA
theorem n2_pos : 0 < ⟪c.N, c.N⟫ := real_inner_self_pos.mpr c.hN
theorem e2_pos : 0 < ⟪c.E, c.E⟫ := real_inner_self_pos.mpr c.hE

theorem inner_coord_A (a b d : ℝ) : ⟪a • c.A + b • c.N + d • c.E, c.A⟫ = a * ⟪c.A, c.A⟫ := by
  simp only [inner_add_left, real_inner_smul_left, c.hNA, c.hEA]; ring

theorem inner_coord_N (a b d : ℝ) : ⟪a • c.A + b • c.N + d • c.E, c.N⟫ = b * ⟪c.N, c.N⟫ := by
  simp only [inner_add_left, real_inner_smul_left, c.hAN, c.hEN]; ring

theorem inner_coord_E (a b d : ℝ) : ⟪a • c.A + b • c.N + d • c.E, c.E⟫ = d * ⟪c.E, c.E⟫ := by
  simp only [inner_add_left, real_inner_smul_left, c.hAE, c.hNE]; ring

theorem coord_eq_zero {a b d : ℝ} (h : a • c.A + b • c.N + d • c.E = 0) :
    a = 0 ∧ b = 0 ∧ d = 0 := by
  have h1 := c.inner_coord_A a b d
  have h2 := c.inner_coord_N a b d
  have h3 := c.inner_coord_E a b d
  rw [h, inner_zero_left] at h1 h2 h3
  refine ⟨?_, ?_, ?_⟩
  · exact (mul_eq_zero.mp h1.symm).resolve_right c.a2_pos.ne'
  · exact (mul_eq_zero.mp h2.symm).resolve_right c.n2_pos.ne'
  · exact (mul_eq_zero.mp h3.symm).resolve_right c.e2_pos.ne'

theorem cpt_inj {x y z x' y' z' : ℝ}
    (h : cpt c.v c.A c.N c.E x y z = cpt c.v c.A c.N c.E x' y' z') :
    x = x' ∧ y = y' ∧ z = z' := by
  have h0 : cpt c.v c.A c.N c.E x y z - cpt c.v c.A c.N c.E x' y' z' = 0 := sub_eq_zero.mpr h
  rw [cpt_sub] at h0
  obtain ⟨h1, h2, h3⟩ := c.coord_eq_zero h0
  exact ⟨by linarith, by linarith, by linarith⟩

/-- The determinant of the frame. -/
noncomputable def D : ℝ := det3 c.A c.N c.E

theorem D_smul (w : ℝ³) :
    c.D • w = ⟪w, c.A⟫ • cross c.N c.E + ⟪w, c.N⟫ • cross c.E c.A + ⟪w, c.E⟫ • cross c.A c.N := by
  ext i
  fin_cases i <;>
  simp [D, det3, cross, PiLp.inner_apply, Fin.sum_univ_three] <;> ring

theorem gram_det (A N E : ℝ³) : det3 A N E ^ 2 = ⟪A, A⟫ * ⟪N, N⟫ * ⟪E, E⟫ +
    2 * ⟪A, N⟫ * ⟪N, E⟫ * ⟪E, A⟫ - ⟪A, A⟫ * ⟪N, E⟫ ^ 2 - ⟪N, N⟫ * ⟪E, A⟫ ^ 2 -
    ⟪E, E⟫ * ⟪A, N⟫ ^ 2 := by
  simp only [det3, cross, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
  simp
  ring

theorem D_sq : c.D ^ 2 = ⟪c.A, c.A⟫ * ⟪c.N, c.N⟫ * ⟪c.E, c.E⟫ := by
  have := gram_det c.A c.N c.E
  rw [c.hAN, c.hNE, c.hEA] at this
  simpa [D] using this

theorem D_ne : c.D ≠ 0 := by
  intro h0
  have := c.D_sq
  rw [h0] at this
  have : 0 < ⟪c.A, c.A⟫ * ⟪c.N, c.N⟫ * ⟪c.E, c.E⟫ :=
    mul_pos (mul_pos c.a2_pos c.n2_pos) c.e2_pos
  nlinarith

theorem DD_pos : 0 < c.D * c.D := mul_self_pos.mpr c.D_ne

/-- Every vector is its expansion in the orthogonal frame. -/
theorem expand (w : ℝ³) : w = (⟪w, c.A⟫ / ⟪c.A, c.A⟫) • c.A + (⟪w, c.N⟫ / ⟪c.N, c.N⟫) • c.N +
    (⟪w, c.E⟫ / ⟪c.E, c.E⟫) • c.E := by
  have hD := c.D_ne
  have hA := c.D_smul c.A
  have hN := c.D_smul c.N
  have hE := c.D_smul c.E
  have h := c.D_smul w
  rw [c.hAN, c.hAE, zero_smul, zero_smul, add_zero, add_zero] at hA
  rw [c.hNA, c.hNE, zero_smul, zero_smul, zero_add, add_zero] at hN
  rw [c.hEA, c.hEN, zero_smul, zero_smul, zero_add, zero_add] at hE
  have a2 := c.a2_pos.ne'
  have n2 := c.n2_pos.ne'
  have e2 := c.e2_pos.ne'
  have e1 : c.D • ((⟪w, c.A⟫ / ⟪c.A, c.A⟫) • c.A) = ⟪w, c.A⟫ • cross c.N c.E := by
    rw [smul_comm, hA, smul_smul, div_mul_cancel₀ _ a2]
  have e2' : c.D • ((⟪w, c.N⟫ / ⟪c.N, c.N⟫) • c.N) = ⟪w, c.N⟫ • cross c.E c.A := by
    rw [smul_comm, hN, smul_smul, div_mul_cancel₀ _ n2]
  have e3 : c.D • ((⟪w, c.E⟫ / ⟪c.E, c.E⟫) • c.E) = ⟪w, c.E⟫ • cross c.A c.N := by
    rw [smul_comm, hE, smul_smul, div_mul_cancel₀ _ e2]
  have key : c.D • w = c.D • ((⟪w, c.A⟫ / ⟪c.A, c.A⟫) • c.A + (⟪w, c.N⟫ / ⟪c.N, c.N⟫) • c.N +
      (⟪w, c.E⟫ / ⟪c.E, c.E⟫) • c.E) := by
    simp only [smul_add, e1, e2', e3]
    exact h
  exact (smul_right_inj hD).mp key

/-! #### The seven points -/

/-- The apex `v` in frame coordinates. -/
theorem v_eq : c.v = cpt c.v c.A c.N c.E 0 0 0 := by simp [cpt]

/-- The far end `p = v + A` of `F1`. -/
noncomputable def pP : ℝ³ := cpt c.v c.A c.N c.E 1 0 0
/-- The upper middle `M+` of `F1`. -/
noncomputable def M1 : ℝ³ := cpt c.v c.A c.N c.E c.t1 0 c.h1
/-- The lower middle `M-` of `F1`. -/
noncomputable def M2 : ℝ³ := cpt c.v c.A c.N c.E c.t2 0 (-c.h2)
/-- The far end `B = q` of `F2`. -/
noncomputable def Bq : ℝ³ := cpt c.v c.A c.N c.E c.b 1 0
/-- The upper middle `N+` of `F2`. -/
noncomputable def N1 : ℝ³ := cpt c.v c.A c.N c.E (c.s1 * c.b) c.s1 c.k1
/-- The lower middle `N-` of `F2`. -/
noncomputable def N2 : ℝ³ := cpt c.v c.A c.N c.E (c.s2 * c.b) c.s2 (-c.k2)

/-- The seven points of the case-(c) shape. -/
noncomputable def V : Finset ℝ³ := by
  classical
  exact {c.v, c.pP, c.M1, c.M2, c.Bq, c.N1, c.N2}

theorem det3_cpt_A (x0 y0 z0 x1 y1 z1 x2 y2 z2 : ℝ) :
    det3 (cpt c.v c.A c.N c.E x1 y1 z1 - cpt c.v c.A c.N c.E x0 y0 z0)
      (cpt c.v c.A c.N c.E x2 y2 z2 - cpt c.v c.A c.N c.E x0 y0 z0) c.A =
      c.D * ((y1 - y0) * (z2 - z0) - (z1 - z0) * (y2 - y0)) := by
  rw [cpt_sub, cpt_sub]
  have h := det3_coord c.A c.N c.E (x1 - x0) (y1 - y0) (z1 - z0) (x2 - x0) (y2 - y0) (z2 - z0) 1 0 0
  simp only [one_smul, zero_smul, add_zero] at h
  rw [h]; unfold D; ring

theorem det3_cpt_E (x0 y0 z0 x1 y1 z1 x2 y2 z2 : ℝ) :
    det3 (cpt c.v c.A c.N c.E x1 y1 z1 - cpt c.v c.A c.N c.E x0 y0 z0)
      (cpt c.v c.A c.N c.E x2 y2 z2 - cpt c.v c.A c.N c.E x0 y0 z0) c.E =
      c.D * ((x1 - x0) * (y2 - y0) - (y1 - y0) * (x2 - x0)) := by
  rw [cpt_sub, cpt_sub]
  have h := det3_coord c.A c.N c.E (x1 - x0) (y1 - y0) (z1 - z0) (x2 - x0) (y2 - y0) (z2 - z0) 0 0 1
  simp only [one_smul, zero_smul, add_zero, zero_add] at h
  rw [h]; unfold D; ring

theorem pos_DD {q : ℝ} (h : 0 < q) : 0 < c.D * (c.D * q) := by
  rw [← mul_assoc]; exact mul_pos c.DD_pos h

/-! #### Rim edges and the absence of persistent double normals -/

/-- The five possible corners of the rim at the horizontal view. -/
def IsRim (P : ℝ³) : Prop := P = c.M1 ∨ P = c.M2 ∨ P = c.N2 ∨ P = c.Bq ∨ P = c.N1

/-- The edges that can occur in a rim cycle, one orientation. -/
def EdgeU (P Q : ℝ³) : Prop :=
  (P = c.M1 ∧ Q = c.M2) ∨ (P = c.M2 ∧ Q = c.N2) ∨ (P = c.M2 ∧ Q = c.Bq) ∨
    (P = c.N2 ∧ Q = c.Bq) ∨ (P = c.Bq ∧ Q = c.N1) ∨ (P = c.M1 ∧ Q = c.Bq) ∨ (P = c.M1 ∧ Q = c.N1)

/-- The edges that can occur in a rim cycle. -/
def Edge (P Q : ℝ³) : Prop := c.EdgeU P Q ∨ c.EdgeU Q P

theorem Edge.rim {P Q : ℝ³} (h : c.Edge P Q) : c.IsRim P ∧ c.IsRim Q := by
  unfold Edge EdgeU IsRim at *
  rcases h with h | h <;>
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  simp

theorem seg_cpt {x y z x' y' z' : ℝ} {Y : ℝ³}
    (h : Y ∈ segment ℝ (cpt c.v c.A c.N c.E x y z) (cpt c.v c.A c.N c.E x' y' z')) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧
      Y = cpt c.v c.A c.N c.E (a * x + b * x') (a * y + b * y') (a * z + b * z') := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := h
  refine ⟨a, b, ha, hb, hab, ?_⟩
  obtain rfl : b = 1 - a := by linarith
  simp only [cpt]; module

/-- The coordinates of a difference of two points. -/
theorem inner_cpt_sub_A (x y z x' y' z' : ℝ) :
    ⟪cpt c.v c.A c.N c.E x y z - cpt c.v c.A c.N c.E x' y' z', c.A⟫ = (x - x') * ⟪c.A, c.A⟫ := by
  rw [cpt_sub, c.inner_coord_A]

theorem inner_cpt_sub_N (x y z x' y' z' : ℝ) :
    ⟪cpt c.v c.A c.N c.E x y z - cpt c.v c.A c.N c.E x' y' z', c.N⟫ = (y - y') * ⟪c.N, c.N⟫ := by
  rw [cpt_sub, c.inner_coord_N]

theorem inner_cpt_sub_E (x y z x' y' z' : ℝ) :
    ⟪cpt c.v c.A c.N c.E x y z - cpt c.v c.A c.N c.E x' y' z', c.E⟫ = (z - z') * ⟪c.E, c.E⟫ := by
  rw [cpt_sub, c.inner_coord_E]

/-- Real core for the edges `(M-, F)`: a chord point and an edge point at the same depth
and height must be the vertex `M-`. -/
theorem keyM2 (xF zF : ℝ) (hx : xF ≤ 0) (hz : zF ≤ 0) {a b a' b' : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (ha' : 0 ≤ a') (hb' : 0 ≤ b') (hab' : a' + b' = 1)
    (e1 : a' * c.t1 + b' * c.t2 = a * c.t2 + b * xF)
    (e2 : a' * c.h1 + b' * (-c.h2) = a * (-c.h2) + b * zF) : b = 0 := by
  have h1 := c.ht1; have h2 := c.ht2; have g1 := c.hh1; have g2 := c.hh2
  by_contra hne
  have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hne)
  obtain rfl : a = 1 - b := by linarith
  obtain rfl : b' = 1 - a' := by linarith
  have hlt : a' < b := by nlinarith
  nlinarith [mul_pos (sub_pos.mpr hlt) h2, mul_nonneg ha' h1.le, mul_nonneg hbpos.le (neg_nonneg.mpr hx)]

/-- Real core for the edges `(M+, F)`. -/
theorem keyM1 (xF zF : ℝ) (hx : xF ≤ 0) (hz : 0 ≤ zF) {a b a' b' : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (ha' : 0 ≤ a') (hb' : 0 ≤ b') (hab' : a' + b' = 1)
    (e1 : a' * c.t1 + b' * c.t2 = a * c.t1 + b * xF)
    (e2 : a' * c.h1 + b' * (-c.h2) = a * c.h1 + b * zF) : b = 0 := by
  have h1 := c.ht1; have h2 := c.ht2; have g1 := c.hh1; have g2 := c.hh2
  by_contra hne
  have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hne)
  obtain rfl : a = 1 - b := by linarith
  obtain rfl : a' = 1 - b' := by linarith
  have hlt : b' < b := by nlinarith
  nlinarith [mul_pos (sub_pos.mpr hlt) h1, mul_nonneg hb' h2.le, mul_nonneg hbpos.le (neg_nonneg.mpr hx)]

/-- Real core for the edges between far corners. -/
theorem keyFF (xP xQ : ℝ) (hP : xP ≤ 0) (hQ : xQ ≤ 0) {a b a' b' : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ha' : 0 ≤ a') (hb' : 0 ≤ b') (hab' : a' + b' = 1)
    (e1 : a' * c.t1 + b' * c.t2 = a * xP + b * xQ) : False := by
  have h1 := c.ht1; have h2 := c.ht2
  have : 0 < a' * c.t1 + b' * c.t2 := by
    rcases lt_or_ge 0 a' with h | h
    · nlinarith [mul_pos h h1, mul_nonneg hb' h2.le]
    · have : a' = 0 := le_antisymm h ha'
      subst this
      have : b' = 1 := by linarith
      subst this; linarith
  nlinarith [mul_nonneg ha (neg_nonneg.mpr hP), mul_nonneg hb (neg_nonneg.mpr hQ)]

theorem key_gen {xP yP zP xQ yQ zQ : ℝ}
    (hreal : ∀ a b a' b' : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → 0 ≤ a' → 0 ≤ b' → a' + b' = 1 →
      a' * c.t1 + b' * c.t2 = a * xP + b * xQ →
      a' * c.h1 + b' * (-c.h2) = a * zP + b * zQ → a' * 0 + b' * 0 = a * yP + b * yQ)
    {Y Y' : ℝ³} (hY : Y ∈ segment ℝ (cpt c.v c.A c.N c.E xP yP zP) (cpt c.v c.A c.N c.E xQ yQ zQ))
    (hY' : Y' ∈ segment ℝ c.M1 c.M2)
    (hA : ⟪Y' - Y, c.A⟫ = 0) (hE : ⟪Y' - Y, c.E⟫ = 0) : ⟪Y' - Y, c.N⟫ = 0 := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := c.seg_cpt hY
  obtain ⟨a', b', ha', hb', hab', rfl⟩ := c.seg_cpt (x := c.t1) (y := 0) (z := c.h1)
    (x' := c.t2) (y' := 0) (z' := -c.h2) hY'
  rw [c.inner_cpt_sub_A] at hA
  rw [c.inner_cpt_sub_E] at hE
  rw [c.inner_cpt_sub_N]
  have h1 := (mul_eq_zero.mp hA).resolve_right c.a2_pos.ne'
  have h2 := (mul_eq_zero.mp hE).resolve_right c.e2_pos.ne'
  have := hreal a b a' b' ha hb hab ha' hb' hab' (by linarith) (by linarith)
  rw [this]; ring

theorem key' {P Q : ℝ³} (h : c.EdgeU P Q) {Y Y' : ℝ³} (hY : Y ∈ segment ℝ P Q)
    (hY' : Y' ∈ segment ℝ c.M1 c.M2) (hA : ⟪Y' - Y, c.A⟫ = 0) (hE : ⟪Y' - Y, c.E⟫ = 0) :
    ⟪Y' - Y, c.N⟫ = 0 := by
  have hsb : c.s1 * c.b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos c.hs1.le c.hb
  have hsb2 : c.s2 * c.b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos c.hs2.le c.hb
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact c.key_gen (fun a b a' b' _ _ _ _ _ _ _ _ => by ring) hY hY' hA hE
  · refine c.key_gen (fun a b a' b' ha hb hab ha' hb' hab' e1 e2 => ?_) hY hY' hA hE
    have := c.keyM2 (c.s2 * c.b) (-c.k2) hsb2 (by linarith [c.hk2]) ha hb hab ha' hb' hab' e1 e2
    rw [this]; ring
  · refine c.key_gen (fun a b a' b' ha hb hab ha' hb' hab' e1 e2 => ?_) hY hY' hA hE
    have := c.keyM2 c.b 0 c.hb le_rfl ha hb hab ha' hb' hab' e1 e2
    rw [this]; ring
  · refine c.key_gen (fun a b a' b' ha hb hab ha' hb' hab' e1 e2 => ?_) hY hY' hA hE
    exact (c.keyFF (c.s2 * c.b) c.b hsb2 c.hb ha hb ha' hb' hab' e1).elim
  · refine c.key_gen (fun a b a' b' ha hb hab ha' hb' hab' e1 e2 => ?_) hY hY' hA hE
    exact (c.keyFF c.b (c.s1 * c.b) c.hb hsb ha hb ha' hb' hab' e1).elim
  · refine c.key_gen (fun a b a' b' ha hb hab ha' hb' hab' e1 e2 => ?_) hY hY' hA hE
    have := c.keyM1 c.b 0 c.hb le_rfl ha hb hab ha' hb' hab' e1 e2
    rw [this]; ring
  · refine c.key_gen (fun a b a' b' ha hb hab ha' hb' hab' e1 e2 => ?_) hY hY' hA hE
    have := c.keyM1 (c.s1 * c.b) c.k1 hsb c.hk1.le ha hb hab ha' hb' hab' e1 e2
    rw [this]; ring

theorem key {P Q : ℝ³} (h : c.Edge P Q) {Y Y' : ℝ³} (hY : Y ∈ segment ℝ P Q)
    (hY' : Y' ∈ segment ℝ c.M1 c.M2) (hA : ⟪Y' - Y, c.A⟫ = 0) (hE : ⟪Y' - Y, c.E⟫ = 0) :
    ⟪Y' - Y, c.N⟫ = 0 := by
  rcases h with h | h
  · exact c.key' h hY hY' hA hE
  · rw [segment_symm] at hY
    exact c.key' h hY hY' hA hE

theorem vd {P Q : ℝ³} (hP : c.IsRim P) (hQ : c.IsRim Q) (hA : ⟪Q - P, c.A⟫ = 0)
    (hE : ⟪Q - P, c.E⟫ = 0) : Q = P := by
  have hsb : c.s1 * c.b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos c.hs1.le c.hb
  have hsb2 : c.s2 * c.b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos c.hs2.le c.hb
  have t1 := c.ht1; have t2 := c.ht2; have g1 := c.hh1; have g2 := c.hh2
  have k1 := c.hk1; have k2 := c.hk2
  unfold IsRim at hP hQ
  rcases hP with rfl | rfl | rfl | rfl | rfl <;> rcases hQ with rfl | rfl | rfl | rfl | rfl <;>
  first
  | rfl
  | (exfalso
     simp only [M1, M2, N1, N2, Bq] at hA hE
     rw [inner_cpt_sub_A] at hA
     rw [inner_cpt_sub_E] at hE
     have h1 := (mul_eq_zero.mp hA).resolve_right c.a2_pos.ne'
     have h2 := (mul_eq_zero.mp hE).resolve_right c.e2_pos.ne'
     linarith)

theorem ec {P Q : ℝ³} (h : c.Edge P Q) (hN : ⟪Q - P, c.N⟫ = 0) :
    (P = c.M1 ∧ Q = c.M2) ∨ (P = c.M2 ∧ Q = c.M1) := by
  have s1 := c.hs1; have s1' := c.hs1'; have s2 := c.hs2; have s2' := c.hs2'
  unfold Edge EdgeU at h
  rcases h with h | h <;>
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  first
  | (left; exact ⟨rfl, rfl⟩)
  | (right; exact ⟨rfl, rfl⟩)
  | (exfalso
     simp only [M1, M2, N1, N2, Bq] at hN
     rw [inner_cpt_sub_N] at hN
     have h1 := (mul_eq_zero.mp hN).resolve_right c.n2_pos.ne'
     linarith)

theorem inner_perpTo_self' (w e : ℝ³) : ⟪perpTo w e, e⟫ = 0 := by
  by_cases he : ⟪e, e⟫ = 0
  · have : e = 0 := inner_self_eq_zero.mp he
    rw [this, inner_zero_right]
  · simp only [perpTo, inner_sub_left, real_inner_smul_left]
    rw [div_mul_cancel₀ _ he, sub_self]

theorem ln {l : ℝ³} (hl : l ≠ 0) (hA : ⟪l, c.A⟫ = 0) (hE : ⟪l, c.E⟫ = 0) :
    ∃ κ : ℝ, κ ≠ 0 ∧ l = κ • c.N := by
  refine ⟨⟪l, c.N⟫ / ⟪c.N, c.N⟫, ?_, ?_⟩
  · intro h0
    apply hl
    have := c.expand l
    rw [hA, hE, h0] at this
    simpa using this
  · have := c.expand l
    rw [hA, hE] at this
    simpa using this

theorem noBad {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (hedge : ∀ i, c.Edge (x i) (x (i + 1))) :
    NoBadNormalR x c.A c.E := by
  intro i j hov l hl
  by_contra hcon
  simp only [not_or, not_not, ne_eq] at hcon
  obtain ⟨hlA, hlE, hNF⟩ := hcon
  unfold NoFeet at hNF
  rw [not_not] at hNF
  obtain ⟨Y, hY, Y', hY', r, hr, hYY⟩ := hNF
  have hl' := hl
  unfold pairDirs at hl'
  rw [Finset.mem_filter] at hl'
  obtain ⟨hlmem, hl0⟩ := hl'
  obtain ⟨κ, hκ, hlκ⟩ := c.ln hl0 hlA hlE
  have hdA : ⟪Y' - Y, c.A⟫ = 0 := by rw [hYY, real_inner_smul_left, hlA, mul_zero]
  have hdE : ⟪Y' - Y, c.E⟫ = 0 := by rw [hYY, real_inner_smul_left, hlE, mul_zero]
  have hNN : ⟪Y' - Y, c.N⟫ ≠ 0 := by
    rw [hYY, hlκ, smul_smul, real_inner_smul_left]
    exact mul_ne_zero (mul_ne_zero hr hκ) c.n2_pos.ne'
  have hei := hedge i
  have hej := hedge j
  -- an inner product with `l` vanishing gives one with `N`
  have toN : ∀ w : ℝ³, ⟪l, w⟫ = 0 → ⟪w, c.N⟫ = 0 := by
    intro w hw
    rw [hlκ, real_inner_smul_left] at hw
    rw [real_inner_comm]
    exact (mul_eq_zero.mp hw).resolve_left hκ
  -- the chord case of an edge
  have chordseg : ∀ P Q : ℝ³, ((P = c.M1 ∧ Q = c.M2) ∨ (P = c.M2 ∧ Q = c.M1)) →
      ∀ Z, Z ∈ segment ℝ P Q → Z ∈ segment ℝ c.M1 c.M2 := by
    intro P Q h Z hZ
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hZ
    · rwa [segment_symm] at hZ
  have negdiff : ∀ w w' : ℝ³, ⟪w - w', c.A⟫ = 0 → ⟪w' - w, c.A⟫ = 0 := by
    intro w w' h; rw [← neg_sub, inner_neg_left, h, neg_zero]
  have negdiffE : ∀ w w' : ℝ³, ⟪w - w', c.E⟫ = 0 → ⟪w' - w, c.E⟫ = 0 := by
    intro w w' h; rw [← neg_sub, inner_neg_left, h, neg_zero]
  have negdiffN : ∀ w w' : ℝ³, ⟪w - w', c.N⟫ = 0 → ⟪w' - w, c.N⟫ = 0 := by
    intro w w' h; rw [← neg_sub, inner_neg_left, h, neg_zero]
  -- the case `l ⟂ edge i` forcing `i` to be the chord; then use the feet on edge `j`
  have caseI : ⟪c.N, x (i + 1) - x i⟫ = 0 → False := by
    intro hN
    have hch := c.ec hei (by rw [real_inner_comm]; exact hN)
    have hY1 := chordseg _ _ hch Y hY
    have := c.key hej hY' hY1 (negdiff _ _ hdA) (negdiffE _ _ hdE)
    exact hNN (negdiffN _ _ this)
  have caseJ : ⟪c.N, x (j + 1) - x j⟫ = 0 → False := by
    intro hN
    have hch := c.ec hej (by rw [real_inner_comm]; exact hN)
    have hY1 := chordseg _ _ hch Y' hY'
    exact hNN (c.key hei hY hY1 hdA hdE)
  rcases Finset.mem_insert.mp hlmem with hcr | hbig
  · -- the cross product of the two edges
    have h1 : ⟪c.N, x (i + 1) - x i⟫ = 0 := by
      rw [real_inner_comm]; apply toN
      rw [hcr]; exact inner_cross_left _ _
    exact caseI h1
  · obtain ⟨⟨m, n⟩, hmn, hlq⟩ := Finset.mem_biUnion.mp hbig
    simp only [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton] at hmn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hlq
    rcases hlq with h | h | h
    · apply caseJ
      rw [real_inner_comm]; apply toN
      rw [h]; exact inner_perpTo_self' _ _
    · apply caseI
      rw [real_inner_comm]; apply toN
      rw [h]; exact inner_perpTo_self' _ _
    · have hm : c.IsRim (x m) := by
        rcases hmn.1 with rfl | rfl
        · exact (hei.rim).1
        · exact (hei.rim).2
      have hn : c.IsRim (x n) := by
        rcases hmn.2 with rfl | rfl
        · exact (hej.rim).1
        · exact (hej.rim).2
      have := c.vd hm hn (by rw [← h]; exact hlA) (by rw [← h]; exact hlE)
      apply hl0
      rw [h, this, sub_self]

/-! #### The middles lie over the chord -/

theorem mid_gen (X t s δ : ℝ)
    (hs : s * ((c.t2 - c.t1) * t + c.h1 + c.h2) = c.h1 + t * (X - c.t1))
    (hδ : δ = X - c.t1 - s * (c.t2 - c.t1)) :
    cpt c.v c.A c.N c.E X 0 0 = c.M1 + s • (c.M2 - c.M1) + δ • (c.A + t • c.E) := by
  have hx : c.t1 + s * (c.t2 - c.t1) + δ = X := by rw [hδ]; ring
  have hz : c.h1 + s * (-c.h2 - c.h1) + δ * t = 0 := by rw [hδ]; linear_combination -hs
  have : c.M1 + s • (c.M2 - c.M1) + δ • (c.A + t • c.E) =
      cpt c.v c.A c.N c.E (c.t1 + s * (c.t2 - c.t1) + δ) 0 (c.h1 + s * (-c.h2 - c.h1) + δ * t) := by
    simp only [M1, M2, cpt]; module
  rw [this, hx, hz]

theorem mid_v : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
    c.v = c.M1 + s • (c.M2 - c.M1) + δ • (c.A + t • c.E) := by
  have e1 := eventually_pos_affine (A := c.h1 + c.h2) (B := c.t2 - c.t1) (Or.inl (by linarith [c.hh1, c.hh2]))
  have e2 := eventually_pos_affine (A := c.h1) (B := -c.t1) (Or.inl c.hh1)
  filter_upwards [e1, e2, self_mem_nhdsWithin] with t h1 h2 ht
  have ht : 0 < t := ht
  have hden : 0 < (c.t2 - c.t1) * t + c.h1 + c.h2 := by nlinarith
  set den := (c.t2 - c.t1) * t + c.h1 + c.h2 with hdendef
  refine ⟨(c.h1 + t * (0 - c.t1)) / den, 0 - c.t1 - (c.h1 + t * (0 - c.t1)) / den * (c.t2 - c.t1),
    div_pos (by nlinarith) hden, ?_, ?_, ?_⟩
  · rw [div_lt_one hden]; nlinarith [c.ht2, c.hh2]
  · have : 0 - c.t1 - (c.h1 + t * (0 - c.t1)) / den * (c.t2 - c.t1) =
        -(c.t1 * c.h2 + c.h1 * c.t2) / den := by
      field_simp; rw [hdendef]; ring
    rw [this]
    exact div_ne_zero (by nlinarith [mul_pos c.ht1 c.hh2, mul_pos c.hh1 c.ht2]) hden.ne'
  · rw [← c.mid_gen 0 t _ _ (div_mul_cancel₀ _ hden.ne') rfl]
    simp [cpt]

theorem mid_p : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
    c.pP = c.M1 + s • (c.M2 - c.M1) + δ • (c.A + t • c.E) := by
  have e1 := eventually_pos_affine (A := c.h1 + c.h2) (B := c.t2 - c.t1) (Or.inl (by linarith [c.hh1, c.hh2]))
  have e2 := eventually_pos_affine (A := c.h2) (B := -(1 - c.t2)) (Or.inl c.hh2)
  filter_upwards [e1, e2, self_mem_nhdsWithin] with t h1 h2 ht
  have ht : 0 < t := ht
  have hden : 0 < (c.t2 - c.t1) * t + c.h1 + c.h2 := by nlinarith
  set den := (c.t2 - c.t1) * t + c.h1 + c.h2 with hdendef
  have t1' := c.ht1'
  refine ⟨(c.h1 + t * (1 - c.t1)) / den, 1 - c.t1 - (c.h1 + t * (1 - c.t1)) / den * (c.t2 - c.t1),
    div_pos (by nlinarith [mul_pos ht (sub_pos.mpr t1'), c.hh1]) hden, ?_, ?_, ?_⟩
  · rw [div_lt_one hden]; nlinarith
  · have : 1 - c.t1 - (c.h1 + t * (1 - c.t1)) / den * (c.t2 - c.t1) =
        (c.h2 * (1 - c.t1) + c.h1 * (1 - c.t2)) / den := by
      field_simp; rw [hdendef]; ring
    rw [this]
    exact div_ne_zero (by nlinarith [mul_pos c.hh2 (sub_pos.mpr c.ht1'), mul_pos c.hh1 (sub_pos.mpr c.ht2')]) hden.ne'
  · rw [pP, ← c.mid_gen 1 t _ _ (div_mul_cancel₀ _ hden.ne') rfl]

/-! #### The slide along `F1`'s circle -/

theorem rim_mem_V {P : ℝ³} (h : c.IsRim P) : P ∈ c.V := by
  classical
  unfold IsRim at h
  unfold V
  rcases h with rfl | rfl | rfl | rfl | rfl <;> simp

theorem v_mem_V : c.v ∈ c.V := by
  classical
  unfold V
  simp

theorem pP_mem_V : c.pP ∈ c.V := by
  classical
  unfold V
  simp

theorem rim_ne_v {P : ℝ³} (h : c.IsRim P) : P ≠ c.v := by
  intro hP
  have hv := c.v_eq
  unfold IsRim at h
  have t1 := c.ht1; have g1 := c.hh1; have g2 := c.hh2
  have k1 := c.hk1; have k2 := c.hk2; have s1 := c.hs1; have s2 := c.hs2
  rcases h with rfl | rfl | rfl | rfl | rfl <;>
  · rw [hv] at hP
    have := c.cpt_inj hP
    linarith [this.1, this.2.1, this.2.2]

theorem rim_ne_p {P : ℝ³} (h : c.IsRim P) : P ≠ c.pP := by
  intro hP
  unfold IsRim at h
  have t1 := c.ht1; have g1 := c.hh1; have g2 := c.hh2
  have k1 := c.hk1; have k2 := c.hk2; have s1 := c.hs1; have s2 := c.hs2
  rcases h with rfl | rfl | rfl | rfl | rfl <;>
  · have := c.cpt_inj hP
    linarith [this.1, this.2.1, this.2.2]

/-- **The slide along `F1`'s circle for a rim cycle through the chord** (the shared core of
the four regimes of Theorem 24.8): a cycle `x` of rim corners with `x 0 = M+`, `x 1 = M-`,
strictly convex at the horizontal view along `A` (or with zero test and positive derivative
along `E`), all the other points of `V` off `v`, `p` strictly inside (or on the boundary with
positive derivative), and distinct unimodal depths along the slide, makes `V` Rupert.  The
absence of a persistent horizontal double normal is `noBad`. -/
theorem slide_core {k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : ZMod k → ℝ³)
    (hx0 : x 0 = c.M1) (hx1 : x 1 = c.M2) (hedge : ∀ i, c.Edge (x i) (x (i + 1)))
    (hinj : Function.Injective x)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 →
      SlideTest c.D (x (i + 1) - x i) (x j - x i) c.A c.E)
    (hrest : ∀ y ∈ c.V, y ∉ ({c.v, c.pP} : Finset ℝ³) → (∀ j, y ≠ x j) → ∀ i,
      SlideTest c.D (x (i + 1) - x i) (y - x i) c.A c.E)
    (hz : ∀ᶠ t in 𝓝[>] (0 : ℝ), Function.Injective (fun i => ⟪x i, c.A + t • c.E⟫) →
      IsCyclicUnimodal (fun i => ⟪x i, c.A + t • c.E⟫)) : IsRupert c.V := by
  classical
  have hxV : ∀ i, x i ∈ c.V := fun i => c.rim_mem_V (hedge i).rim.1
  have hxM : ∀ i, x i ∉ ({c.v, c.pP} : Finset ℝ³) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with h | h
    · exact c.rim_ne_v (hedge i).rim.1 h
    · exact c.rim_ne_p (hedge i).rim.1 h
  refine isRupert_of_slideG c.V {c.v, c.pP} c.A c.E c.hA x hxV hxM hinj hk c.D c.D_ne ?_
    (c.noBad x hedge)
  have h1 := eventually_forall_cycle fun i j hi hj => eventually_det3_slide (hcyc i j hi hj)
  have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ y ∈ c.V, ∀ i : ZMod k, y ∉ ({c.v, c.pP} : Finset ℝ³) →
      (∀ j, y ≠ x j) → 0 < c.D * det3 (x (i + 1) - x i) (y - x i) (c.A + t • c.E) := by
    refine (eventually_all_finset c.V).mpr fun y hy => eventually_all.mpr fun i => ?_
    by_cases hyM : y ∉ ({c.v, c.pP} : Finset ℝ³)
    · by_cases hyx : ∀ j, y ≠ x j
      · filter_upwards [eventually_det3_slide (hrest y hy hyM hyx i)] with t ht _ _ using ht
      · filter_upwards with t _ h using absurd h hyx
    · filter_upwards with t h using absurd h hyM
  have h3 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ m ∈ ({c.v, c.pP} : Finset ℝ³), ∃ i : ZMod k, ∃ s δ : ℝ,
      0 < s ∧ s < 1 ∧ δ ≠ 0 ∧ m = x i + s • (x (i + 1) - x i) + δ • (c.A + t • c.E) := by
    refine (eventually_all_finset _).mpr fun m hm => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · filter_upwards [c.mid_v] with t ⟨s, δ, hs0, hs1, hδ, he⟩
      exact ⟨0, s, δ, hs0, hs1, hδ, by rw [zero_add, hx0, hx1]; exact he⟩
    · filter_upwards [c.mid_p] with t ⟨s, δ, hs0, hs1, hδ, he⟩
      exact ⟨0, s, δ, hs0, hs1, hδ, by rw [zero_add, hx0, hx1]; exact he⟩
  filter_upwards [h1, h2, h3, hz] with t ht1 ht2 ht3 ht4
  exact ⟨ht1, fun y hy hyM hyx i => ht2 y hy i hyM hyx, ht3, Or.inl ht4⟩

/-! #### The tests at the horizontal view -/

theorem st_pos {x0 y0 z0 x1 y1 z1 x2 y2 z2 : ℝ}
    (h : 0 < (y1 - y0) * (z2 - z0) - (z1 - z0) * (y2 - y0)) :
    SlideTest c.D (cpt c.v c.A c.N c.E x1 y1 z1 - cpt c.v c.A c.N c.E x0 y0 z0)
      (cpt c.v c.A c.N c.E x2 y2 z2 - cpt c.v c.A c.N c.E x0 y0 z0) c.A c.E :=
  Or.inl (by rw [det3_cpt_A]; exact c.pos_DD h)

theorem st_zero {x0 y0 z0 x1 y1 z1 x2 y2 z2 : ℝ}
    (h0 : (y1 - y0) * (z2 - z0) - (z1 - z0) * (y2 - y0) = 0)
    (h1 : 0 < (x1 - x0) * (y2 - y0) - (y1 - y0) * (x2 - x0)) :
    SlideTest c.D (cpt c.v c.A c.N c.E x1 y1 z1 - cpt c.v c.A c.N c.E x0 y0 z0)
      (cpt c.v c.A c.N c.E x2 y2 z2 - cpt c.v c.A c.N c.E x0 y0 z0) c.A c.E :=
  Or.inr ⟨by rw [det3_cpt_A, h0, mul_zero], by rw [det3_cpt_E]; exact c.pos_DD h1⟩

/-- The derivative terms of the two corners that can sit on a rim edge. -/
theorem d1_pos : 0 < c.t1 * (1 - c.s1) := mul_pos c.ht1 (sub_pos.mpr c.hs1')
theorem d2_pos : 0 < c.t2 * (1 - c.s2) := mul_pos c.ht2 (sub_pos.mpr c.hs2')

/-- Depth differences along the slide. -/
theorem depth_sub (x y z x' y' z' t : ℝ) :
    ⟪cpt c.v c.A c.N c.E x y z, c.A + t • c.E⟫ - ⟪cpt c.v c.A c.N c.E x' y' z', c.A + t • c.E⟫ =
      (x - x') * ⟪c.A, c.A⟫ + t * ((z - z') * ⟪c.E, c.E⟫) := by
  rw [← inner_sub_left, inner_add_right, real_inner_smul_right, inner_cpt_sub_A, inner_cpt_sub_E]

/-! #### The four regimes -/

theorem rim_distinct : c.M1 ≠ c.M2 ∧ c.M1 ≠ c.N2 ∧ c.M1 ≠ c.Bq ∧ c.M1 ≠ c.N1 ∧ c.M2 ≠ c.N2 ∧
    c.M2 ≠ c.Bq ∧ c.M2 ≠ c.N1 ∧ c.N2 ≠ c.Bq ∧ c.N2 ≠ c.N1 ∧ c.Bq ≠ c.N1 := by
  have t1 := c.ht1; have g1 := c.hh1; have g2 := c.hh2; have k1 := c.hk1; have k2 := c.hk2
  have s1 := c.hs1; have s2 := c.hs2; have s1' := c.hs1'; have s2' := c.hs2'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · intro h
    have := c.cpt_inj h
    linarith [this.1, this.2.1, this.2.2]

theorem facts0 : 0 < (c.h1 + c.h2) * c.s2 ∧ 0 < c.h1 + c.h2 ∧ 0 < (c.h1 + c.h2) * c.s1 ∧
    0 < c.k2 + c.h1 * (1 - c.s2) ∧ 0 < c.k1 + c.h2 * (1 - c.s1) ∧
    0 < (1 - c.s2) * c.k1 + c.k2 * (1 - c.s1) := by
  have g1 := c.hh1; have g2 := c.hh2; have k1 := c.hk1; have k2 := c.hk2
  have s1 := c.hs1; have s2 := c.hs2; have s1' := c.hs1'; have s2' := c.hs2'
  refine ⟨by positivity, by positivity, by positivity, ?_, ?_, ?_⟩
  · nlinarith [mul_pos g1 (sub_pos.mpr s2')]
  · nlinarith [mul_pos g2 (sub_pos.mpr s1')]
  · nlinarith [mul_pos (sub_pos.mpr s2') k1, mul_pos k2 (sub_pos.mpr s1')]

theorem f135 (hc1 : 0 ≤ c.k1 - c.h1 * (1 - c.s1)) :
    0 < c.s2 * (c.k1 - c.h1) + c.s1 * (c.k2 + c.h1) := by
  have g1 := c.hh1; have k2 := c.hk2
  have s1 := c.hs1; have s2 := c.hs2; have s1' := c.hs1'; have s2' := c.hs2'
  nlinarith [mul_pos s1 (add_pos k2 (mul_pos g1 (sub_pos.mpr s2'))), mul_nonneg s2.le hc1]

theorem f235 (hc2 : 0 ≤ c.k2 - c.h2 * (1 - c.s2)) :
    0 < c.s1 * (c.k2 - c.h2) + c.s2 * (c.k1 + c.h2) := by
  have g2 := c.hh2; have k1 := c.hk1
  have s1 := c.hs1; have s2 := c.hs2; have s1' := c.hs1'; have s2' := c.hs2'
  nlinarith [mul_pos s2 (add_pos k1 (mul_pos g2 (sub_pos.mpr s1'))), mul_nonneg s1.le hc2]

/-! #### Unimodality along the slide -/

theorem V_cases {y : ℝ³} (hy : y ∈ c.V) : y = c.v ∨ y = c.pP ∨ c.IsRim y := by
  classical
  simp only [V, Finset.mem_insert, Finset.mem_singleton] at hy
  unfold IsRim
  tauto

theorem dz_N2_M2 (t : ℝ)
    (h : 0 < (c.t2 - c.s2 * c.b) * ⟪c.A, c.A⟫ + t * ((c.k2 - c.h2) * ⟪c.E, c.E⟫)) :
    ⟪c.N2, c.A + t • c.E⟫ < ⟪c.M2, c.A + t • c.E⟫ := by
  have := c.depth_sub (c.s2 * c.b) c.s2 (-c.k2) c.t2 0 (-c.h2) t
  simp only [N2, M2]
  nlinarith

theorem dz_N1_M1 (t : ℝ)
    (h : 0 < (c.t1 - c.s1 * c.b) * ⟪c.A, c.A⟫ + t * ((c.h1 - c.k1) * ⟪c.E, c.E⟫)) :
    ⟪c.N1, c.A + t • c.E⟫ < ⟪c.M1, c.A + t • c.E⟫ := by
  have := c.depth_sub (c.s1 * c.b) c.s1 c.k1 c.t1 0 c.h1 t
  simp only [N1, M1]
  nlinarith

theorem dz_B_N1 (t : ℝ) (ht : 0 < t) :
    ⟪c.Bq, c.A + t • c.E⟫ < ⟪c.N1, c.A + t • c.E⟫ := by
  have := c.depth_sub c.b 1 0 (c.s1 * c.b) c.s1 c.k1 t
  simp only [Bq, N1]
  have h1 : c.b * (1 - c.s1) * ⟪c.A, c.A⟫ ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg c.hb (sub_nonneg.mpr c.hs1'.le))
      c.a2_pos.le
  nlinarith [mul_pos (mul_pos ht c.hk1) c.e2_pos]

theorem dz_B_M1 (t : ℝ) (ht : 0 < t) :
    ⟪c.Bq, c.A + t • c.E⟫ < ⟪c.M1, c.A + t • c.E⟫ := by
  have := c.depth_sub c.b 1 0 c.t1 0 c.h1 t
  simp only [Bq, M1]
  nlinarith [mul_pos (mul_pos ht c.hh1) c.e2_pos, mul_pos c.ht1 c.a2_pos,
    mul_nonpos_of_nonpos_of_nonneg c.hb c.a2_pos.le]

theorem ev_N2_M2 : ∀ᶠ t in 𝓝[>] (0 : ℝ),
    0 < (c.t2 - c.s2 * c.b) * ⟪c.A, c.A⟫ + t * ((c.k2 - c.h2) * ⟪c.E, c.E⟫) := by
  refine eventually_pos_affine (Or.inl (mul_pos ?_ c.a2_pos))
  nlinarith [mul_nonpos_of_nonneg_of_nonpos c.hs2.le c.hb, c.ht2]

theorem ev_N1_M1 : ∀ᶠ t in 𝓝[>] (0 : ℝ),
    0 < (c.t1 - c.s1 * c.b) * ⟪c.A, c.A⟫ + t * ((c.h1 - c.k1) * ⟪c.E, c.E⟫) := by
  refine eventually_pos_affine (Or.inl (mul_pos ?_ c.a2_pos))
  nlinarith [mul_nonpos_of_nonneg_of_nonpos c.hs1.le c.hb, c.ht1]

/-- Regime with both far middles corners of the rim (`N+`: `c1 ≥ 0`, `N-`: `c2 > 0`). -/
theorem regime5 (hc1 : 0 ≤ c.k1 - c.h1 * (1 - c.s1)) (hc2 : 0 < c.k2 - c.h2 * (1 - c.s2)) :
    IsRupert c.V := by
  classical
  obtain ⟨f123, f124, f125, f134, f245, f345⟩ := c.facts0
  have f135 := c.f135 hc1
  have f235 := c.f235 hc2.le
  have d1 := c.d1_pos
  have d2 := c.d2_pos
  obtain ⟨n12, n13, n14, n15, n23, n24, n25, n34, n35, n45⟩ := c.rim_distinct
  obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_sub_one
  refine c.slide_core (k := 5) (by norm_num) (quint c.M1 c.M2 c.N2 c.Bq c.N1) rfl rfl ?_ ?_ ?_ ?_ ?_
  · -- the edges
    intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    simp only [a0, a1, a2, a3, a4, quint_0, quint_1, quint_2, quint_3, quint_4, Edge, EdgeU] <;>
    simp
  · -- injective
    intro i j h
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [quint_0, quint_1, quint_2, quint_3, quint_4] at h <;>
    first | rfl | exact absurd h (by assumption) | exact absurd h.symm (by assumption)
  · -- the tests of the cycle
    intro i j hi hj
    rcases zmod5_pairs i j hi hj with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ |
      ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ <;>
    simp only [a0, a1, a2, a3, a4, quint_0, quint_1, quint_2, quint_3, quint_4, M1, M2, N1, N2, Bq] <;>
    first
    | exact c.st_pos (by linarith)
    | (rcases hc1.lt_or_eq with h | h
       · exact c.st_pos (by linarith)
       · exact c.st_zero (by linarith) (by linarith))
  · -- the other points: there are none
    intro y hy hyM hyx
    exfalso
    rcases c.V_cases hy with rfl | rfl | hr
    · exact hyM (by simp)
    · exact hyM (by simp)
    · unfold IsRim at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact hyx 0 rfl
      · exact hyx 1 rfl
      · exact hyx 2 rfl
      · exact hyx 3 rfl
      · exact hyx 4 rfl
  · -- unimodal depths
    filter_upwards [c.ev_N2_M2, c.ev_N1_M1, self_mem_nhdsWithin] with t e1 e2 ht hinj
    have ht : 0 < t := ht
    have z2 := c.dz_N2_M2 t e1
    have z3 := c.dz_B_N1 t ht
    have z4 := c.dz_N1_M1 t e2
    refine isCyclicUnimodal_of_atMostOne (by norm_num) hinj fun i j hi hj => ?_
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3,
      quint_4] at hi hj <;>
    first | rfl | (exfalso; linarith [hi.1, hi.2, hj.1, hj.2])

/-- Regime with `N-` a corner and `N+` inside the rim (`c1 < 0`, `c2 > 0`). -/
theorem regime4a (hc1 : c.k1 - c.h1 * (1 - c.s1) < 0) (hc2 : 0 < c.k2 - c.h2 * (1 - c.s2)) :
    IsRupert c.V := by
  classical
  obtain ⟨f123, f124, f125, f134, f245, f345⟩ := c.facts0
  have f235 := c.f235 hc2.le
  obtain ⟨n12, n13, n14, n15, n23, n24, n25, n34, n35, n45⟩ := c.rim_distinct
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  obtain ⟨b0, b1, b2, b3⟩ : ((0 : ZMod 4) - 1 = 3 ∧ (1 : ZMod 4) - 1 = 0 ∧ (2 : ZMod 4) - 1 = 1 ∧
    (3 : ZMod 4) - 1 = 2) := by decide
  refine c.slide_core (k := 4) (by norm_num) (quad c.M1 c.M2 c.N2 c.Bq) rfl rfl ?_ ?_ ?_ ?_ ?_
  · intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3, Edge, EdgeU] <;>
    simp
  · intro i j h
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    simp only [quad_0, quad_1, quad_2, quad_3] at h <;>
    first | rfl | exact absurd h (by assumption) | exact absurd h.symm (by assumption)
  · intro i j hi hj
    rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3, M1, M2, N2, Bq] <;>
    exact c.st_pos (by linarith)
  · intro y hy hyM hyx
    rcases c.V_cases hy with rfl | rfl | hr
    · exact absurd (by simp) hyM
    · exact absurd (by simp) hyM
    · unfold IsRim at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact absurd (show c.M1 = quad c.M1 c.M2 c.N2 c.Bq 0 from rfl) (hyx 0)
      · exact absurd (show c.M2 = quad c.M1 c.M2 c.N2 c.Bq 1 from rfl) (hyx 1)
      · exact absurd (show c.N2 = quad c.M1 c.M2 c.N2 c.Bq 2 from rfl) (hyx 2)
      · exact absurd (show c.Bq = quad c.M1 c.M2 c.N2 c.Bq 3 from rfl) (hyx 3)
      · intro i
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3, M1, M2, N1, N2, Bq] <;>
        exact c.st_pos (by linarith)
  · filter_upwards [c.ev_N2_M2, self_mem_nhdsWithin] with t e1 ht hinj
    have ht : 0 < t := ht
    have z2 := c.dz_N2_M2 t e1
    have z3 := c.dz_B_M1 t ht
    refine isCyclicUnimodal_of_atMostOne (by norm_num) hinj fun i j hi hj => ?_
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    simp only [a0, a1, a2, a3, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3] at hi hj <;>
    first | rfl | (exfalso; linarith [hi.1, hi.2, hj.1, hj.2])

/-- Regime with `N+` a corner and `N-` inside the rim (`c1 ≥ 0`, `c2 ≤ 0`). -/
theorem regime4b (hc1 : 0 ≤ c.k1 - c.h1 * (1 - c.s1)) (hc2 : c.k2 - c.h2 * (1 - c.s2) ≤ 0) :
    IsRupert c.V := by
  classical
  obtain ⟨f123, f124, f125, f134, f245, f345⟩ := c.facts0
  have f135 := c.f135 hc1
  have d1 := c.d1_pos
  have d2 := c.d2_pos
  obtain ⟨n12, n13, n14, n15, n23, n24, n25, n34, n35, n45⟩ := c.rim_distinct
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  obtain ⟨b0, b1, b2, b3⟩ : ((0 : ZMod 4) - 1 = 3 ∧ (1 : ZMod 4) - 1 = 0 ∧ (2 : ZMod 4) - 1 = 1 ∧
    (3 : ZMod 4) - 1 = 2) := by decide
  refine c.slide_core (k := 4) (by norm_num) (quad c.M1 c.M2 c.Bq c.N1) rfl rfl ?_ ?_ ?_ ?_ ?_
  · intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3, Edge, EdgeU] <;>
    simp
  · intro i j h
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    simp only [quad_0, quad_1, quad_2, quad_3] at h <;>
    first | rfl | exact absurd h (by assumption) | exact absurd h.symm (by assumption)
  · intro i j hi hj
    rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3, M1, M2, N1, Bq] <;>
    first
    | exact c.st_pos (by linarith)
    | (rcases hc1.lt_or_eq with h | h
       · exact c.st_pos (by linarith)
       · exact c.st_zero (by linarith) (by linarith))
  · intro y hy hyM hyx
    rcases c.V_cases hy with rfl | rfl | hr
    · exact absurd (by simp) hyM
    · exact absurd (by simp) hyM
    · unfold IsRim at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact absurd (show c.M1 = quad c.M1 c.M2 c.Bq c.N1 0 from rfl) (hyx 0)
      · exact absurd (show c.M2 = quad c.M1 c.M2 c.Bq c.N1 1 from rfl) (hyx 1)
      · intro i
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3, M1, M2, N1, N2, Bq] <;>
        first
        | exact c.st_pos (by linarith)
        | (rcases hc2.lt_or_eq with h | h
           · exact c.st_pos (by linarith)
           · exact c.st_zero (by linarith) (by linarith))
      · exact absurd (show c.Bq = quad c.M1 c.M2 c.Bq c.N1 2 from rfl) (hyx 2)
      · exact absurd (show c.N1 = quad c.M1 c.M2 c.Bq c.N1 3 from rfl) (hyx 3)
  · filter_upwards [c.ev_N1_M1, self_mem_nhdsWithin] with t e1 ht hinj
    have ht : 0 < t := ht
    have z2 := c.dz_B_N1 t ht
    have z3 := c.dz_N1_M1 t e1
    refine isCyclicUnimodal_of_atMostOne (by norm_num) hinj fun i j hi hj => ?_
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    simp only [a0, a1, a2, a3, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3] at hi hj <;>
    first | rfl | (exfalso; linarith [hi.1, hi.2, hj.1, hj.2])

/-- Regime with both far middles inside the rim (`c1 < 0`, `c2 ≤ 0`): the rim is the
triangle `M+, M-, B`. -/
theorem regime3 (hc1 : c.k1 - c.h1 * (1 - c.s1) < 0) (hc2 : c.k2 - c.h2 * (1 - c.s2) ≤ 0) :
    IsRupert c.V := by
  classical
  obtain ⟨f123, f124, f125, f134, f245, f345⟩ := c.facts0
  have d2 := c.d2_pos
  obtain ⟨n12, n13, n14, n15, n23, n24, n25, n34, n35, n45⟩ := c.rim_distinct
  obtain ⟨a0, a1, a2⟩ := zmod3_add_one
  refine c.slide_core (k := 3) (by norm_num) (tri c.M1 c.M2 c.Bq) rfl rfl ?_ ?_ ?_ ?_ ?_
  · intro i
    rcases zmod3_cases i with rfl | rfl | rfl <;>
    simp only [a0, a1, a2, tri_0, tri_1, tri_2, Edge, EdgeU] <;>
    simp
  · intro i j h
    rcases zmod3_cases i with rfl | rfl | rfl <;>
    rcases zmod3_cases j with rfl | rfl | rfl <;>
    simp only [tri_0, tri_1, tri_2] at h <;>
    first | rfl | exact absurd h (by assumption) | exact absurd h.symm (by assumption)
  · intro i j hi hj
    rcases zmod3_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [a0, a1, a2, tri_0, tri_1, tri_2, M1, M2, Bq] <;>
    exact c.st_pos (by linarith)
  · intro y hy hyM hyx
    rcases c.V_cases hy with rfl | rfl | hr
    · exact absurd (by simp) hyM
    · exact absurd (by simp) hyM
    · unfold IsRim at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact absurd (show c.M1 = tri c.M1 c.M2 c.Bq 0 from rfl) (hyx 0)
      · exact absurd (show c.M2 = tri c.M1 c.M2 c.Bq 1 from rfl) (hyx 1)
      · intro i
        rcases zmod3_cases i with rfl | rfl | rfl <;>
        simp only [a0, a1, a2, tri_0, tri_1, tri_2, M1, M2, N2, Bq] <;>
        first
        | exact c.st_pos (by linarith)
        | (rcases hc2.lt_or_eq with h | h
           · exact c.st_pos (by linarith)
           · exact c.st_zero (by linarith) (by linarith))
      · exact absurd (show c.Bq = tri c.M1 c.M2 c.Bq 2 from rfl) (hyx 2)
      · intro i
        rcases zmod3_cases i with rfl | rfl | rfl <;>
        simp only [a0, a1, a2, tri_0, tri_1, tri_2, M1, M2, N1, Bq] <;>
        exact c.st_pos (by linarith)
  · filter_upwards with t hinj
    exact isCyclicUnimodal_three hinj

/-- **The shape theorem** (Theorem 24.8 of `FEWER-FACES-PROOFS.md`, Euclidean model): the
seven points `v`, `p`, `M±`, `B`, `N±` of a case-(c) shape with `⟨a, b⟩ ≤ 0` (the angle of
the shadow triangle at the apex `v` at least `π/2`, `b ≤ 0`) form a Rupert polyhedron.  There is
no exceptional set: the persistent double normals of the paper do not occur, since the far
corners `B`, `N±` all have depth `≤ 0` along `A` and the chord `M+ M-` has depth `> 0`. -/
theorem isRupert_model : IsRupert c.V := by
  by_cases h1 : 0 ≤ c.k1 - c.h1 * (1 - c.s1)
  · by_cases h2 : 0 < c.k2 - c.h2 * (1 - c.s2)
    · exact c.regime5 h1 h2
    · exact c.regime4b h1 (not_lt.mp h2)
  · by_cases h2 : 0 < c.k2 - c.h2 * (1 - c.s2)
    · exact c.regime4a (not_le.mp h1) h2
    · exact c.regime3 (not_le.mp h1) (not_lt.mp h2)

end CObt

theorem expand3 {A N E : ℝ³} (hAN : ⟪A, N⟫ = 0) (hAE : ⟪A, E⟫ = 0) (hNE : ⟪N, E⟫ = 0)
    (hA : A ≠ 0) (hN : N ≠ 0) (hE : E ≠ 0) (w : ℝ³) :
    w = (⟪w, A⟫ / ⟪A, A⟫) • A + (⟪w, N⟫ / ⟪N, N⟫) • N + (⟪w, E⟫ / ⟪E, E⟫) • E := by
  have hNA : ⟪N, A⟫ = 0 := by rw [real_inner_comm]; exact hAN
  have hEA : ⟪E, A⟫ = 0 := by rw [real_inner_comm]; exact hAE
  have hEN : ⟪E, N⟫ = 0 := by rw [real_inner_comm]; exact hNE
  have a2 : ⟪A, A⟫ ≠ 0 := (real_inner_self_pos.mpr hA).ne'
  have n2 : ⟪N, N⟫ ≠ 0 := (real_inner_self_pos.mpr hN).ne'
  have e2 : ⟪E, E⟫ ≠ 0 := (real_inner_self_pos.mpr hE).ne'
  have hsq : det3 A N E ^ 2 = ⟪A, A⟫ * ⟪N, N⟫ * ⟪E, E⟫ := by
    have := CObt.gram_det A N E
    rw [hAN, hNE, hEA] at this
    simpa using this
  have hD : det3 A N E ≠ 0 := by
    intro h0
    rw [h0] at hsq
    have : 0 < ⟪A, A⟫ * ⟪N, N⟫ * ⟪E, E⟫ :=
      mul_pos (mul_pos (real_inner_self_pos.mpr hA) (real_inner_self_pos.mpr hN))
        (real_inner_self_pos.mpr hE)
    nlinarith
  have D_smul : ∀ w : ℝ³, det3 A N E • w = ⟪w, A⟫ • cross N E + ⟪w, N⟫ • cross E A +
      ⟪w, E⟫ • cross A N := by
    intro w
    ext i
    fin_cases i <;>
    simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three] <;> ring
  have hA' := D_smul A
  have hN' := D_smul N
  have hE' := D_smul E
  have h := D_smul w
  rw [hAN, hAE, zero_smul, zero_smul, add_zero, add_zero] at hA'
  rw [hNA, hNE, zero_smul, zero_smul, zero_add, add_zero] at hN'
  rw [hEA, hEN, zero_smul, zero_smul, zero_add, zero_add] at hE'
  have e1 : det3 A N E • ((⟪w, A⟫ / ⟪A, A⟫) • A) = ⟪w, A⟫ • cross N E := by
    rw [smul_comm, hA', smul_smul, div_mul_cancel₀ _ a2]
  have e2' : det3 A N E • ((⟪w, N⟫ / ⟪N, N⟫) • N) = ⟪w, N⟫ • cross E A := by
    rw [smul_comm, hN', smul_smul, div_mul_cancel₀ _ n2]
  have e3 : det3 A N E • ((⟪w, E⟫ / ⟪E, E⟫) • E) = ⟪w, E⟫ • cross A N := by
    rw [smul_comm, hE', smul_smul, div_mul_cancel₀ _ e2]
  have key : det3 A N E • w = det3 A N E • ((⟪w, A⟫ / ⟪A, A⟫) • A + (⟪w, N⟫ / ⟪N, N⟫) • N +
      (⟪w, E⟫ / ⟪E, E⟫) • E) := by
    simp only [smul_add, e1, e2', e3]
    exact h
  exact (smul_right_inj hD).mp key

theorem aff_add (f : ℝ³ →ᵃ[ℝ] ℝ) (v w : ℝ³) : f (v + w) = f v + f.linear w := by
  have := f.map_vadd v w
  simpa [vadd_eq_add, add_comm] using this

theorem aff_sub (f : ℝ³ →ᵃ[ℝ] ℝ) (v x : ℝ³) : f x = f v + f.linear (x - v) := by
  have := aff_add f v (x - v)
  rwa [add_sub_cancel] at this

theorem card4_eq {a b c d : ℝ³} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : ({a, b, c, d} : Finset ℝ³).card = 4 := by
  classical
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hcd]
  · simp [hbc, hbd]
  · simp [hab, hac, had]

set_option maxHeartbeats 4000000 in
/-- **Theorem 24.8 in facet form** (`FEWER-FACES-PROOFS.md` §24, case (c) of the triple tie with
a right or obtuse angle of the shadow triangle at the apex `v`).  Two quadrilateral facets
`Q1`, `Q2` of the 7-point set `V = Q1 ∪ Q2` meeting in the single vertex `v`; `e` the direction
of the line of their planes; `p ∈ Q1`, `q ∈ Q2` the far ends (farthest from the other plane);
the far ends and `v` at one depth along `e`, the angle `p v q` at least `π/2`, and no
settling of the tie by `TieHT` (in particular both faces two-sided there).  Then `V` is Rupert:
the views of the face circle of `Q1` just beside the view along `p - v` have a unimodal rim with
distinct depths, and no persistent horizontal double normal. -/
theorem isRupert_of_obtuse_apex (V Q1 Q2 : Finset ℝ³) (hgen : NoThreeCollinear V) (v : ℝ³)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v}) (h1c : Q1.card = 4)
    (h2c : Q2.card = 4) (hcov : Q1 ∪ Q2 = V) (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ)
    (z1 : ∀ p ∈ Q1, f1 p = 0) (n1 : ∀ p ∈ V, p ∉ Q1 → f1 p < 0)
    (z2 : ∀ p ∈ Q2, f2 p = 0) (n2 : ∀ p ∈ V, p ∉ Q2 → f2 p < 0)
    (e : ℝ³) (he : e ≠ 0) (e1 : f1 (v + e) = 0) (e2 : f2 (v + e) = 0)
    (hpar : ∀ p ∈ V, ∀ q ∈ V, p ≠ q → ∀ c : ℝ, q - p = c • e →
      MidPair Q1 Q2 (fun p => ∀ p' ∈ Q1, f2 p ≤ f2 p') (fun q => ∀ q' ∈ Q2, f1 q ≤ f1 q') p q)
    (p : ℝ³) (hp : p ∈ Q1) (q : ℝ³) (hq : q ∈ Q2) (hpq : p ≠ q)
    (hpm : ∀ p' ∈ Q1, f2 p ≤ f2 p') (hqm : ∀ q' ∈ Q2, f1 q ≤ f1 q')
    (hnot : ¬ TieHT Q1 Q2 v p q (fun x => ⟪x, e⟫))
    (hobt : ⟪p, e⟫ = ⟪q, e⟫ ∧ ⟪v, e⟫ = ⟪p, e⟫ ∧ ⟪p - v, q - v⟫ ≤ 0) : IsRupert V := by
  classical
  have hv1 : v ∈ Q1 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).1
  have hv2 : v ∈ Q2 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).2
  have only : ∀ x ∈ Q1, x ∈ Q2 → x = v := by
    intro x h1 h2
    have : x ∈ Q1 ∩ Q2 := Finset.mem_inter.mpr ⟨h1, h2⟩
    rwa [hint, Finset.mem_singleton] at this
  have f1v : f1 v = 0 := z1 v hv1
  have f2v : f2 v = 0 := z2 v hv2
  obtain ⟨p0, hp0, hp0v⟩ := Finset.exists_mem_ne (by omega : 1 < Q1.card) v
  obtain ⟨q0, hq0, hq0v⟩ := Finset.exists_mem_ne (by omega : 1 < Q2.card) v
  have f2p0 : f2 p0 < 0 := n2 p0 (h1V hp0) (fun h => hp0v (only p0 hp0 h))
  have f1q0 : f1 q0 < 0 := n1 q0 (h2V hq0) (fun h => hq0v (only q0 h hq0))
  have hpv : p ≠ v := by
    intro h; have := hpm p0 hp0; rw [h, f2v] at this; linarith
  have hqv : q ≠ v := by
    intro h; have := hqm q0 hq0; rw [h, f1v] at this; linarith
  have hf2p : f2 p < 0 := lt_of_le_of_lt (hpm p0 hp0) f2p0
  have hf1q : f1 q < 0 := lt_of_le_of_lt (hqm q0 hq0) f1q0
  have f1p : f1 p = 0 := z1 p hp
  have f2q : f2 q = 0 := z2 q hq
  have hpV : p ∈ V := h1V hp
  have hqV : q ∈ V := h2V hq
  have hvV : v ∈ V := h1V hv1
  -- the orthogonal frame
  obtain ⟨A, hAd⟩ : ∃ A : ℝ³, A = p - v := ⟨_, rfl⟩
  obtain ⟨Bv, hBd⟩ : ∃ Bv : ℝ³, Bv = q - v := ⟨_, rfl⟩
  have hA0 : A ≠ 0 := by rw [hAd]; exact sub_ne_zero.mpr hpv
  have hAe : ⟪A, e⟫ = 0 := by rw [hAd, inner_sub_left, hobt.2.1]; ring
  have hBe : ⟪Bv, e⟫ = 0 := by rw [hBd, inner_sub_left, ← hobt.1, hobt.2.1]; ring
  have ha2 : 0 < ⟪A, A⟫ := real_inner_self_pos.mpr hA0
  obtain ⟨b, hbd⟩ : ∃ b : ℝ, b = ⟪Bv, A⟫ / ⟪A, A⟫ := ⟨_, rfl⟩
  have hb : b ≤ 0 := by
    rw [hbd]
    apply div_nonpos_of_nonpos_of_nonneg _ ha2.le
    rw [real_inner_comm, hAd, hBd]; exact hobt.2.2
  obtain ⟨N, hNd⟩ : ∃ N : ℝ³, N = Bv - b • A := ⟨_, rfl⟩
  have hAN : ⟪A, N⟫ = 0 := by
    rw [hNd, inner_sub_right, real_inner_smul_right, hbd, div_mul_cancel₀ _ ha2.ne',
      real_inner_comm A Bv, sub_self]
  have hNe : ⟪N, e⟫ = 0 := by
    rw [hNd, inner_sub_left, real_inner_smul_left, hAe, hBe]; ring
  have φ1A : f1.linear A = 0 := by
    have := aff_sub f1 v p; rw [f1p, f1v, ← hAd] at this; linarith
  have φ1e : f1.linear e = 0 := by
    have := aff_add f1 v e; rw [e1, f1v] at this; linarith
  have φ1B : f1.linear Bv = f1 q := by
    have := aff_sub f1 v q; rw [f1v, ← hBd] at this; linarith
  have φ2A : f2.linear A = f2 p := by
    have := aff_sub f2 v p; rw [f2v, ← hAd] at this; linarith
  have φ2e : f2.linear e = 0 := by
    have := aff_add f2 v e; rw [e2, f2v] at this; linarith
  have φ2B : f2.linear Bv = 0 := by
    have := aff_sub f2 v q; rw [f2q, f2v, ← hBd] at this; linarith
  have φ1N : f1.linear N = f1 q := by
    rw [hNd, map_sub, map_smul, φ1A, φ1B]; simp
  have φ2N : f2.linear N = -(b * f2 p) := by
    rw [hNd, map_sub, map_smul, φ2A, φ2B]; simp
  have hN0 : N ≠ 0 := by
    intro h0; rw [h0, map_zero] at φ1N; linarith
  have hn2 : 0 < ⟪N, N⟫ := real_inner_self_pos.mpr hN0
  have he2 : 0 < ⟪e, e⟫ := real_inner_self_pos.mpr he
  have exp := expand3 hAN hAe hNe hA0 hN0 he
  -- coordinates
  obtain ⟨α, hα⟩ : ∃ α : ℝ³ → ℝ, ∀ x, α x = ⟪x - v, A⟫ / ⟪A, A⟫ := ⟨fun x => _, fun _ => rfl⟩
  obtain ⟨ν, hν⟩ : ∃ ν : ℝ³ → ℝ, ∀ x, ν x = ⟪x - v, N⟫ / ⟪N, N⟫ := ⟨fun x => _, fun _ => rfl⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℝ³ → ℝ, ∀ x, ζ x = ⟪x - v, e⟫ / ⟪e, e⟫ := ⟨fun x => _, fun _ => rfl⟩
  have hcoef : ∀ x, x - v = α x • A + ν x • N + ζ x • e := by
    intro x; rw [hα, hν, hζ]; exact exp (x - v)
  have hcoef' : ∀ x, x = v + (α x • A + ν x • N + ζ x • e) := by
    intro x; exact eq_add_of_sub_eq' (hcoef x)
  have hlin1 : ∀ x, f1 x = ν x * f1 q := by
    intro x
    rw [aff_sub f1 v x, f1v, zero_add, hcoef x]
    simp only [map_add, map_smul, φ1A, φ1e, φ1N, smul_eq_mul]; ring
  have hlin2 : ∀ x, f2 x = (α x - b * ν x) * f2 p := by
    intro x
    rw [aff_sub f2 v x, f2v, zero_add, hcoef x]
    simp only [map_add, map_smul, φ2A, φ2e, φ2N, smul_eq_mul]; ring
  have hzz : ∀ x, ⟪x, e⟫ - ⟪v, e⟫ = ζ x * ⟪e, e⟫ := by
    intro x; rw [hζ, div_mul_cancel₀ _ he2.ne', inner_sub_left]
  have hBA : b • A + N = Bv := by rw [hNd]; abel
  -- the points of `Q1` other than `v`, `p`
  have key1 : ∀ x ∈ Q1, x ≠ v → x ≠ p →
      0 < α x ∧ α x < 1 ∧ ν x = 0 ∧ ζ x ≠ 0 := by
    intro x hx hxv hxp
    have hxV : x ∈ V := h1V hx
    have hν0 : ν x = 0 := by
      have := hlin1 x
      rw [z1 x hx] at this
      exact (mul_eq_zero.mp this.symm).resolve_right hf1q.ne
    have hxQ2 : x ∉ Q2 := fun h => hxv (only x hx h)
    have hf2x : f2 x < 0 := n2 x hxV hxQ2
    have h2x := hlin2 x
    rw [hν0, mul_zero, sub_zero] at h2x
    have hα0 : 0 < α x := by
      by_contra hcon
      push Not at hcon
      rw [h2x] at hf2x
      nlinarith
    have hα1 : α x ≤ 1 := by
      have := hpm x hx
      rw [h2x] at this
      nlinarith
    have hα1' : α x ≠ 1 := by
      intro h1
      have hc : p - x = (-(ζ x)) • e := by
        have := hcoef x
        rw [hν0, h1, zero_smul, one_smul, add_zero] at this
        have h2 : x - (p + ζ x • e) = 0 := by
          calc x - (p + ζ x • e) = (x - v) - (A + ζ x • e) := by rw [hAd]; abel
            _ = 0 := by rw [this]; exact sub_self _
        have hxp' : x - p = ζ x • e := sub_eq_of_eq_add' (sub_eq_zero.mp h2)
        rw [neg_smul, ← hxp', neg_sub]
      rcases hpar x hxV p hpV hxp _ hc with ⟨-, -, -, nf⟩ | ⟨-, hp2, -, -⟩ | ⟨hx1, -, -, -⟩
      · exact nf hpm
      · exact hpv (only p hp hp2)
      · exact absurd hx hx1
    have hζ0 : ζ x ≠ 0 := by
      intro h0
      apply hgen v hvV p hpV x hxV hpv.symm hxv.symm hxp.symm (α x)
      have := hcoef x
      rw [hν0, h0, zero_smul, zero_smul, add_zero, add_zero, hAd] at this
      exact this
    exact ⟨hα0, lt_of_le_of_ne hα1 hα1', hν0, hζ0⟩
  -- the points of `Q2` other than `v`, `q`
  have key2 : ∀ y ∈ Q2, y ≠ v → y ≠ q →
      0 < ν y ∧ ν y < 1 ∧ α y = b * ν y ∧ ζ y ≠ 0 := by
    intro y hy hyv hyq
    have hyV : y ∈ V := h2V hy
    have hαy : α y = b * ν y := by
      have := hlin2 y
      rw [z2 y hy] at this
      have h0 := (mul_eq_zero.mp this.symm).resolve_right hf2p.ne
      linarith
    have hyQ1 : y ∉ Q1 := fun h => hyv (only y h hy)
    have hf1y : f1 y < 0 := n1 y hyV hyQ1
    have h1y := hlin1 y
    have hν0 : 0 < ν y := by
      by_contra hcon
      push Not at hcon
      rw [h1y] at hf1y
      nlinarith
    have hν1 : ν y ≤ 1 := by
      have := hqm y hy
      rw [h1y] at this
      nlinarith
    have hν1' : ν y ≠ 1 := by
      intro h1
      have hc : q - y = (-(ζ y)) • e := by
        have := hcoef y
        rw [hαy, h1, mul_one, one_smul, hBA] at this
        have h2 : y - (q + ζ y • e) = 0 := by
          calc y - (q + ζ y • e) = (y - v) - (Bv + ζ y • e) := by rw [hBd]; abel
            _ = 0 := by rw [this]; exact sub_self _
        have hyq' : y - q = ζ y • e := sub_eq_of_eq_add' (sub_eq_zero.mp h2)
        rw [neg_smul, ← hyq', neg_sub]
      rcases hpar y hyV q hqV hyq _ hc with ⟨hy1, hq1, -, -⟩ | ⟨-, -, -, nf⟩ | ⟨-, hy2, -, -⟩
      · exact hqv (only q hq1 hq)
      · exact nf hqm
      · exact absurd hy hy2
    have hζ0 : ζ y ≠ 0 := by
      intro h0
      apply hgen v hvV q hqV y hyV hqv.symm hyv.symm hyq.symm (ν y)
      have := hcoef y
      rw [hαy, h0, zero_smul, add_zero] at this
      rw [← hBd, ← hBA, smul_add, smul_smul, mul_comm (ν y) b]
      exact this
    exact ⟨hν0, lt_of_le_of_ne hν1 hν1', hαy, hζ0⟩
  -- two-sidedness of both faces
  have hOS1 : ¬ OneSided Q1 v p (fun x => ⟪x, e⟫) := fun h' =>
    hnot (Or.inr ⟨hobt.1, hobt.2.1, Or.inl h'⟩)
  have hOS2 : ¬ OneSided Q2 v q (fun x => ⟪x, e⟫) := fun h' =>
    hnot (Or.inr ⟨hobt.1, hobt.2.1, Or.inr (Or.inl h')⟩)
  obtain ⟨xp, hxp, hxpv, hxpp, hxpz⟩ : ∃ x ∈ Q1, x ≠ v ∧ x ≠ p ∧ 0 < ζ x := by
    by_contra hcon
    push Not at hcon
    apply hOS1
    refine ⟨1, Or.inl rfl, fun x hx hxv hxp => ?_⟩
    have hneg : ζ x < 0 := lt_of_le_of_ne (hcon x hx hxv hxp) (key1 x hx hxv hxp).2.2.2
    have := hzz x
    show 1 * ⟪x, e⟫ < 1 * ⟪v, e⟫
    nlinarith
  obtain ⟨xm, hxm, hxmv, hxmp, hxmz⟩ : ∃ x ∈ Q1, x ≠ v ∧ x ≠ p ∧ ζ x < 0 := by
    by_contra hcon
    push Not at hcon
    apply hOS1
    refine ⟨-1, Or.inr rfl, fun x hx hxv hxp => ?_⟩
    have hpos : 0 < ζ x := lt_of_le_of_ne (hcon x hx hxv hxp) (key1 x hx hxv hxp).2.2.2.symm
    have := hzz x
    show -1 * ⟪x, e⟫ < -1 * ⟪v, e⟫
    nlinarith
  obtain ⟨yp, hyp, hypv, hypq, hypz⟩ : ∃ y ∈ Q2, y ≠ v ∧ y ≠ q ∧ 0 < ζ y := by
    by_contra hcon
    push Not at hcon
    apply hOS2
    refine ⟨1, Or.inl rfl, fun x hx hxv hxq => ?_⟩
    have hneg : ζ x < 0 := lt_of_le_of_ne (hcon x hx hxv hxq) (key2 x hx hxv hxq).2.2.2
    have := hzz x
    show 1 * ⟪x, e⟫ < 1 * ⟪v, e⟫
    nlinarith
  obtain ⟨ym, hym, hymv, hymq, hymz⟩ : ∃ y ∈ Q2, y ≠ v ∧ y ≠ q ∧ ζ y < 0 := by
    by_contra hcon
    push Not at hcon
    apply hOS2
    refine ⟨-1, Or.inr rfl, fun x hx hxv hxq => ?_⟩
    have hpos : 0 < ζ x := lt_of_le_of_ne (hcon x hx hxv hxq) (key2 x hx hxv hxq).2.2.2.symm
    have := hzz x
    show -1 * ⟪x, e⟫ < -1 * ⟪v, e⟫
    nlinarith
  have hxx : xp ≠ xm := fun h => by rw [h] at hxpz; linarith
  have hyy : yp ≠ ym := fun h => by rw [h] at hypz; linarith
  have hQ1 : ({v, p, xp, xm} : Finset ℝ³) = Q1 := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    · rw [h1c, card4_eq hpv.symm hxpv.symm hxmv.symm hxpp.symm hxmp.symm hxx]
  have hQ2 : ({v, q, yp, ym} : Finset ℝ³) = Q2 := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    · rw [h2c, card4_eq hqv.symm hypv.symm hymv.symm hypq.symm hymq.symm hyy]
  -- the model
  obtain ⟨xp1, xp2, xp3, xp4⟩ := key1 xp hxp hxpv hxpp
  obtain ⟨xm1, xm2, xm3, xm4⟩ := key1 xm hxm hxmv hxmp
  obtain ⟨yp1, yp2, yp3, yp4⟩ := key2 yp hyp hypv hypq
  obtain ⟨ym1, ym2, ym3, ym4⟩ := key2 ym hym hymv hymq
  obtain ⟨c, hcv, hcA, hcN, hcE, hcb, hct1, hct2, hch1, hch2, hcs1, hcs2, hck1, hck2⟩ :
      ∃ c : CObt, c.v = v ∧ c.A = A ∧ c.N = N ∧ c.E = e ∧ c.b = b ∧ c.t1 = α xp ∧
        c.t2 = α xm ∧ c.h1 = ζ xp ∧ c.h2 = -ζ xm ∧ c.s1 = ν yp ∧ c.s2 = ν ym ∧
        c.k1 = ζ yp ∧ c.k2 = -ζ ym :=
    ⟨{ v := v, A := A, N := N, E := e, b := b, t1 := α xp, t2 := α xm, h1 := ζ xp,
       h2 := -ζ xm, s1 := ν yp, s2 := ν ym, k1 := ζ yp, k2 := -ζ ym, hAN := hAN, hAE := hAe,
       hNE := hNe, hA := hA0, hN := hN0, hE := he, hb := hb, ht1 := xp1, ht1' := xp2,
       ht2 := xm1, ht2' := xm2, hh1 := hxpz, hh2 := neg_pos.mpr hxmz, hs1 := yp1, hs1' := yp2,
       hs2 := ym1, hs2' := ym2, hk1 := hypz, hk2 := neg_pos.mpr hymz },
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hM1 : c.M1 = xp := by
    calc c.M1 = v + (α xp • A + ν xp • N + ζ xp • e) := by
          rw [xp3]; simp only [CObt.M1, cpt, hcv, hcA, hcN, hcE, hct1, hch1]; module
      _ = xp := (hcoef' xp).symm
  have hM2 : c.M2 = xm := by
    calc c.M2 = v + (α xm • A + ν xm • N + ζ xm • e) := by
          rw [xm3]; simp only [CObt.M2, cpt, hcv, hcA, hcN, hcE, hct2, hch2]; module
      _ = xm := (hcoef' xm).symm
  have hN1 : c.N1 = yp := by
    calc c.N1 = v + (α yp • A + ν yp • N + ζ yp • e) := by
          rw [yp3]; simp only [CObt.N1, cpt, hcv, hcA, hcN, hcE, hcb, hcs1, hck1]; module
      _ = yp := (hcoef' yp).symm
  have hN2 : c.N2 = ym := by
    calc c.N2 = v + (α ym • A + ν ym • N + ζ ym • e) := by
          rw [ym3]; simp only [CObt.N2, cpt, hcv, hcA, hcN, hcE, hcb, hcs2, hck2]; module
      _ = ym := (hcoef' ym).symm
  have hP : c.pP = p := by
    simp only [CObt.pP, cpt, hcv, hcA, hAd]; module
  have hB : c.Bq = q := by
    simp only [CObt.Bq, cpt, hcv, hcA, hcN, hcE, hcb]
    calc v + b • A + (1:ℝ) • N + (0:ℝ) • e = v + (b • A + N) := by module
      _ = q := by rw [hBA, hBd]; abel
  have hV : c.V = V := by
    rw [← hcov, ← hQ1, ← hQ2]
    ext x
    simp only [CObt.V, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
    rw [hM1, hM2, hN1, hN2, hP, hB, hcv]
    tauto
  rw [← hV]
  exact c.isRupert_model

/-- The former general position `TriGenTieON`, kept for reference: as `TriGenTieO`, with no
segment at all parallel to the line.  `TriGenTieON.weaken` gives `TriGenTieO`. -/
def TriGenTieON (V Q1 Q2 : Finset ℝ³) (v : ℝ³) : Prop :=
  ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ, (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
    (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
    ∀ e : ℝ³, e ≠ 0 → f1 (v + e) = 0 → f2 (v + e) = 0 →
      (∀ p ∈ V, ∀ q ∈ V, p ≠ q → ∀ c : ℝ, q - p ≠ c • e) ∧
      ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
        TieHT Q1 Q2 v p q (fun x => ⟪x, e⟫) ∨
          (⟪p, e⟫ = ⟪q, e⟫ ∧ ⟪v, e⟫ = ⟪p, e⟫ ∧ ⟪p - v, q - v⟫ ≤ 0)


/-- **General position for Lemma T at the line of the planes of two facets, the triple tie
settled including a right or obtuse apex** (Theorems 24.5 and 24.8 of
`FEWER-FACES-PROOFS.md` §24): as `TriGenTieT`, with one more way out at the far ends `p`, `q`:
`p`, `q` and the shared vertex `v` at one depth along the line, and the angle of the shadow
triangle `(v, p, q)` at `v` at least `π/2` (`⟪p - v, q - v⟫ ≤ 0`).  By Theorem 24.8 this settles
the case-(c) triple tie (both faces two-sided) of two quadrilateral faces covering the seven
points: the views of the face circle of `Q1` beside the view along `p - v` have a unimodal
rim with distinct depths, so `V` is Rupert by Theorem 18.1 (`isRupert_of_obtuse_apex`).  Segments
parallel to the line are allowed between two middles of one face or two hidden vertices
(`MidPair`; Proposition 23.19 (2), (3)); the earlier form without any parallel segment is `TriGenTieON`.  What it excludes beyond
such a segment: the triple tie with both faces two-sided and the shadow triangle acute at `v`
and neither obtuse at `p` nor at `q`. -/
def TriGenTieO (V Q1 Q2 : Finset ℝ³) (v : ℝ³) : Prop :=
  ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ, (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
    (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
    ∀ e : ℝ³, e ≠ 0 → f1 (v + e) = 0 → f2 (v + e) = 0 →
      (∀ p ∈ V, ∀ q ∈ V, p ≠ q → ∀ c : ℝ, q - p = c • e →
        MidPair Q1 Q2 (fun p => ∀ p' ∈ Q1, f2 p ≤ f2 p') (fun q => ∀ q' ∈ Q2, f1 q ≤ f1 q')
          p q) ∧
      ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
        TieHT Q1 Q2 v p q (fun x => ⟪x, e⟫) ∨
          (⟪p, e⟫ = ⟪q, e⟫ ∧ ⟪v, e⟫ = ⟪p, e⟫ ∧ ⟪p - v, q - v⟫ ≤ 0)

/-- No parallel segment at all gives `TriGenTieO`. -/
theorem TriGenTieON.weaken {V Q1 Q2 : Finset ℝ³} {v : ℝ³} (h : TriGenTieON V Q1 Q2 v) :
    TriGenTieO V Q1 Q2 v := by
  intro f1 f2 z1 n1 z2 n2 e he e1 e2
  obtain ⟨hpar, hfar⟩ := h f1 f2 z1 n1 z2 n2 e he e1 e2
  exact ⟨fun p hp q hq hpq c hc => absurd hc (hpar p hp q hq hpq c), hfar⟩

theorem TriGenTieT.toO {V Q1 Q2 : Finset ℝ³} {v : ℝ³} (h : TriGenTieT V Q1 Q2 v) :
    TriGenTieO V Q1 Q2 v := by
  intro f1 f2 z1 n1 z2 n2 e he e1 e2
  obtain ⟨hpar, hfar⟩ := h f1 f2 z1 n1 z2 n2 e he e1 e2
  exact ⟨hpar, fun p hp q hq hpq h1 h2 => Or.inl (hfar p hp q hq hpq h1 h2)⟩

/-- **Lemma T over a vertex, the triple tie settled including a right or obtuse apex, facet
form** (Theorems 24.5 and 24.8 of `FEWER-FACES-PROOFS.md`): as `isRupert_of_facets_vertex_tieT`,
for two quadrilateral facets covering `V`, with `TriGenTieO`. -/
theorem isRupert_of_facets_vertex_tieO (V : Finset ℝ³) (hgen : NoThreeCollinear V)
    (Q1 Q2 : Finset ℝ³) (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (h1f : IsFacet V Q1) (h2f : IsFacet V Q2)
    (v : ℝ³) (hint : Q1 ∩ Q2 = {v}) (h1c : Q1.card = 4) (h2c : Q2.card = 4)
    (hcov : Q1 ∪ Q2 = V) (hT : TriGenTieO V Q1 Q2 v)
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ≠ v ∧ xb ≠ v ∧ ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ,
      (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
      (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1)
    (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty) : IsRupert V := by
  classical
  by_cases hTT : TriGenTieT V Q1 Q2 v
  · exact isRupert_of_facets_vertex_tieT V hgen Q1 Q2 h1V h2V h1f h2f v hint
      (Finset.exists_mem_ne (by omega : 1 < Q1.card) v)
      (Finset.exists_mem_ne (by omega : 1 < Q2.card) v) hTT hin hsol
  · unfold TriGenTieT at hTT
    push Not at hTT
    obtain ⟨f1, f2, z1, n1, z2, n2, e, he, e1, e2, hneg⟩ := hTT
    obtain ⟨hpar, hfar⟩ := hT f1 f2 z1 n1 z2 n2 e he e1 e2
    obtain ⟨p, hp, q, hq, hpq, h1, h2, hnot⟩ := hneg hpar
    rcases hfar p hp q hq hpq h1 h2 with h | h
    · exact absurd h hnot
    · exact isRupert_of_obtuse_apex V Q1 Q2 hgen v h1V h2V hint h1c h2c hcov f1 f2 z1 n1 z2 n2 e
        he e1 e2 hpar p hp q hq hpq h1 h2 hnot h

end Minimality

end
