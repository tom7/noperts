module

public import Minimality.EdgeView

@[expose] public section

/-!
# Four quadrilateral facets on seven points

Toward "a 7-point nopert has at most three quadrilateral facets"
(FEWER-FACES.md, "Bridge plan"): two facets of a set of extreme points share at
most two points, and when they share exactly two, these span a side of each.
-/

namespace Minimality

open Finset
open scoped RealInnerProductSpace

/-- The case `(u × w)₀ ≠ 0` of `dot_zero_of_parallel`. -/
theorem dot_zero_of_parallel₀ {p0 p1 p2 q0 q1 q2 u0 u1 u2 w0 w1 w2 d0 d1 d2 : ℝ}
    (pu : p0 * u0 + p1 * u1 + p2 * u2 = 0) (pw : p0 * w0 + p1 * w1 + p2 * w2 = 0)
    (qu : q0 * u0 + q1 * u1 + q2 * u2 = 0) (qw : q0 * w0 + q1 * w1 + q2 * w2 = 0)
    (hm : u1 * w2 - u2 * w1 ≠ 0)
    (hq : q0 ≠ 0 ∨ q1 ≠ 0 ∨ q2 ≠ 0) (qd : q0 * d0 + q1 * d1 + q2 * d2 = 0) :
    p0 * d0 + p1 * d1 + p2 * d2 = 0 := by
  -- p × m = 0 and q × m = 0 for m = u × w (BAC-CAB)
  have a20 : p2 * (u1 * w2 - u2 * w1) - p0 * (u0 * w1 - u1 * w0) = 0 := by
    linear_combination u1 * pw - w1 * pu
  have a01 : p0 * (u2 * w0 - u0 * w2) - p1 * (u1 * w2 - u2 * w1) = 0 := by
    linear_combination u2 * pw - w2 * pu
  have b20 : q2 * (u1 * w2 - u2 * w1) - q0 * (u0 * w1 - u1 * w0) = 0 := by
    linear_combination u1 * qw - w1 * qu
  have b01 : q0 * (u2 * w0 - u0 * w2) - q1 * (u1 * w2 - u2 * w1) = 0 := by
    linear_combination u2 * qw - w2 * qu
  set m0 := u1 * w2 - u2 * w1
  set m1 := u2 * w0 - u0 * w2
  set m2 := u0 * w1 - u1 * w0
  -- q ∥ m and m0 ≠ 0 force q0 ≠ 0
  have hq0 : q0 ≠ 0 := by
    intro h0
    have h1 : q1 * m0 = 0 := by rw [h0] at b01; linarith
    have h2 : q2 * m0 = 0 := by rw [h0] at b20; linarith
    have h1' := (mul_eq_zero.mp h1).resolve_right hm
    have h2' := (mul_eq_zero.mp h2).resolve_right hm
    rcases hq with h | h | h <;> exact h (by assumption)
  -- p_j q0 = p0 q_j
  have r1 : p1 * q0 = p0 * q1 := by
    apply mul_right_cancel₀ (pow_ne_zero 2 hm)
    linear_combination -(q0 * m0) * a01 + (p0 * m0) * b01
  have r2 : p2 * q0 = p0 * q2 := by
    apply mul_right_cancel₀ (pow_ne_zero 2 hm)
    linear_combination (q0 * m0) * a20 - (p0 * m0) * b20
  apply mul_right_cancel₀ hq0
  linear_combination d1 * r1 + d2 * r2 + p0 * qd

/-- Linear algebra in coordinates: if `p` and `q` are both orthogonal to `u` and
`w` with `u × w ≠ 0`, and `q ≠ 0`, then `q · d = 0` implies `p · d = 0`. -/
theorem dot_zero_of_parallel {p0 p1 p2 q0 q1 q2 u0 u1 u2 w0 w1 w2 d0 d1 d2 : ℝ}
    (pu : p0 * u0 + p1 * u1 + p2 * u2 = 0) (pw : p0 * w0 + p1 * w1 + p2 * w2 = 0)
    (qu : q0 * u0 + q1 * u1 + q2 * u2 = 0) (qw : q0 * w0 + q1 * w1 + q2 * w2 = 0)
    (hm : u1 * w2 - u2 * w1 ≠ 0 ∨ u2 * w0 - u0 * w2 ≠ 0 ∨ u0 * w1 - u1 * w0 ≠ 0)
    (hq : q0 ≠ 0 ∨ q1 ≠ 0 ∨ q2 ≠ 0) (qd : q0 * d0 + q1 * d1 + q2 * d2 = 0) :
    p0 * d0 + p1 * d1 + p2 * d2 = 0 := by
  rcases hm with h | h | h
  · exact dot_zero_of_parallel₀ pu pw qu qw h hq qd
  · -- rotate coordinates 1 → 0
    have := dot_zero_of_parallel₀ (p0 := p1) (p1 := p2) (p2 := p0) (q0 := q1) (q1 := q2) (q2 := q0)
      (u0 := u1) (u1 := u2) (u2 := u0) (w0 := w1) (w1 := w2) (w2 := w0) (d0 := d1) (d1 := d2)
      (d2 := d0) (by linarith) (by linarith) (by linarith) (by linarith) h
      (by rcases hq with h' | h' | h'
          · exact Or.inr (Or.inr h')
          · exact Or.inl h'
          · exact Or.inr (Or.inl h')) (by linarith)
    linarith
  · have := dot_zero_of_parallel₀ (p0 := p2) (p1 := p0) (p2 := p1) (q0 := q2) (q1 := q0) (q2 := q1)
      (u0 := u2) (u1 := u0) (u2 := u1) (w0 := w2) (w1 := w0) (w2 := w1) (d0 := d2) (d1 := d0)
      (d2 := d1) (by linarith) (by linarith) (by linarith) (by linarith) h
      (by rcases hq with h' | h' | h'
          · exact Or.inr (Or.inl h')
          · exact Or.inr (Or.inr h')
          · exact Or.inl h') (by linarith)
    linarith

/-- Two affine functions on `ℝ³` vanishing on three non-collinear points `a, b, c`
(with `f2` not constant) vanish together: `f2 y = 0 → f1 y = 0`. -/
theorem affine_zero_of_zero_three (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ) {a b c y z : ℝ³}
    (hm : cross (b - a) (c - a) ≠ 0)
    (h1a : f1 a = 0) (h1b : f1 b = 0) (h1c : f1 c = 0)
    (h2a : f2 a = 0) (h2b : f2 b = 0) (h2c : f2 c = 0) (h2z : f2 z ≠ 0) (h2y : f2 y = 0) :
    f1 y = 0 := by
  obtain ⟨K1, p0, p1, p2, e1⟩ := affine_xyz f1
  obtain ⟨K2, q0, q1, q2, e2⟩ := affine_xyz f2
  rw [e1] at h1a h1b h1c ⊢
  rw [e2] at h2a h2b h2c h2z h2y
  have hm' : (b 1 - a 1) * (c 2 - a 2) - (b 2 - a 2) * (c 1 - a 1) ≠ 0 ∨
      (b 2 - a 2) * (c 0 - a 0) - (b 0 - a 0) * (c 2 - a 2) ≠ 0 ∨
      (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0) ≠ 0 := by
    by_contra h; push Not at h; apply hm
    ext i; fin_cases i
    · simp [cross]; linear_combination h.1
    · simp [cross]; linear_combination h.2.1
    · simp [cross]; linear_combination h.2.2
  have hq : q0 ≠ 0 ∨ q1 ≠ 0 ∨ q2 ≠ 0 := by
    by_contra h; push Not at h; obtain ⟨h0, h1, h2⟩ := h
    apply h2z; rw [h0, h1, h2] at h2a ⊢; linarith
  have := dot_zero_of_parallel (p0 := p0) (p1 := p1) (p2 := p2) (q0 := q0) (q1 := q1) (q2 := q2)
    (d0 := y 0 - a 0) (d1 := y 1 - a 1) (d2 := y 2 - a 2)
    (by linear_combination h1b - h1a) (by linear_combination h1c - h1a)
    (by linear_combination h2b - h2a) (by linear_combination h2c - h2a) hm' hq
    (by linear_combination h2y - h2a)
  linear_combination this + h1a

/-- Collinear: `c - a` is a multiple of `b - a` (for `a ≠ b`). -/
theorem exists_smul_of_cross_eq_zero {a b c : ℝ³} (hab : a ≠ b)
    (h : cross (b - a) (c - a) = 0) : ∃ t : ℝ, c - a = t • (b - a) := by
  have c0 := congrArg (fun v : ℝ³ => v 0) h
  have c1 := congrArg (fun v : ℝ³ => v 1) h
  have c2 := congrArg (fun v : ℝ³ => v 2) h
  simp [cross] at c0 c1 c2
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  by_cases h0 : b 0 - a 0 = 0
  · by_cases h1 : b 1 - a 1 = 0
    · have h2 : b 2 - a 2 ≠ 0 := by
        intro h2; apply hba; ext i; fin_cases i <;> simp <;> linarith
      refine ⟨(c 2 - a 2) / (b 2 - a 2), ?_⟩
      ext i; fin_cases i <;> simp <;> field_simp
      · rw [h0] at c1 ⊢; nlinarith [c1]
      · rw [h1] at c0 ⊢; nlinarith [c0]
    · refine ⟨(c 1 - a 1) / (b 1 - a 1), ?_⟩
      ext i; fin_cases i <;> simp <;> field_simp
      · nlinarith [c2]
      · nlinarith [c0]
  · refine ⟨(c 0 - a 0) / (b 0 - a 0), ?_⟩
    ext i; fin_cases i <;> simp <;> field_simp
    · nlinarith [c2]
    · nlinarith [c1]

/-- Three distinct collinear points: one lies on the segment of the other two. -/
theorem mem_segment_of_cross_eq_zero {a b c : ℝ³} (hab : a ≠ b)
    (h : cross (b - a) (c - a) = 0) :
    c ∈ segment ℝ a b ∨ b ∈ segment ℝ a c ∨ a ∈ segment ℝ c b := by
  obtain ⟨t, ht⟩ := exists_smul_of_cross_eq_zero hab h
  have hc : c = a + t • (b - a) := by rw [← ht]; abel
  rcases le_or_gt 0 t with h0 | h0
  · rcases le_or_gt t 1 with h1 | h1
    · left
      refine ⟨1 - t, t, by linarith, h0, by ring, ?_⟩
      rw [hc]; ext i; simp; ring
    · right; left
      refine ⟨1 - 1 / t, 1 / t, ?_, ?_, by ring, ?_⟩
      · rw [sub_nonneg, div_le_one (by linarith)]; linarith
      · positivity
      · rw [hc]; ext i; simp; field_simp; ring
  · right; right
    have h1t : 1 - t ≠ 0 := (by linarith : (0 : ℝ) < 1 - t).ne'
    refine ⟨1 / (1 - t), -t / (1 - t), ?_, ?_, ?_, ?_⟩
    · apply div_nonneg <;> linarith
    · apply div_nonneg <;> linarith
    · field_simp; ring
    · rw [hc]; ext i; simp; field_simp; ring

/-- Two distinct proper facets of a set of extreme points share at most two
points: three shared points are not collinear (one would lie between the
others), so they span both facet planes, and the facets coincide. -/
theorem card_inter_le_two_of_facets {V F1 F2 : Finset ℝ³}
    (hext : ∀ x ∈ V, x ∉ convexHull ℝ ((V.erase x : Finset ℝ³) : Set ℝ³))
    (h1 : IsFacet V F1) (h2 : IsFacet V F2) (hF1 : F1 ⊆ V) (hF2 : F2 ⊆ V)
    (hV1 : F1 ≠ V) (hV2 : F2 ≠ V) (hne : F1 ≠ F2) : (F1 ∩ F2).card ≤ 2 := by
  classical
  by_contra hlt
  push Not at hlt
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hlt
  rw [Finset.mem_inter] at ha hb hc
  -- the three shared points are not collinear
  have hm : cross (b - a) (c - a) ≠ 0 := by
    intro hm
    have mem : ∀ {p q r : ℝ³}, p ∈ V → q ∈ V → r ∈ V → p ≠ r → q ≠ r →
        r ∈ segment ℝ p q → False := fun {p q r} hp hq hr hpr hqr hseg =>
      hext r hr (segment_subset_convexHull (by simpa using ⟨hp, hpr⟩)
        (by simpa using ⟨hq, hqr⟩) hseg)
    rcases mem_segment_of_cross_eq_zero hab hm with h | h | h
    · exact mem (hF1 ha.1) (hF1 hb.1) (hF1 hc.1) hac hbc h
    · exact mem (hF1 ha.1) (hF1 hc.1) (hF1 hb.1) hab hbc.symm h
    · exact mem (hF1 hc.1) (hF1 hb.1) (hF1 ha.1) hac.symm hab.symm h
  obtain ⟨f1, hf10, hf1n⟩ := h1
  obtain ⟨f2, hf20, hf2n⟩ := h2
  -- each facet function is not constant
  obtain ⟨z1, hz1V, hz1F⟩ : ∃ z ∈ V, z ∉ F1 := by
    by_contra h; push Not at h; exact hV1 (Finset.Subset.antisymm hF1 h)
  obtain ⟨z2, hz2V, hz2F⟩ : ∃ z ∈ V, z ∉ F2 := by
    by_contra h; push Not at h; exact hV2 (Finset.Subset.antisymm hF2 h)
  apply hne
  ext y
  constructor
  · intro hy
    by_contra hy2
    have := affine_zero_of_zero_three f2 f1 hm (hf20 a ha.2) (hf20 b hb.2) (hf20 c hc.2)
      (hf10 a ha.1) (hf10 b hb.1) (hf10 c hc.1) (hf1n z1 hz1V hz1F).ne (hf10 y hy)
    exact (hf2n y (hF1 hy) hy2).ne this
  · intro hy
    by_contra hy1
    have := affine_zero_of_zero_three f1 f2 hm (hf10 a ha.1) (hf10 b hb.1) (hf10 c hc.1)
      (hf20 a ha.2) (hf20 b hb.2) (hf20 c hc.2) (hf2n z2 hz2V hz2F).ne (hf20 y hy)
    exact (hf1n y (hF2 hy) hy1).ne this

/-- A point on a (nonconstant) affine function's zero plane through three
non-collinear points is an affine combination of them. -/
theorem exists_affine_repr (f : ℝ³ →ᵃ[ℝ] ℝ) {x0 x1 x2 x3 z : ℝ³}
    (hm : cross (x1 - x0) (x2 - x0) ≠ 0)
    (h0 : f x0 = 0) (h1 : f x1 = 0) (h2 : f x2 = 0) (h3 : f x3 = 0) (hz : f z ≠ 0) :
    ∃ α β : ℝ, x3 = x0 + α • (x1 - x0) + β • (x2 - x0) := by
  have hm' : (x1 - x0) 1 * (x2 - x0) 2 - (x1 - x0) 2 * (x2 - x0) 1 ≠ 0 ∨
      (x1 - x0) 2 * (x2 - x0) 0 - (x1 - x0) 0 * (x2 - x0) 2 ≠ 0 ∨
      (x1 - x0) 0 * (x2 - x0) 1 - (x1 - x0) 1 * (x2 - x0) 0 ≠ 0 := by
    by_contra h; push Not at h; apply hm
    ext i; fin_cases i
    · simp only [cross]; simp at h ⊢; linear_combination h.1
    · simp only [cross]; simp at h ⊢; linear_combination h.2.1
    · simp only [cross]; simp at h ⊢; linear_combination h.2.2
  set u := x1 - x0 with hu
  set w := x2 - x0 with hw
  set m := cross u w with hmdef
  set d := x3 - x0 with hd
  -- |m|² ≠ 0
  have hmm : m 0 * m 0 + m 1 * m 1 + m 2 * m 2 ≠ 0 := by
    intro h; apply hm
    have a := mul_self_nonneg (m 0); have b := mul_self_nonneg (m 1); have c := mul_self_nonneg (m 2)
    ext i; fin_cases i <;> simp <;> nlinarith
  -- m · d = 0: m and f's normal are both orthogonal to u and w
  obtain ⟨K, q0, q1, q2, e⟩ := affine_xyz f
  rw [e] at h0 h1 h2 h3 hz
  have hq : q0 ≠ 0 ∨ q1 ≠ 0 ∨ q2 ≠ 0 := by
    by_contra h; push Not at h; obtain ⟨a, b, c⟩ := h
    apply hz; rw [a, b, c] at h0 ⊢; linarith
  have hmd : m 0 * d 0 + m 1 * d 1 + m 2 * d 2 = 0 := by
    refine dot_zero_of_parallel (q0 := q0) (q1 := q1) (q2 := q2) (u0 := u 0) (u1 := u 1) (u2 := u 2)
      (w0 := w 0) (w1 := w 1) (w2 := w 2) ?_ ?_ ?_ ?_ hm' hq ?_
    · simp [hmdef, cross]; ring
    · simp [hmdef, cross]; ring
    · simp [hu]; linear_combination h1 - h0
    · simp [hw]; linear_combination h2 - h0
    · simp [hd]; linear_combination h3 - h0
  -- d = α u + β w (+ (m·d)/|m|² m = 0) with the dual basis
  refine ⟨((cross d w) 0 * m 0 + (cross d w) 1 * m 1 + (cross d w) 2 * m 2) /
      (m 0 * m 0 + m 1 * m 1 + m 2 * m 2),
    ((cross u d) 0 * m 0 + (cross u d) 1 * m 1 + (cross u d) 2 * m 2) /
      (m 0 * m 0 + m 1 * m 1 + m 2 * m 2), ?_⟩
  have key : ∀ i, d i * (m 0 * m 0 + m 1 * m 1 + m 2 * m 2) =
      ((cross d w) 0 * m 0 + (cross d w) 1 * m 1 + (cross d w) 2 * m 2) * u i +
      ((cross u d) 0 * m 0 + (cross u d) 1 * m 1 + (cross u d) 2 * m 2) * w i +
      (m 0 * d 0 + m 1 * d 1 + m 2 * d 2) * m i := by
    intro i; fin_cases i <;> simp [hmdef, cross] <;> ring
  have hx3 : x3 = x0 + d := by rw [hd]; abel
  rw [hx3]
  ext i
  have := key i
  rw [hmd, zero_mul, add_zero] at this
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hdi : d i = (((cross d w) 0 * m 0 + (cross d w) 1 * m 1 + (cross d w) 2 * m 2) * u i +
      ((cross u d) 0 * m 0 + (cross u d) 1 * m 1 + (cross u d) 2 * m 2) * w i) /
      (m 0 * m 0 + m 1 * m 1 + m 2 * m 2) := by
    rw [eq_div_iff hmm]; linarith
  rw [hdi]; ring

/-- An affine function at an affine combination. -/
theorem affine_at_comb (g : ℝ³ →ᵃ[ℝ] ℝ) (x0 x1 x2 : ℝ³) (α β : ℝ) :
    g (x0 + α • (x1 - x0) + β • (x2 - x0)) = g x0 + α * (g x1 - g x0) + β * (g x2 - g x0) := by
  obtain ⟨K, a, b, c, e⟩ := affine_xyz g
  simp only [e, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; ring

/-- Three points where an affine function vanishes at two and not at the third
are not collinear. -/
theorem cross_ne_of_affine {g : ℝ³ →ᵃ[ℝ] ℝ} {x0 x1 x2 : ℝ³} (h01 : x0 ≠ x1)
    (g0 : g x0 = 0) (g1 : g x1 = 0) (g2 : g x2 ≠ 0) : cross (x1 - x0) (x2 - x0) ≠ 0 := by
  intro hc
  obtain ⟨t, ht⟩ := exists_smul_of_cross_eq_zero h01 hc
  have hx2 : x2 = x0 + t • (x1 - x0) + (0 : ℝ) • (x2 - x0) := by rw [← ht]; simp
  have := affine_at_comb g x0 x1 x2 t 0
  rw [← hx2, g0, g1] at this
  exact g2 (by linarith)

/-- **No three sides at one vertex.** In a quadrilateral facet `x0 x1 x2 x3`
(an affine `f` vanishing there, nonconstant), the pairs `x0x1`, `x0x2`, `x0x3`
cannot all be sides cut out by other facets `g1`, `g2`, `g3` (each vanishing on
its pair and negative on the other two points). -/
theorem not_three_sides_at_vertex {f g1 g2 g3 : ℝ³ →ᵃ[ℝ] ℝ} {x0 x1 x2 x3 z : ℝ³}
    (f0 : f x0 = 0) (f1 : f x1 = 0) (f2 : f x2 = 0) (f3 : f x3 = 0) (fz : f z ≠ 0)
    (a0 : g1 x0 = 0) (a1 : g1 x1 = 0) (a2 : g1 x2 < 0) (a3 : g1 x3 < 0)
    (b0 : g2 x0 = 0) (b2 : g2 x2 = 0) (b1 : g2 x1 < 0) (b3 : g2 x3 < 0)
    (c0 : g3 x0 = 0) (c3 : g3 x3 = 0) (c1 : g3 x1 < 0) (c2 : g3 x2 < 0) : False := by
  have h01 : x0 ≠ x1 := fun h => by rw [h] at b0; linarith
  obtain ⟨α, β, hx3⟩ := exists_affine_repr f (cross_ne_of_affine h01 a0 a1 a2.ne) f0 f1 f2 f3 fz
  have e1 := affine_at_comb g1 x0 x1 x2 α β
  have e2 := affine_at_comb g2 x0 x1 x2 α β
  have e3 := affine_at_comb g3 x0 x1 x2 α β
  rw [← hx3] at e1 e2 e3
  rw [a0, a1] at e1; rw [b0, b2] at e2; rw [c0, c3] at e3
  -- β > 0 from g1, α > 0 from g2, then g3 x3 < 0
  have hβ : 0 < β := by nlinarith
  have hα : 0 < α := by nlinarith
  nlinarith [mul_pos hα (neg_pos.mpr c1), mul_pos hβ (neg_pos.mpr c2)]

/-- **No triangle of sides.** If `x0x1`, `x0x2`, `x1x2` are all sides of the
quadrilateral facet `x0 x1 x2 x3` (cut out by facets `g1`, `g2`, `g3`), then
`x3` lies in the triangle `x0 x1 x2`. -/
theorem mem_triangle_of_three_sides {f g1 g2 g3 : ℝ³ →ᵃ[ℝ] ℝ} {x0 x1 x2 x3 z : ℝ³}
    (f0 : f x0 = 0) (f1 : f x1 = 0) (f2 : f x2 = 0) (f3 : f x3 = 0) (fz : f z ≠ 0)
    (a0 : g1 x0 = 0) (a1 : g1 x1 = 0) (a2 : g1 x2 < 0) (a3 : g1 x3 < 0)
    (b0 : g2 x0 = 0) (b2 : g2 x2 = 0) (b1 : g2 x1 < 0) (b3 : g2 x3 < 0)
    (c1 : g3 x1 = 0) (c2 : g3 x2 = 0) (c0 : g3 x0 < 0) (c3 : g3 x3 < 0) :
    x3 ∈ convexHull ℝ ({x0, x1, x2} : Set ℝ³) := by
  have h01 : x0 ≠ x1 := fun h => by rw [h] at b0; linarith
  obtain ⟨α, β, hx3⟩ := exists_affine_repr f (cross_ne_of_affine h01 a0 a1 a2.ne) f0 f1 f2 f3 fz
  have e1 := affine_at_comb g1 x0 x1 x2 α β
  have e2 := affine_at_comb g2 x0 x1 x2 α β
  have e3 := affine_at_comb g3 x0 x1 x2 α β
  rw [← hx3] at e1 e2 e3
  rw [a0, a1] at e1; rw [b0, b2] at e2; rw [c1, c2] at e3
  have hβ : 0 < β := by nlinarith
  have hα : 0 < α := by nlinarith
  have hγ : 0 < 1 - α - β := by nlinarith
  have hS := convex_convexHull ℝ ({x0, x1, x2} : Set ℝ³)
  have m0 : x0 ∈ convexHull ℝ ({x0, x1, x2} : Set ℝ³) := subset_convexHull ℝ _ (by simp)
  have m1 : x1 ∈ convexHull ℝ ({x0, x1, x2} : Set ℝ³) := subset_convexHull ℝ _ (by simp)
  have m2 : x2 ∈ convexHull ℝ ({x0, x1, x2} : Set ℝ³) := subset_convexHull ℝ _ (by simp)
  have hab : 0 < α + β := by linarith
  have my := hS m1 m2 (div_pos hα hab).le (div_pos hβ hab).le (by field_simp)
  have mx := hS m0 my hγ.le hab.le (by ring)
  convert mx using 1
  rw [hx3]; ext i; simp; field_simp; ring

/-! ### The classification (kernel-decided)

Four 4-subsets of `Fin 7` (the first one `{0, 1, 2, 3}`, by choosing the
enumeration), distinct, pairwise sharing at most two points, with no three
distinct shared pairs of one of them meeting at a point or forming a triangle,
are the type-02 pattern in some order. -/

/-- The three shared pairs of `X` (with `Y`, `Z`, `W`), when all have two
points and are distinct, neither meet at a point nor form a triangle. -/
def QuadSidesOK (X Y Z W : Finset (Fin 7)) : Prop :=
  ¬ ((X ∩ Y).card = 2 ∧ (X ∩ Z).card = 2 ∧ (X ∩ W).card = 2 ∧
    X ∩ Y ≠ X ∩ Z ∧ X ∩ Y ≠ X ∩ W ∧ X ∩ Z ≠ X ∩ W ∧
    ((X ∩ Y ∩ Z ∩ W).Nonempty ∨ ((X ∩ Y) ∪ (X ∩ Z) ∪ (X ∩ W)).card = 3))

instance (X Y Z W : Finset (Fin 7)) : Decidable (QuadSidesOK X Y Z W) := by
  unfold QuadSidesOK; infer_instance

/-- The type-02 pattern: the sets are 3014, 3564, 3025, 4126 for distinct
labels `v0, …, v6`. -/
def IsType02Pattern (P1 P2 P3 P4 : Finset (Fin 7)) : Prop :=
  ∃ v3 ∈ P1 ∩ P2 ∩ P3, ∃ v4 ∈ P1 ∩ P2 ∩ P4, ∃ v2 ∈ P3 ∩ P4, ∃ v0 ∈ P1 ∩ P3, ∃ v1 ∈ P1 ∩ P4,
    ∃ v5 ∈ P2 ∩ P3, ∃ v6 ∈ P2 ∩ P4,
    [v0, v1, v2, v3, v4, v5, v6].Nodup ∧ P1 = {v3, v0, v1, v4} ∧ P2 = {v3, v5, v6, v4} ∧
      P3 = {v3, v0, v2, v5} ∧ P4 = {v4, v1, v2, v6}

instance (P1 P2 P3 P4 : Finset (Fin 7)) : Decidable (IsType02Pattern P1 P2 P3 P4) := by
  unfold IsType02Pattern; infer_instance

set_option maxRecDepth 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 4096 in
/-- **The classification**, decided by the kernel (about 15 s). -/
theorem quad_facets_classify : ∀ B ∈ (Finset.univ : Finset (Fin 7)).powersetCard 4,
    ({0, 1, 2, 3} ∩ B).card ≤ 2 →
    ∀ C ∈ (Finset.univ : Finset (Fin 7)).powersetCard 4,
    ({0, 1, 2, 3} ∩ C).card ≤ 2 → (B ∩ C).card ≤ 2 → B ≠ C →
    ∀ D ∈ (Finset.univ : Finset (Fin 7)).powersetCard 4,
    ({0, 1, 2, 3} ∩ D).card ≤ 2 → (B ∩ D).card ≤ 2 → (C ∩ D).card ≤ 2 → B ≠ D → C ≠ D →
    QuadSidesOK {0, 1, 2, 3} B C D → QuadSidesOK B {0, 1, 2, 3} C D →
    QuadSidesOK C {0, 1, 2, 3} B D → QuadSidesOK D {0, 1, 2, 3} B C →
    (IsType02Pattern {0, 1, 2, 3} B C D ∨ IsType02Pattern {0, 1, 2, 3} C B D ∨
     IsType02Pattern {0, 1, 2, 3} D B C ∨ IsType02Pattern B C {0, 1, 2, 3} D ∨
     IsType02Pattern B D {0, 1, 2, 3} C ∨ IsType02Pattern C D {0, 1, 2, 3} B) := by
  decide +kernel

/-! ### From the geometry to `QuadSidesOK` -/

/-- A two-element set containing `v` is `{v, p}` for some `p ≠ v`. -/
theorem exists_pair_of_mem {α : Type*} [DecidableEq α] {S : Finset α} {v : α}
    (h2 : S.card = 2) (hv : v ∈ S) : ∃ p, p ≠ v ∧ S = {v, p} := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp h2
  rcases Finset.mem_insert.mp hv with rfl | hv
  · exact ⟨y, hxy.symm, rfl⟩
  · rw [Finset.mem_singleton] at hv; subst hv
    exact ⟨x, hxy, Finset.pair_comm _ _⟩

/-- **Three sides at a vertex or in a triangle.** If three distinct two-element
subsets `S1, S2, S3` of a set have a common point, they are `{v,p}, {v,q}, {v,r}`
with `v, p, q, r` distinct; if their union has three points, they are
`{x,y}, {c,x}, {c,y}` with `x, y, c` distinct. -/
theorem three_pairs_cases {α : Type*} [DecidableEq α] {S1 S2 S3 : Finset α}
    (h1 : S1.card = 2) (h2 : S2.card = 2) (h3 : S3.card = 2)
    (n12 : S1 ≠ S2) (n13 : S1 ≠ S3) (n23 : S2 ≠ S3)
    (h : (S1 ∩ S2 ∩ S3).Nonempty ∨ (S1 ∪ S2 ∪ S3).card = 3) :
    (∃ v p q r, [v, p, q, r].Nodup ∧ S1 = {v, p} ∧ S2 = {v, q} ∧ S3 = {v, r}) ∨
    (∃ x y c, [x, y, c].Nodup ∧ S1 = {x, y} ∧ S2 = {c, x} ∧ S3 = {c, y}) := by
  rcases h with ⟨v, hv⟩ | hU
  · left
    simp only [Finset.mem_inter] at hv
    obtain ⟨p, hp, rfl⟩ := exists_pair_of_mem h1 hv.1.1
    obtain ⟨q, hq, rfl⟩ := exists_pair_of_mem h2 hv.1.2
    obtain ⟨r, hr, rfl⟩ := exists_pair_of_mem h3 hv.2
    have hpq : p ≠ q := fun e => n12 (by rw [e])
    have hpr : p ≠ r := fun e => n13 (by rw [e])
    have hqr : q ≠ r := fun e => n23 (by rw [e])
    exact ⟨v, p, q, r, by simp [hp.symm, hq.symm, hr.symm, hpq, hpr, hqr], rfl, rfl, rfl⟩
  · right
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp h1
    -- the third point c of the union
    obtain ⟨c, hcU, hcS1⟩ : ∃ c ∈ ({x, y} : Finset α) ∪ S2 ∪ S3, c ∉ ({x, y} : Finset α) := by
      by_contra hc; push Not at hc
      have : ({x, y} : Finset α) ∪ S2 ∪ S3 ⊆ {x, y} := hc
      have := Finset.card_le_card this
      rw [hU, Finset.card_pair hxy] at this; omega
    have hU' : ({x, y} : Finset α) ∪ S2 ∪ S3 = {c, x, y} := by
      apply (Finset.eq_of_subset_of_card_le ?_ ?_).symm
      · intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl
        · exact hcU
        · simp
        · simp
      · rw [hU, Finset.card_insert_of_notMem hcS1, Finset.card_pair hxy]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcS1
    -- S2, S3 are 2-subsets of {c, x, y} other than {x, y}: each contains c
    have sub2 : S2 ⊆ {c, x, y} := hU' ▸ (Finset.subset_union_right.trans Finset.subset_union_left)
    have sub3 : S3 ⊆ {c, x, y} := hU' ▸ Finset.subset_union_right
    have pick : ∀ S : Finset α, S.card = 2 → S ⊆ {c, x, y} → S ≠ {x, y} →
        S = {c, x} ∨ S = {c, y} := by
      intro S hS hsub hne
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hS
      have ha := hsub (by simp : a ∈ ({a, b} : Finset α))
      have hb := hsub (by simp : b ∈ ({a, b} : Finset α))
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
        first
        | exact absurd rfl hab
        | exact Or.inl rfl
        | exact Or.inr rfl
        | exact Or.inl (Finset.pair_comm _ _)
        | exact Or.inr (Finset.pair_comm _ _)
        | exact absurd rfl hne
        | exact absurd (Finset.pair_comm _ _) hne
    have hc1 : c ≠ x := hcS1.1
    have hc2 : c ≠ y := hcS1.2
    rcases pick S2 h2 sub2 (Ne.symm n12) with e2 | e2 <;>
      rcases pick S3 h3 sub3 (Ne.symm n13) with e3 | e3
    · exact absurd (e2.trans e3.symm) n23
    · exact ⟨x, y, c, by simp [hxy, hc1.symm, hc2.symm], rfl, e2, e3⟩
    · exact ⟨y, x, c, by simp [hxy.symm, hc1.symm, hc2.symm], Finset.pair_comm _ _, e2, e3⟩
    · exact absurd (e2.trans e3.symm) n23

/-! ### From the type-02 pattern to Rupertness -/

/-- **General position** of a point set, as used by Theorem B: no two segments
between its points are parallel or orthogonal (for distinct pairs). -/
def GenPos (V : Finset ℝ³) : Prop :=
  ∀ a ∈ V, ∀ b ∈ V, ∀ c ∈ V, ∀ d ∈ V, a ≠ b → c ≠ d → ({a, b} : Finset ℝ³) ≠ {c, d} →
    (∀ t : ℝ, b - a ≠ t • (d - c)) ∧ ⟪b - a, d - c⟫ ≠ 0

set_option linter.unusedSimpArgs false in
/-- Seven points labelled by an injective `e`, with four facets whose index sets
form the type-02 pattern, in general position, are Rupert (Theorem B). -/
theorem isRupert_of_type02Pattern (e : Fin 7 → ℝ³) (he : Function.Injective e)
    (hext : ∀ i, e i ∉ convexHull ℝ ((Finset.univ.image e).erase (e i) : Set ℝ³))
    (hgen : GenPos (Finset.univ.image e))
    (P1 P2 P3 P4 : Finset (Fin 7)) (f1 f2 f3 f4 : ℝ³ →ᵃ[ℝ] ℝ)
    (h1 : ∀ i, (i ∈ P1 → f1 (e i) = 0) ∧ (i ∉ P1 → f1 (e i) < 0))
    (h2 : ∀ i, (i ∈ P2 → f2 (e i) = 0) ∧ (i ∉ P2 → f2 (e i) < 0))
    (h3 : ∀ i, (i ∈ P3 → f3 (e i) = 0) ∧ (i ∉ P3 → f3 (e i) < 0))
    (h4 : ∀ i, (i ∈ P4 → f4 (e i) = 0) ∧ (i ∉ P4 → f4 (e i) < 0))
    (hpat : IsType02Pattern P1 P2 P3 P4) : IsRupert (Finset.univ.image e) := by
  obtain ⟨v3, -, v4, -, v2, -, v0, -, v1, -, v5, -, v6, -, hnd, e1, e2, e3, e4⟩ := hpat
  set lab : Fin 7 → Fin 7 := [v0, v1, v2, v3, v4, v5, v6].get with hlab
  have hlabi : Function.Injective lab := List.nodup_iff_injective_get.mp hnd
  have hlabs : Function.Surjective lab := Finite.surjective_of_injective hlabi
  set x : Fin 7 → ℝ³ := fun k => e (lab k) with hx
  have himg : Finset.univ.image x = Finset.univ.image e := by
    ext y; simp only [Finset.mem_image, Finset.mem_univ, true_and, hx]
    constructor
    · rintro ⟨k, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨i, rfl⟩; obtain ⟨k, rfl⟩ := hlabs i; exact ⟨k, rfl⟩
  rw [← himg]
  have xi : ∀ k, x k = e (lab k) := fun k => rfl
  have l0 : lab 0 = v0 := rfl
  have l1 : lab 1 = v1 := rfl
  have l2 : lab 2 = v2 := rfl
  have l3 : lab 3 = v3 := rfl
  have l4 : lab 4 = v4 := rfl
  have l5 : lab 5 = v5 := rfl
  have l6 : lab 6 = v6 := rfl
  have d01 : v0 ≠ v1 := hlabi.ne (by decide : (0 : Fin 7) ≠ 1)
  have d02 : v0 ≠ v2 := hlabi.ne (by decide : (0 : Fin 7) ≠ 2)
  have d03 : v0 ≠ v3 := hlabi.ne (by decide : (0 : Fin 7) ≠ 3)
  have d04 : v0 ≠ v4 := hlabi.ne (by decide : (0 : Fin 7) ≠ 4)
  have d05 : v0 ≠ v5 := hlabi.ne (by decide : (0 : Fin 7) ≠ 5)
  have d06 : v0 ≠ v6 := hlabi.ne (by decide : (0 : Fin 7) ≠ 6)
  have d10 : v1 ≠ v0 := hlabi.ne (by decide : (1 : Fin 7) ≠ 0)
  have d12 : v1 ≠ v2 := hlabi.ne (by decide : (1 : Fin 7) ≠ 2)
  have d13 : v1 ≠ v3 := hlabi.ne (by decide : (1 : Fin 7) ≠ 3)
  have d14 : v1 ≠ v4 := hlabi.ne (by decide : (1 : Fin 7) ≠ 4)
  have d15 : v1 ≠ v5 := hlabi.ne (by decide : (1 : Fin 7) ≠ 5)
  have d16 : v1 ≠ v6 := hlabi.ne (by decide : (1 : Fin 7) ≠ 6)
  have d20 : v2 ≠ v0 := hlabi.ne (by decide : (2 : Fin 7) ≠ 0)
  have d21 : v2 ≠ v1 := hlabi.ne (by decide : (2 : Fin 7) ≠ 1)
  have d23 : v2 ≠ v3 := hlabi.ne (by decide : (2 : Fin 7) ≠ 3)
  have d24 : v2 ≠ v4 := hlabi.ne (by decide : (2 : Fin 7) ≠ 4)
  have d25 : v2 ≠ v5 := hlabi.ne (by decide : (2 : Fin 7) ≠ 5)
  have d26 : v2 ≠ v6 := hlabi.ne (by decide : (2 : Fin 7) ≠ 6)
  have d30 : v3 ≠ v0 := hlabi.ne (by decide : (3 : Fin 7) ≠ 0)
  have d31 : v3 ≠ v1 := hlabi.ne (by decide : (3 : Fin 7) ≠ 1)
  have d32 : v3 ≠ v2 := hlabi.ne (by decide : (3 : Fin 7) ≠ 2)
  have d34 : v3 ≠ v4 := hlabi.ne (by decide : (3 : Fin 7) ≠ 4)
  have d35 : v3 ≠ v5 := hlabi.ne (by decide : (3 : Fin 7) ≠ 5)
  have d36 : v3 ≠ v6 := hlabi.ne (by decide : (3 : Fin 7) ≠ 6)
  have d40 : v4 ≠ v0 := hlabi.ne (by decide : (4 : Fin 7) ≠ 0)
  have d41 : v4 ≠ v1 := hlabi.ne (by decide : (4 : Fin 7) ≠ 1)
  have d42 : v4 ≠ v2 := hlabi.ne (by decide : (4 : Fin 7) ≠ 2)
  have d43 : v4 ≠ v3 := hlabi.ne (by decide : (4 : Fin 7) ≠ 3)
  have d45 : v4 ≠ v5 := hlabi.ne (by decide : (4 : Fin 7) ≠ 5)
  have d46 : v4 ≠ v6 := hlabi.ne (by decide : (4 : Fin 7) ≠ 6)
  have d50 : v5 ≠ v0 := hlabi.ne (by decide : (5 : Fin 7) ≠ 0)
  have d51 : v5 ≠ v1 := hlabi.ne (by decide : (5 : Fin 7) ≠ 1)
  have d52 : v5 ≠ v2 := hlabi.ne (by decide : (5 : Fin 7) ≠ 2)
  have d53 : v5 ≠ v3 := hlabi.ne (by decide : (5 : Fin 7) ≠ 3)
  have d54 : v5 ≠ v4 := hlabi.ne (by decide : (5 : Fin 7) ≠ 4)
  have d56 : v5 ≠ v6 := hlabi.ne (by decide : (5 : Fin 7) ≠ 6)
  have d60 : v6 ≠ v0 := hlabi.ne (by decide : (6 : Fin 7) ≠ 0)
  have d61 : v6 ≠ v1 := hlabi.ne (by decide : (6 : Fin 7) ≠ 1)
  have d62 : v6 ≠ v2 := hlabi.ne (by decide : (6 : Fin 7) ≠ 2)
  have d63 : v6 ≠ v3 := hlabi.ne (by decide : (6 : Fin 7) ≠ 3)
  have d64 : v6 ≠ v4 := hlabi.ne (by decide : (6 : Fin 7) ≠ 4)
  have d65 : v6 ≠ v5 := hlabi.ne (by decide : (6 : Fin 7) ≠ 5)
  have l0 : lab 0 = v0 := rfl
  have l1 : lab 1 = v1 := rfl
  have l2 : lab 2 = v2 := rfl
  have l3 : lab 3 = v3 := rfl
  have l4 : lab 4 = v4 := rfl
  have l5 : lab 5 = v5 := rfl
  have l6 : lab 6 = v6 := rfl
  have mem : ∀ k, x k ∈ Finset.univ.image e := fun k => Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have xne : ∀ k l : Fin 7, k ≠ l → x k ≠ x l := fun k l h => he.ne (hlabi.ne h)
  have pairne : ∀ a b c d : Fin 7, a ≠ c → a ≠ d → ({x a, x b} : Finset ℝ³) ≠ {x c, x d} := by
    intro a b c d hac had h
    have : x a ∈ ({x c, x d} : Finset ℝ³) := h ▸ (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h' | h'
    · exact xne _ _ hac h'
    · exact xne _ _ had h'
  refine isRupert_type02 x (xne 3 4 (by decide)) ⟨f1, ?_⟩ ⟨f2, ?_⟩ ⟨f3, ?_⟩ ⟨f4, ?_⟩ ?_ ?_ ?_ ?_
  · -- 0134: P1 = {v3, v0, v1, v4}
    refine ⟨(h1 _).1 (by rw [e1]; simp [l0, l1, l2, l3, l4, l5, l6]), (h1 _).1 (by rw [e1]; simp [l0, l1, l2, l3, l4, l5, l6]), (h1 _).1 (by rw [e1]; simp [l0, l1, l2, l3, l4, l5, l6]),
      (h1 _).1 (by rw [e1]; simp [l0, l1, l2, l3, l4, l5, l6]), (h1 _).2 (by rw [e1]; simp [l0, l1, l2, l3, l4, l5, l6, d01, d02, d03, d04, d05, d06, d10, d12, d13, d14, d15, d16, d20, d21, d23, d24, d25, d26, d30, d31, d32, d34, d35, d36, d40, d41, d42, d43, d45, d46, d50, d51, d52, d53, d54, d56, d60, d61, d62, d63, d64, d65]),
      (h1 _).2 (by rw [e1]; simp [l0, l1, l2, l3, l4, l5, l6, d01, d02, d03, d04, d05, d06, d10, d12, d13, d14, d15, d16, d20, d21, d23, d24, d25, d26, d30, d31, d32, d34, d35, d36, d40, d41, d42, d43, d45, d46, d50, d51, d52, d53, d54, d56, d60, d61, d62, d63, d64, d65]), (h1 _).2 (by rw [e1]; simp [l0, l1, l2, l3, l4, l5, l6, d01, d02, d03, d04, d05, d06, d10, d12, d13, d14, d15, d16, d20, d21, d23, d24, d25, d26, d30, d31, d32, d34, d35, d36, d40, d41, d42, d43, d45, d46, d50, d51, d52, d53, d54, d56, d60, d61, d62, d63, d64, d65])⟩
  · -- 3564: P2 = {v3, v5, v6, v4}
    refine ⟨(h2 _).1 (by rw [e2]; simp [l0, l1, l2, l3, l4, l5, l6]), (h2 _).1 (by rw [e2]; simp [l0, l1, l2, l3, l4, l5, l6]), (h2 _).1 (by rw [e2]; simp [l0, l1, l2, l3, l4, l5, l6]),
      (h2 _).1 (by rw [e2]; simp [l0, l1, l2, l3, l4, l5, l6]), (h2 _).2 (by rw [e2]; simp [l0, l1, l2, l3, l4, l5, l6, d01, d02, d03, d04, d05, d06, d10, d12, d13, d14, d15, d16, d20, d21, d23, d24, d25, d26, d30, d31, d32, d34, d35, d36, d40, d41, d42, d43, d45, d46, d50, d51, d52, d53, d54, d56, d60, d61, d62, d63, d64, d65]),
      (h2 _).2 (by rw [e2]; simp [l0, l1, l2, l3, l4, l5, l6, d01, d02, d03, d04, d05, d06, d10, d12, d13, d14, d15, d16, d20, d21, d23, d24, d25, d26, d30, d31, d32, d34, d35, d36, d40, d41, d42, d43, d45, d46, d50, d51, d52, d53, d54, d56, d60, d61, d62, d63, d64, d65]), (h2 _).2 (by rw [e2]; simp [l0, l1, l2, l3, l4, l5, l6, d01, d02, d03, d04, d05, d06, d10, d12, d13, d14, d15, d16, d20, d21, d23, d24, d25, d26, d30, d31, d32, d34, d35, d36, d40, d41, d42, d43, d45, d46, d50, d51, d52, d53, d54, d56, d60, d61, d62, d63, d64, d65])⟩
  · -- 3025: P3 = {v3, v0, v2, v5}
    refine ⟨(h3 _).1 (by rw [e3]; simp [l0, l1, l2, l3, l4, l5, l6]), (h3 _).1 (by rw [e3]; simp [l0, l1, l2, l3, l4, l5, l6]), (h3 _).1 (by rw [e3]; simp [l0, l1, l2, l3, l4, l5, l6]),
      (h3 _).1 (by rw [e3]; simp [l0, l1, l2, l3, l4, l5, l6]), (h3 _).2 (by rw [e3]; simp [l0, l1, l2, l3, l4, l5, l6, d01, d02, d03, d04, d05, d06, d10, d12, d13, d14, d15, d16, d20, d21, d23, d24, d25, d26, d30, d31, d32, d34, d35, d36, d40, d41, d42, d43, d45, d46, d50, d51, d52, d53, d54, d56, d60, d61, d62, d63, d64, d65]),
      (h3 _).2 (by rw [e3]; simp [l0, l1, l2, l3, l4, l5, l6, d01, d02, d03, d04, d05, d06, d10, d12, d13, d14, d15, d16, d20, d21, d23, d24, d25, d26, d30, d31, d32, d34, d35, d36, d40, d41, d42, d43, d45, d46, d50, d51, d52, d53, d54, d56, d60, d61, d62, d63, d64, d65]), (h3 _).2 (by rw [e3]; simp [l0, l1, l2, l3, l4, l5, l6, d01, d02, d03, d04, d05, d06, d10, d12, d13, d14, d15, d16, d20, d21, d23, d24, d25, d26, d30, d31, d32, d34, d35, d36, d40, d41, d42, d43, d45, d46, d50, d51, d52, d53, d54, d56, d60, d61, d62, d63, d64, d65])⟩
  · -- 4126: P4 = {v4, v1, v2, v6}
    refine ⟨(h4 _).1 (by rw [e4]; simp [l0, l1, l2, l3, l4, l5, l6]), (h4 _).1 (by rw [e4]; simp [l0, l1, l2, l3, l4, l5, l6]), (h4 _).1 (by rw [e4]; simp [l0, l1, l2, l3, l4, l5, l6]),
      (h4 _).1 (by rw [e4]; simp [l0, l1, l2, l3, l4, l5, l6]), (h4 _).2 (by rw [e4]; simp [l0, l1, l2, l3, l4, l5, l6, d01, d02, d03, d04, d05, d06, d10, d12, d13, d14, d15, d16, d20, d21, d23, d24, d25, d26, d30, d31, d32, d34, d35, d36, d40, d41, d42, d43, d45, d46, d50, d51, d52, d53, d54, d56, d60, d61, d62, d63, d64, d65]),
      (h4 _).2 (by rw [e4]; simp [l0, l1, l2, l3, l4, l5, l6, d01, d02, d03, d04, d05, d06, d10, d12, d13, d14, d15, d16, d20, d21, d23, d24, d25, d26, d30, d31, d32, d34, d35, d36, d40, d41, d42, d43, d45, d46, d50, d51, d52, d53, d54, d56, d60, d61, d62, d63, d64, d65]), (h4 _).2 (by rw [e4]; simp [l0, l1, l2, l3, l4, l5, l6, d01, d02, d03, d04, d05, d06, d10, d12, d13, d14, d15, d16, d20, d21, d23, d24, d25, d26, d30, d31, d32, d34, d35, d36, d40, d41, d42, d43, d45, d46, d50, d51, d52, d53, d54, d56, d60, d61, d62, d63, d64, d65])⟩
  · -- 2 is not in the hull of 0, 1, 5, 6
    intro hmem
    apply hext (lab 2)
    refine convexHull_mono ?_ hmem
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
    rcases hy with rfl | rfl | rfl | rfl
    · exact ⟨mem 0, xne 0 2 (by decide)⟩
    · exact ⟨mem 1, xne 1 2 (by decide)⟩
    · exact ⟨mem 5, xne 5 2 (by decide)⟩
    · exact ⟨mem 6, xne 6 2 (by decide)⟩
  · exact (hgen _ (mem 0) _ (mem 1) _ (mem 3) _ (mem 4) (xne 0 1 (by decide)) (xne 3 4 (by decide))
      (pairne 0 1 3 4 (by decide) (by decide))).1
  · exact (hgen _ (mem 5) _ (mem 6) _ (mem 3) _ (mem 4) (xne 5 6 (by decide)) (xne 3 4 (by decide))
      (pairne 5 6 3 4 (by decide) (by decide))).1
  · -- distinct depths along 34
    intro i j hij
    by_contra hne
    have h0 : ⟪x i - x j, x 4 - x 3⟫ = 0 := by
      simp only at hij; rw [inner_sub_left, hij, sub_self]
    have h34 : x 3 ≠ x 4 := xne 3 4 (by decide)
    by_cases hp : ({x j, x i} : Finset ℝ³) = {x 3, x 4}
    · have hi : x i ∈ ({x 3, x 4} : Finset ℝ³) := hp ▸ (by simp)
      have hj : x j ∈ ({x 3, x 4} : Finset ℝ³) := hp ▸ (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
      have hij' : x i ≠ x j := xne i j hne
      have hn : 0 < ⟪x 4 - x 3, x 4 - x 3⟫ := by
        rw [real_inner_self_eq_norm_sq]; exact pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr h34.symm)) 2
      rcases hi with hi | hi <;> rcases hj with hj | hj
      · exact hij' (hi.trans hj.symm)
      · rw [hi, hj] at h0
        have : ⟪x 3 - x 4, x 4 - x 3⟫ = -⟪x 4 - x 3, x 4 - x 3⟫ := by
          rw [← inner_neg_left, neg_sub]
        linarith
      · rw [hi, hj] at h0; linarith
      · exact hij' (hi.trans hj.symm)
    · exact (hgen _ (mem j) _ (mem i) _ (mem 3) _ (mem 4) (xne j i (Ne.symm hne))
        (xne 3 4 (by decide)) hp).2 h0

/-- **The side conditions from the facets.** For index sets of four facets of
seven extreme points (labelled by `e`), `QuadSidesOK` holds. -/
theorem quadSidesOK_of_facets (e : Fin 7 → ℝ³) (he : Function.Injective e)
    (hext : ∀ i, e i ∉ convexHull ℝ ((Finset.univ.image e).erase (e i) : Set ℝ³))
    {X Y Z W : Finset (Fin 7)} (hXc : X.card = 4) {fX fY fZ fW : ℝ³ →ᵃ[ℝ] ℝ}
    (hX : ∀ i, (i ∈ X → fX (e i) = 0) ∧ (i ∉ X → fX (e i) < 0))
    (hY : ∀ i, (i ∈ Y → fY (e i) = 0) ∧ (i ∉ Y → fY (e i) < 0))
    (hZ : ∀ i, (i ∈ Z → fZ (e i) = 0) ∧ (i ∉ Z → fZ (e i) < 0))
    (hW : ∀ i, (i ∈ W → fW (e i) = 0) ∧ (i ∉ W → fW (e i) < 0)) :
    QuadSidesOK X Y Z W := by
  rintro ⟨cY, cZ, cW, nYZ, nYW, nZW, hcase⟩
  -- a point off X, where fX ≠ 0
  obtain ⟨k, hk⟩ : ∃ k, k ∉ X := by
    by_contra h; push Not at h
    have : X = Finset.univ := Finset.eq_univ_of_forall h
    rw [this, Finset.card_univ, Fintype.card_fin] at hXc; omega
  have fz : fX (e k) ≠ 0 := ((hX k).2 hk).ne
  -- membership from `X ∩ S = {a, b}`
  have memI : ∀ {S : Finset (Fin 7)} {a b : Fin 7}, X ∩ S = {a, b} → (a ∈ X ∧ a ∈ S) ∧ (b ∈ X ∧ b ∈ S) := by
    intro S a b h
    have ha : a ∈ X ∩ S := h ▸ (by simp)
    have hb : b ∈ X ∩ S := h ▸ (by simp)
    exact ⟨Finset.mem_inter.mp ha, Finset.mem_inter.mp hb⟩
  have notI : ∀ {S : Finset (Fin 7)} {a b q : Fin 7}, X ∩ S = {a, b} → q ∈ X → q ≠ a → q ≠ b → q ∉ S := by
    intro S a b q h hq hqa hqb hqS
    have : q ∈ X ∩ S := Finset.mem_inter.mpr ⟨hq, hqS⟩
    rw [h] at this; simp at this; tauto
  have hcase' : (X ∩ Y ∩ (X ∩ Z) ∩ (X ∩ W)).Nonempty ∨ (X ∩ Y ∪ X ∩ Z ∪ X ∩ W).card = 3 := by
    rcases hcase with ⟨v, hv⟩ | h
    · left; exact ⟨v, by simp only [Finset.mem_inter] at hv ⊢; tauto⟩
    · exact Or.inr h
  rcases three_pairs_cases cY cZ cW nYZ nYW nZW hcase' with
    ⟨v, p, q, r, hnd, eY, eZ, eW⟩ | ⟨x, y, c, hnd, eY, eZ, eW⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or] at hnd
    obtain ⟨⟨hvp, hvq, hvr, -⟩, ⟨hpq, hpr, -⟩, ⟨hqr, -⟩, -, -⟩ := hnd
    obtain ⟨⟨vX, vY⟩, ⟨pX, pY⟩⟩ := memI eY
    obtain ⟨⟨-, vZ⟩, ⟨qX, qZ⟩⟩ := memI eZ
    obtain ⟨⟨-, vW⟩, ⟨rX, rW⟩⟩ := memI eW
    exact not_three_sides_at_vertex (z := e k) ((hX _).1 vX) ((hX _).1 pX) ((hX _).1 qX)
      ((hX _).1 rX) fz ((hY _).1 vY) ((hY _).1 pY)
      ((hY _).2 (notI eY qX (Ne.symm hvq) (Ne.symm hpq)))
      ((hY _).2 (notI eY rX (Ne.symm hvr) (Ne.symm hpr))) ((hZ _).1 vZ) ((hZ _).1 qZ)
      ((hZ _).2 (notI eZ pX (Ne.symm hvp) hpq)) ((hZ _).2 (notI eZ rX (Ne.symm hvr) (Ne.symm hqr)))
      ((hW _).1 vW) ((hW _).1 rW) ((hW _).2 (notI eW pX (Ne.symm hvp) hpr))
      ((hW _).2 (notI eW qX (Ne.symm hvq) hqr))
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or] at hnd
    obtain ⟨⟨hxy, hxc, -⟩, ⟨hyc, -⟩, -, -⟩ := hnd
    have hcx : c ≠ x := fun h => hxc h.symm
    have hcy : c ≠ y := fun h => hyc h.symm
    have hyx : y ≠ x := fun h => hxy h.symm
    obtain ⟨⟨xX, xY⟩, ⟨yX, yY⟩⟩ := memI eY
    obtain ⟨⟨cX, cZ'⟩, ⟨-, xZ⟩⟩ := memI eZ
    obtain ⟨⟨-, cW'⟩, ⟨-, yW⟩⟩ := memI eW
    -- the fourth point d of X
    obtain ⟨d, dX, hdx, hdy, hdc⟩ : ∃ d ∈ X, d ≠ x ∧ d ≠ y ∧ d ≠ c := by
      by_contra h; push Not at h
      have : X ⊆ {x, y, c} := fun d hd => by
        by_cases h1 : d = x; · simp [h1]
        by_cases h2 : d = y; · simp [h2]
        simp [h d hd h1 h2]
      have := Finset.card_le_card this
      rw [hXc] at this
      have := Finset.card_le_three (a := x) (b := y) (c := c); omega
    have hmem := mem_triangle_of_three_sides (z := e k) ((hX _).1 xX) ((hX _).1 yX) ((hX _).1 cX)
      ((hX _).1 dX) fz ((hY _).1 xY) ((hY _).1 yY) ((hY _).2 (notI eY cX hcx hcy))
      ((hY _).2 (notI eY dX hdx hdy)) ((hZ _).1 xZ) ((hZ _).1 cZ')
      ((hZ _).2 (notI eZ yX hyc hyx)) ((hZ _).2 (notI eZ dX hdc hdx))
      ((hW _).1 yW) ((hW _).1 cW') ((hW _).2 (notI eW xX hxc hxy))
      ((hW _).2 (notI eW dX hdc hdy))
    apply hext d
    refine convexHull_mono ?_ hmem
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff,
      Finset.mem_image, Finset.mem_univ, true_and]
    rcases hw with rfl | rfl | rfl
    · exact ⟨⟨x, rfl⟩, he.ne hdx.symm⟩
    · exact ⟨⟨y, rfl⟩, he.ne hdy.symm⟩
    · exact ⟨⟨c, rfl⟩, he.ne hdc.symm⟩

/-! ### Four quadrilateral facets -/

/-- An enumeration of seven points listing a given four of them first. -/
theorem exists_enum_four_first (V Q : Finset ℝ³) (hV : V.card = 7) (hQV : Q ⊆ V)
    (hQ : Q.card = 4) : ∃ e : Fin 7 → ℝ³, Function.Injective e ∧ Finset.univ.image e = V ∧
      ∀ i : Fin 7, e i ∈ Q ↔ i.val < 4 := by
  classical
  have h3 : (V \ Q).card = 3 := by rw [Finset.card_sdiff_of_subset hQV, hV, hQ]
  set a : Fin 4 → ℝ³ := fun i => ((Q.equivFinOfCardEq hQ).symm i : ℝ³) with ha
  set b : Fin 3 → ℝ³ := fun j => (((V \ Q).equivFinOfCardEq h3).symm j : ℝ³) with hb
  have aQ : ∀ i, a i ∈ Q := fun i => ((Q.equivFinOfCardEq hQ).symm i).2
  have bV : ∀ j, b j ∈ V \ Q := fun j => (((V \ Q).equivFinOfCardEq h3).symm j).2
  have ainj : Function.Injective a := fun i i' h =>
    (Q.equivFinOfCardEq hQ).symm.injective (Subtype.ext h)
  have binj : Function.Injective b := fun j j' h =>
    ((V \ Q).equivFinOfCardEq h3).symm.injective (Subtype.ext h)
  have split : ∀ x : Fin 7, (∃ i : Fin 4, x = Fin.castAdd 3 i) ∨ ∃ j : Fin 3, x = Fin.natAdd 4 j := by
    decide
  refine ⟨fun i => Fin.append a b i, ?_, ?_, ?_⟩
  · intro i i' h
    rcases split i with ⟨i, rfl⟩ | ⟨j, rfl⟩ <;> rcases split i' with ⟨i', rfl⟩ | ⟨j', rfl⟩
    · simp only [Fin.append_left] at h; rw [ainj h]
    · simp only [Fin.append_left, Fin.append_right] at h
      exact absurd (h ▸ aQ i) (Finset.mem_sdiff.mp (bV j')).2
    · simp only [Fin.append_left, Fin.append_right] at h
      exact absurd (h ▸ aQ i') (Finset.mem_sdiff.mp (bV j)).2
    · simp only [Fin.append_right] at h; rw [binj h]
  · ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      rcases split i with ⟨i, rfl⟩ | ⟨j, rfl⟩
      · simp only [Fin.append_left]; exact hQV (aQ i)
      · simp only [Fin.append_right]; exact (Finset.mem_sdiff.mp (bV j)).1
    · intro hy
      by_cases hyQ : y ∈ Q
      · refine ⟨Fin.castAdd 3 (Q.equivFinOfCardEq hQ ⟨y, hyQ⟩), ?_⟩
        simp only [Fin.append_left, ha, Equiv.symm_apply_apply]
      · refine ⟨Fin.natAdd 4 ((V \ Q).equivFinOfCardEq h3 ⟨y, Finset.mem_sdiff.mpr ⟨hy, hyQ⟩⟩), ?_⟩
        simp only [Fin.append_right, hb, Equiv.symm_apply_apply]
  · intro i
    rcases split i with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · simp only [Fin.append_left, Fin.val_castAdd]; exact ⟨fun _ => i.2, fun _ => aQ i⟩
    · simp only [Fin.append_right, Fin.val_natAdd]
      exact ⟨fun h => absurd h (Finset.mem_sdiff.mp (bV j)).2, fun h => by omega⟩

/-- **Four quadrilateral facets** (Theorem B, general position): seven extreme
points in general position with four distinct quadrilateral facets are Rupert. -/
theorem isRupert_of_four_quad_facets (V : Finset ℝ³) (hV : V.card = 7)
    (hext : ∀ y ∈ V, y ∉ convexHull ℝ ((V.erase y : Finset ℝ³) : Set ℝ³)) (hgen : GenPos V)
    (Q : Fin 4 → Finset ℝ³) (hQV : ∀ k, Q k ⊆ V) (hQc : ∀ k, (Q k).card = 4)
    (hQf : ∀ k, IsFacet V (Q k)) (hQi : Function.Injective Q) : IsRupert V := by
  classical
  obtain ⟨e, he, himg, hQ0⟩ := exists_enum_four_first V (Q 0) hV (hQV 0) (hQc 0)
  have heV : ∀ i, e i ∈ V := fun i => himg ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hext' : ∀ i, e i ∉ convexHull ℝ ((Finset.univ.image e).erase (e i) : Set ℝ³) := by
    rw [himg]; exact fun i => hext _ (heV i)
  have hgen' : GenPos (Finset.univ.image e) := himg ▸ hgen
  set I : Fin 4 → Finset (Fin 7) := fun k => Finset.univ.filter (fun i => e i ∈ Q k) with hIdef
  have memI : ∀ k i, i ∈ I k ↔ e i ∈ Q k := fun k i => by simp [hIdef]
  -- images under e
  have imgS : ∀ S : Finset ℝ³, S ⊆ V → (Finset.univ.filter (fun i => e i ∈ S)).image e = S := by
    intro S hS; ext y; simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hy
      have : y ∈ Finset.univ.image e := himg ▸ hS hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp this
      exact ⟨i, hy, rfl⟩
  have cardS : ∀ S : Finset ℝ³, S ⊆ V → (Finset.univ.filter (fun i => e i ∈ S)).card = S.card := by
    intro S hS; rw [← Finset.card_image_of_injective _ he, imgS S hS]
  have hIc : ∀ k, (I k).card = 4 := fun k => (cardS (Q k) (hQV k)).trans (hQc k)
  have hImem : ∀ k, I k ∈ (Finset.univ : Finset (Fin 7)).powersetCard 4 := fun k =>
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hIc k⟩
  have hQne : ∀ k, Q k ≠ V := fun k h => by have := hQc k; rw [h, hV] at this; omega
  have hle2 : ∀ j k, j ≠ k → (I j ∩ I k).card ≤ 2 := by
    intro j k hjk
    have e1 : I j ∩ I k = Finset.univ.filter (fun i => e i ∈ Q j ∩ Q k) := by
      ext i; simp [memI]
    rw [e1, cardS _ (Finset.inter_subset_left.trans (hQV j))]
    exact card_inter_le_two_of_facets hext (hQf j) (hQf k) (hQV j) (hQV k) (hQne j) (hQne k)
      (hQi.ne hjk)
  have hIne : ∀ j k, j ≠ k → I j ≠ I k := by
    intro j k hjk h
    apply hQi.ne hjk
    rw [← imgS (Q j) (hQV j), ← imgS (Q k) (hQV k)]
    exact congrArg (Finset.image e) h
  have hF : ∀ k, ∃ f : ℝ³ →ᵃ[ℝ] ℝ, ∀ i, (i ∈ I k → f (e i) = 0) ∧ (i ∉ I k → f (e i) < 0) := by
    intro k
    obtain ⟨f, h0, hn⟩ := hQf k
    exact ⟨f, fun i => ⟨fun h => h0 _ ((memI k i).mp h),
      fun h => hn _ (heV i) (fun h' => h ((memI k i).mpr h'))⟩⟩
  choose F hFk using hF
  have hI0 : I 0 = {0, 1, 2, 3} := by
    ext i; rw [memI, hQ0]; fin_cases i <;> simp
  have sides : ∀ a b c d : Fin 4, QuadSidesOK (I a) (I b) (I c) (I d) := fun a b c d =>
    quadSidesOK_of_facets e he hext' (hIc a) (hFk a) (hFk b) (hFk c) (hFk d)
  have s0 := sides 0 1 2 3
  have s1 := sides 1 0 2 3
  have s2 := sides 2 0 1 3
  have s3 := sides 3 0 1 2
  have l01 := hle2 0 1 (by decide)
  have l02 := hle2 0 2 (by decide)
  have l03 := hle2 0 3 (by decide)
  have F0 := hFk 0
  rw [hI0] at s0 s1 s2 s3 l01 l02 l03 F0
  have cls := quad_facets_classify (I 1) (hImem 1) l01 (I 2) (hImem 2) l02 (hle2 1 2 (by decide))
    (hIne 1 2 (by decide)) (I 3) (hImem 3) l03 (hle2 1 3 (by decide)) (hle2 2 3 (by decide))
    (hIne 1 3 (by decide)) (hIne 2 3 (by decide)) s0 s1 s2 s3
  rw [← himg]
  rcases cls with h | h | h | h | h | h
  · exact isRupert_of_type02Pattern e he hext' hgen' _ _ _ _ _ _ _ _ F0 (hFk 1) (hFk 2) (hFk 3) h
  · exact isRupert_of_type02Pattern e he hext' hgen' _ _ _ _ _ _ _ _ F0 (hFk 2) (hFk 1) (hFk 3) h
  · exact isRupert_of_type02Pattern e he hext' hgen' _ _ _ _ _ _ _ _ F0 (hFk 3) (hFk 1) (hFk 2) h
  · exact isRupert_of_type02Pattern e he hext' hgen' _ _ _ _ _ _ _ _ (hFk 1) (hFk 2) F0 (hFk 3) h
  · exact isRupert_of_type02Pattern e he hext' hgen' _ _ _ _ _ _ _ _ (hFk 1) (hFk 3) F0 (hFk 2) h
  · exact isRupert_of_type02Pattern e he hext' hgen' _ _ _ _ _ _ _ _ (hFk 2) (hFk 3) F0 (hFk 1) h

/-- `isRupert_of_four_quad_facets` for a solid hull, without assuming that all
seven points are extreme: if one is in the hull of the others, there are at most
six vertices. -/
theorem isRupert_of_four_quad_facets_solid (V : Finset ℝ³) (hV : V.card = 7)
    (hint : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty) (hgen : GenPos V)
    (Q : Fin 4 → Finset ℝ³) (hQV : ∀ k, Q k ⊆ V) (hQc : ∀ k, (Q k).card = 4)
    (hQf : ∀ k, IsFacet V (Q k)) (hQi : Function.Injective Q) : IsRupert V := by
  classical
  by_cases hext : ∃ x ∈ V, x ∈ convexHull ℝ ((V.erase x : Finset ℝ³) : Set ℝ³)
  · obtain ⟨x, hx, hxh⟩ := hext
    have hhull : convexHull ℝ ((V.erase x : Finset ℝ³) : Set ℝ³) = convexHull ℝ (V : Set ℝ³) := by
      apply le_antisymm (convexHull_mono (by simp))
      refine convexHull_min (fun y hy => ?_) (convex_convexHull ℝ _)
      by_cases hyx : y = x
      · rw [hyx]; exact hxh
      · exact subset_convexHull ℝ _ (by simpa [hyx] using hy)
    refine isRupert_of_convexHull_eq hhull (isRupert_of_card_le_six _ ?_ ?_)
    · rw [Finset.card_erase_of_mem hx]; omega
    · rw [hhull]; exact hint
  push Not at hext
  exact isRupert_of_four_quad_facets V hV hext hgen Q hQV hQc hQf hQi

end Minimality
