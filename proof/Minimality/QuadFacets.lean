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

end Minimality
