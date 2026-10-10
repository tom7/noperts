module

public import SmallRupert.Oct9Weak

@[expose] public section

/-!
# Theorem 9.9, the parallel case `f = 0` (LEMMAS.md §9.6)

With normalized labels (`κ_A, κ_B, κ_C > 0`), `f = g_a + g_b + g_c = 0`
means that the opposite faces `abc` and `a'b'c'` are parallel.  Each pair `W`
gives two weak quad edges (Lemma 9.6 with `f = 0`) that are not bad (same
argument as §9.5).  By Lemma 9.11 (`isRupert_weak_edge`) each gives a passage
unless it is touching or its lateral edge is parallel to the common normal;
two touching edges give a passage by Lemma 9.4; and at most one edge of the
octahedron is parallel to the normal.
-/

namespace SmallRupert

open scoped RealInnerProductSpace Topology
open Finset Filter

theorem cross_cross_eq (a b n : ℝ³) : cross (cross a b) n = ⟪a, n⟫ • b - ⟪b, n⟫ • a := by
  ext i; fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, cross_apply_zero, cross_apply_one,
      cross_apply_two, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, PiLp.inner_apply,
      Fin.sum_univ_three, RCLike.inner_apply, conj_trivial] <;> ring

/-- A vector orthogonal to two independent vectors is a multiple of their cross
product. -/
theorem eq_smul_cross_of_perp {e₁ e₂ d : ℝ³} (hc : cross e₁ e₂ ≠ 0) (h1 : ⟪d, e₁⟫ = 0)
    (h2 : ⟪d, e₂⟫ = 0) : ∃ s : ℝ, d = s • cross e₁ e₂ := by
  refine ⟨_, eq_smul_of_cross_eq_zero hc ?_⟩
  rw [cross_cross_eq, real_inner_comm, h1, real_inner_comm, h2, zero_smul, zero_smul, sub_zero]

/-- Orthogonality to a plane, transferred through a parallel plane. -/
theorem perp_transfer {e₁ e₂ N d w : ℝ³} (hc : cross e₁ e₂ ≠ 0) (hN : N ≠ 0)
    (hN1 : ⟪N, e₁⟫ = 0) (hN2 : ⟪N, e₂⟫ = 0) (hd1 : ⟪d, e₁⟫ = 0) (hd2 : ⟪d, e₂⟫ = 0)
    (hw : ⟪N, w⟫ = 0) : ⟪d, w⟫ = 0 := by
  obtain ⟨s, hs⟩ := eq_smul_cross_of_perp hc hd1 hd2
  obtain ⟨t, ht⟩ := eq_smul_cross_of_perp hc hN1 hN2
  have ht0 : t ≠ 0 := by rintro rfl; rw [zero_smul] at ht; exact hN ht
  have : ⟪cross e₁ e₂, w⟫ = 0 := by
    rw [ht, real_inner_smul_left] at hw
    exact (mul_eq_zero.mp hw).resolve_left ht0
  rw [hs, real_inner_smul_left, this, mul_zero]

/-- Two disjoint edges parallel to one direction `n`, the first inside a facet
and the second from a vertex of that facet to a vertex beneath it: impossible. -/
theorem two_parallel_contra {f : ℝ³ → ℝ} {N : ℝ³} (hf : ∀ y z, f y - f z = ⟪N, y - z⟫)
    {A B Q S n : ℝ³} {s t : ℝ} (hA : f A = 0) (hB : f B = 0) (hQ : f Q = 0) (hS : f S < 0)
    (h1 : B - A = s • n) (hs : s ≠ 0) (h2 : S - Q = t • n) : False := by
  have e1 : ⟪N, n⟫ = 0 := by
    have := hf B A
    rw [hA, hB, h1, real_inner_smul_right, sub_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hs
  have := hf S Q
  rw [hQ, h2, real_inner_smul_right, e1, mul_zero, sub_zero] at this
  linarith

/-- **`f = 0` makes the faces `abc` and `a'b'c'` parallel**: every affine
function vanishing on `a', b', c'` is constant on `a, b, c`. -/
theorem facet_eq_of_f0 {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ} (hl : IsDep a a' b b' c c' l)
    (hm : IsDep a a' b b' c c' m) (hfl : l a + l b + l c = 0) (hfm : m a + m b + m c = 0)
    (hbc : galeD l m b c ≠ 0) {f : ℝ³ → ℝ} {N : ℝ³} (hf : ∀ y z, f y - f z = ⟪N, y - z⟫)
    (ha' : f a' = 0) (hb' : f b' = 0) (hc' : f c' = 0) : f a = f c ∧ f b = f c := by
  have r1 := hl.apply hf
  have r2 := hm.apply hf
  rw [ha', hb', hc'] at r1 r2
  simp only [galeD] at hbc
  have k1 : (l b * m c - m b * l c) * (f b - f a) = 0 := by
    have ea : l a = -(l b + l c) := by linarith
    have eb : m a = -(m b + m c) := by linarith
    rw [ea] at r1; rw [eb] at r2
    linear_combination m c * r1 - l c * r2
  have k2 : (l b * m c - m b * l c) * (f c - f a) = 0 := by
    have ea : l a = -(l b + l c) := by linarith
    have eb : m a = -(m b + m c) := by linarith
    rw [ea] at r1; rw [eb] at r2
    linear_combination -m b * r1 + l b * r2
  have z1 := (mul_eq_zero.mp k1).resolve_left hbc
  have z2 := (mul_eq_zero.mp k2).resolve_left hbc
  constructor <;> linarith

/-- **Theorem 9.9, case `f = 0`** (§9.6). -/
theorem isRupert_octahedron_parallel {a a' b b' c c' : ℝ³} (h : IsOctahedron a a' b b' c c')
    (G : GaleData a a' b b' c c') (hκa : 0 < galeD G.l G.m a a')
    (hκb : 0 < galeD G.l G.m b b') (hκc : 0 < galeD G.l G.m c c')
    (hf : G.l a + G.l b + G.l c = 0 ∧ G.m a + G.m b + G.m c = 0) :
    IsRupert {a, a', b, b', c, c'} := by
  sorry

end SmallRupert

end
