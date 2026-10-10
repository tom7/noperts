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

theorem finset_perm_bac {a a' b b' c c' : ℝ³} :
    ({b, b', a, a', c, c'} : Finset ℝ³) = {a, a', b, b', c, c'} := by
  ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

theorem finset_perm_cba {a a' b b' c c' : ℝ³} :
    ({c, c', b, b', a, a'} : Finset ℝ³) = {a, a', b, b', c, c'} := by
  ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

/-- **The pair `W = C` in the parallel case** (`U = A`): the weak edges
`b → a` and `a' → b'` give a passage, or one of the lateral edges `c a'`,
`b c'` is orthogonal to the bottom, resp. top, face. -/
theorem isRupert_pair_f0 {a a' b b' c c' : ℝ³} (h : IsOctahedron a a' b b' c c')
    (G : GaleData a a' b b' c c') (hκa : 0 < galeD G.l G.m a a')
    (hκb : 0 < galeD G.l G.m b b') (hκc : 0 < galeD G.l G.m c c')
    (hf : G.l a + G.l b + G.l c = 0 ∧ G.m a + G.m b + G.m c = 0)
    (hU : 0 < galeD G.l G.m c a) :
    IsRupert {a, a', b, b', c, c'} ∨ (⟪c - a', a - b⟫ = 0 ∧ ⟪c - a', c - a⟫ = 0) ∨
      (⟪c' - b, b' - a'⟫ = 0 ∧ ⟪c' - b, c' - b'⟫ = 0) := by
  obtain ⟨F⟩ := h.nonempty_octFacets
  have hl := G.hl; have hm := G.hm
  have anti := galeD_anti G.l G.m
  have self := galeD_self G.l G.m
  -- pole signs at `c`, `c'`, `a`, `b'`, `b`
  obtain ⟨c1, c2, c3⟩ := pole_signs F.perm₂₃.perm₁₂ (hl.galeD hm c).perm₂₃.perm₁₂
    (self c) hκc.ne'
  obtain ⟨d1, d2, d3⟩ := pole_signs F.perm₂₃.perm₁₂.swap₁ (hl.galeD hm c').perm₂₃.perm₁₂.swap₁
    (self c') (by rw [anti]; linarith)
  obtain ⟨a1, a2, a3⟩ := pole_signs F (hl.galeD hm a) (self a) hκa.ne'
  obtain ⟨b1, b2, b3⟩ := pole_signs F.perm₁₂.swap₁ (hl.galeD hm b').perm₁₂.swap₁
    (self b') (by rw [anti]; linarith)
  obtain ⟨-, -, e3⟩ := pole_signs F.perm₁₂ (hl.galeD hm b).perm₁₂ (self b) hκb.ne'
  have hca' : 0 < galeD G.l G.m c a' := pos_of_mul_pos_pos c1 hU
  have hcb : galeD G.l G.m c b < 0 := neg_of_mul_neg_pos (by rwa [mul_comm] at c3) hU
  have hc'a : 0 < galeD G.l G.m c' a := by
    have e : galeD G.l G.m a c * galeD G.l G.m a c' = galeD G.l G.m c a * galeD G.l G.m c' a := by
      rw [anti c a, anti c' a]; ring
    exact pos_of_mul_pos_pos (e ▸ a2) hU
  have hc'b : galeD G.l G.m c' b < 0 := neg_of_mul_neg_pos (by rwa [mul_comm] at d3) hc'a
  have hac : galeD G.l G.m a c < 0 := by rw [anti]; linarith
  have hab : 0 < galeD G.l G.m a b := pos_of_mul_neg_neg (by linarith) hac
  have hab' : 0 < galeD G.l G.m a b' := pos_of_mul_pos_pos a1 hab
  have hb'c : 0 < galeD G.l G.m b' c := by
    rw [anti]; linarith [neg_of_mul_pos_neg (by linarith : 0 < galeD G.l G.m c b *
      galeD G.l G.m c b') hcb]
  have hb'a : galeD G.l G.m b' a < 0 := neg_of_mul_neg_pos b3 hb'c
  have hb'a' : galeD G.l G.m b' a' < 0 := neg_of_mul_pos_neg b1 hb'a
  have hb'c' : 0 < galeD G.l G.m b' c' := pos_of_mul_pos_pos b2 hb'c
  have hbc : galeD G.l G.m b c ≠ 0 := by
    intro h0; rw [h0, mul_zero] at e3; exact lt_irrefl _ e3
  -- `f = 0`
  have hF0 : ∀ t, galeD G.l G.m t a + galeD G.l G.m t b + galeD G.l G.m t c = 0 := by
    intro t; rw [← galeF_eq]; simp only [galeF]; rw [hf.1, hf.2]; ring
  have sc := galeD_sum hl hm c
  have hF0c := hF0 c
  have hF0c' := hF0 c'
  rw [self] at sc hF0c
  have hcc' := anti c c'
  have hfl' : G.l a' + G.l b' + G.l c' = 0 := by linarith [hl.sum, hf.1]
  have hfm' : G.m a' + G.m b' + G.m c' = 0 := by linarith [hm.sum, hf.2]
  have hb'c'0 : galeD G.l G.m b' c' ≠ 0 := hb'c'.ne'
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  have hnab : a ≠ b := hnd.1.2.1
  have hnab' : a' ≠ b' := hnd.2.1.2.1
  -- the edge `b → a` (poles `c`, `c'`; top face `b' a' c'`)
  have hq₁ := facet_lt_of_dep (hl.galeD hm c').perm₁₂ (F.perm₁₂).a'b'c (by simp) (by simp)
    (F.perm₁₂).nodup (self c') (mul_neg_of_neg_of_pos hc'b (by linarith))
  obtain ⟨T1, T2⟩ := facet_eq_of_f0 hl hm hf.1 hf.2 hbc (F.perm₁₂).a'b'c'.hN
    (F.perm₁₂).a'b'c'.hQ (F.perm₁₂).a'b'c'.hP (F.perm₁₂).a'b'c'.hR
  have hgood₁ := not_bad_of_dep (hl.galeD hm b').perm₁₂ (Ne.symm hnab) (self b')
    (by rw [anti]; linarith) (by rw [anti b b']; linarith) hb'a'.le hb'c.le hb'c'.le
  have r₁ := isRupert_weak_edge F.perm₁₂ hq₁ (by rw [T1, T2]) (by rw [T1]) hgood₁
  -- the edge `a' → b'` (poles `c'`, `c`; top face `a b c`)
  have hq₂ := facet_lt_of_dep (hl.galeD hm c).swap₁.swap₂.swap₃ (F.swap₁.swap₂.swap₃).a'b'c
    (by simp) (by simp) (F.swap₁.swap₂.swap₃).nodup (self c)
    (mul_neg_of_pos_of_neg hca' (by linarith))
  obtain ⟨B1, B2⟩ := facet_eq_of_f0 hl.swap₁.swap₂.swap₃ hm.swap₁.swap₂.swap₃ hfl' hfm'
    hb'c'0 (F.swap₁.swap₂.swap₃).a'b'c'.hN (F.swap₁.swap₂.swap₃).a'b'c'.hP
    (F.swap₁.swap₂.swap₃).a'b'c'.hQ (F.swap₁.swap₂.swap₃).a'b'c'.hR
  have hgood₂ := not_bad_of_dep (L := fun t => galeD G.l G.m t a)
    (hl.galeD' hm a).swap₁.swap₂.swap₃ hnab' (self a) (by rw [anti]; linarith)
    (by rw [anti a a', anti a b']; linarith) (by rw [anti]; linarith) hc'a.le hU.le
  have r₂ := isRupert_weak_edge F.swap₁.swap₂.swap₃ hq₂ (by rw [B1, B2]) (by rw [B2]) hgood₂
  rcases r₁ with r₁ | t₁ | l₁
  · left
    exact isRupert_congr_set r₁ finset_perm_bac
  · rcases r₂ with r₂ | t₂ | l₂
    · left; rwa [finset_perm_a'b'] at r₂
    · left
      have := isRupert_of_touching_pair h.perm₂₃.perm₁₂.perm₂₃
        (by rw [inner_sub_left]; linarith [t₁.1]) (by rw [inner_sub_left]; linarith [t₂.1])
      exact isRupert_congr_set this finset_perm_cba
    · right; right; exact l₂
  · right; left; exact l₁


/-- **Theorem 9.9, case `f = 0`** (§9.6). -/
theorem isRupert_octahedron_parallel {a a' b b' c c' : ℝ³} (h : IsOctahedron a a' b b' c c')
    (G : GaleData a a' b b' c c') (hκa : 0 < galeD G.l G.m a a')
    (hκb : 0 < galeD G.l G.m b b') (hκc : 0 < galeD G.l G.m c c')
    (hf : G.l a + G.l b + G.l c = 0 ∧ G.m a + G.m b + G.m c = 0) :
    IsRupert {a, a', b, b', c, c'} := by
  sorry

end SmallRupert

end
