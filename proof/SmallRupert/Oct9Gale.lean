module

public import SmallRupert.Oct9Quad

@[expose] public section

/-!
# The Gale diagram of an octahedron, as dependencies (L9 §9.4)

Two affine dependencies `l`, `m` of the six vertices play the role of the
Gale vectors `g_t = (-m t, l t)`; `galeD l m s t = det (g_s, g_t)` up to sign.
Everything the proof of Theorem 9.9 needs from the Gale diagram follows by
applying dependencies to facet functions (pole coordinates, Lemma 9.6) and from
the three-term Plücker relation (a `ring` identity).
-/

namespace SmallRupert

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- `l` (a function on the vertices) is an affine dependency of the six points. -/
structure IsDep (a a' b b' c c' : ℝ³) (l : ℝ³ → ℝ) : Prop where
  sum : l a + l a' + l b + l b' + l c + l c' = 0
  vsum : l a • a + l a' • a' + l b • b + l b' • b' + l c • c + l c' • c' = 0

theorem IsDep.apply {a a' b b' c c' : ℝ³} {l : ℝ³ → ℝ} (h : IsDep a a' b b' c c' l)
    {f : ℝ³ → ℝ} {N : ℝ³} (hf : ∀ y z, f y - f z = ⟪N, y - z⟫) :
    l a * f a + l a' * f a' + l b * f b + l b' * f b' + l c * f c + l c' * f c' = 0 := by
  have e : ∀ t, f t = f a + ⟪N, t - a⟫ := fun t => by rw [← hf]; ring
  have hv := congrArg (fun v => ⟪N, v⟫) h.vsum
  simp only [inner_add_right, real_inner_smul_right, inner_zero_right] at hv
  rw [e a', e b, e b', e c, e c']
  simp only [inner_sub_right]
  have hs := h.sum
  linear_combination hv + (f a - ⟪N, a⟫) * hs

theorem IsDep.comb {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ} (hl : IsDep a a' b b' c c' l)
    (hm : IsDep a a' b b' c c' m) (α β : ℝ) :
    IsDep a a' b b' c c' (fun t => α * l t + β * m t) := by
  constructor
  · linear_combination α * hl.sum + β * hm.sum
  · have h1 := hl.vsum; have h2 := hm.vsum
    calc _ = α • (l a • a + l a' • a' + l b • b + l b' • b' + l c • c + l c' • c') +
          β • (m a • a + m a' • a' + m b • b + m b' • b' + m c • c + m c' • c') := by
            simp only [add_smul, smul_add, smul_smul]; abel
      _ = 0 := by rw [h1, h2, smul_zero, smul_zero, add_zero]

theorem IsDep.swap₁ {a a' b b' c c' : ℝ³} {l : ℝ³ → ℝ} (h : IsDep a a' b b' c c' l) :
    IsDep a' a b b' c c' l :=
  ⟨by linarith [h.sum], by rw [← h.vsum]; abel⟩

theorem IsDep.swap₂ {a a' b b' c c' : ℝ³} {l : ℝ³ → ℝ} (h : IsDep a a' b b' c c' l) :
    IsDep a a' b' b c c' l :=
  ⟨by linarith [h.sum], by rw [← h.vsum]; abel⟩

theorem IsDep.swap₃ {a a' b b' c c' : ℝ³} {l : ℝ³ → ℝ} (h : IsDep a a' b b' c c' l) :
    IsDep a a' b b' c' c l :=
  ⟨by linarith [h.sum], by rw [← h.vsum]; abel⟩

theorem IsDep.perm₁₂ {a a' b b' c c' : ℝ³} {l : ℝ³ → ℝ} (h : IsDep a a' b b' c c' l) :
    IsDep b b' a a' c c' l :=
  ⟨by linarith [h.sum], by rw [← h.vsum]; abel⟩

theorem IsDep.perm₂₃ {a a' b b' c c' : ℝ³} {l : ℝ³ → ℝ} (h : IsDep a a' b b' c c' l) :
    IsDep a a' c c' b b' l :=
  ⟨by linarith [h.sum], by rw [← h.vsum]; abel⟩

/-- `det (g_s, g_t)` for the Gale vectors of the dependencies `l`, `m`. -/
def galeD (l m : ℝ³ → ℝ) (s t : ℝ³) : ℝ := l s * m t - m s * l t

theorem galeD_self (l m : ℝ³ → ℝ) (s : ℝ³) : galeD l m s s = 0 := by simp [galeD]; ring

theorem galeD_anti (l m : ℝ³ → ℝ) (s t : ℝ³) : galeD l m t s = -galeD l m s t := by
  simp [galeD]; ring

theorem galeD_plucker (l m : ℝ³ → ℝ) (a b c d : ℝ³) :
    galeD l m a b * galeD l m c d - galeD l m a c * galeD l m b d +
      galeD l m a d * galeD l m b c = 0 := by
  simp only [galeD]; ring

/-- The dependency `t ↦ det (g_s, g_t)` vanishing at `s`. -/
theorem IsDep.galeD {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ} (hl : IsDep a a' b b' c c' l)
    (hm : IsDep a a' b b' c c' m) (s : ℝ³) : IsDep a a' b b' c c' (galeD l m s) := by
  have := hl.comb hm (-m s) (l s)
  convert this using 2 with t; simp only [SmallRupert.galeD]; ring

/-- Two terms of a dependency applied to a facet. -/
theorem pair_sign {L₁ L₂ f₁ f₂ : ℝ} (h : L₁ * f₁ + L₂ * f₂ = 0) (h₁ : f₁ < 0) (h₂ : f₂ < 0) :
    L₁ * L₂ ≤ 0 ∧ (L₁ = 0 ↔ L₂ = 0) := by
  constructor
  · by_contra hc; push Not at hc
    rcases lt_or_gt_of_ne (show L₁ ≠ 0 by rintro rfl; simp at hc) with hl | hl
    · have : L₂ < 0 := by nlinarith
      nlinarith [mul_pos_of_neg_of_neg hl h₁, mul_pos_of_neg_of_neg this h₂]
    · have : 0 < L₂ := by nlinarith
      nlinarith [mul_neg_of_pos_of_neg hl h₁, mul_neg_of_pos_of_neg this h₂]
  · constructor
    · rintro rfl; simp at h; rcases h with h | h; exact h; linarith
    · rintro rfl; simp at h; rcases h with h | h; exact h; linarith

/-- **Pole coordinates (i).**  A dependency vanishing at `t` and not at `t'`
has, on the equator of the axis `t t'`, one strict sign on each diagonal and
opposite signs on the two diagonals. -/
theorem pole_signs {t t' e e' g g' : ℝ³} (F : OctFacets t t' e e' g g') {L : ℝ³ → ℝ}
    (hL : IsDep t t' e e' g g' L) (h0 : L t = 0) (hκ : L t' ≠ 0) :
    0 < L e * L e' ∧ 0 < L g * L g' ∧ L e * L g < 0 := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨htt, hte, hte', htg, htg'⟩, ⟨ht'e, ht'e', ht'g, ht'g'⟩, ⟨hee', heg, heg'⟩,
    ⟨he'g, he'g'⟩, hgg', -⟩ := hnd
  have r1 := hL.apply F.a'bc.hN
  rw [F.a'bc.hP, F.a'bc.hQ, F.a'bc.hR, h0] at r1
  have r2 := hL.apply F.a'bc'.hN
  rw [F.a'bc'.hP, F.a'bc'.hQ, F.a'bc'.hR, h0] at r2
  have r3 := hL.apply F.a'b'c.hN
  rw [F.a'b'c.hP, F.a'b'c.hQ, F.a'b'c.hR, h0] at r3
  have r4 := hL.apply F.a'b'c'.hN
  rw [F.a'b'c'.hP, F.a'b'c'.hQ, F.a'b'c'.hR, h0] at r4
  have n1e' := F.a'bc.neg e' (by simp) (Ne.symm ht'e') (Ne.symm hee') he'g
  have n1g' := F.a'bc.neg g' (by simp) (Ne.symm ht'g') (Ne.symm heg') (Ne.symm hgg')
  have n2e' := F.a'bc'.neg e' (by simp) (Ne.symm ht'e') (Ne.symm hee') he'g'
  have n2g := F.a'bc'.neg g (by simp) (Ne.symm ht'g) (Ne.symm heg) hgg'
  have n3e := F.a'b'c.neg e (by simp) (Ne.symm ht'e) hee' heg
  have n3g' := F.a'b'c.neg g' (by simp) (Ne.symm ht'g') (Ne.symm he'g') (Ne.symm hgg')
  have n4e := F.a'b'c'.neg e (by simp) (Ne.symm ht'e) hee' heg'
  have n4g := F.a'b'c'.neg g (by simp) (Ne.symm ht'g) (Ne.symm he'g) hgg'
  obtain ⟨s1, z1⟩ := pair_sign (L₁ := L e') (L₂ := L g') (by linarith) n1e' n1g'
  obtain ⟨s2, z2⟩ := pair_sign (L₁ := L e') (L₂ := L g) (by linarith) n2e' n2g
  obtain ⟨s3, z3⟩ := pair_sign (L₁ := L e) (L₂ := L g') (by linarith) n3e n3g'
  obtain ⟨s4, z4⟩ := pair_sign (L₁ := L e) (L₂ := L g) (by linarith) n4e n4g
  have hs := hL.sum
  rw [h0] at hs
  have he' : L e' ≠ 0 := by
    intro h'
    have a1 := z1.mp h'; have a2 := z2.mp h'; have a4 := z4.mpr a2
    apply hκ; linarith
  have hg' : L g' ≠ 0 := fun h' => he' (z1.mpr h')
  have hg : L g ≠ 0 := fun h' => he' (z2.mpr h')
  have he : L e ≠ 0 := fun h' => hg (z4.mp h')
  have q1 : L e' * L g' < 0 := lt_of_le_of_ne s1 (mul_ne_zero he' hg')
  have q2 : L e' * L g < 0 := lt_of_le_of_ne s2 (mul_ne_zero he' hg)
  have q3 : L e * L g' < 0 := lt_of_le_of_ne s3 (mul_ne_zero he hg')
  have q4 : L e * L g < 0 := lt_of_le_of_ne s4 (mul_ne_zero he hg)
  refine ⟨?_, ?_, q4⟩
  · have := mul_pos_of_neg_of_neg q4 q2
    have hgg : 0 < L g * L g := mul_self_pos.mpr hg
    nlinarith
  · have := mul_pos_of_neg_of_neg q4 q3
    have hee : 0 < L e * L e := mul_self_pos.mpr he
    nlinarith

end SmallRupert

end
