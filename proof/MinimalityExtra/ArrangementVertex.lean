module

public import Mathlib
public import MinimalityExtra

@[expose] public section

namespace MinimalityExtra

open scoped Matrix

private lemma dsp {v : Fin 3 → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v := by
  by_contra h
  push Not at h
  apply hv
  refine dotProduct_self_eq_zero.mp (le_antisymm h ?_)
  simp only [dotProduct, Fin.sum_univ_three]
  nlinarith [mul_self_nonneg (v 0), mul_self_nonneg (v 1), mul_self_nonneg (v 2)]

/-- Moving from a point of the closed cone along a direction that decreases some form:
stop at the first new vanishing form. -/
private lemma step {n : ℕ} (l : Fin n → Fin 3 → ℝ) (u w : Fin 3 → ℝ)
    (hu : ∀ k, 0 ≤ l k ⬝ᵥ u) (hw : ∃ k, l k ⬝ᵥ w < 0) :
    ∃ t : ℝ, 0 ≤ t ∧ (∀ k, 0 ≤ l k ⬝ᵥ (u + t • w)) ∧
      ∃ k, l k ⬝ᵥ w < 0 ∧ l k ⬝ᵥ (u + t • w) = 0 := by
  classical
  obtain ⟨k₁, hk₁⟩ := hw
  set S := Finset.univ.filter (fun k => l k ⬝ᵥ w < 0) with hS
  have hne : S.Nonempty := ⟨k₁, by simp [hS, hk₁]⟩
  obtain ⟨k₀, hk₀S, hmin⟩ := Finset.exists_min_image S
    (fun k => (l k ⬝ᵥ u) / (-(l k ⬝ᵥ w))) hne
  have hk₀ : l k₀ ⬝ᵥ w < 0 := by simpa [hS] using hk₀S
  set t := (l k₀ ⬝ᵥ u) / (-(l k₀ ⬝ᵥ w)) with ht
  have hnegpos : 0 < -(l k₀ ⬝ᵥ w) := by linarith
  have ht0 : 0 ≤ t := div_nonneg (hu k₀) hnegpos.le
  refine ⟨t, ht0, ?_, k₀, hk₀, ?_⟩
  · intro k
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    by_cases hk : l k ⬝ᵥ w < 0
    · have hkS : k ∈ S := by simp [hS, hk]
      have h1 := hmin k hkS
      have hkp : 0 < -(l k ⬝ᵥ w) := by linarith
      rw [le_div_iff₀ hkp] at h1
      nlinarith
    · push Not at hk
      have := hu k
      nlinarith
  · have h := div_mul_cancel₀ (l k₀ ⬝ᵥ u) hnegpos.ne'
    rw [← ht] at h
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    linarith [h, mul_neg t (l k₀ ⬝ᵥ w)]

/-- For independent `a, b` there is `w` with `a ⬝ w = 1`, `b ⬝ w = 0`. -/
private lemma preimage {a b : Fin 3 → ℝ} (h : LinearIndependent ℝ ![a, b]) :
    ∃ w, a ⬝ᵥ w = 1 ∧ b ⬝ᵥ w = 0 := by
  have hc : crossProduct a b ≠ 0 := crossProduct_ne_zero_iff_linearIndependent.mpr h
  have hN := dsp hc
  refine ⟨(1 / ((crossProduct a b) ⬝ᵥ (crossProduct a b))) • crossProduct b (crossProduct a b),
    ?_, ?_⟩
  · rw [dotProduct_smul, smul_eq_mul]
    have key : a ⬝ᵥ crossProduct b (crossProduct a b)
        = (crossProduct a b) ⬝ᵥ (crossProduct a b) := by
      simp only [dotProduct, Fin.sum_univ_three, cross_apply, Matrix.cons_val]
      ring
    rw [key]; field_simp
  · rw [dotProduct_smul, dot_self_cross, smul_zero]

private lemma pair_indep {a b w : Fin 3 → ℝ} (ha : a ≠ 0) (haw : a ⬝ᵥ w = 0)
    (hbw : b ⬝ᵥ w ≠ 0) : LinearIndependent ℝ ![a, b] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 : (s • a + t • b) ⬝ᵥ w = 0 := by rw [hst]; simp
  rw [add_dotProduct, smul_dotProduct, smul_dotProduct, haw, smul_eq_mul, smul_eq_mul] at h1
  have ht : t = 0 := by
    have : t * (b ⬝ᵥ w) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right hbw
  subst ht
  simp only [zero_smul, add_zero] at hst
  exact ⟨(smul_eq_zero.mp hst).resolve_right ha, rfl⟩

theorem arrangementVerticesSuffice : ArrangementVerticesSuffice := by
  intro n l ⟨i, j, hij⟩ ⟨d, hd⟩
  obtain ⟨w₁, hw₁i, hw₁j⟩ := preimage hij
  -- round 1: from d along -w₁
  obtain ⟨t₁, ht₁, hC₁, k₁, hk₁, hk₁z⟩ :=
    step l d (-w₁) (fun k => (hd k).le) ⟨i, by rw [dotProduct_neg, hw₁i]; norm_num⟩
  set u₁ := d + t₁ • (-w₁) with hu₁
  have hjd := hd j
  have hu₁ne : u₁ ≠ 0 := by
    intro h
    have : l j ⬝ᵥ u₁ = 0 := by rw [h]; simp
    rw [hu₁, dotProduct_add, dotProduct_smul, dotProduct_neg, hw₁j] at this
    simp at this; linarith
  have hl₁ne : l k₁ ≠ 0 := by
    intro h; have := hd k₁; rw [h] at this; simp at this
  -- round 2: along w₂ = l k₁ × u₁
  set w₂ := crossProduct (l k₁) u₁ with hw₂
  have hw₂ne : w₂ ≠ 0 := by
    intro h
    have h0 : crossProduct (l k₁) u₁ ⬝ᵥ crossProduct (l k₁) u₁ = 0 := by rw [← hw₂, h]; simp
    rw [cross_dot_cross, hk₁z, dotProduct_comm u₁ (l k₁), hk₁z] at h0
    have := dsp hl₁ne; have := dsp hu₁ne
    nlinarith
  have h2k₁ : l k₁ ⬝ᵥ w₂ = 0 := by rw [hw₂]; exact dot_self_cross _ _
  have h2u₁ : u₁ ⬝ᵥ w₂ = 0 := by
    rw [hw₂, ← triple_product_permutation, dot_self_cross]
  by_cases hall : ∀ m, l m ⬝ᵥ w₂ = 0
  · refine ⟨w₂, i, j, d, hw₂ne, hij, hall i, hall j, fun k => Or.inr ⟨hall k, hd k⟩⟩
  · push Not at hall
    obtain ⟨m, hm⟩ := hall
    -- choose the sign
    obtain ⟨w, hwm, hwk₁, hwu⟩ : ∃ w : Fin 3 → ℝ, (∃ m, l m ⬝ᵥ w < 0) ∧ l k₁ ⬝ᵥ w = 0 ∧
        u₁ ⬝ᵥ w = 0 := by
      rcases lt_or_gt_of_ne hm with h | h
      · exact ⟨w₂, ⟨m, h⟩, h2k₁, h2u₁⟩
      · refine ⟨-w₂, ⟨m, ?_⟩, ?_, ?_⟩
        · rw [dotProduct_neg]; linarith
        · rw [dotProduct_neg, h2k₁, neg_zero]
        · rw [dotProduct_neg, h2u₁, neg_zero]
    obtain ⟨t₂, ht₂, hC₂, k₂, hk₂, hk₂z⟩ := step l u₁ w hC₁ hwm
    set u₂ := u₁ + t₂ • w with hu₂
    have hu₂ne : u₂ ≠ 0 := by
      intro h
      have h0 : u₁ ⬝ᵥ u₂ = 0 := by rw [h]; simp
      rw [hu₂, dotProduct_add, dotProduct_smul, hwu, smul_eq_mul, mul_zero, add_zero] at h0
      have h2 := dsp hu₁ne
      linarith
    have hk₁z₂ : l k₁ ⬝ᵥ u₂ = 0 := by
      rw [hu₂, dotProduct_add, dotProduct_smul, hwk₁, hk₁z]; simp
    refine ⟨u₂, k₁, k₂, d, hu₂ne, pair_indep hl₁ne hwk₁ hk₂.ne, hk₁z₂, hk₂z, ?_⟩
    intro k
    rcases (hC₂ k).lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.symm, hd k⟩



private lemma exists_pair_of_span {n : ℕ} (l : Fin n → Fin 3 → ℝ)
    (h : Submodule.span ℝ (Set.range l) = ⊤) : ∃ i j, LinearIndependent ℝ ![l i, l j] := by
  by_contra hno
  push Not at hno
  by_cases hz : ∀ i, l i = 0
  · have : Submodule.span ℝ (Set.range l) ≤ ⊥ := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      simp [hz i]
    rw [h] at this
    exact absurd (top_le_iff.mp this) (bot_ne_top : (⊥ : Submodule ℝ (Fin 3 → ℝ)) ≠ ⊤)
  · push Not at hz
    obtain ⟨i₀, hi₀⟩ := hz
    have hle : Submodule.span ℝ (Set.range l) ≤ ℝ ∙ l i₀ := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      have h1 := hno i₀ k
      rw [LinearIndependent.pair_iff' hi₀] at h1
      push Not at h1
      obtain ⟨a, ha⟩ := h1
      rw [← ha]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    rw [h] at hle
    have h2 : ℝ ∙ l i₀ = ⊤ := top_le_iff.mp hle
    have h3 := finrank_span_singleton (K := ℝ) hi₀
    rw [h2, finrank_top, Module.finrank_fin_fun] at h3
    omega

theorem arrangementVerticesSufficeSpan : ArrangementVerticesSufficeSpan := by
  intro n l hspan hd
  exact arrangementVerticesSuffice n l (exists_pair_of_span l hspan) hd

private lemma eps_exists (n : ℕ) (l : Fin n → Fin 3 → ℝ) (u₀ d : Fin 3 → ℝ)
    (h : ∀ k, 0 < l k ⬝ᵥ u₀ ∨ (l k ⬝ᵥ u₀ = 0 ∧ 0 < l k ⬝ᵥ d)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ k, 0 < l k ⬝ᵥ (u₀ + ε • d) := by
  have hk : ∀ k, ∃ e : ℝ, 0 < e ∧ ∀ ε : ℝ, 0 < ε → ε < e → 0 < l k ⬝ᵥ (u₀ + ε • d) := by
    intro k
    rcases h k with hp | ⟨hz, hd⟩
    · refine ⟨(l k ⬝ᵥ u₀) / (|l k ⬝ᵥ d| + 1), by positivity, ?_⟩
      intro ε hε hlt
      rw [lt_div_iff₀ (by positivity)] at hlt
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
      nlinarith [neg_abs_le (l k ⬝ᵥ d), abs_nonneg (l k ⬝ᵥ d), mul_le_mul_of_nonneg_left
        (neg_abs_le (l k ⬝ᵥ d)) hε.le]
    · refine ⟨1, one_pos, ?_⟩
      intro ε hε _
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul, hz]
      positivity
  choose e he0 he using hk
  by_cases hn : Nonempty (Fin n)
  · obtain ⟨k₀, -, hmin⟩ := Finset.exists_min_image Finset.univ e
      (Finset.univ_nonempty_iff.mpr hn)
    exact ⟨e k₀, he0 k₀, fun ε hε hlt k =>
      he k ε hε (lt_of_lt_of_le hlt (hmin k (Finset.mem_univ k)))⟩
  · refine ⟨1, one_pos, fun ε _ _ k => ?_⟩
    exact absurd ⟨k⟩ hn

theorem arrangementVerticesSufficeLex : ArrangementVerticesSufficeLex := by
  intro n l hpair hd
  obtain ⟨u₀, i, j, d, h1, h2, h3, h4, h5⟩ := arrangementVerticesSuffice n l hpair hd
  exact ⟨u₀, i, j, d, h1, h2, h3, h4, eps_exists n l u₀ d h5⟩

private lemma no_pair_fin_one (l : Fin 1 → Fin 3 → ℝ) :
    ¬ ∃ i j, LinearIndependent ℝ ![l i, l j] := by
  rintro ⟨i, j, h⟩
  have hij : i = j := Subsingleton.elim i j
  subst hij
  have := h.injective (a₁ := 0) (a₂ := 1) (by simp)
  exact zero_ne_one this

theorem chamberNeedsRank : ChamberNeedsRank := by
  refine ⟨1, fun _ => ![1, 0, 0], Nat.one_pos, ⟨![1, 0, 0], fun k => ?_⟩, no_pair_fin_one _⟩
  simp [dotProduct, Fin.sum_univ_three]

end MinimalityExtra

#print axioms MinimalityExtra.arrangementVerticesSuffice
#print axioms MinimalityExtra.arrangementVerticesSufficeSpan
#print axioms MinimalityExtra.arrangementVerticesSufficeLex
#print axioms MinimalityExtra.chamberNeedsRank
