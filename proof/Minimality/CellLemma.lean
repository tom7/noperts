module

public import Mathlib

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Topology

namespace Minimality.CL

/-- Value of the `k`-th affine form `A k + t * B k`. -/
def fv {ι : Type*} (A B : ι → ℝ) (t : ℝ) : ι → ℝ := fun k => A k + t * B k

/-- Signs agree between `a ≤ b` when no root of a nonconstant form lies in `[a,b]`. -/
theorem sign_eq_of_no_root {ι : Type*} (A B : ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    (h : ∀ k, B k ≠ 0 → -A k / B k ∉ Set.Icc a b) (k : ι) :
    SignType.sign (fv A B a k) = SignType.sign (fv A B b k) := by
  by_cases hB : B k = 0
  · simp [fv, hB]
  have hne : ∀ s ∈ Set.Icc a b, A k + s * B k ≠ 0 := by
    intro s hs h0
    exact h k hB ⟨by rw [show -A k / B k = s by field_simp; linarith]; exact hs.1,
      by rw [show -A k / B k = s by field_simp; linarith]; exact hs.2⟩
  have key : ¬ (A k + a * B k) * (A k + b * B k) < 0 := by
    intro hlt
    set x := A k + a * B k
    set y := A k + b * B k
    have hxy : x - y ≠ 0 := by intro h0; rw [sub_eq_zero] at h0; rw [h0] at hlt; nlinarith
    have hba : (b - a) * B k = y - x := by simp only [x, y]; ring
    have hx : x ≠ 0 := by intro h0; rw [h0] at hlt; simp at hlt
    have hy : y ≠ 0 := by intro h0; rw [h0] at hlt; simp at hlt
    have hs0 : 0 ≤ x / (x - y) ∧ x / (x - y) ≤ 1 := by
      rcases lt_or_gt_of_ne hx with hx' | hx'
      · have : y > 0 := by nlinarith
        constructor
        · exact div_nonneg_of_nonpos hx'.le (by linarith)
        · rw [div_le_one_of_neg (by linarith)]; linarith
      · have : y < 0 := by nlinarith
        constructor
        · exact div_nonneg hx'.le (by linarith)
        · rw [div_le_one (by linarith)]; linarith
    apply hne (a + x / (x - y) * (b - a))
    · exact ⟨by nlinarith [hs0.1], by nlinarith [hs0.2]⟩
    · have : A k + (a + x / (x - y) * (b - a)) * B k = x + x / (x - y) * ((b - a) * B k) := by
        simp only [x]; ring
      rw [this, hba]; field_simp; ring
  simp only [fv]
  have hx : A k + a * B k ≠ 0 := hne a ⟨le_rfl, hab⟩
  have hy : A k + b * B k ≠ 0 := hne b ⟨hab, le_rfl⟩
  push Not at key
  rcases lt_or_gt_of_ne hx with h1 | h1
  · have : A k + b * B k < 0 := by
      rcases lt_or_gt_of_ne hy with h2 | h2
      · exact h2
      · nlinarith
    rw [sign_neg h1, sign_neg this]
  · have : 0 < A k + b * B k := by
      rcases lt_or_gt_of_ne hy with h2 | h2
      · nlinarith
      · exact h2
    rw [sign_pos h1, sign_pos this]

/-- **Lemma CL** (right form). `P` depends only on the signs of the forms; `t0` is not a root
of any form that is not identically zero. If `P` holds at `t0`, then `P` holds on a right
neighbourhood of a root of a nonconstant form, or for all sufficiently small `t`. -/
theorem cl_right {ι : Type*} [Fintype ι] (A B : ι → ℝ) (P : (ι → ℝ) → Prop)
    (hP : ∀ v w, (∀ k, SignType.sign (v k) = SignType.sign (w k)) → P v → P w)
    (t0 : ℝ) (hgen : ∀ k, (A k ≠ 0 ∨ B k ≠ 0) → A k + t0 * B k ≠ 0)
    (h0 : P (fv A B t0)) :
    (∃ k, B k ≠ 0 ∧ ∀ᶠ t in 𝓝[>] (-A k / B k), P (fv A B t)) ∨
      ∀ᶠ t in atBot, P (fv A B t) := by
  classical
  have hroot : ∀ k, B k ≠ 0 → -A k / B k ≠ t0 := by
    intro k hB he
    apply hgen k (Or.inr hB)
    rw [← he]; field_simp; ring
  set T : Finset ℝ := (Finset.univ.filter (fun k => B k ≠ 0 ∧ -A k / B k < t0)).image
    (fun k => -A k / B k) with hT
  by_cases hne : T.Nonempty
  · left
    obtain ⟨k, hk, hkr⟩ : ∃ k, B k ≠ 0 ∧ -A k / B k = T.max' hne := by
      have := T.max'_mem hne
      simp only [hT, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at this
      obtain ⟨k, ⟨hB, _⟩, hk⟩ := this
      exact ⟨k, hB, hk⟩
    have hlt : T.max' hne < t0 := by
      have := T.max'_mem hne
      simp only [hT, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at this
      obtain ⟨k', ⟨_, hl⟩, hk'⟩ := this
      rw [← hk']; exact hl
    refine ⟨k, hk, ?_⟩
    rw [hkr]
    filter_upwards [Ioo_mem_nhdsGT hlt] with t ht
    refine hP _ _ (fun j => ?_) h0
    symm
    apply sign_eq_of_no_root A B ht.2.le
    intro j hj ⟨h1, h2⟩
    rcases lt_or_gt_of_ne (hroot j hj) with hl | hl
    · have : -A j / B j ≤ T.max' hne := T.le_max' _ (by
        simp only [hT, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨j, ⟨hj, hl⟩, rfl⟩)
      linarith [ht.1]
    · linarith
  · right
    rw [Filter.eventually_atBot]
    refine ⟨t0, fun t ht => hP _ _ (fun j => ?_) h0⟩
    symm
    apply sign_eq_of_no_root A B ht
    intro j hj ⟨h1, h2⟩
    rcases lt_or_gt_of_ne (hroot j hj) with hl | hl
    · exact hne ⟨_, by
        simp only [hT, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨j, ⟨hj, hl⟩, rfl⟩⟩
    · linarith

/-- **Lemma CL** (left form, by `t ↦ -t`). -/
theorem cl_left {ι : Type*} [Fintype ι] (A B : ι → ℝ) (P : (ι → ℝ) → Prop)
    (hP : ∀ v w, (∀ k, SignType.sign (v k) = SignType.sign (w k)) → P v → P w)
    (t0 : ℝ) (hgen : ∀ k, (A k ≠ 0 ∨ B k ≠ 0) → A k + t0 * B k ≠ 0)
    (h0 : P (fv A B t0)) :
    (∃ k, B k ≠ 0 ∧ ∀ᶠ t in 𝓝[<] (-A k / B k), P (fv A B t)) ∨
      ∀ᶠ t in atTop, P (fv A B t) := by
  have hneg : ∀ t, fv A (fun k => - B k) (-t) = fv A B t := by
    intro t; ext k; simp [fv]
  rcases cl_right A (fun k => - B k) P hP (-t0)
    (fun k hk => by
      have := hgen k (hk.imp id neg_ne_zero.mp)
      simpa [mul_neg, neg_mul] using this)
    (by rw [hneg]; exact h0) with ⟨k, hk, hev⟩ | hev
  · left
    refine ⟨k, by simpa using hk, ?_⟩
    have hc : Tendsto (fun t : ℝ => -t) (𝓝[<] (-A k / B k)) (𝓝[>] (-A k / -B k)) := by
      have : -A k / -B k = -(-A k / B k) := by rw [div_neg, neg_div]
      rw [this]
      exact (continuous_neg.continuousWithinAt).tendsto_nhdsWithin
        (fun x hx => by simpa using hx)
    filter_upwards [hc.eventually hev] with t ht
    rwa [hneg t] at ht
  · right
    have hc : Tendsto (fun t : ℝ => -t) atTop atBot := tendsto_neg_atTop_atBot
    filter_upwards [hc.eventually hev] with t ht
    rw [← hneg t]; exact ht

/-- Trichotomy `wc_circle`: a predicate `Ok` on the circle that holds at every generic `t`
where `P` holds, and conversely from root/end data, gives
`(∃ t generic, P t) → CircleOK` where `CircleOK` is the disjunction over roots and ends. -/
theorem cl_circleOK {ι : Type*} [Fintype ι] (A B : ι → ℝ) (P : (ι → ℝ) → Prop)
    (hP : ∀ v w, (∀ k, SignType.sign (v k) = SignType.sign (w k)) → P v → P w)
    (t0 : ℝ) (hgen : ∀ k, (A k ≠ 0 ∨ B k ≠ 0) → A k + t0 * B k ≠ 0)
    (h0 : P (fv A B t0)) :
    (∃ k, B k ≠ 0 ∧ ∀ᶠ t in 𝓝[>] (-A k / B k), P (fv A B t)) ∨
    (∃ k, B k ≠ 0 ∧ ∀ᶠ t in 𝓝[<] (-A k / B k), P (fv A B t)) ∨
    (∀ᶠ t in atTop, P (fv A B t)) ∨ (∀ᶠ t in atBot, P (fv A B t)) := by
  rcases cl_right A B P hP t0 hgen h0 with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr h))

end Minimality.CL
