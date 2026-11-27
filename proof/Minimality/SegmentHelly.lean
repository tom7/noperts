module

public import Mathlib

/-!
# 1-D Helly on a segment: finitely many affine forms are simultaneously positive somewhere

For finitely many affine functions `f_i(λ) = (1 - λ) a_i + λ b_i` (values `a_i`, `b_i` at the two ends of a
segment), some interior `λ ∈ (0, 1)` has all `f_i(λ) > 0` iff

* (U) every `f_i` is positive at one of the two ends, and
* (B) for every pair `(i, j)` with `f_i` rising through `0` (`a_i ≤ 0 < b_i`) and `f_j` falling through `0`
  (`b_j ≤ 0 < a_j`) the crossing of `f_i` comes before the crossing of `f_j`, i.e. the determinant
  `a_i b_j - b_i a_j` is negative.

Proof: the strict solution set of one `f_i` is an open half-line `λ > r_i` (rising), `λ < r_j` (falling) or
everything; the rising roots lie in `[0, 1)`, the falling roots in `(0, 1]`.  Pairwise `r_i < r_j` gives a gap.

* `Minimality.exists_on_segment_iff`: the equivalence (pure real arithmetic, Mathlib only).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Minimality

/-- Two finite families of reals with every lower element below every upper one are separated by a point. -/
private theorem exists_sep {ι : Type*} [Fintype ι] (l u : ι → ℝ) (p q : ι → Prop)
    (h : ∀ i j, p i → q j → l i < u j) (h0 : ∀ j, q j → 0 < u j) (h1 : ∀ i, p i → l i < 1) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ (∀ i, p i → l i < t) ∧ (∀ j, q j → t < u j) := by
  classical
  -- lower end `m = max (0, l i)`, upper end `M = min (1, u j)`
  let A : Finset ℝ := insert 0 ((Finset.univ.filter p).image l)
  let B : Finset ℝ := insert 1 ((Finset.univ.filter q).image u)
  have hA : A.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  have hB : B.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  have hAB : A.max' hA < B.min' hB := by
    obtain ⟨a, ha, hmax⟩ : ∃ a ∈ A, A.max' hA = a := ⟨_, A.max'_mem hA, rfl⟩
    obtain ⟨b, hb, hmin⟩ : ∃ b ∈ B, B.min' hB = b := ⟨_, B.min'_mem hB, rfl⟩
    rw [hmax, hmin]
    simp only [A, B, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    rcases ha with rfl | ⟨i, hi, rfl⟩ <;> rcases hb with rfl | ⟨j, hj, rfl⟩
    · exact zero_lt_one
    · exact h0 j hj
    · exact h1 i hi
    · exact h i j hi hj
  refine ⟨(A.max' hA + B.min' hB) / 2, ?_, ?_, ?_, ?_⟩
  · have := A.le_max' 0 (Finset.mem_insert_self _ _)
    have := B.min'_le 1 (Finset.mem_insert_self _ _)
    have hB0 : (0:ℝ) < B.min' hB := by
      obtain ⟨b, hb, hmin⟩ : ∃ b ∈ B, B.min' hB = b := ⟨_, B.min'_mem hB, rfl⟩
      rw [hmin]
      simp only [B, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hb
      rcases hb with rfl | ⟨j, hj, rfl⟩
      · exact zero_lt_one
      · exact h0 j hj
    linarith
  · have hA1 : A.max' hA < 1 := by
      obtain ⟨a, ha, hmax⟩ : ∃ a ∈ A, A.max' hA = a := ⟨_, A.max'_mem hA, rfl⟩
      rw [hmax]
      simp only [A, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      rcases ha with rfl | ⟨i, hi, rfl⟩
      · exact zero_lt_one
      · exact h1 i hi
    have := B.min'_le 1 (Finset.mem_insert_self _ _)
    linarith
  · intro i hi
    have := A.le_max' (l i) (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨i, by simp [hi], rfl⟩))
    linarith
  · intro j hj
    have := B.min'_le (u j) (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨j, by simp [hj], rfl⟩))
    linarith

/-- **1-D Helly on a segment.**  For finitely many affine forms `(1 - λ) a_i + λ b_i`, an interior parameter
`λ ∈ (0, 1)` makes all of them positive iff each is positive at an end (U) and every rising `i` (`a_i ≤ 0 < b_i`)
and falling `j` (`b_j ≤ 0 < a_j`) satisfy `a_i b_j - b_i a_j < 0` (B: the rising root is below the falling root). -/
theorem exists_on_segment_iff {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    (∃ t : ℝ, 0 < t ∧ t < 1 ∧ ∀ i, 0 < (1 - t) * a i + t * b i) ↔
      (∀ i, 0 < a i ∨ 0 < b i) ∧
        (∀ i j, a i ≤ 0 → b j ≤ 0 → 0 < b i → 0 < a j → a i * b j - b i * a j < 0) := by
  constructor
  · rintro ⟨t, ht0, ht1, h⟩
    refine ⟨fun i => ?_, fun i j hai hbj hbi haj => ?_⟩
    · by_contra hc
      push Not at hc
      nlinarith [h i, hc.1, hc.2, mul_nonneg (sub_nonneg.2 ht1.le) (neg_nonneg.2 hc.1),
        mul_nonneg ht0.le (neg_nonneg.2 hc.2)]
    · have hp := h i
      have hq := h j
      have key : t * (b i * a j - a i * b j) = ((1 - t) * a i + t * b i) * a j - a i * ((1 - t) * a j + t * b j) := by
        ring
      have : 0 < t * (b i * a j - a i * b j) := by
        rw [key]; nlinarith [mul_pos hp haj, mul_nonneg (neg_nonneg.2 hai) hq.le]
      have := (pos_iff_pos_of_mul_pos this).1 ht0
      linarith
  · rintro ⟨hU, hB⟩
    classical
    -- roots `r i = a i / (a i - b i)`
    let r : ι → ℝ := fun i => a i / (a i - b i)
    obtain ⟨t, ht0, ht1, hl, hu⟩ := exists_sep r r (fun i => a i ≤ 0) (fun j => b j ≤ 0)
      (fun i j hi hj => by
        have hbi : 0 < b i := (hU i).resolve_left (not_lt.2 hi)
        have haj : 0 < a j := (hU j).resolve_right (not_lt.2 hj)
        have h1 := hB i j hi hj hbi haj
        have d1 : a i - b i < 0 := by linarith
        have d2 : 0 < a j - b j := by linarith
        show a i / (a i - b i) < a j / (a j - b j)
        rw [div_lt_iff_of_neg d1, div_mul_eq_mul_div, div_lt_iff₀ d2]
        nlinarith)
      (fun j hj => by
        have haj : 0 < a j := (hU j).resolve_right (not_lt.2 hj)
        have d2 : 0 < a j - b j := by linarith
        exact div_pos haj d2)
      (fun i hi => by
        have hbi : 0 < b i := (hU i).resolve_left (not_lt.2 hi)
        have d1 : a i - b i < 0 := by linarith
        show a i / (a i - b i) < 1
        rw [div_lt_one_of_neg d1]; linarith)
    refine ⟨t, ht0, ht1, fun i => ?_⟩
    by_cases hai : a i ≤ 0
    · have hbi : 0 < b i := (hU i).resolve_left (not_lt.2 hai)
      have d1 : a i - b i < 0 := by linarith
      have := hl i hai
      change a i / (a i - b i) < t at this
      rw [div_lt_iff_of_neg d1] at this
      nlinarith
    · push Not at hai
      by_cases hbi : b i ≤ 0
      · have d2 : 0 < a i - b i := by linarith
        have := hu i hbi
        change t < a i / (a i - b i) at this
        rw [lt_div_iff₀ d2] at this
        nlinarith
      · push Not at hbi
        nlinarith [mul_pos (sub_pos.2 ht1) hai, mul_pos ht0 hbi]

end Minimality
