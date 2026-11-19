module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Set.Basic

@[expose] public section

open scoped BigOperators

namespace Minimality

/-- **The Band Hexagon Emptiness Theorem (Wall Helly Bound).**
Let `L, U : Fin 3 → ℝ` define a bounding box in `ℝ³`.
The intersection of the box with the zero-sum plane `{x | ∑ i, x i = 0}` is empty
if and only if:
1. Some coordinate interval is empty (`∃ i, U i < L i`), or
2. The lower sum is strictly positive (`0 < ∑ i, L i`), or
3. The upper sum is strictly negative (`∑ i, U i < 0`).
Therefore, any minimal cover of diagonal metrics across the three walls uses at most 3 cells. -/
theorem band_hexagon_empty_iff (L U : Fin 3 → ℝ) :
    ({x : Fin 3 → ℝ | (∑ i, x i = 0) ∧ ∀ i, L i ≤ x i ∧ x i ≤ U i} = ∅) ↔
      (∃ i, U i < L i) ∨ (0 < ∑ i, L i) ∨ (∑ i, U i < 0) := by
  constructor
  · intro hempty
    by_contra hc
    have hnot1 : ¬(∃ i, U i < L i) := fun h => hc (Or.inl h)
    have hnot2 : ¬(0 < ∑ i, L i) := fun h => hc (Or.inr (Or.inl h))
    have hnot3 : ¬(∑ i, U i < 0) := fun h => hc (Or.inr (Or.inr h))
    have hLU : ∀ i, L i ≤ U i := fun i => not_lt.mp fun h => hnot1 ⟨i, h⟩
    have hSL : ∑ i, L i ≤ 0 := not_lt.mp hnot2
    have hSU : 0 ≤ ∑ i, U i := not_lt.mp hnot3
    set SL := ∑ i, L i
    set SU := ∑ i, U i
    have hex : ∃ x : Fin 3 → ℝ, (∑ i, x i = 0) ∧ ∀ i, L i ≤ x i ∧ x i ≤ U i := by
      by_cases hsum : SU = SL
      · refine ⟨L, ?_, fun i => ⟨le_rfl, hLU i⟩⟩
        have hle : SL ≤ SU := Finset.sum_le_sum fun i _ => hLU i
        change SL = 0
        linarith
      · have hle : SL ≤ SU := Finset.sum_le_sum fun i _ => hLU i
        have hdiff_pos : 0 < SU - SL := by
          have hlt : SL < SU := lt_of_le_of_ne hle (Ne.symm hsum)
          linarith
        set t := -SL / (SU - SL)
        have ht0 : 0 ≤ t := div_nonneg (by linarith) (le_of_lt hdiff_pos)
        have ht1 : t ≤ 1 := by
          rw [div_le_iff₀ hdiff_pos]
          linarith
        have h1t : 0 ≤ 1 - t := by linarith
        set x : Fin 3 → ℝ := fun i => (1 - t) * L i + t * U i
        refine ⟨x, ?_, ?_⟩
        · dsimp [x]
          have hdist : ∑ i, ((1 - t) * L i + t * U i) = (1 - t) * SL + t * SU := by
            simp only [SL, SU, Finset.sum_add_distrib, ← Finset.mul_sum]
          rw [hdist]
          have hdiv : -SL / (SU - SL) * (SU - SL) = -SL :=
            div_mul_cancel₀ (-SL) (ne_of_gt hdiff_pos)
          calc (1 - t) * SL + t * SU = SL + t * (SU - SL) := by ring
            _ = SL + (-SL / (SU - SL)) * (SU - SL) := rfl
            _ = SL + -SL := by rw [hdiv]
            _ = 0 := by ring
        · intro i
          dsimp [x]
          have h1 : L i ≤ (1 - t) * L i + t * U i := by
            have hdiff : (1 - t) * L i + t * U i - L i = t * (U i - L i) := by ring
            have hpos : 0 ≤ t * (U i - L i) := mul_nonneg ht0 (by linarith [hLU i])
            linarith
          have h2 : (1 - t) * L i + t * U i ≤ U i := by
            have hdiff : U i - ((1 - t) * L i + t * U i) = (1 - t) * (U i - L i) := by ring
            have hpos : 0 ≤ (1 - t) * (U i - L i) := mul_nonneg h1t (by linarith [hLU i])
            linarith
          exact ⟨h1, h2⟩
    rcases hex with ⟨x, hx⟩
    have hmem : x ∈ {x : Fin 3 → ℝ | (∑ i, x i = 0) ∧ ∀ i, L i ≤ x i ∧ x i ≤ U i} := hx
    rw [hempty] at hmem
    exact hmem
  · rintro (⟨i, hi⟩ | hpos | hneg)
    · ext x
      constructor
      · rintro ⟨-, hx⟩
        have h1 := (hx i).1
        have h2 := (hx i).2
        linarith
      · intro h
        cases h
    · ext x
      constructor
      · rintro ⟨hzero, hx⟩
        have hle : ∑ i, L i ≤ ∑ i, x i := Finset.sum_le_sum fun i _ => (hx i).1
        linarith
      · intro h
        cases h
    · ext x
      constructor
      · rintro ⟨hzero, hx⟩
        have hle : ∑ i, x i ≤ ∑ i, U i := Finset.sum_le_sum fun i _ => (hx i).2
        linarith
      · intro h
        cases h

end Minimality
