module

public import MinimalityExtra.NoUnimodal

/-!
# Sanity checks for the definitions of `MinimalityExtra.lean`

`¬ HasUnimodalView` would be empty if the definition could never hold. So: the witness does
have a strict rim, and `HasUnimodalView` is satisfiable.
-/

@[expose] public section

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace MinimalityExtra
open scoped RealInnerProductSpace

/-- Sanity: `¬ HasUnimodalView` is not vacuous for the witness: it has a strict rim, a 6-cycle. -/
theorem NoUni.exists_strictRim :
    ∃ lab : ZMod 6 → Fin 7, Function.Injective lab ∧ StrictRim NoUni.vx NoUni.vw lab := by
  have key : ∀ a b : Fin 7, (a, b) ∈ [((0 : Fin 7), (1 : Fin 7)), (1, 2), (2, 6), (6, 4), (4, 5), (5, 0)] →
      ∀ m, m ≠ a → m ≠ b → 0 < det3 (NoUni.vx b - NoUni.vx a) (NoUni.vx m - NoUni.vx a) NoUni.vw := by
    intro a b h m h1 h2
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      fin_cases m <;>
      first
      | exact absurd rfl h1
      | exact absurd rfl h2
      | norm_num [det3, NoUni.vx, NoUni.xN, NoUni.pt, NoUni.ptl, NoUni.vw]
  refine ⟨![0, 1, 2, 6, 4, 5], ?_, fun m i h1 h2 => key _ _ ?_ m h1 h2⟩
  · intro a b h
    fin_cases a <;> fin_cases b <;> first | rfl | exact absurd h (by decide)
  · clear h1 h2
    fin_cases i <;> decide

/-- Sanity: `HasUnimodalView` is satisfiable: a triangle at three depths around four inner points. -/
theorem exists_hasUnimodalView : ∃ x : Fin 7 → ℝ³, HasUnimodalView x := by
  let x : Fin 7 → ℝ³ := ![!₂[0, 0, 0], !₂[6, 0, 1], !₂[0, 6, 2], !₂[1, 1, 0], !₂[2, 1, 0], !₂[1, 2, 0], !₂[2, 2, 0]]
  have hz : (fun i : ZMod 3 => ⟪x ((![0, 1, 2] : ZMod 3 → Fin 7) i), (!₂[0, 0, 1] : ℝ³)⟫) = ![0, 1, 2] := by
    funext i
    fin_cases i <;> simp [x, PiLp.inner_apply, Fin.sum_univ_three]
  refine ⟨x, !₂[0, 0, 1], 3, inferInstance, ![0, 1, 2], le_rfl, ?_, ?_, ?_⟩
  · intro a b h
    fin_cases a <;> fin_cases b <;> first | rfl | exact absurd h (by decide)
  · have key : ∀ a b : Fin 7, (a, b) ∈ [((0 : Fin 7), (1 : Fin 7)), (1, 2), (2, 0)] →
        ∀ m, m ≠ a → m ≠ b → 0 < det3 (x b - x a) (x m - x a) (!₂[0, 0, 1] : ℝ³) := by
      intro a b h m h1 h2
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> fin_cases m <;>
        first
        | exact absurd rfl h1
        | exact absurd rfl h2
        | norm_num [det3, x]
    intro m i h1 h2
    refine key _ _ ?_ m h1 h2
    clear h1 h2
    fin_cases i <;> decide
  · rw [hz]
    have all3 : ∀ a : ZMod 3, a = 0 ∨ a = 1 ∨ a = 2 := by decide
    have e01 : ((0 : ZMod 3) + 1) = 1 := by decide
    have e12 : ((1 : ZMod 3) + 1) = 2 := by decide
    have e20 : ((2 : ZMod 3) + 1) = 0 := by decide
    have f0 : ((0 : ZMod 3) - 1) = 2 := by decide
    have f1 : ((1 : ZMod 3) - 1) = 0 := by decide
    have f2 : ((2 : ZMod 3) - 1) = 1 := by decide
    have v0 : (![0, 1, 2] : ZMod 3 → ℝ) 0 = 0 := rfl
    have v1 : (![0, 1, 2] : ZMod 3 → ℝ) 1 = 1 := rfl
    have v2 : (![0, 1, 2] : ZMod 3 → ℝ) 2 = 2 := rfl
    refine ⟨?_, Finset.card_eq_one.2 ⟨2, ?_⟩⟩
    · intro a b h
      rcases all3 a with rfl | rfl | rfl <;> rcases all3 b with rfl | rfl | rfl <;>
        first | rfl | (exfalso; rw [v0] at h <;> norm_num [v1, v2] at h) | (exfalso; norm_num [v0, v1, v2] at h)
    · ext i
      rcases all3 i with rfl | rfl | rfl <;>
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, e01, e12, e20, f0, f1, f2, v0, v1, v2] <;> norm_num <;> decide
end MinimalityExtra

#print axioms MinimalityExtra.NoUni.exists_strictRim
#print axioms MinimalityExtra.exists_hasUnimodalView
