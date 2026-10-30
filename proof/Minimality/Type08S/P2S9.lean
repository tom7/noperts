module

public import Minimality.Type08S.P2S8

@[expose] public section

set_option relaxedAutoImplicit true
set_option autoImplicit true
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality

theorem Tp_caseA_core_neg (d A B C : ℝ³) {α4 β1 γ4 β6 γ6 : ℝ}
    (hH : det3 A C B < 0)
    (hα4 : 1 < α4) (hγ4 : 0 < γ4) (hβ1 : 0 < β1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hsep : max 0 ⟪A, B⟫ < min (α4 * ⟪A, B⟫ + γ4 * ⟪C, B⟫) ⟪C, B⟫) :
    IsRupert (insert d ({d + A, d + β6 • B + γ6 • C, d + B, d + α4 • A + γ4 • C, d + C,
      d + A + β1 • B} : Finset ℝ³)) := by
  classical
  let e : ℝ³ := EuclideanSpace.single 0 1
  have he : ⟪e, e⟫ = 1 := by simp [e]
  let f : ℝ³ → ℝ³ := fun x => x - (2 * ⟪x, e⟫) • e
  have hfa : ∀ p q, f (p + q) = f p + f q := fun p q => refl_add e p q
  have hfs : ∀ p t, f (t • p) = t • f p := fun p t => refl_smul e p t
  have hfi : ∀ p q, ⟪f p, f q⟫ = ⟪p, q⟫ := fun p q => refl_inner e p q he
  refine Type08Sp.isRupert_of_reflect e he _ ?_
  simp only [Finset.image_insert, Finset.image_singleton]
  show IsRupert (insert (f d) {f (d + A), f (d + β6 • B + γ6 • C), f (d + B), f (d + α4 • A + γ4 • C),
    f (d + C), f (d + A + β1 • B)})
  simp only [hfa, hfs]
  refine Tp_caseA_core (f d) (f A) (f B) (f C) ?_ hα4 hγ4 hβ1 hβ6 hγ6 hγ61 ?_
  · have := refl_det e A C B he
    show 0 < det3 (A - (2 * ⟪A, e⟫) • e) (C - (2 * ⟪C, e⟫) • e) (B - (2 * ⟪B, e⟫) • e)
    rw [this]; linarith
  · simp only [hfi]; exact hsep

theorem Tp_caseA_core_any (d A B C : ℝ³) {α4 β1 γ4 β6 γ6 : ℝ}
    (hH : det3 A C B ≠ 0)
    (hα4 : 1 < α4) (hγ4 : 0 < γ4) (hβ1 : 0 < β1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hsep : max 0 ⟪A, B⟫ < min (α4 * ⟪A, B⟫ + γ4 * ⟪C, B⟫) ⟪C, B⟫) :
    IsRupert (insert d ({d + A, d + β6 • B + γ6 • C, d + B, d + α4 • A + γ4 • C, d + C,
      d + A + β1 • B} : Finset ℝ³)) := by
  rcases lt_or_gt_of_ne hH with h | h
  · exact Tp_caseA_core_neg d A B C h hα4 hγ4 hβ1 hβ6 hγ6 hγ61 hsep
  · exact Tp_caseA_core d A B C h hα4 hγ4 hβ1 hβ6 hγ6 hγ61 hsep

namespace Type08Sp
variable {a a' b b' c c' d : ℝ³}

/-- **Case A at `T'`** (`α4 > 1`, `{d, a}` strictly below `{b', c}` along `ℓ`). -/
theorem Tp_caseA (N : Norm08 a a' b b' c c' d) (hT' : IsT' a b c' d)
    {α4 γ4 : ℝ} (hb'rep : b' = d + α4 • (a - d) + γ4 • (c - d)) (hα : 1 < α4)
    (hsep : max ⟪d, b - d⟫ ⟪a, b - d⟫ < min ⟪b', b - d⟫ ⟪c, b - d⟫) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨β1, β6, γ6, hne, hc', ha', hα4, hγ4, hαγ, hβ1, hβ6, hγ6, hγ61⟩ := Tp_frame N hT' hb'rep
  have key := Tp_caseA_core_any d (a - d) (b - d) (c - d) (β1 := β1) (β6 := β6) (γ6 := γ6)
    (α4 := α4) (γ4 := γ4) hne hα hγ4 hβ1 hβ6 hγ6 hγ61 (by
      have e1 : ⟪a - d, b - d⟫ = ⟪a, b - d⟫ - ⟪d, b - d⟫ := inner_sub_left _ _ _
      have e2 : ⟪c - d, b - d⟫ = ⟪c, b - d⟫ - ⟪d, b - d⟫ := inner_sub_left _ _ _
      have e4 : ⟪b' - d, b - d⟫ = ⟪b', b - d⟫ - ⟪d, b - d⟫ := inner_sub_left _ _ _
      have e6 : ⟪b' - d, b - d⟫ = α4 * ⟪a - d, b - d⟫ + γ4 * ⟪c - d, b - d⟫ := by
        have : b' - d = α4 • (a - d) + γ4 • (c - d) := by rw [hb'rep]; module
        rw [this, inner_add_left, real_inner_smul_left, real_inner_smul_left]
      rw [← e6]
      simp only [max_lt_iff, lt_min_iff] at hsep ⊢
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hsep
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith)
  have ea : d + (a - d) = a := by abel
  have eb : d + (b - d) = b := by abel
  have ec : d + (c - d) = c := by abel
  rw [← hc', ea, eb, ec, ← ha', ← hb'rep] at key
  exact key

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.Tp_caseA
