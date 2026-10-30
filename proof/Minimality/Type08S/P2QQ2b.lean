module

public import Minimality.Type08S.P2QQ2a
public import Minimality.Type08S.P2E3
public import Minimality.Type08S.P2J1

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkQ / Q2b: `r2t08_w`, `r2t08_T4_w` (statements as in PQ0; copies of `r2t08`, `r2t08_T4`, cores replaced).
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

set_option maxHeartbeats 1000000 in
theorem r2t08_w {o E₁ E₂ E₃ : ℝ³} (hE : det3 E₁ E₂ E₃ ≠ 0) {θ : Fin 6 → ℝ} (hθ : Ineq08w θ)
    (hy : Function.Injective (nfShape08 o E₁ E₂ E₃ θ))
    (hseg : ∀ i j m : Fin 7, nfShape08 o E₁ E₂ E₃ θ m ≠ nfShape08 o E₁ E₂ E₃ θ i →
      nfShape08 o E₁ E₂ E₃ θ m ≠ nfShape08 o E₁ E₂ E₃ θ j → ∀ s : ℝ, 0 < s → s < 1 →
      nfShape08 o E₁ E₂ E₃ θ m ≠ nfShape08 o E₁ E₂ E₃ θ i +
        s • (nfShape08 o E₁ E₂ E₃ θ j - nfShape08 o E₁ E₂ E₃ θ i))
    (i : Fin 3) (hcase : (i = 0 ∧ 1 < θ 5) ∨ (i = 1 ∧ θ 5 < 1 ∧ 1 < θ 0)) :
    (∃ j, IsRobustUnimodal ((test08 i true j).depth (nfShape08 o E₁ E₂ E₃ θ))) ∨
      WStraddle (nfShape08 o E₁ E₂ E₃ θ) (grp08 i) := by
  set y := nfShape08 o E₁ E₂ E₃ θ with hydef
  have hord := ord08_w (o := o) hE hθ i
  rcases hcase with ⟨rfl, h6⟩ | ⟨rfl, h6, h0⟩
  · have e1 : test08 0 true true = LabTest.quad (fun y => y 4 - y 1) 4 2 5 3 := rfl
    have e2 : test08 0 true false = LabTest.quad (fun y => y 4 - y 1) 1 2 5 3 := rfl
    have R := r2t_star y (fun y => y 4 - y 1) (covView_diff08 4 1) 4 1 2 5 3 hy (by decide) hseg
      hord (by
        intro L hL h1 h2
        have hinj : ∀ j, Function.Injective ((test08 0 true j).depth
            (nfShape08 (L o) (L E₁) (L E₂) (L E₃) θ)) := by
          intro j; cases j
          · rw [e2, ← mapShape_nfShape08]; exact h2
          · rw [e1, ← mapShape_nfShape08]; exact h1
        obtain ⟨j, hj⟩ := N2_core_w o E₁ E₂ E₃ hE θ hθ h6 L hL hinj
        rw [← mapShape_nfShape08] at hj
        cases j
        · right; rw [← e2]; exact hj
        · left; rw [← e1]; exact hj)
    rcases R with h | h | h
    · exact Or.inl ⟨true, by rw [e1]; exact h⟩
    · exact Or.inl ⟨false, by rw [e2]; exact h⟩
    · exact Or.inr h
  · have e1 : test08 1 true true = LabTest.quad (fun y => y 2 - y 6) 2 5 3 4 := rfl
    have e2 : test08 1 true false = LabTest.quad (fun y => y 2 - y 6) 6 5 3 4 := rfl
    have R := r2t_star y (fun y => y 2 - y 6) (covView_diff08 2 6) 2 6 5 3 4 hy (by decide) hseg
      hord (by
        intro L hL h1 h2
        have hinj : ∀ j, Function.Injective ((test08 1 true j).depth
            (nfShape08 (L o) (L E₁) (L E₂) (L E₃) θ)) := by
          intro j; cases j
          · rw [e2, ← mapShape_nfShape08]; exact h2
          · rw [e1, ← mapShape_nfShape08]; exact h1
        obtain ⟨j, hj⟩ := T4_core_w o E₁ E₂ E₃ hE θ hθ L hL hinj
        rw [← mapShape_nfShape08] at hj
        cases j
        · right; rw [← e2]; exact hj
        · left; rw [← e1]; exact hj)
    rcases R with h | h | h
    · exact Or.inl ⟨true, by rw [e1]; exact h⟩
    · exact Or.inl ⟨false, by rw [e2]; exact h⟩
    · exact Or.inr h

/-- R2T* for the T4 group at a frame shape, no condition on `θ 0`, `θ 5` (only `hθ`). -/
theorem r2t08_T4_w {o E₁ E₂ E₃ : ℝ³} (hE : det3 E₁ E₂ E₃ ≠ 0) {θ : Fin 6 → ℝ} (hθ : Ineq08w θ)
    (hy : Function.Injective (nfShape08 o E₁ E₂ E₃ θ))
    (hseg : ∀ i j m : Fin 7, nfShape08 o E₁ E₂ E₃ θ m ≠ nfShape08 o E₁ E₂ E₃ θ i →
      nfShape08 o E₁ E₂ E₃ θ m ≠ nfShape08 o E₁ E₂ E₃ θ j → ∀ s : ℝ, 0 < s → s < 1 →
      nfShape08 o E₁ E₂ E₃ θ m ≠ nfShape08 o E₁ E₂ E₃ θ i +
        s • (nfShape08 o E₁ E₂ E₃ θ j - nfShape08 o E₁ E₂ E₃ θ i)) :
    IsRobustUnimodal ((test08 1 true true).depth (nfShape08 o E₁ E₂ E₃ θ)) ∨
      IsRobustUnimodal ((test08 1 true false).depth (nfShape08 o E₁ E₂ E₃ θ)) ∨
      (let y := nfShape08 o E₁ E₂ E₃ θ; let u := y 2 - y 6
       ⟪y 5, u⟫ = ⟪y 3, u⟫ ∧ ⟪y 3, u⟫ = ⟪y 4, u⟫ ∧ ⟪y 6, u⟫ ≤ ⟪y 3, u⟫ ∧ ⟪y 3, u⟫ ≤ ⟪y 2, u⟫) := by
  set y := nfShape08 o E₁ E₂ E₃ θ with hydef
  have hord := ord08_w (o := o) hE hθ 1
  have e1 : test08 1 true true = LabTest.quad (fun y => y 2 - y 6) 2 5 3 4 := rfl
  have e2 : test08 1 true false = LabTest.quad (fun y => y 2 - y 6) 6 5 3 4 := rfl
  have R := r2t_star y (fun y => y 2 - y 6) (covView_diff08 2 6) 2 6 5 3 4 hy (by decide) hseg
    hord (by
      intro L hL h1 h2
      have hinj : ∀ j, Function.Injective ((test08 1 true j).depth
          (nfShape08 (L o) (L E₁) (L E₂) (L E₃) θ)) := by
        intro j; cases j
        · rw [e2, ← mapShape_nfShape08]; exact h2
        · rw [e1, ← mapShape_nfShape08]; exact h1
      obtain ⟨j, hj⟩ := T4_core_w o E₁ E₂ E₃ hE θ hθ L hL hinj
      rw [← mapShape_nfShape08] at hj
      cases j
      · right; rw [← e2]; exact hj
      · left; rw [← e1]; exact hj)
  rcases R with h | h | h
  · exact Or.inl (by rw [e1]; exact h)
  · exact Or.inr (Or.inl (by rw [e2]; exact h))
  · exact Or.inr (Or.inr h)

end Type08Sp
end Minimality
