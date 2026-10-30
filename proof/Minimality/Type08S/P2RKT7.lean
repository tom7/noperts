module

public import Minimality.Type08S.P2RKT6

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkR / K2 / KT7: **face cell theorem** in frame coordinates (`p = a-d`, `q = c-d`, `r = b-d`).
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- **Face cell (frame form).**  `V` consists of the seven frame points `d, a, b', c, b, c', a'`; `p, q ⊥ r`;
`α > 1`, `γ > 0`, `β1, β6 > 0`, `0 < γ6 < 1`.  Then `V` has a lex cell at the base view `r`. -/
theorem face_hasLexCellAt (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0)
    (hpr : ⟪p, r⟫ = 0) (hqr : ⟪q, r⟫ = 0) {α γ β1 β6 γ6 : ℝ} (hα : 1 < α) (hγ : 0 < γ)
    (hβ1 : 0 < β1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hO : fpoint p q r d (0, 0, 0) ∈ V) (hA : fpoint p q r d (1, 0, 0) ∈ V)
    (hB : fpoint p q r d (α, γ, 0) ∈ V) (hC : fpoint p q r d (0, 1, 0) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint p q r d (0, 0, 0) ∨ y = fpoint p q r d (1, 0, 0) ∨
      y = fpoint p q r d (α, γ, 0) ∨ y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (0, 0, 1) ∨
      y = fpoint p q r d (1, 0, β1) ∨ y = fpoint p q r d (0, γ6, β6)) :
    HasLexCellAt V r := by
  obtain ⟨lam, hl0, hl1, hA0, hC0, hAC, hB0, hBA, hBC⟩ := face_tilt p q r hΔ hα hγ
  set vv := fcomb p q r (-lam) (-1) 0 with hvv
  set A := ⟪p, vv⟫ with hAdef
  set C := ⟪q, vv⟫ with hCdef
  have hz : ∀ i j : ZMod 4, ⟪fpoint p q r d (quad (0, 0, 0) (1, 0, 0) (α, γ, 0) (0, 1, 0) i), r⟫ =
      ⟪fpoint p q r d (quad (0, 0, 0) (1, 0, 0) (α, γ, 0) (0, 1, 0) j), r⟫ := by
    have h : ∀ i : ZMod 4, ⟪fpoint p q r d (quad (0, 0, 0) (1, 0, 0) (α, γ, 0) (0, 1, 0) i), r⟫ = ⟪d, r⟫ := by
      intro i
      rcases z4_cases i with rfl | rfl | rfl | rfl <;>
        simp [inner_fpoint, quad4_0, quad4_1, quad4_2, quad4_3, hpr, hqr]
    intro i j; rw [h, h]
  have hzN : ∀ i j : ZMod 4, ⟪fpoint p q r d (quad (0, 0, 0) (0, 1, 0) (α, γ, 0) (1, 0, 0) i), r⟫ =
      ⟪fpoint p q r d (quad (0, 0, 0) (0, 1, 0) (α, γ, 0) (1, 0, 0) j), r⟫ := by
    have h : ∀ i : ZMod 4, ⟪fpoint p q r d (quad (0, 0, 0) (0, 1, 0) (α, γ, 0) (1, 0, 0) i), r⟫ = ⟪d, r⟫ := by
      intro i
      rcases z4_cases i with rfl | rfl | rfl | rfl <;>
        simp [inner_fpoint, quad4_0, quad4_1, quad4_2, quad4_3, hpr, hqr]
    intro i j; rw [h, h]
  rcases hΔ.lt_or_gt with hneg | hpos
  · -- cycle (d, c, b', a)
    refine ⟨4, inferInstance, fun i => fpoint p q r d (faceCycN α γ i), fcomb p q r (-lam) (-1) 0, ?_⟩
    refine lexCell_coord V p q r d (by norm_num) (faceCycN α γ) (-lam, -1, 0) ?_
      (faceN_cyc hneg hα hγ hl0) ?_ ?_
    · intro i
      rcases z4_cases i with rfl | rfl | rfl | rfl
      exacts [hO, hC, hB, hA]
    · intro y hy hyx
      have hr := faceN_rest hneg hα hγ hl0 hl1 hβ1 hβ6 hγ6 hγ61
      rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hyx 0 rfl).elim
      · exact (hyx 3 rfl).elim
      · exact (hyx 2 rfl).elim
      · exact (hyx 1 rfl).elim
      · exact ⟨_, rfl, hr.1⟩
      · exact ⟨_, rfl, hr.2.1⟩
      · exact ⟨_, rfl, hr.2.2⟩
    · refine face_lexUni (w0 := ⟪d, vv⟫) (P := C) (Q := A) (B := α * A + γ * C) hzN ?_ hC0 hA0
        (Ne.symm hAC) hB0 hBC hBA ?_ ?_
      · funext i
        rcases z4_cases i with rfl | rfl | rfl | rfl <;>
          simp [inner_fpoint, faceCycN, quad4_0, quad4_1, quad4_2, quad4_3, hAdef, hCdef] <;> ring
      · rw [max_comm C A]; exact (face_nonalt (A := A) (C := C) hα hγ).1
      · rw [min_comm C A]; exact (face_nonalt (A := A) (C := C) hα hγ).2
  · -- cycle (d, a, b', c)
    refine ⟨4, inferInstance, fun i => fpoint p q r d (faceCycP α γ i), fcomb p q r (-lam) (-1) 0, ?_⟩
    refine lexCell_coord V p q r d (by norm_num) (faceCycP α γ) (-lam, -1, 0) ?_
      (faceP_cyc hpos hα hγ hl0) ?_ ?_
    · intro i
      rcases z4_cases i with rfl | rfl | rfl | rfl
      exacts [hO, hA, hB, hC]
    · intro y hy hyx
      have hr := faceP_rest hpos hα hγ hl0 hl1 hβ1 hβ6 hγ6 hγ61
      rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hyx 0 rfl).elim
      · exact (hyx 1 rfl).elim
      · exact (hyx 2 rfl).elim
      · exact (hyx 3 rfl).elim
      · exact ⟨_, rfl, hr.1⟩
      · exact ⟨_, rfl, hr.2.1⟩
      · exact ⟨_, rfl, hr.2.2⟩
    · refine face_lexUni (w0 := ⟪d, vv⟫) (P := A) (Q := C) (B := α * A + γ * C) hz ?_ hA0 hC0
        hAC hB0 hBA hBC (face_nonalt hα hγ).1 (face_nonalt hα hγ).2
      funext i
      rcases z4_cases i with rfl | rfl | rfl | rfl <;>
        simp [inner_fpoint, faceCycP, quad4_0, quad4_1, quad4_2, quad4_3, hAdef, hCdef] <;> ring

end Type08Sp
end Minimality
