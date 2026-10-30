module

public import Minimality.Type08S.P2TDefs
public import Minimality.Type08S.P2TL1
public import Minimality.Type08S.P2TB0a
public import Minimality.Type08S.P2TB0b

@[expose] public section

set_option relaxedAutoImplicit true
set_option autoImplicit true
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

set_option maxHeartbeats 1000000 in
/-- R2T* for the N2 group at a frame shape with `θ 5 = 1` (copy of the `i = 0` branch of `r2t08`). -/
theorem r2t08_N2_T {o E₁ E₂ E₃ : ℝ³} (hE : det3 E₁ E₂ E₃ ≠ 0) {θ : Fin 6 → ℝ} (hθ : ∀ k, 0 < ineq08 θ k)
    (hy : Function.Injective (nfShape08 o E₁ E₂ E₃ θ))
    (hseg : ∀ i j m : Fin 7, nfShape08 o E₁ E₂ E₃ θ m ≠ nfShape08 o E₁ E₂ E₃ θ i →
      nfShape08 o E₁ E₂ E₃ θ m ≠ nfShape08 o E₁ E₂ E₃ θ j → ∀ s : ℝ, 0 < s → s < 1 →
      nfShape08 o E₁ E₂ E₃ θ m ≠ nfShape08 o E₁ E₂ E₃ θ i +
        s • (nfShape08 o E₁ E₂ E₃ θ j - nfShape08 o E₁ E₂ E₃ θ i))
    (h5 : θ 5 = 1) :
    (∃ j, IsRobustUnimodal ((test08 0 true j).depth (nfShape08 o E₁ E₂ E₃ θ))) ∨
      WStraddle (nfShape08 o E₁ E₂ E₃ θ) (grp08 0) := by
  set y := nfShape08 o E₁ E₂ E₃ θ with hydef
  have hord := ord08 (o := o) hE hθ 0
  have e1 : test08 0 true true = LabTest.quad (fun y => y 4 - y 1) 4 2 5 3 := rfl
  have e2 : test08 0 true false = LabTest.quad (fun y => y 4 - y 1) 1 2 5 3 := rfl
  have R := r2t_star y (fun y => y 4 - y 1) (covView_diff08 4 1) 4 1 2 5 3 hy (by decide) hseg
    hord (by
      intro L hL h1 h2
      have hinj : ∀ j, Function.Injective ((test08 0 true j).depth
          (nfShape08 (L o) (L E₁) (L E₂) (L E₃) θ)) := by
        intro j; cases j
        · rw [e2, ← mapShape_nfShape08]; exact h2
        · rw [e1, ← mapShape_nfShape08]; exact h1
      obtain ⟨j, hj⟩ := N2_core_T o E₁ E₂ E₃ hE θ hθ h5 L hL hinj
      rw [← mapShape_nfShape08] at hj
      cases j
      · right; rw [← e2]; exact hj
      · left; rw [← e1]; exact hj)
  rcases R with h | h | h
  · exact Or.inl ⟨true, by rw [e1]; exact h⟩
  · exact Or.inl ⟨false, by rw [e2]; exact h⟩
  · exact Or.inr h

set_option maxHeartbeats 4000000 in
theorem caseB_Xba {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hT : IsT a' b c d)
    (hB : ¬ RobKb a a' b b' c c' d) :
    RobXba a' b b' c' d ∨
      (⟪b, b - d⟫ = ⟪c', b - d⟫ ∧ ⟪b', b - d⟫ = ⟪c', b - d⟫ ∧ ⟪c, b - d⟫ ≤ ⟪c', b - d⟫ ∧
        ⟪c', b - d⟫ ≤ ⟪a', b - d⟫) := by
  classical
  obtain ⟨o, E₁, E₂, E₃, θ, hE, hθ, hpts⟩ := exists_nf08 N
  obtain ⟨hg1, hg2⟩ := T_closure_T4 N hT
  have hnd := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have hfc : N.F.abc'.f c < 0 := N.F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc'
  have hg := region_gamma6 N hE hθ hpts
  have h5 : θ 5 = 1 := by
    rw [hg] at hg1; nlinarith
  obtain ⟨hseg, hsp⟩ := seg08 N
  simp only [hpts] at hseg hsp
  have hy : Function.Injective (nfShape08 o E₁ E₂ E₃ θ) := by rw [← hpts]; exact pts08_inj N
  have p4 : 0 < θ 4 := (common08 θ hθ).2.2.2.2.1
  have key : pts08 a a' b b' c c' d 1 = pts08 a a' b b' c c' d 6 +
      θ 4 • (pts08 a a' b b' c c' d 2 - pts08 a a' b b' c c' d 6) +
      θ 5 • (pts08 a a' b b' c c' d 4 - pts08 a a' b b' c c' d 6) := by
    rw [hpts]
    simp only [nfShape08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.head_cons]; module
  simp only [pts08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.head_cons] at key
  rw [h5] at key
  have hu : c - a' = (-θ 4) • (b - d) := by rw [key]; module
  set k : ℝ := -θ 4 with hk
  have hk0 : k < 0 := by rw [hk]; linarith
  have hin : ∀ p : ℝ³, ⟪p, c - a'⟫ = k * ⟪p, b - d⟫ := fun p => by rw [hu, inner_smul_right]
  have R := r2t08_N2_T hE hθ hy hseg h5
  rw [← hpts] at R
  rcases R with ⟨j, hj⟩ | hw
  · cases j
    · -- K_a' robust: `RobXba`
      left
      have hq : (test08 0 true false).depth (pts08 a a' b b' c c' d) =
          quad (k * ⟪a', b - d⟫) (k * ⟪b, b - d⟫) (k * ⟪c', b - d⟫) (k * ⟪b', b - d⟫) := by
        funext i
        rcases zmod4_cases i with rfl | rfl | rfl | rfl
        exacts [hin a', hin b, hin c', hin b']
      rw [hq] at hj
      have hs := notSep_of_rob hj
      rw [sep_mul_neg hk0] at hs
      intro hsep
      apply hs
      simp only [Sep, max_le_iff, le_min_iff] at hsep ⊢
      tauto
    · -- K_c robust: contradiction with `¬ RobKb`
      exfalso
      have hq : (test08 0 true true).depth (pts08 a a' b b' c c' d) =
          quad (k * ⟪c, b - d⟫) (k * ⟪b, b - d⟫) (k * ⟪c', b - d⟫) (k * ⟪b', b - d⟫) := by
        funext i
        rcases zmod4_cases i with rfl | rfl | rfl | rfl
        exacts [hin c, hin b, hin c', hin b']
      rw [hq] at hj
      have hs := notSep_of_rob hj
      rw [sep_mul_neg hk0] at hs
      apply hB
      unfold RobKb
      have hq2 : (test08 1 true true).depth (pts08 a a' b b' c c' d) =
          quad ⟪b, b - d⟫ ⟪c', b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫ := by
        funext i
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rfl
      rw [hq2]
      apply robust4
      intro hsep
      apply hs
      simp only [Sep, max_le_iff, le_min_iff] at hsep ⊢
      tauto
  · right
    simp only [grp08, WStraddle, pts08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.head_cons] at hw
    obtain ⟨h1, h2, h3, h4⟩ := hw
    simp only [hin] at h1 h2 h3 h4
    rw [neg_mul_le_iff hk0] at h3 h4
    refine ⟨?_, ?_, h4, h3⟩
    · nlinarith
    · nlinarith

end Type08Sp
end Minimality

