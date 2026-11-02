module

public import Minimality.Type08S.C2K6MC

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

theorem k6m_B_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {α1 β1 β6 γ6 : ℝ}
    (hα1 : 0 < α1) (hα11 : α1 < 1) (hβ1 : 0 < β1) (hs : 1 < α1 + β1)
    (hb6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hmem : ∀ i, fpoint P Q R d (kqCyc α1 β1 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
      y = fpoint P Q R d (α1, β1, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, -1) ∨
      y = fpoint P Q R d (α1, 0, -β1) ∨ y = fpoint P Q R d (0, γ6, -β6)) :
    HasLexCellAt V R := by
  refine fc_cell V P Q R d hΔ (kqCyc α1 β1) (β := α1) (γ := β1) hα1 hβ1 hs ?_
    ?_ hmem [((0 : ℝ), (0 : ℝ), (-1 : ℝ)), (α1, 0, -β1), (0, γ6, -β6)] ?_
    (u1 := 1) (u2 := 1) (t1 := 0) (t2 := 1) (lo := 0) (hi := 1) (by norm_num) (by norm_num)
    (fun v1 v2 => 0 < v1 ∧ 0 < v2) ?_ ?_
  · simp only [kqCyc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Prod.ext_iff]
    simp
  · intro i j h
    have e1 := congrArg Prod.fst h
    have e2 := congrArg (fun t => t.2.1) h
    rcases z4_cases i with rfl | rfl | rfl | rfl <;> rcases z4_cases j with rfl | rfl | rfl | rfl <;>
      first | rfl | (exfalso; simp only [kqCyc_0, kqCyc_1, kqCyc_2, kqCyc_3] at e1 e2; linarith)
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inl ⟨3, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam h0 h1
    refine ⟨by simp, by simp; nlinarith⟩
  · intro v1 v2 ⟨hv1, hv2⟩
    exact k6m_B_tsc hα1 hα11 hβ1 hs hb6 hγ6 hγ61 hv1 hv2

end C2
end Type08Sp
end Minimality
