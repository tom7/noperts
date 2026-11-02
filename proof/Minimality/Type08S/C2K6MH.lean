module

public import Minimality.Type08S.C2K6MG

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

theorem k6mTCyc_inj {α1 β1 : ℝ} (hα1 : 0 < α1) (hβ1 : 1 < β1) :
    ∀ i j, k6mTCyc α1 β1 i = k6mTCyc α1 β1 j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  have e3 := congrArg (fun t => t.2.2) h
  rcases z3_cases i with rfl | rfl | rfl <;> rcases z3_cases j with rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [k6mTCyc_0, k6mTCyc_1, k6mTCyc_2] at e1 e2 e3; linarith)

set_option maxHeartbeats 1600000 in
theorem k6m_T_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {α1 β1 β6 γ6 : ℝ}
    (hα1 : 0 < α1) (hβ1 : 1 < β1) (hb6 : 0 < β6) (hγ6 : 0 < γ6) (hσ : β6 + γ6 < β1)
    (hmem : ∀ i, fpoint P Q R d (k6mTCyc α1 β1 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 0, 1) ∨ y = fpoint P Q R d (β1, 0, α1) ∨
      y = fpoint P Q R d (0, β1, α1) ∨ y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
      y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (β6, γ6, 0)) :
    HasLexCellAt V R := by
  refine cyc_cell V P Q R d hΔ (k := 3) (by norm_num) (k6mTCyc α1 β1) (k6mTCyc_inj hα1 hβ1) hmem
    [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (1, 0, 0), (0, 1, 0), (β6, γ6, 0)] ?_
    (u1 := 1) (u2 := 1) (t1 := 0) (t2 := 1) (lo := 0) (hi := 1) (by norm_num) (by norm_num)
    (fun v1 v2 => 0 < v1 ∧ 0 < v2) ?_ ?_ ?_
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam h0 h1
    refine ⟨by simp, by simp; nlinarith⟩
  · intro v1 v2 ⟨hv1, hv2⟩
    exact k6m_T_tsc hα1 hβ1 hb6 hγ6 hσ hv1 hv2
  · intro v1 v2 _ h
    exact k6m_lexUni3 _ _ h

set_option maxHeartbeats 1600000 in
/-- **Box T** (`β1 > 1`, `σ < β1`, view `a - d`): triangle face `(a, c', b')`, metric-free. -/
theorem k6m_T_hasLexCell {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 0 < α1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6)
    (hβ11 : 1 < β1) (hσ : β6 + γ6 < β1) : HasLexCell (V8 a a' b b' c c' d) := by
  set P := b - d with hP
  set Q := c - d with hQ
  set R := a - d with hR
  have hΔ : det3 P Q R ≠ 0 := by
    intro h; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = det3 P Q R := by simp only [hP, hQ, hR, det3_expand]; ring
    rw [e, h]
  have eO : fpoint P Q R d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eB : fpoint P Q R d (1, 0, 0) = b := by simp only [fpoint, fcomb, hP]; module
  have eC : fpoint P Q R d (0, 1, 0) = c := by simp only [fpoint, fcomb, hQ]; module
  have eA' : fpoint P Q R d (β6, γ6, 0) = a' := by rw [ha']; simp only [fpoint, fcomb, hP, hQ]; module
  have eA1 : fpoint P Q R d (0, 0, 1) = a := by simp only [fpoint, fcomb, hR]; module
  have eC' : fpoint P Q R d (β1, 0, α1) = c' := by rw [hc']; simp only [fpoint, fcomb, hP, hR]; module
  have eB' : fpoint P Q R d (0, β1, α1) = b' := by rw [hb']; simp only [fpoint, fcomb, hQ, hR]; module
  have hA : HasLexCellAt (V8 a a' b b' c c' d) R := by
    refine k6m_T_frame (V8 a a' b b' c c' d) P Q R d hΔ hα1 hβ11 hβ6 hγ6 hσ ?_ ?_
    · intro i
      rcases z3_cases i with rfl | rfl | rfl
      · simp only [k6mTCyc_0, eA1]; simp [V8]
      · simp only [k6mTCyc_1, eC']; simp [V8]
      · simp only [k6mTCyc_2, eB']; simp [V8]
    · intro y hy
      rw [eA1, eC', eB', eO, eB, eC, eA']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
  refine ⟨R, ?_, hA⟩
  intro h0; apply hΔ; rw [h0]; simp [det3_expand]

end C2
end Type08Sp
end Minimality
