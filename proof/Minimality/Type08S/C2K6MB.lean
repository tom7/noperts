module

public import Minimality.Type08S.C2K6MA

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

set_option maxHeartbeats 1600000 in
/-- **Box A** (`β1 < 1`): face `Q_bc` at `a - d`, metric-free. -/
theorem k6m_A_hasLexCell {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 0 < α1) (hβ1 : 0 < β1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hs : 1 < β6 + γ6)
    (hβ11 : β1 < 1) : HasLexCell (V8 a a' b b' c c' d) := by
  set p := b - d with hp
  set q := c - d with hq
  set r := a - d with hr
  have hΔ : det3 p q r ≠ 0 := by
    intro h; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = det3 p q r := by simp only [hp, hq, hr, det3_expand]; ring
    rw [e, h]
  have eO : fpoint p q r d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eB : fpoint p q r d (1, 0, 0) = b := by simp only [fpoint, fcomb, hp]; module
  have eC : fpoint p q r d (0, 1, 0) = c := by simp only [fpoint, fcomb, hq]; module
  have eA' : fpoint p q r d (β6, γ6, 0) = a' := by rw [ha']; simp only [fpoint, fcomb, hp, hq]; module
  have eA1 : fpoint p q r d (0, 0, 1) = a := by simp only [fpoint, fcomb, hr]; module
  have eC' : fpoint p q r d (β1, 0, α1) = c' := by rw [hc']; simp only [fpoint, fcomb, hp, hr]; module
  have eB' : fpoint p q r d (0, β1, α1) = b' := by rw [hb']; simp only [fpoint, fcomb, hq, hr]; module
  have hA : HasLexCellAt (V8 a a' b b' c c' d) r := by
    refine faA_hasLexCellAt (V8 a a' b b' c c' d) p q r d hΔ hβ6 hγ6 hs
      hα1 hβ1 hβ11 hα1 hβ1 hβ11 ?_ ?_
    · intro i
      rcases z4_cases i with rfl | rfl | rfl | rfl
      · simp only [faCyc_0, eO]; simp [V8]
      · simp only [faCyc_1, eB]; simp [V8]
      · simp only [faCyc_2, eA']; simp [V8]
      · simp only [faCyc_3, eC]; simp [V8]
    · intro y hy
      rw [eO, eB, eA', eC, eA1, eC', eB']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
  refine ⟨r, ?_, hA⟩
  intro h0; apply hΔ; rw [h0]; simp [det3_expand]

end C2
end Type08Sp
end Minimality
