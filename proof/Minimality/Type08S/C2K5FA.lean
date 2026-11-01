module

public import Minimality.Type08S.C2K5LP
public import Minimality.Type08S.C2FA3
public import Minimality.Type08S.C2FB3

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- Box A of K5f: `β1 < 1`, view `a - d`, face `Q_bc`. -/
theorem k5f_A_hasLexCell {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT : IsT a' b c d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0)
    (hβ : det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) < 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα1, hβ1, hαβ, hα4, hγ4, hαγ, hβ6, -⟩ :=
    norm08w_coordsT W hT
  have hκ' := (planar_a_iff hdet hc' hb').1 hκ
  rw [det_beta1 hc'] at hβ
  have hβ11 : β1 < 1 := by
    have : 0 < det3 (a - d) (b - d) (c - d) ^ 2 := by positivity
    nlinarith
  have hγ1 : γ4 < 1 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg hα1.le (by linarith : 0 ≤ γ4 - 1), mul_pos hα4 (sub_pos.2 hβ11)]
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
  have eA' : fpoint p q r d (β6, 1, 0) = a' := by rw [ha']; simp only [fpoint, fcomb, hp, hq]; module
  have eA1 : fpoint p q r d (0, 0, 1) = a := by simp only [fpoint, fcomb, hr]; module
  have eC' : fpoint p q r d (β1, 0, α1) = c' := by rw [hc']; simp only [fpoint, fcomb, hp, hr]; module
  have eB' : fpoint p q r d (0, γ4, α4) = b' := by rw [hb']; simp only [fpoint, fcomb, hq, hr]; module
  have hA : HasLexCellAt (V8 a a' b b' c c' d) r := by
    refine faA_hasLexCellAt (V8 a a' b b' c c' d) p q r d hΔ (γ6 := 1) hβ6 one_pos (by linarith)
      hα1 hβ1 hβ11 hα4 hγ4 hγ1 ?_ ?_
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
