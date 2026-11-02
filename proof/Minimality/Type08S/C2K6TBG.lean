module

public import Minimality.Type08S.C2K6TBE

@[expose] public section

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

/-- **6c, `β1 < 1`**: QPa with `α4 = 1` (so `β1 = γ4` by `κ_a`), `β1 < 1`: face `Q_bc = (d,b,a',c)` at `a - d`. -/
theorem k6t2_pa6c_lt {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT' : IsT' a b c' d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0) (hα4 : det3 (b' - a) (b - d) (c - d) = 0)
    (hβ : det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) < 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hβ1, hα4p, hγ4, hαγ, hβ6, hγ6, hγ6s, -⟩ :=
    norm08w_coordsTp W hT'
  have hκ' := (planar_a_iff hdet hc' hb').1 hκ
  rw [one_mul] at hκ'
  rw [det_alpha4 hb'] at hα4
  have hα41 : α4 = 1 := by
    rcases mul_eq_zero.1 hα4 with h | h
    · linarith
    · exact absurd h hdet
  subst hα41
  have hbg : β1 = γ4 := by linarith
  rw [det_beta1 hc'] at hβ
  have hβ11 : β1 < 1 := by
    have : 0 < det3 (a - d) (b - d) (c - d) ^ 2 := by positivity
    nlinarith
  have hγ1 : γ4 < 1 := by linarith
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
  have eC' : fpoint p q r d (β1, 0, 1) = c' := by rw [hc']; simp only [fpoint, fcomb, hp, hr]; module
  have eB' : fpoint p q r d (0, γ4, 1) = b' := by rw [hb']; simp only [fpoint, fcomb, hq, hr]; module
  have hA : HasLexCellAt (V8 a a' b b' c c' d) r := by
    refine faA_hasLexCellAt (V8 a a' b b' c c' d) p q r d hΔ hβ6 hγ6 hγ6s one_pos hβ1
      hβ11 one_pos hγ4 hγ1 ?_ ?_
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
