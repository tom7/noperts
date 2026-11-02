module

public import Minimality.Type08S.C2K6TAA

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

set_option maxHeartbeats 3200000 in
/-- **Box B extended to the ties `α4 = 1` or `β6 = 1`** (`T`, face `Q_ab` at `c - d`).  `Δ = det3 (a-d) (b-d) (c-d)`.
`hα : α4 ≤ 1`, `hβ : β6 ≤ 1` (not both equal), `hβ1 : β1 > 1` (needed for `β6 = 1`), `hfar` (needed for `α4 = 1`). -/
theorem k6t1_B_hasLexCell {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT : IsT a' b c d)
    (hfar : W.F.a'bc.f c' < W.F.a'bc.f a)
    (hα : det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) ≤ 0)
    (hβ : det3 (a' - b) (c - d) (a - d) * det3 (a - d) (b - d) (c - d) ≤ 0)
    (hne : det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) < 0 ∨
      det3 (a' - b) (c - d) (a - d) * det3 (a - d) (b - d) (c - d) < 0)
    (hβ1 : 0 < det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d)) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα1, hβ1', hαβ, hα4, hγ4, hαγ, hβ6, hfa⟩ :=
    norm08w_coordsT W hT
  have hα11 : 1 < α1 := hfa hfar
  have hΔ2 : 0 < det3 (a - d) (b - d) (c - d) ^ 2 := by positivity
  rw [det_alpha4 hb'] at hα hne
  rw [det_beta1 hc'] at hβ1
  have eB6 : det3 (a' - b) (c - d) (a - d) = (β6 - 1) * det3 (a - d) (b - d) (c - d) := by
    rw [ha']
    simp only [det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  rw [eB6] at hβ hne
  have hα41 : α4 ≤ 1 := by nlinarith
  have hβ61 : β6 ≤ 1 := by nlinarith
  have hβ11 : 1 < β1 := by nlinarith
  have hone : α4 < 1 ∨ β6 < 1 := by
    rcases hne with h | h
    · left; nlinarith
    · right; nlinarith
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  have eO : fpoint p q r d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eA : fpoint p q r d (1, 0, 0) = a := by simp only [fpoint, fcomb, hp]; module
  have eB : fpoint p q r d (0, 1, 0) = b := by simp only [fpoint, fcomb, hq]; module
  have eC : fpoint p q r d (0, 0, 1) = c := by simp only [fpoint, fcomb, hr]; module
  have eC' : fpoint p q r d (α1, β1, 0) = c' := by rw [hc']; simp only [fpoint, fcomb, hp, hq]; module
  have eB' : fpoint p q r d (α4, 0, γ4) = b' := by rw [hb']; simp only [fpoint, fcomb, hp, hr]; module
  have eA' : fpoint p q r d (0, β6, 1) = a' := by rw [ha']; simp only [fpoint, fcomb, hq, hr]; module
  have hA : HasLexCellAt (V8 a a' b b' c c' d) r := by
    refine k6t1_faA_hasLexCellAt (V8 a a' b b' c c' d) p q r d hdet (β6 := α1) (γ6 := β1) (α1 := γ4)
      (β1 := α4) (α4 := 1) (γ4 := β6) hα1 hβ1' hαβ hγ4 hα4 ?_ one_pos hβ6 ?_ ?_ ?_ ?_
    · rcases hα41.lt_or_eq with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hα11⟩
    · rcases hβ61.lt_or_eq with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hβ11⟩
    · exact hone
    · intro i
      rcases z4_cases i with rfl | rfl | rfl | rfl
      · simp only [faCyc_0, eO]; simp [V8]
      · simp only [faCyc_1, eA]; simp [V8]
      · simp only [faCyc_2, eC']; simp [V8]
      · simp only [faCyc_3, eB]; simp [V8]
    · intro y hy
      rw [eO, eA, eC', eB, eC, eB', eA']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
  refine ⟨r, ?_, hA⟩
  intro h0; apply hdet; have : det3 p q r = 0 := by rw [h0]; simp [det3_expand]
  exact this

end C2
end Type08Sp
end Minimality
