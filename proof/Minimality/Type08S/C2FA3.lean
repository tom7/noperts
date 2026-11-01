module

public import Minimality.Type08S.C2FA2
public import Minimality.Type08S.P2RDefs
public import Minimality.Type08S.G6J2

@[expose] public section

/-!
# C2 / FA3: at `T` with `γ4 < 1`, the face `Q_bc` is a lex cell at the edge view `a - d`

`norm08_coords3` (the `T` frame: `c' = d + α1 (a-d) + β1 (b-d)`, `b' = d + α4 (a-d) + γ4 (c-d)`,
`a' = d + β6 (b-d) + (c-d)`, `1 < α1`, `0 < α4, γ4, β1, β6`, `0 < α4 - α4 β1 - α1 (1 - γ4)`).
`¬ AngBig` is `γ4 ≤ 1`; with `γ4 ≠ 1` (`det3 (c - b') (a - d) (b - d) ≠ 0`) the last inequality gives `β1 < 1`,
and `faA_hasLexCellAt` applies in the frame `(b - d, c - d, a - d)` with `γ6 = 1`.
Consequence: every item of `S4TR` (L2, (B2), (B3): all carry `IsT ∧ ¬ AngBig`) has a lex cell unless
`γ4 = 1` (H2: `b'c ∥ Q_ab`), i.e. `S4TR ∧ ¬ HasLexCell` has codimension 5.
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem lexCell_ad_T {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hT : IsT a' b c d)
    (hA : ¬ AngBig a b b' c d) (h1 : det3 (c - b') (a - d) (b - d) ≠ 0) :
    HasLexCellAt (V8 a a' b b' c c' d) (a - d) := by
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα1, hα4, hγ4, hβ1, hβ6, hE⟩ := norm08_coords3 N hT
  set D := det3 (a - d) (c - d) (b - d) with hD
  have hD0 : D ≠ 0 := by
    intro h0; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = -D := by simp only [hD, det3_expand]; ring
    rw [e, h0, neg_zero]
  have eA : det3 (c - b') (a - d) (b - d) = -(1 - γ4) * D := by
    rw [hb']; simp only [hD, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hγ1 : γ4 < 1 := by
    have hle : γ4 ≤ 1 := by
      by_contra hc
      apply hA
      unfold AngBig
      rw [eA]
      have : 0 < D * D := mul_self_pos.2 hD0
      nlinarith
    rcases hle.lt_or_eq with h | h
    · exact h
    · exfalso; apply h1; rw [eA, h]; ring
  have hβ11 : β1 < 1 := by nlinarith [mul_pos (lt_trans one_pos hα1) (sub_pos.2 hγ1)]
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
  refine faA_hasLexCellAt (V8 a a' b b' c c' d) p q r d hΔ (γ6 := 1) hβ6 one_pos (by linarith)
    (lt_trans one_pos hα1) hβ1 hβ11 hα4 hγ4 hγ1 ?_ ?_
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

/-- **The `T` items of `Resid08FinalJ` off `γ4 = 1`.**  `S4TR` (L2, (B2), (B3)) with `b'c ∦ Q_ab` has a lex cell
(at the edge view `a - d`, the face `Q_bc`). -/
theorem s4TR_hasLexCell {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (h : S4TR a a' b b' c c' d)
    (h1 : det3 (c - b') (a - d) (b - d) ≠ 0) : HasLexCell (V8 a a' b b' c c' d) := by
  have hA : ¬ AngBig a b b' c d := by
    obtain ⟨-, ⟨-, -, hA, -⟩ | ⟨-, -, hA, -⟩ | ⟨-, -, hA, -⟩⟩ := h <;> exact hA
  refine ⟨a - d, ?_, lexCell_ad_T N h.1 hA h1⟩
  intro had; apply h1
  rw [had]; simp [det3_expand]

end C2
end Type08Sp
end Minimality
