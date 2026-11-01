module

public import Minimality.Type08S.C2FB2
public import Minimality.Type08S.C2FA3
public import Minimality.Type08S.P2TpSetup
public import Minimality.Type08S.P2I9b

@[expose] public section

/-!
# C2 / FB3: `S4TpR` (the P1 tie at `T'` with `α4 < 1`) has a lex cell at the edge view `c - d`

`norm08_coordsTp'` (the `T'` frame: `c' = d + (a-d) + β1 (b-d)`, `b' = d + α4 (a-d) + γ4 (c-d)`,
`a' = d + β6 (b-d) + γ6 (c-d)`).  In the frame `(a - d, b - d, c - d)`:
* `β6 < 1`: the face `Q_ab = (d, a, c', b)` (`faA_hasLexCellAt` relabelled; needs `α4 < 1`, `β6 < 1`);
* `β6 > 1` and `D_c = ⟪c - d, b - d⟫ > 0`: the 5-cycle `(c', a', b, d, a)` (`fbC_hasLexCellAt`).
Left: `β6 = 1` (`a'b ∥ cd`, `det3 (a' - b) (c - d) (a - d) = 0`) or `D_c ≤ 0` (inside `S4TpR` this forces
`γ4 = 1` and `⟪a - d, b - d⟫ = 0`); both codim 5.
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem lexCell_cd_Tp {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hT' : IsT' a b c' d)
    (hAl : Al4Lt a b' c d) (hb6 : det3 (a' - b) (c - d) (a - d) ≠ 0)
    (hC : 0 < ⟪c - d, b - d⟫ ∨ det3 (a' - b) (c - d) (a - d) * det3 (b - d) (c - d) (a - d) < 0) :
    HasLexCellAt (V8 a a' b b' c c' d) (c - d) := by
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hα4, hγ4, hαγ, hβ1, hβ6, hγ6, hγ61, hcv⟩ :=
    norm08_coordsTp' N hT'
  set D := det3 (a - d) (c - d) (b - d) with hD
  have hD0 : D ≠ 0 := by
    intro h0; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = -D := by simp only [hD, det3_expand]; ring
    rw [e, h0, neg_zero]
  have hα41 : α4 < 1 := by
    obtain ⟨α, γ, hrep, hα⟩ := hAl
    have e1 := det_alpha (b := b) hb'
    have e2 := det_alpha (b := b) hrep
    have : (α4 - α) * D = 0 := by rw [hD]; linarith
    have := (mul_eq_zero.mp this).resolve_right hD0
    linarith
  set E := det3 (b - d) (c - d) (a - d) with hE
  have hE' : E = -D := by simp only [hE, hD, det3_expand]; ring
  have eB6 : det3 (a' - b) (c - d) (a - d) = (β6 - 1) * E := by
    rw [ha']; simp only [hE, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hb61 : β6 ≠ 1 := by intro h; apply hb6; rw [eB6, h]; ring
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  have hΔ : det3 p q r ≠ 0 := hdet
  have eO : fpoint p q r d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eA : fpoint p q r d (1, 0, 0) = a := by simp only [fpoint, fcomb, hp]; module
  have eB : fpoint p q r d (0, 1, 0) = b := by simp only [fpoint, fcomb, hq]; module
  have eC : fpoint p q r d (0, 0, 1) = c := by simp only [fpoint, fcomb, hr]; module
  have eC' : fpoint p q r d (1, β1, 0) = c' := by rw [hc']; simp only [fpoint, fcomb, hp, hq]; module
  have eB' : fpoint p q r d (α4, 0, γ4) = b' := by rw [hb']; simp only [fpoint, fcomb, hp, hr]; module
  have eA' : fpoint p q r d (0, β6, γ6) = a' := by rw [ha']; simp only [fpoint, fcomb, hq, hr]; module
  rcases lt_or_gt_of_ne hb61 with hlt | hgt
  · -- the face `Q_ab`
    refine faA_hasLexCellAt (V8 a a' b b' c c' d) p q r d hΔ (β6 := 1) (γ6 := β1) (α1 := γ4) (β1 := α4)
      (α4 := γ6) (γ4 := β6) one_pos hβ1 (by linarith) hγ4 hα4 hα41 hγ6 hβ6 hlt ?_ ?_
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
  · -- the 5-cycle `(c', a', b, d, a)`
    have hB : 0 < ⟪q, r⟫ := by
      rcases hC with h | h
      · rw [real_inner_comm]; exact h
      · exfalso
        rw [eB6, hE'] at h
        have : 0 < D * D := mul_self_pos.2 hD0
        nlinarith
    refine fbC_hasLexCellAt (V8 a a' b b' c c' d) p q r d hΔ hβ1 hα4 hα41 hγ4 hgt hγ6 hB ?_ ?_
    · intro i
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · simp only [fbCyc, pc5_0, eC']; simp [V8]
      · simp only [fbCyc, pc5_1, eA']; simp [V8]
      · simp only [fbCyc, pc5_2, eB]; simp [V8]
      · simp only [fbCyc, pc5_3, eO]; simp [V8]
      · simp only [fbCyc, pc5_4, eA]; simp [V8]
    · intro y hy
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inl eO.symm)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl eA.symm))))
      · exact Or.inr (Or.inl eA'.symm)
      · exact Or.inr (Or.inr (Or.inl eB.symm))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr eB'.symm)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl eC.symm)))))
      · exact Or.inl eC'.symm

/-- **`S4TpR` off two codim-5 conditions.**  With `a'b ∦ cd` (`β6 ≠ 1`) and either `D_c > 0` or `β6 < 1`, the
P1 tie at `T'` has a lex cell (at the edge view `c - d`). -/
theorem s4TpR_hasLexCell {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (h : S4TpR a a' b b' c c' d)
    (hb6 : det3 (a' - b) (c - d) (a - d) ≠ 0)
    (hC : 0 < ⟪c - d, b - d⟫ ∨ det3 (a' - b) (c - d) (a - d) * det3 (b - d) (c - d) (a - d) < 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hT', -, -, -, hAl, -⟩ := h
  refine ⟨c - d, ?_, lexCell_cd_Tp N hT' hAl hb6 hC⟩
  intro hcd; apply hb6
  rw [hcd]; simp [det3_expand]

end C2
end Type08Sp
end Minimality
