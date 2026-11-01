module

public import Minimality.Type08S.C2K2C

@[expose] public section

/-!
# C2 / K2D: `P3Tpii` and `L2 ∧ γ4 = 1` have a lex cell at the edge view `a - d`
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- The frame wrapper: `γ4 = 1`, `B' = 0`, `D_c > 0`, `β1 < 1`, `γ6 ≤ 1` give the cell at `a - d`. -/
theorem k2_cell_of_coords {a a' b b' c c' d : ℝ³} {α1 α4 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α4 • (a - d) + (1 : ℝ) • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 0 < α1) (hα4 : 0 < α4) (hβ1 : 0 < β1) (hβ11 : β1 < 1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6)
    (hγ61 : γ6 ≤ 1) (hs : 1 < β6 + γ6) (hB0 : ⟪a - d, b - d⟫ = 0) (hDc : 0 < ⟪c - d, b - d⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
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
  have eA : fpoint p q r d (0, 0, 1) = a := by simp only [fpoint, fcomb, hr]; module
  have eA' : fpoint p q r d (β6, γ6, 0) = a' := by rw [ha']; simp only [fpoint, fcomb, hp, hq]; module
  have eC' : fpoint p q r d (β1, 0, α1) = c' := by rw [hc']; simp only [fpoint, fcomb, hp, hr]; module
  have eB' : fpoint p q r d (0, 1, α4) = b' := by rw [hb']; simp only [fpoint, fcomb, hq, hr]; module
  refine ⟨a - d, ?_, k2_hasLexCellAt (V8 a a' b b' c c' d) p q r d hΔ hα1 hβ1 hβ11 hα4 hβ6 hγ6 hγ61 hs
    (by rw [real_inner_comm]; exact hB0) hDc ?_ ?_⟩
  · intro had; apply hdet
    have h0 : r = 0 := had
    rw [h0]; simp [det3_expand]
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [kCyc, pc5_0, eA]; simp [V8]
    · simp only [kCyc, pc5_1, eO]; simp [V8]
    · simp only [kCyc, pc5_2, eB]; simp [V8]
    · simp only [kCyc, pc5_3, eA']; simp [V8]
    · simp only [kCyc, pc5_4, eB']; simp [V8]
  · intro y hy
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl eO.symm)
    · exact Or.inl eA.symm
    · exact Or.inr (Or.inr (Or.inr (Or.inl eA'.symm)))
    · exact Or.inr (Or.inr (Or.inl eB.symm))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl eB'.symm))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl eC.symm)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr eC'.symm)))))

/-- **`P3Tpii` has a lex cell** (`T'`, tie `D_a = D_d`, `QacTop`, off the level face): `γ4 = 1`, `D_c > 0`. -/
theorem p3Tpii_hasLexCell {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (h : P3Tpii a a' b b' c c' d) : HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨⟨hT', hQ, hAd, hLev⟩, -, hDc0, -, -, -⟩ := h
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hα4, hγ4, hαγ, hβ1, hβ6, hγ6, hγ61, hcv⟩ :=
    norm08_coordsTp' N hT'
  have hB0 : ⟪a - d, b - d⟫ = 0 := by rw [inner_sub_left]; linarith
  have hDc : 0 < ⟪c - d, b - d⟫ :=
    lt_of_le_of_ne hDc0 (fun h => hLev ⟨hB0, h.symm⟩)
  have hγ4 : γ4 = 1 := by
    have e1 : ⟪b', b - d⟫ = ⟪d, b - d⟫ + γ4 * ⟪c - d, b - d⟫ := by
      rw [hb']
      simp only [inner_add_left, real_inner_smul_left, hB0]; ring
    have e2 : ⟪c, b - d⟫ = ⟪d, b - d⟫ + ⟪c - d, b - d⟫ := by rw [inner_sub_left]; ring
    have e3 : ⟪a, b - d⟫ = ⟪d, b - d⟫ := by rw [inner_sub_left] at hB0; linarith
    unfold QacTop at hQ
    rw [e1, e2, e3, max_eq_right (by linarith), max_eq_right (by nlinarith [mul_pos hγ4 hDc])] at hQ
    have : (1 - γ4) * ⟪c - d, b - d⟫ = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_right hDc.ne'
    linarith
  subst hγ4
  -- `β1 < 1` from `κ_a > 0`, `κ_b > 0`
  have hβ11 : β1 < 1 := by
    obtain ⟨F, hd, G, hκa, hκb, hκc, hU⟩ := N
    obtain ⟨μ, h1, h2⟩ := gale_coords_gen G hdet hc' hb' ha' (by linarith)
    have hμ : 0 < μ := by
      have : 0 < μ * (β6 * (1 - 1) + β1 * (1 - γ6)) := h2 ▸ hκb
      have h3 : 0 < β1 * (1 - γ6) := mul_pos hβ1 (by linarith)
      nlinarith
    have : 0 < μ * (α4 - α4 * β1 - 1 + 1 * 1) := h1 ▸ hκa
    have h4 : 0 < α4 - α4 * β1 - 1 + 1 * 1 := pos_of_mul_pos_right this hμ.le
    nlinarith
  exact k2_cell_of_coords hdet hc' hb' ha' one_pos hα4 hβ1 hβ11 hβ6 hγ6 hγ61.le
    hcv hB0 hDc

/-- **`L2 ∧ γ4 = 1` has a lex cell** (the `L2` item of `S4TR`: `IsT`, `TouchT`, `b'c ∥ Q_ab`). -/
theorem l2K_hasLexCell {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hT : IsT a' b c d)
    (hTouch : TouchT b b' c c' d) (hγ : det3 (c - b') (a - d) (b - d) = 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨⟨hcb', -⟩, hdc, -⟩ := hTouch
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα1, hα4, hγ4, hβ1, hβ6, hE⟩ := norm08_coords3 N hT
  set D := det3 (a - d) (c - d) (b - d) with hD
  have hD0 : D ≠ 0 := by
    intro h0; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = -D := by simp only [hD, det3_expand]; ring
    rw [e, h0, neg_zero]
  have eA : det3 (c - b') (a - d) (b - d) = -(1 - γ4) * D := by
    rw [hb']; simp only [hD, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hγ41 : γ4 = 1 := by
    have := (mul_eq_zero.mp (by rw [← eA]; exact hγ : -(1 - γ4) * D = 0)).resolve_right hD0
    linarith
  subst hγ41
  have hDc : 0 < ⟪c - d, b - d⟫ := by rw [inner_sub_left]; linarith
  have hB0 : ⟪a - d, b - d⟫ = 0 := by
    have e1 : ⟪b', b - d⟫ = ⟪d, b - d⟫ + α4 * ⟪a - d, b - d⟫ + 1 * ⟪c - d, b - d⟫ := by
      rw [hb']
      simp only [inner_add_left, real_inner_smul_left]
    have e2 : ⟪c, b - d⟫ = ⟪d, b - d⟫ + ⟪c - d, b - d⟫ := by rw [inner_sub_left]; ring
    have : α4 * ⟪a - d, b - d⟫ = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hα4.ne'
  have hβ11 : β1 < 1 := by nlinarith
  exact k2_cell_of_coords hdet hc' (by rw [hb']) (by rw [ha']; simp) (by linarith) hα4 hβ1 hβ11 hβ6 one_pos
    le_rfl (by linarith) hB0 hDc

end C2
end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.C2.p3Tpii_hasLexCell
#print axioms Minimality.Type08Sp.C2.l2K_hasLexCell
