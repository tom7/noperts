module

public import Minimality.Type08S.C2K4C

@[expose] public section

/-!
# C2 / K4D: `S4TpRK` has a lex cell

* `s4TpR_Dnonpos`: in `S4TpR`, `D_c = ⟪c - d, b - d⟫ ≤ 0` forces `⟪a - d, b - d⟫ = 0`, `D_c < 0`, `γ4 = 1`.
* `s4TpR_dcneg_hasLexCell`: `S4TpR ∧ D_c < 0` (any `β6`): the 6-cycle `(a, c', b, a', c, b')` at `a - d`.
* `s4TpR_b6one_hasLexCell`: `S4TpR ∧ β6 = 1` (`det3 (a' - b) (c - d) (a - d) = 0`) `∧ D_c > 0`: the 5-cycle
  `(c', a', b, d, a)` at `c - d`.
* **`s4TpRK_hasLexCell`**: `Norm08 → S4TpRK → HasLexCell (V8 …)`.
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- `α4 < 1` from `Al4Lt` and the coordinates. -/
theorem k4_alpha41 {a b b' c d : ℝ³} {α4 γ4 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hb' : b' = d + α4 • (a - d) + γ4 • (c - d)) (hAl : Al4Lt a b' c d) : α4 < 1 := by
  set D := det3 (a - d) (c - d) (b - d) with hD
  have hD0 : D ≠ 0 := by
    intro h0; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = -D := by simp only [hD, det3_expand]; ring
    rw [e, h0, neg_zero]
  obtain ⟨α, γ, hrep, hα⟩ := hAl
  have e1 := det_alpha (b := b) hb'
  have e2 := det_alpha (b := b) hrep
  have : (α4 - α) * D = 0 := by rw [hD]; linarith
  have := (mul_eq_zero.mp this).resolve_right hD0
  linarith

/-- `D_c ≤ 0` inside `S4TpR` (coordinates): `B' = 0`, `D_c < 0`, `γ4 = 1`. -/
theorem s4TpR_Dnonpos {a b b' c d : ℝ³} {α4 γ4 : ℝ} (hb' : b' = d + α4 • (a - d) + γ4 • (c - d))
    (hα4 : 0 < α4) (hQ : QacTop a b b' c d) (htie : ⟪c, b - d⟫ = ⟪b', b - d⟫)
    (hLev : ¬ LevelQac a b c d) (hD : ⟪c - d, b - d⟫ ≤ 0) :
    ⟪a - d, b - d⟫ = 0 ∧ ⟪c - d, b - d⟫ < 0 ∧ γ4 = 1 := by
  have e1 : ⟪b', b - d⟫ = ⟪d, b - d⟫ + α4 * ⟪a - d, b - d⟫ + γ4 * ⟪c - d, b - d⟫ := by
    rw [hb']; simp only [inner_add_left, real_inner_smul_left]
  have e2 : ⟪c, b - d⟫ = ⟪d, b - d⟫ + ⟪c - d, b - d⟫ := by rw [inner_sub_left]; ring
  have e3 : ⟪a, b - d⟫ = ⟪d, b - d⟫ + ⟪a - d, b - d⟫ := by rw [inner_sub_left]; ring
  set E := ⟪a - d, b - d⟫ with hE
  set Dc := ⟪c - d, b - d⟫ with hDc
  have htie' : Dc = α4 * E + γ4 * Dc := by linarith
  unfold QacTop at hQ
  have hb'' : ⟪b', b - d⟫ = ⟪d, b - d⟫ + Dc := by rw [← htie, e2]
  rw [e2, e3, hb''] at hQ
  rw [max_eq_left (by linarith)] at hQ
  have hE0 : E = 0 := by
    rcases le_or_gt E Dc with h | h
    · rw [max_eq_right (by linarith)] at hQ
      have hDc0 : Dc = 0 := by linarith
      have : α4 * E = 0 := by rw [hDc0] at htie'; linarith
      exact (mul_eq_zero.mp this).resolve_left hα4.ne'
    · rw [max_eq_left (by linarith)] at hQ; linarith
  have hneg : Dc < 0 := by
    rcases hD.lt_or_eq with h | h
    · exact h
    · exact absurd ⟨hE0, h⟩ hLev
  refine ⟨hE0, hneg, ?_⟩
  have : (1 - γ4) * Dc = 0 := by rw [hE0] at htie'; linarith
  have := (mul_eq_zero.mp this).resolve_right hneg.ne
  linarith

/-- The frame wrapper at `a - d` (`D_c < 0`). -/
theorem s4TpR_dcneg_hasLexCell {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (h : S4TpR a a' b b' c c' d) (hDc : ⟪c - d, b - d⟫ < 0) : HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hT', hQ, htie, hLev, hAl, -⟩ := h
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hα4, hγ4, hαγ, hβ1, hβ6, hγ6, hγ61, hcv⟩ :=
    norm08_coordsTp' N hT'
  obtain ⟨hB0, -, hγ4'⟩ := s4TpR_Dnonpos hb' hα4 hQ htie hLev hDc.le
  have hα41 := k4_alpha41 hdet hb' hAl
  subst hγ4'
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
  have eC' : fpoint p q r d (β1, 0, 1) = c' := by rw [hc']; simp only [fpoint, fcomb, hp, hr]; module
  have eB' : fpoint p q r d (0, 1, α4) = b' := by rw [hb']; simp only [fpoint, fcomb, hq, hr]; module
  refine ⟨a - d, ?_, k4_hasLexCellAt (V8 a a' b b' c c' d) p q r d hΔ hβ1 hβ11 hα4 hα41 hβ6 hγ6 hγ61.le
    (by linarith) (by rw [real_inner_comm]; exact hB0) hDc ?_ ?_⟩
  · intro had; apply hdet
    have h0 : r = 0 := had
    rw [h0]; simp [det3_expand]
  · intro i
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [k4Cyc, pc6_0, eA]; simp [V8]
    · simp only [k4Cyc, pc6_1, eC']; simp [V8]
    · simp only [k4Cyc, pc6_2, eB]; simp [V8]
    · simp only [k4Cyc, pc6_3, eA']; simp [V8]
    · simp only [k4Cyc, pc6_4, eC]; simp [V8]
    · simp only [k4Cyc, pc6_5, eB']; simp [V8]
  · intro y hy
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr eO.symm)))))
    · exact Or.inl eA.symm
    · exact Or.inr (Or.inr (Or.inr (Or.inl eA'.symm)))
    · exact Or.inr (Or.inr (Or.inl eB.symm))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl eB'.symm)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl eC.symm))))
    · exact Or.inr (Or.inl eC'.symm)

/-- The frame wrapper at `c - d` (`β6 = 1`, `D_c > 0`). -/
theorem s4TpR_b6one_hasLexCell {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (h : S4TpR a a' b b' c c' d) (hb6 : det3 (a' - b) (c - d) (a - d) = 0) (hDc : 0 < ⟪c - d, b - d⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hT', hQ, htie, hLev, hAl, -⟩ := h
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hα4, hγ4, hαγ, hβ1, hβ6, hγ6, hγ61, hcv⟩ :=
    norm08_coordsTp' N hT'
  have hα41 := k4_alpha41 hdet hb' hAl
  set D := det3 (a - d) (c - d) (b - d) with hD
  have hD0 : D ≠ 0 := by
    intro h0; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = -D := by simp only [hD, det3_expand]; ring
    rw [e, h0, neg_zero]
  set E := det3 (b - d) (c - d) (a - d) with hE
  have hE' : E = -D := by simp only [hE, hD, det3_expand]; ring
  have eB6 : det3 (a' - b) (c - d) (a - d) = (β6 - 1) * E := by
    rw [ha']; simp only [hE, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hβ61 : β6 = 1 := by
    rw [eB6] at hb6
    have hE0 : E ≠ 0 := by rw [hE']; exact neg_ne_zero.2 hD0
    have := (mul_eq_zero.mp hb6).resolve_right hE0
    linarith
  subst hβ61
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
  have eA' : fpoint p q r d (0, 1, γ6) = a' := by rw [ha']; simp only [fpoint, fcomb, hq, hr]; module
  refine ⟨c - d, ?_, k4b_hasLexCellAt (V8 a a' b b' c c' d) p q r d hΔ hβ1 hα4 hα41 hγ4 hγ6
    (by rw [real_inner_comm]; exact hDc) ?_ ?_⟩
  · intro hcd; apply hdet
    have h0 : r = 0 := hcd
    rw [h0]; simp [det3_expand]
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k4bCyc, pc5_0, eC']; simp [V8]
    · simp only [k4bCyc, pc5_1, eA']; simp [V8]
    · simp only [k4bCyc, pc5_2, eB]; simp [V8]
    · simp only [k4bCyc, pc5_3, eO]; simp [V8]
    · simp only [k4bCyc, pc5_4, eA]; simp [V8]
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

/-- **`S4TpRK` has a lex cell**: `β6 = 1` or `D_c ≤ 0` (the latter for every `β6`). -/
theorem s4TpRK_hasLexCell {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (h : S4TpRK a a' b b' c c' d) : HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hS, hK⟩ := h
  by_cases hle : ⟪c - d, b - d⟫ ≤ 0
  · obtain ⟨hT', hQ, htie, hLev, hAl, -⟩ := id hS
    obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hα4, -⟩ := norm08_coordsTp' N hT'
    obtain ⟨-, hneg, -⟩ := s4TpR_Dnonpos hb' hα4 hQ htie hLev hle
    exact s4TpR_dcneg_hasLexCell N hS hneg
  · rcases hK with hK | ⟨hK, -⟩
    · exact s4TpR_b6one_hasLexCell N hS hK (not_le.1 hle)
    · exact absurd hK hle

end C2
end Type08Sp
end Minimality

