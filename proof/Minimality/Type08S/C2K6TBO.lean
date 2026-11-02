module

public import Minimality.Type08S.C2K6TBN

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

/-- **Pa, `β1 < 1`** (any `α4`, any of the three ties): face `Q_bc = (d,b,a',c)` at `a - d`
(`κ_a = 0` gives `γ4 = 1 - α4 (1 - β1) < 1`). -/
theorem k6t2_pa_faceA {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT' : IsT' a b c' d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0)
    (hβ : det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) < 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hβ1, hα4p, hγ4, hαγ, hβ6, hγ6, hγ6s, -⟩ :=
    norm08w_coordsTp W hT'
  have hκ' := (planar_a_iff hdet hc' hb').1 hκ
  rw [one_mul] at hκ'
  rw [det_beta1 hc'] at hβ
  have hβ11 : β1 < 1 := by
    have : 0 < det3 (a - d) (b - d) (c - d) ^ 2 := by positivity
    nlinarith
  have hγ1 : γ4 < 1 := by nlinarith [mul_pos hα4p (sub_pos.2 hβ11)]
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
  have eB' : fpoint p q r d (0, γ4, α4) = b' := by rw [hb']; simp only [fpoint, fcomb, hq, hr]; module
  have hA : HasLexCellAt (V8 a a' b b' c c' d) r := by
    refine faA_hasLexCellAt (V8 a a' b b' c c' d) p q r d hΔ hβ6 hγ6 hγ6s one_pos hβ1
      hβ11 hα4p hγ4 hγ1 ?_ ?_
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

/-- **Pa, pentagon `(a,c',b',c,d)` for `β1 > 1`** (so `γ4 = 1 + α4 (β1 - 1) > 1`): `ζ(b',c) < 0` (any `α4`),
or `ζ(b',c) = 0` with `ζ(a,d) < 0`.  Used for 6c (`α4 = 1`, `ζ(b',c) < 0`) and 6b (`α4 < 1`, `u < 0`). -/
theorem k6t2_pa_p4 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT' : IsT' a b c' d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0) (hfar : W.F.abc'.f c < W.F.abc'.f a')
    (hβ : 0 < det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d))
    (hw : ⟪b' - c, d - b⟫ < 0 ∨ (⟪b' - c, d - b⟫ = 0 ∧ ⟪a - d, d - b⟫ < 0)) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hΔ, hβ1, hα4p, hγ4, hαγ, hβ6, hγ6, hγ6s, hfar', hc', hb', ha',
    hmem7, hVall⟩ := k5d_setup W hT'
  have hγ61 := hfar' hfar
  have hκ' := (planar_a_iff hdet hc' hb').1 hκ
  rw [one_mul] at hκ'
  rw [det_beta1 hc'] at hβ
  have hβ11 : 1 < β1 := by
    have : 0 < det3 (a - d) (b - d) (c - d) ^ 2 := by positivity
    nlinarith
  have hγ41 : 1 < γ4 := by nlinarith [mul_pos hα4p (sub_pos.2 hβ11)]
  have hz3 : ⟪b' - c, d - b⟫ = α4 * ⟪a - d, d - b⟫ + γ4 * ⟪c - d, d - b⟫ - ⟪c - d, d - b⟫ := by
    rw [hb']; simp only [inner_sub_left, inner_add_left, real_inner_smul_left]; ring
  have hmemX : ∀ {n : ℕ} {X : ZMod n → ℝ × ℝ × ℝ}, (∀ i, X i ∈ k5dL α4 γ4 β1 β6 γ6) →
      ∀ i, fpoint (a - d) (c - d) (d - b) d (X i) ∈ V8 a a' b b' c c' d :=
    fun h i => hmem7 _ (h i)
  refine ⟨d - b, k5d_R_ne hΔ, ?_⟩
  refine k6t2_c4g_frame _ _ _ _ _ hΔ hα4p hγ41 hαγ hβ1 hβ6 hγ6 (Or.inl hγ61) ?_
    (hmemX (k5dX4_mem α4 γ4 β1 β6 γ6)) hVall
  rcases hw with h | ⟨h, h'⟩
  · left; linarith
  · right; exact ⟨by linarith, h'⟩

end C2
end Type08Sp
end Minimality
