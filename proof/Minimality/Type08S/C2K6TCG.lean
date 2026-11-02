module

public import Minimality.Type08S.C2K6TCF

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

/-- **Pc leaf 1**: `K5ZsPc` with `ζ_{a-d}(c,a') = ⟪c - a', a - d⟫ > 0`: the cell `(a,d,b,a',b')` at `c - a'`. -/
theorem k6t3_pc1 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K5ZsPc a a' b b' c c' d)
    (hu : 0 < ⟪c - a', a - d⟫) : HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hT', hnT, hκc, hα⟩ := h
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hβ1, hα4p, hγ4, hαγ, hβ6, hγ6, hγ6s, hfa⟩ :=
    norm08w_coordsTp W hT'
  have hg61 : γ6 < 1 := hfa (k5z_far1 W hT' hnT)
  rw [det_alpha4 hb'] at hα
  have hα41 : α4 = 1 := by
    rcases mul_eq_zero.1 hα with h | h
    · linarith
    · exact absurd h hdet
  have hκ' := (planar_c_iff hdet hb' ha').1 hκc
  subst hα41
  have hβ61 : β6 = 1 := by
    have : γ4 * (1 - β6) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  subst hβ61
  have hfacet := k6t3_facet_a'b'c' W hc' hb' ha' hβ1 hγ4 hγ6
  set m : ℝ := 1 - γ6 with hm
  have hm0 : 0 < m := by rw [hm]; linarith
  have hm1 : m < 1 := by rw [hm]; linarith
  have hmne : m ≠ 0 := hm0.ne'
  have hγ6m : γ6 = 1 - m := by rw [hm]; ring
  set P := a - d with hP
  set Q := (1 / m) • (b - d) with hQ
  set R := (1 / m) • (c - a') with hR
  have hca' : c - a' = m • (c - d) - (b - d) := by
    rw [ha', hγ6m]; module
  have hΔ0 : det3 P Q R = det3 (a - d) (b - d) (c - d) / m := by
    rw [hP, hQ, hR, hca']
    simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hΔ : det3 P Q R ≠ 0 := by rw [hΔ0]; exact div_ne_zero hdet hmne
  have hfp : ∀ x y z : ℝ, fpoint P Q R d (x, y, z) = d + x • P + y • Q + z • R := by
    intro x y z; simp only [fpoint, fcomb]; module
  have eO : fpoint P Q R d (0, 0, 0) = d := by rw [hfp]; simp
  have eA : fpoint P Q R d (1, 0, 0) = a := by rw [hfp, hP]; module
  have eB' : fpoint P Q R d (1, γ4, γ4) = b' := by
    rw [hfp, hb', hP, hQ, hR, hca']; match_scalars <;> field_simp <;> ring
  have eC : fpoint P Q R d (0, 1, 1) = c := by
    rw [hfp, hQ, hR, hca']; match_scalars <;> field_simp <;> ring
  have eA' : fpoint P Q R d (0, 1, 1 - m) = a' := by
    rw [hfp, hQ, hR, hca', ha', hγ6m]
    match_scalars <;> field_simp <;> ring
  have eC' : fpoint P Q R d (1, β1 * m, 0) = c' := by
    rw [hfp, hc', hP, hQ]; match_scalars <;> field_simp <;> ring
  have eB : fpoint P Q R d (0, m, 0) = b := by
    rw [hfp, hQ]; match_scalars <;> field_simp <;> ring
  have hmem : ∀ i, fpoint P Q R d (k6t3_pcX m γ4 i) ∈ V8 a a' b b' c c' d := by
    intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · rw [k6t3_pcX_0, eA]; simp [V8]
    · rw [k6t3_pcX_1, eB']; simp [V8]
    · rw [k6t3_pcX_2, eA']; simp [V8]
    · rw [k6t3_pcX_3, eB]; simp [V8]
    · rw [k6t3_pcX_4, eO]; simp [V8]
  have hVall : ∀ y ∈ V8 a a' b b' c c' d, y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
      y = fpoint P Q R d (1, γ4, γ4) ∨ y = fpoint P Q R d (0, 1, 1) ∨ y = fpoint P Q R d (0, 1, 1 - m) ∨
      y = fpoint P Q R d (1, β1 * m, 0) ∨ y = fpoint P Q R d (0, m, 0) := by
    intro y hy
    rw [eO, eA, eB', eC, eA', eC', eB]
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  have hR0 : R ≠ 0 := by
    intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  refine ⟨R, hR0, ?_⟩
  have hu' : 0 < ⟪P, R⟫ := by
    rw [hP, hR, real_inner_smul_right, real_inner_comm]
    exact mul_pos (by positivity) hu
  exact k6t3_pc1_frame _ P Q R d hΔ hm0 hm1 hγ4 (mul_pos hβ1 hm0) (by nlinarith) hu' hmem hVall

end C2
end Type08Sp
end Minimality
