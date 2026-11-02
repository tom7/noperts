module

public import Minimality.Type08S.C2K22Z1C3A
public import Minimality.Type08S.C2K17HZ

@[expose] public section


set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

set_option maxHeartbeats 12800000 in
/-- Corner `K17hTcZ1`, cell C3: view `a - c'`, silhouette cycle `(b, a', b', c')` (strict `S2 > 0`; needs `γ4 > 1`). -/
theorem k22z1_c3_strict {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17hTcZ1 a a' b b' c c' d)
    (hS : 0 < ⟪b - a, a - c'⟫)
    (hγ : ∀ α4 γ4 : ℝ, b' = d + α4 • (a - d) + γ4 • (c - d) → 1 < γ4) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hK, hOC, hOB, hOA⟩ := h
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα11, hα41, hβ1, hγ4p, hb6, hrel, hE0⟩ :=
    k17ga_tc_coords W hK
  have hγ4 : 1 < γ4 := hγ α4 γ4 hb'
  have hzdb : ⟪d - b, a - b'⟫ = 0 := hK.2.2.1
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  have hpq : ⟪p, q⟫ = 0 := hOA
  have hqp : ⟪q, p⟫ = 0 := by rw [real_inner_comm]; exact hpq
  have hq0 : q ≠ 0 := by intro h0; apply hdet; rw [h0]; simp [det3_expand]
  have hqq : 0 < ⟪q, q⟫ := real_inner_self_pos.2 hq0
  -- β1 = 1
  have hβ11 : β1 = 1 := by
    have e1 : d - b = -q := by rw [hq]; module
    have e2 : c' - b = α1 • p + (β1 - 1) • q := by rw [hc', hq, hp]; module
    rw [e1, e2] at hOB
    simp only [inner_neg_left, inner_add_right, inner_smul_right, hqp] at hOB
    have : (β1 - 1) * ⟪q, q⟫ = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hqq.ne'
  -- q ⟂ r
  have hqr : ⟪q, r⟫ = 0 := by
    have e1 : d - b = -q := by rw [hq]; module
    have e2 : a - b' = (1 - α4) • p - γ4 • r := by rw [hb', hp, hr]; module
    rw [e1, e2] at hzdb
    simp only [inner_neg_left, inner_sub_right, inner_smul_right, hpq, hqp] at hzdb
    have : γ4 * ⟪q, r⟫ = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact h
  have hrq : ⟪r, q⟫ = 0 := by rw [real_inner_comm]; exact hqr
  -- the frame
  obtain ⟨u, hu⟩ : ∃ u, u = α1 - 1 := ⟨_, rfl⟩
  have hu0 : 0 < u := by linarith
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = u⁻¹ := ⟨_, rfl⟩
  have hℓ0 : 0 < ℓ := by rw [hℓ]; positivity
  have hℓu : ℓ * u = 1 := by rw [hℓ]; field_simp
  set R := a - c' with hR
  have hRv : R = (-u) • p - q := by
    rw [hR, hc', hβ11, hp, hq, hu]; module
  have hΔ : det3 q r R ≠ 0 := by
    have e : det3 q r R = (-u) * det3 p q r := by
      rw [hRv]
      simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e]; exact mul_ne_zero (neg_ne_zero.2 hu0.ne') hdet
  have Ed : fpoint q r R d (0, 0, 0) = d := by rw [k17f_fp]; module
  have Eb : fpoint q r R d (1, 0, 0) = b := by rw [k17f_fp, hq]; module
  have Ec : fpoint q r R d (0, 1, 0) = c := by rw [k17f_fp, hr]; module
  have Ea : fpoint q r R d (-ℓ, 0, -ℓ) = a := by
    rw [k17f_fp, hRv]; rw [hp]
    match_scalars <;> nlinarith [hℓu]
  have Ec' : fpoint q r R d (-ℓ, 0, -ℓ - 1) = c' := by
    rw [k17f_fp, hRv, hc', hβ11, hp, hq]
    match_scalars <;> nlinarith [hℓu]
  have Eb' : fpoint q r R d (-α4 * ℓ, γ4, -α4 * ℓ) = b' := by
    rw [k17f_fp, hRv, hb', hp, hr]
    match_scalars <;> nlinarith [hℓu]
  have Ea' : fpoint q r R d (β6, 1, 0) = a' := by rw [k17f_fp, ha', hq, hr]; module
  -- inner products
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint q r R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪q, R⟫ + t.2.1 * ⟪r, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have iqR : ⟪q, R⟫ = -⟪q, q⟫ := by rw [hRv, inner_sub_right, inner_smul_right, hqp]; ring
  have irR : ⟪r, R⟫ = -u * ⟪r, p⟫ := by rw [hRv, inner_sub_right, inner_smul_right, hrq]; ring
  have ipR : ⟪p, R⟫ = -u * ⟪p, p⟫ := by rw [hRv, inner_sub_right, inner_smul_right, hpq]; ring
  have iRR : ⟪R, R⟫ = u ^ 2 * ⟪p, p⟫ + ⟪q, q⟫ := by
    conv_lhs => rw [hRv]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, conj_trivial, hpq, hqp]
    have := ipR; rw [hRv] at this
    simp only [inner_sub_right, inner_smul_right, hpq] at this
    nlinarith
  have hS2 : 0 < u * ⟪p, p⟫ - ⟪q, q⟫ := by
    have e : b - a = q - p := by rw [hp, hq]; module
    rw [e, inner_sub_left, iqR, ipR] at hS
    linarith
  have hpp : 0 < ⟪p, p⟫ := by
    by_contra hn; push_neg at hn
    nlinarith [mul_nonneg hu0.le (by linarith : 0 ≤ -⟪p, p⟫)]
  set x := ⟪r, p⟫ with hx
  set pp := ⟪p, p⟫ with hpp'
  set qq := ⟪q, q⟫ with hqq'
  have hβ6 : β6 * γ4 = γ4 + α4 - 1 := by nlinarith
  have zb : ⟪fpoint q r R d (1, 0, 0), R⟫ = ⟪d, R⟫ - qq := by rw [hz]; simp only [iqR]; ring
  have za' : ⟪fpoint q r R d (β6, 1, 0), R⟫ = ⟪d, R⟫ - β6 * qq - u * x := by
    rw [hz]; simp only [iqR, irR]; ring
  have zb' : ⟪fpoint q r R d (-α4 * ℓ, γ4, -α4 * ℓ), R⟫ = ⟪d, R⟫ - γ4 * u * x - α4 * u * pp := by
    rw [hz]; simp only [iqR, irR, iRR]
    linear_combination (-(α4 * pp * u)) * hℓu
  have zc' : ⟪fpoint q r R d (-ℓ, 0, -ℓ - 1), R⟫ = ⟪d, R⟫ - u * pp - u ^ 2 * pp - qq := by
    rw [hz]; simp only [iqR, irR, iRR]
    linear_combination (-(pp * u)) * hℓu
  refine ⟨R, ?_, ?_⟩
  · intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  refine k18_cone_cell (V8 a a' b b' c c' d) q r R d hΔ (k := 4) (by norm_num) (k22z1c3Y ℓ α4 γ4 β6)
    (k22z1c3Y_inj hℓ0 hα41 hγ4 (by nlinarith)) ?_ [(0, -1), (-γ4, -(α4 - 1) * ℓ)] (by simp) ?_ ?_ ?_
    (ρ1 := -1) (ρ2 := -1) (δ1 := 0) (δ2 := 0) ?_
  · intro i
    rcases k19_z4_cases i with rfl | rfl | rfl | rfl
    · rw [k22z1c3Y_0, Eb]; simp [V8]
    · rw [k22z1c3Y_1, Ea']; simp [V8]
    · rw [k22z1c3Y_2, Eb']; simp [V8]
    · rw [k22z1c3Y_3, Ec']; simp [V8]
  · intro v1 v2 hC D hD
    have h1 := hC (0, -1) (by simp)
    have h2 := hC (-γ4, -(α4 - 1) * ℓ) (by simp)
    simp only at h1 h2
    exact (k22z1c3_tsc hD hℓ0 hα41 hγ4 hβ6 (by linarith) (by nlinarith)).1
  · intro y hy hyx
    have hV : y = fpoint q r R d (-ℓ, 0, -ℓ) ∨ y = fpoint q r R d (-ℓ, 0, -ℓ - 1) ∨
        y = fpoint q r R d (1, 0, 0) ∨ y = fpoint q r R d (β6, 1, 0) ∨
        y = fpoint q r R d (-α4 * ℓ, γ4, -α4 * ℓ) ∨ y = fpoint q r R d (0, 0, 0) ∨
        y = fpoint q r R d (0, 1, 0) := by
      rw [Ea, Ed, Eb, Ea', Ec, Eb', Ec']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    have hT : ∀ v1 v2 : ℝ, k18Cone [(0, -1), (-γ4, -(α4 - 1) * ℓ)] v1 v2 → ∀ D : ℝ, 0 < D →
        ∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 1, 0), (-ℓ, 0, -ℓ)], ∀ i : ZMod 4,
          TSc D (k22z1c3Y ℓ α4 γ4 β6 (i + 1) - k22z1c3Y ℓ α4 γ4 β6 i) (t - k22z1c3Y ℓ α4 γ4 β6 i) (v1, v2, 0) := by
      intro v1 v2 hC D hD
      have h1 := hC (0, -1) (by simp)
      have h2 := hC (-γ4, -(α4 - 1) * ℓ) (by simp)
      simp only at h1 h2
      exact (k22z1c3_tsc hD hℓ0 hα41 hγ4 hβ6 (by linarith) (by nlinarith)).2
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
    · exact (hyx 3 (by rw [k22z1c3Y_3])).elim
    · exact (hyx 0 (by rw [k22z1c3Y_0])).elim
    · exact (hyx 1 (by rw [k22z1c3Y_1])).elim
    · exact (hyx 2 (by rw [k22z1c3Y_2])).elim
    · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
    · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
  · intro v1 v2 hC hw
    refine k22z1c3_uni _ _ hw ?_ ?_
    · simp only [k22z1c3Y_3, k22z1c3Y_0, zb, zc']; nlinarith [mul_pos hu0 hpp, mul_pos (mul_pos hu0 hu0) hpp]
    · simp only [k22z1c3Y_0, k22z1c3Y_1, k22z1c3Y_2, zb, za', zb']
      intro hle
      have h1 : 0 ≤ u * x + (β6 - 1) * qq := by linarith
      have h2 := mul_nonneg (sub_nonneg.2 hγ4.le) h1
      have h3 : β6 * γ4 * qq = (γ4 + α4 - 1) * qq := by rw [hβ6]
      have h4 := mul_pos (by linarith : 0 < α4) hS2
      nlinarith
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> (left; simp <;> nlinarith [mul_pos hℓ0 (sub_pos.2 hα41), hℓ0])

end C2
end Type08Sp
end Minimality
