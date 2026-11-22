module

public import Minimality.Type29Exact
public import Minimality.Chi29

@[expose] public section

/-!
# Type 29: symbolic front pairs for U023Q-exact (A18-REFEREE section 6)

`GenQuad.frontOf_of_scaled`; `NF29.mV`; vector identities `u023_vec_Q3/Q4/Q5/Q12`; `front_u023_Q1` .. `Q5`, `Q5`'`;
Chi29 bridges (`mV_eq_chi`, `eta3_eq_chi`, `eta5_eq_chi`, `h0256_iff_chi`, `hq_pos_eta`); payoff
`lexAny29_U023Qx`'` / `lexAny29_U023Qx8`'`: the five FrontOf hypotheses replaced by `h0 del2 < h2 del0` and the sign
of chi(0256).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.Gen Minimality.LexCell Minimality.H21 Minimality.H29

namespace Minimality.GenQuad

/-- `FrontOf` from a scaled (cleared-denominator) relation: witnesses `L/W`, `M/W`, `E/W`. -/
theorem frontOf_of_scaled {p q r s b : ℝ³} {W L M E : ℝ} (hW : 0 < W) (hL0 : 0 ≤ L) (hL1 : L ≤ W)
    (hM0 : 0 ≤ M) (hM1 : M ≤ W) (hE : 0 < E)
    (h : L • p + (W - L) • q = M • r + (W - M) • s + E • b) : FrontOf p q r s b := by
  refine ⟨L / W, M / W, E / W, div_nonneg hL0 hW.le, (div_le_one hW).2 hL1, div_nonneg hM0 hW.le,
    (div_le_one hW).2 hM1, div_pos hE hW, ?_⟩
  have h' := congrArg (fun v => W⁻¹ • v) h
  simp only [smul_add, smul_smul] at h'
  have hW0 : W ≠ 0 := hW.ne'
  have e1 : L / W = W⁻¹ * L := by rw [div_eq_inv_mul]
  have e2 : 1 - L / W = W⁻¹ * (W - L) := by field_simp
  have e3 : M / W = W⁻¹ * M := by rw [div_eq_inv_mul]
  have e4 : 1 - M / W = W⁻¹ * (W - M) := by field_simp
  have e5 : E / W = W⁻¹ * E := by rw [div_eq_inv_mul]
  rw [e2, e4, e1, e3, e5]
  exact h'

end Minimality.GenQuad

namespace Minimality.NF29

variable {x : Fin 7 → ℝ³}

/-- `mV = -V`; `chi_0245 = -D mV`. -/
noncomputable def mV (N : NF29 x) : ℝ := N.h2 * N.del0 - N.h0 * N.del2

theorem DG4_sub_DG5 (N : NF29 x) : N.DG4 - N.DG5 = N.dG4 - N.dG := by
  unfold DG4 DG5; ring

theorem u023_vec_Q3 (N : NF29 x) :
    (N.h0 * (N.DG4 - N.D023)) • x 2 + ((N.h2 * N.DG4 - N.h0 * N.D023) - N.h0 * (N.DG4 - N.D023)) • x 6 =
      (N.h2 * (N.DG4 - N.D023)) • x 0 +
        ((N.h2 * N.DG4 - N.h0 * N.D023) - N.h2 * (N.DG4 - N.D023)) • x 4 +
        (N.P5 * (N.s + N.t - 1) + N.mV * N.t) • N.u23Q x := by
  dsimp only [u23Q, mV, P5, del0, del2, DG4, D023, D02, dG, dG4]
  nf29_vec N

theorem u023_vec_Q4 (N : NF29 x) :
    (N.h0 * (N.dG4 - N.dG)) • x 2 + ((N.h2 * N.DG4 - N.h0 * N.DG5) - N.h0 * (N.dG4 - N.dG)) • x 5 =
      (N.h2 * (N.dG4 - N.dG)) • x 0 +
        ((N.h2 * N.DG4 - N.h0 * N.DG5) - N.h2 * (N.dG4 - N.dG)) • x 4 + N.mV • N.u23Q x := by
  dsimp only [u23Q, mV, del0, del2, DG4, DG5, D02, dG, dG4]
  nf29_vec N

theorem u023_vec_Q5 (N : NF29 x) :
    (N.h0 * (N.D023 - N.DG5)) • x 2 + ((N.h2 * N.D023 - N.h0 * N.DG5) - N.h0 * (N.D023 - N.DG5)) • x 5 =
      (N.h2 * (N.D023 - N.DG5)) • x 0 +
        ((N.h2 * N.D023 - N.h0 * N.DG5) - N.h2 * (N.D023 - N.DG5)) • x 6 +
        (N.mV * N.s - N.P4 * (N.s + N.t - 1)) • N.u23Q x := by
  dsimp only [u23Q, mV, P4, del0, del2, DG5, D023, D02, dG, dG4]
  nf29_vec N

theorem u023_vec_Q12 (N : NF29 x) :
    (N.dG4 - N.dG) • x 6 = (N.D023 - N.DG5) • x 4 + (N.DG4 - N.D023) • x 5 +
      (N.s + N.t - 1) • N.u23Q x := by
  dsimp only [u23Q, DG4, DG5, D023, D02, dG, dG4]
  nf29_vec N

theorem DG4_pos (N : NF29 x) : 0 < N.DG4 := by unfold DG4 D02 dG4; linarith [N.hDG4]
theorem DG5_pos (N : NF29 x) : 0 < N.DG5 := by unfold DG5 D02 dG; linarith [N.hDG5]
theorem D023_pos (N : NF29 x) : 0 < N.D023 := by unfold D023 D02 dG dG4; linarith [N.d023]

private theorem mV_pos (N : NF29 x) (hq : N.h0 * N.del2 < N.h2 * N.del0) : 0 < N.mV := by
  unfold mV; linarith

theorem front_u023_Q1 (N : NF29 x) (h4 : 0 < N.D023 - N.DG5) (h5 : 0 < N.DG4 - N.D023) :
    GenQuad.FrontOf (x 2) (x 6) (x 4) (x 5) (N.u23Q x) := by
  have hW : 0 < N.dG4 - N.dG := by linarith [DG4_sub_DG5 N]
  refine GenQuad.frontOf_of_scaled (W := N.dG4 - N.dG) (L := 0) (M := N.D023 - N.DG5) (E := N.s + N.t - 1)
    hW le_rfl hW.le h4.le (by linarith [DG4_sub_DG5 N]) (by linarith [N.hst]) ?_
  have := u023_vec_Q12 N
  rw [zero_smul, zero_add, sub_zero, this]
  have e : N.dG4 - N.dG - (N.D023 - N.DG5) = N.DG4 - N.D023 := by unfold DG4 DG5; ring
  rw [e]

theorem front_u023_Q2 (N : NF29 x) (h4 : 0 < N.D023 - N.DG5) (h5 : 0 < N.DG4 - N.D023) :
    GenQuad.FrontOf (x 0) (x 6) (x 4) (x 5) (N.u23Q x) := by
  have hW : 0 < N.dG4 - N.dG := by linarith [DG4_sub_DG5 N]
  refine GenQuad.frontOf_of_scaled (W := N.dG4 - N.dG) (L := 0) (M := N.D023 - N.DG5) (E := N.s + N.t - 1)
    hW le_rfl hW.le h4.le (by linarith [DG4_sub_DG5 N]) (by linarith [N.hst]) ?_
  have := u023_vec_Q12 N
  rw [zero_smul, zero_add, sub_zero, this]
  have e : N.dG4 - N.dG - (N.D023 - N.DG5) = N.DG4 - N.D023 := by unfold DG4 DG5; ring
  rw [e]

theorem front_u023_Q3 (N : NF29 x) (hh0 : N.h0 < 1) (hh2 : 1 ≤ N.h2) (h5 : 0 < N.DG4 - N.D023)
    (hq : N.h0 * N.del2 < N.h2 * N.del0) :
    GenQuad.FrontOf (x 2) (x 6) (x 0) (x 4) (N.u23Q x) := by
  have hP5 : 0 < N.P5 := by unfold P5; linarith [N.hF4]
  have hS : 0 < N.s + N.t - 1 := by linarith [N.hst]
  have hm := mV_pos N hq
  have h02 : 0 < N.h2 - N.h0 := by linarith
  have h1 := mul_pos h02 N.DG4_pos
  have h2' := mul_pos h02 N.D023_pos
  have hm0 := mul_pos N.hh0 h5
  have hm2 := mul_pos N.hh2 h5
  have eW1 : (N.h2 * N.DG4 - N.h0 * N.D023) - N.h0 * (N.DG4 - N.D023) = (N.h2 - N.h0) * N.DG4 := by ring
  have eW2 : (N.h2 * N.DG4 - N.h0 * N.D023) - N.h2 * (N.DG4 - N.D023) = (N.h2 - N.h0) * N.D023 := by ring
  refine GenQuad.frontOf_of_scaled (W := N.h2 * N.DG4 - N.h0 * N.D023) (L := N.h0 * (N.DG4 - N.D023))
    (M := N.h2 * (N.DG4 - N.D023)) (E := N.P5 * (N.s + N.t - 1) + N.mV * N.t)
    (by linarith) hm0.le (by linarith) hm2.le (by linarith) (by nlinarith [mul_pos hP5 hS, mul_pos hm N.ht])
    (u023_vec_Q3 N)

theorem front_u023_Q4 (N : NF29 x) (hh0 : N.h0 < 1) (hh2 : 1 ≤ N.h2) (h4 : 0 < N.D023 - N.DG5)
    (h5 : 0 < N.DG4 - N.D023) (hq : N.h0 * N.del2 < N.h2 * N.del0) :
    GenQuad.FrontOf (x 2) (x 5) (x 0) (x 4) (N.u23Q x) := by
  have hm := mV_pos N hq
  have hd : 0 < N.dG4 - N.dG := by linarith [DG4_sub_DG5 N]
  have h02 : 0 < N.h2 - N.h0 := by linarith
  have h1 := mul_pos h02 N.DG4_pos
  have h2' := mul_pos h02 N.DG5_pos
  have hm0 := mul_pos N.hh0 hd
  have hm2 := mul_pos N.hh2 hd
  have eW1 : (N.h2 * N.DG4 - N.h0 * N.DG5) - N.h0 * (N.dG4 - N.dG) = (N.h2 - N.h0) * N.DG4 := by
    have := DG4_sub_DG5 N; linear_combination N.h0 * this
  have eW2 : (N.h2 * N.DG4 - N.h0 * N.DG5) - N.h2 * (N.dG4 - N.dG) = (N.h2 - N.h0) * N.DG5 := by
    have := DG4_sub_DG5 N; linear_combination N.h2 * this
  refine GenQuad.frontOf_of_scaled (W := N.h2 * N.DG4 - N.h0 * N.DG5) (L := N.h0 * (N.dG4 - N.dG))
    (M := N.h2 * (N.dG4 - N.dG)) (E := N.mV) (by linarith) hm0.le
    (by linarith) hm2.le (by linarith) hm (u023_vec_Q4 N)

theorem front_u023_Q5 (N : NF29 x) (hh0 : N.h0 < 1) (hh2 : 1 ≤ N.h2) (h4 : 0 < N.D023 - N.DG5)
    (h0256 : 0 < N.mV * N.s - N.P4 * (N.s + N.t - 1)) :
    GenQuad.FrontOf (x 2) (x 5) (x 0) (x 6) (N.u23Q x) := by
  have h02 : 0 < N.h2 - N.h0 := by linarith
  have h1 := mul_pos h02 N.D023_pos
  have h2' := mul_pos h02 N.DG5_pos
  have hm0 := mul_pos N.hh0 h4
  have hm2 := mul_pos N.hh2 h4
  have eW1 : (N.h2 * N.D023 - N.h0 * N.DG5) - N.h0 * (N.D023 - N.DG5) = (N.h2 - N.h0) * N.D023 := by ring
  have eW2 : (N.h2 * N.D023 - N.h0 * N.DG5) - N.h2 * (N.D023 - N.DG5) = (N.h2 - N.h0) * N.DG5 := by ring
  refine GenQuad.frontOf_of_scaled (W := N.h2 * N.D023 - N.h0 * N.DG5) (L := N.h0 * (N.D023 - N.DG5))
    (M := N.h2 * (N.D023 - N.DG5)) (E := N.mV * N.s - N.P4 * (N.s + N.t - 1)) (by linarith) hm0.le
    (by linarith) hm2.le (by linarith) h0256 (u023_vec_Q5 N)

theorem front_u023_Q5' (N : NF29 x) (hh0 : N.h0 < 1) (hh2 : 1 ≤ N.h2) (h4 : 0 < N.D023 - N.DG5)
    (h0256' : N.mV * N.s - N.P4 * (N.s + N.t - 1) < 0) :
    GenQuad.FrontOf (x 0) (x 6) (x 2) (x 5) (N.u23Q x) := by
  have h02 : 0 < N.h2 - N.h0 := by linarith
  have h1 := mul_pos h02 N.D023_pos
  have h2' := mul_pos h02 N.DG5_pos
  have hm0 := mul_pos N.hh0 h4
  have hm2 := mul_pos N.hh2 h4
  have eW1 : (N.h2 * N.D023 - N.h0 * N.DG5) - N.h0 * (N.D023 - N.DG5) = (N.h2 - N.h0) * N.D023 := by ring
  have eW2 : (N.h2 * N.D023 - N.h0 * N.DG5) - N.h2 * (N.D023 - N.DG5) = (N.h2 - N.h0) * N.DG5 := by ring
  refine GenQuad.frontOf_of_scaled (W := N.h2 * N.D023 - N.h0 * N.DG5) (L := N.h2 * (N.D023 - N.DG5))
    (M := N.h0 * (N.D023 - N.DG5)) (E := -(N.mV * N.s - N.P4 * (N.s + N.t - 1))) (by linarith) hm2.le
    (by linarith) hm0.le (by linarith) (by linarith) ?_
  have := u023_vec_Q5 N
  linear_combination (norm := module) (-1 : ℝ) • this


/-! ## Chi29 forms -/

theorem mV_eq_chi (N : NF29 x) :
    N.mV = -(((-1 : ℝ)) * N.h2 + ((1 : ℝ)) * N.h0 + ((-1 : ℝ)) * N.h0 * N.b2 + ((-1 : ℝ)) * N.h0 * N.a2 + ((1 : ℝ)) * N.b0 * N.h2 + ((1 : ℝ)) * N.a0 * N.h2) := by
  unfold mV del0 del2; ring

theorem eta3_eq_chi (N : NF29 x) :
    N.P5 * (N.s + N.t - 1) + N.mV * N.t = -(((-1 : ℝ)) * N.h2 * N.t + ((1 : ℝ)) * N.h0 * N.t + ((-1 : ℝ)) * N.h0 * N.b2 + ((1 : ℝ)) * N.h0 * N.b2 * N.s + ((-1 : ℝ)) * N.h0 * N.a2 * N.t + ((1 : ℝ)) * N.b0 * N.h2 + ((-1 : ℝ)) * N.b0 * N.h2 * N.s + ((1 : ℝ)) * N.a0 * N.h2 * N.t) := by
  unfold mV del0 del2 P5; ring

theorem eta5_eq_chi (N : NF29 x) :
    N.mV * N.s - N.P4 * (N.s + N.t - 1) = ((1 : ℝ)) * N.h2 * N.s + ((-1 : ℝ)) * N.h0 * N.s + ((1 : ℝ)) * N.h0 * N.b2 * N.s + ((1 : ℝ)) * N.h0 * N.a2 + ((-1 : ℝ)) * N.h0 * N.a2 * N.t + ((-1 : ℝ)) * N.b0 * N.h2 * N.s + ((-1 : ℝ)) * N.a0 * N.h2 + ((1 : ℝ)) * N.a0 * N.h2 * N.t := by
  unfold mV del0 del2 P4; ring

/-- `h0256` as a sign of the chirotope entry `chi(0256)`. -/
theorem h0256_iff_chi (N : NF29 x) :
    0 < N.mV * N.s - N.P4 * (N.s + N.t - 1) ↔ 0 < N.D * Split.det3 (x 2 - x 0) (x 5 - x 0) (x 6 - x 0) := by
  rw [chi_0256_eq N, eta5_eq_chi N, ← mul_assoc, ← sq]
  exact (mul_pos_iff_of_pos_left (D_sq_pos N)).symm

/-- `hq` gives the signs of `chi(0245)` and `chi(0246)` (`Chi29`) and the numerators of `eta3`, `eta4`. -/
theorem hq_pos_eta (N : NF29 x) (hq : N.h0 * N.del2 < N.h2 * N.del0) :
    0 < N.mV ∧ 0 < N.P5 * (N.s + N.t - 1) + N.mV * N.t := by
  have h1 := chi_0245_sign N hq
  have h2 := chi_0246_sign N hq
  rw [chi_0245_eq N] at h1
  rw [chi_0246_eq N] at h2
  have hD := D_sq_pos N
  rw [← mul_assoc, ← sq] at h1 h2
  refine ⟨?_, ?_⟩
  · rw [mV_eq_chi N]; nlinarith
  · rw [eta3_eq_chi N]; nlinarith

theorem lexAny29_U023Qx' (N : NF29 x)
    (hdG : N.dG < 0) (hdG4 : 0 < N.dG4) (hh0 : N.h0 < 1) (hE35 : N.E35 < 0)
    (hK : 0 < (-N.dG) * N.P5 + N.dG4 * N.P4) (hh2 : 1 ≤ N.h2)
    (h4 : 0 < N.D023 - N.DG5) (h5 : 0 < N.DG4 - N.D023)
    (hq : N.h0 * N.del2 < N.h2 * N.del0)
    (h0256 : 0 < N.mV * N.s - N.P4 * (N.s + N.t - 1))
    (m0246 : ¬ (⟪x 0 - x 6, N.u23Q x⟫ ≤ ⟪x 2 - x 6, N.u23Q x⟫ ∧ ⟪x 0 - x 6, N.u23Q x⟫ ≤ 0 ∧
                ⟪x 4 - x 6, N.u23Q x⟫ ≤ ⟪x 2 - x 6, N.u23Q x⟫ ∧ ⟪x 4 - x 6, N.u23Q x⟫ ≤ 0))
    (m0245 : ¬ (⟪x 0 - x 6, N.u23Q x⟫ ≤ ⟪x 2 - x 6, N.u23Q x⟫ ∧ ⟪x 0 - x 6, N.u23Q x⟫ ≤ ⟪x 5 - x 6, N.u23Q x⟫ ∧
                ⟪x 4 - x 6, N.u23Q x⟫ ≤ ⟪x 2 - x 6, N.u23Q x⟫ ∧ ⟪x 4 - x 6, N.u23Q x⟫ ≤ ⟪x 5 - x 6, N.u23Q x⟫))
    (m0265 : ¬ (0 ≤ ⟪x 2 - x 6, N.u23Q x⟫ ∧ 0 ≤ ⟪x 5 - x 6, N.u23Q x⟫ ∧
                ⟪x 0 - x 6, N.u23Q x⟫ ≤ ⟪x 2 - x 6, N.u23Q x⟫ ∧ ⟪x 0 - x 6, N.u23Q x⟫ ≤ ⟪x 5 - x 6, N.u23Q x⟫))
    (m0465 : ¬ (⟪x 4 - x 6, N.u23Q x⟫ ≤ ⟪x 0 - x 6, N.u23Q x⟫ ∧ ⟪x 4 - x 6, N.u23Q x⟫ ≤ 0 ∧
                ⟪x 5 - x 6, N.u23Q x⟫ ≤ ⟪x 0 - x 6, N.u23Q x⟫ ∧ ⟪x 5 - x 6, N.u23Q x⟫ ≤ 0))
    (m2465 : ¬ (⟪x 4 - x 6, N.u23Q x⟫ ≤ ⟪x 2 - x 6, N.u23Q x⟫ ∧ ⟪x 4 - x 6, N.u23Q x⟫ ≤ 0 ∧
                ⟪x 5 - x 6, N.u23Q x⟫ ≤ ⟪x 2 - x 6, N.u23Q x⟫ ∧ ⟪x 5 - x 6, N.u23Q x⟫ ≤ 0)) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by
  exact lexAny29_U023Qx N hdG hdG4 hh0 hE35 hK hh2 h4 h5
    (front_u023_Q3 N hh0 hh2 h5 hq) (front_u023_Q4 N hh0 hh2 h4 h5 hq)
    (front_u023_Q5 N hh0 hh2 h4 h0256) (front_u023_Q2 N h4 h5) (front_u023_Q1 N h4 h5) m0246 m0245 m0265 m0465 m2465

theorem lexAny29_U023Qx8' (N : NF29 x)
    (hdG : N.dG < 0) (hdG4 : 0 < N.dG4) (hh0 : N.h0 < 1) (hE35 : N.E35 < 0)
    (hK : 0 < (-N.dG) * N.P5 + N.dG4 * N.P4) (hh2 : 1 ≤ N.h2)
    (h4 : 0 < N.D023 - N.DG5) (h5 : 0 < N.DG4 - N.D023)
    (hq : N.h0 * N.del2 < N.h2 * N.del0)
    (h0256' : N.mV * N.s - N.P4 * (N.s + N.t - 1) < 0)
    (m0246 : ¬ (⟪x 0 - x 6, N.u23Q x⟫ ≤ ⟪x 2 - x 6, N.u23Q x⟫ ∧ ⟪x 0 - x 6, N.u23Q x⟫ ≤ 0 ∧
                ⟪x 4 - x 6, N.u23Q x⟫ ≤ ⟪x 2 - x 6, N.u23Q x⟫ ∧ ⟪x 4 - x 6, N.u23Q x⟫ ≤ 0))
    (m0245 : ¬ (⟪x 0 - x 6, N.u23Q x⟫ ≤ ⟪x 2 - x 6, N.u23Q x⟫ ∧ ⟪x 0 - x 6, N.u23Q x⟫ ≤ ⟪x 5 - x 6, N.u23Q x⟫ ∧
                ⟪x 4 - x 6, N.u23Q x⟫ ≤ ⟪x 2 - x 6, N.u23Q x⟫ ∧ ⟪x 4 - x 6, N.u23Q x⟫ ≤ ⟪x 5 - x 6, N.u23Q x⟫))
    (m0265 : ¬ (⟪x 2 - x 6, N.u23Q x⟫ ≤ ⟪x 0 - x 6, N.u23Q x⟫ ∧ ⟪x 2 - x 6, N.u23Q x⟫ ≤ 0 ∧
                ⟪x 5 - x 6, N.u23Q x⟫ ≤ ⟪x 0 - x 6, N.u23Q x⟫ ∧ ⟪x 5 - x 6, N.u23Q x⟫ ≤ 0))
    (m0465 : ¬ (⟪x 4 - x 6, N.u23Q x⟫ ≤ ⟪x 0 - x 6, N.u23Q x⟫ ∧ ⟪x 4 - x 6, N.u23Q x⟫ ≤ 0 ∧
                ⟪x 5 - x 6, N.u23Q x⟫ ≤ ⟪x 0 - x 6, N.u23Q x⟫ ∧ ⟪x 5 - x 6, N.u23Q x⟫ ≤ 0))
    (m2465 : ¬ (⟪x 4 - x 6, N.u23Q x⟫ ≤ ⟪x 2 - x 6, N.u23Q x⟫ ∧ ⟪x 4 - x 6, N.u23Q x⟫ ≤ 0 ∧
                ⟪x 5 - x 6, N.u23Q x⟫ ≤ ⟪x 2 - x 6, N.u23Q x⟫ ∧ ⟪x 5 - x 6, N.u23Q x⟫ ≤ 0)) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by
  exact lexAny29_U023Qx8 N hdG hdG4 hh0 hE35 hK hh2 h4 h5
    (front_u023_Q3 N hh0 hh2 h5 hq) (front_u023_Q4 N hh0 hh2 h4 h5 hq)
    (front_u023_Q5' N hh0 hh2 h4 h0256') (front_u023_Q2 N h4 h5) (front_u023_Q1 N h4 h5) m0246 m0245 m0265 m0465 m2465

end Minimality.NF29
