module

public import Minimality.Type29CellII45

@[expose] public section

/-!
# Type 29, `K1a ∩ G* ∩ Cell II`, Task L46 (`A46`)

The proved parts of `A46` (`k1c/a46/A46.md`, Lean spec `L46-1 … L46-9`).

* `L46-1` `l46_rw34`: the `w34` Radon identity `RW34` (ring, every view `u`), with `c1 = Phi - V` (`l46_c1_eq`).
* `L46-2` `l46_phi_KY` / `l46_phi_pos`: `del2 C35 Phi = (C35 - A35) K_Y + (-A35)(h2 - h0) del2 D035`, so `Phi > 0` on `K_Y ≥ 0`.
* `L46-3`, `L46-4` `l46_order_56`, `l46_order_20`: the pure order lemmas on the 5-rims `(0,2,4,6,5)`, `(0,2,3,6,5)`.
* `L46-5`, `L46-6` `l46_w34_56_nonneg`, `l46_z20_nonneg`; `L46-7` `RimStepW34` (hypothesis) and
  `l46_w34Rows`: `W34Rows` of `Type29CellII45` holds on `K_Y ≥ 0` under the rim step.
* `L46-8` `l46_c5_forms` (`U4`, `U5`, `Del`, `U4 D234 - U5 P2`, `U4 F55' + m U5`, `-F55'`, `v4 + v5`, the `P`, `Rq`,
  `Q5neg` forms).
* `L46-9` `l46_cert_C5_false` (`m ≥ 0`, or `m < 0` with `P5 ≤ P4`) and `l46_cert_C5_res_false` (`F55' < 0` as a named
  hypothesis, CENSUS on `{m < 0, P5 > P4}`).

Not here (census only): `C5-` with `P5 > P4` as a theorem, `C2` (`L46-10`), `C1 / C3 / C4`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.Gen Minimality.GenQuad Minimality.LexCell Minimality.H21 Minimality.H29

namespace Minimality.NF29

/-! ## Definitions -/

/-- A 5-cycle of reals. -/
def rim5w (a b c d e : ℝ) : ZMod 5 → ℝ := ![a, b, c, d, e]

namespace L42P

variable (p : L42P)

/-- `Phi = h0 P2 - h2 D035`. -/
abbrev Phi : ℝ := p.h0 * p.P2 - p.h2 * p.D035
/-- `c1 = h2 P0 - h0 D234 - (h2 - h0) S` (`= Phi - V`). -/
abbrev c1 : ℝ := p.h2 * p.P0 - p.h0 * p.D234 - (p.h2 - p.h0) * p.S
/-- `Del = S (h2 - h0) D0 (= U4 v5 - U5 v4)`. -/
abbrev Del : ℝ := p.S * (p.h2 - p.h0) * p.D0
/-- `m = (-v4) U4 (P2 c1 + D234 Phi) - P2 Phi Del`. -/
abbrev mC5 : ℝ := (-p.v4) * p.U4 * (p.P2 * p.c1 + p.D234 * p.Phi) - p.P2 * p.Phi * p.Del
/-- `F55' = Phi U4 D234 v5 - P2 (-v4) c1 U5`. -/
abbrev F55p : ℝ := p.Phi * p.U4 * p.D234 * p.v5 - p.P2 * (-p.v4) * p.c1 * p.U5

/-- Depths at `w34 = (-1, 1, 0)` of `x0, x2, x3, x4, x5` (with `x6 = 0`): `z_i = ⟪x_i, G w34⟫`. -/
noncomputable abbrev zw0 : ℝ := p.rowv p.D035 p.P0 p.h0 (-1) 1 0 / p.S
noncomputable abbrev zw2 : ℝ := p.rowv p.P2 p.D234 p.h2 (-1) 1 0 / p.S
abbrev zw3 : ℝ := p.ge3 (-1) 1 0
abbrev zw4 : ℝ := p.ge4 (-1) 1 0
abbrev zw5 : ℝ := p.ge5 (-1) 1 0

end L42P

/-- **L46-7** (hypothesis form): if all four rims at `w34` fail, then the tilt rims `(0,2,4,6,5)` (tilt `234-, 346-`) and
`(0,2,3,6,5)` (tilt `234+, 346+`) are not robustly unimodal (not `LexAny29`, as at `v14`, `u35`, `vQ`). -/
def RimStepW34 (p : L42P) (allRimsFail : Prop) : Prop :=
  allRimsFail → ¬ RobUni (rim5w p.zw0 p.zw2 p.zw4 0 p.zw5) ∧ ¬ RobUni (rim5w p.zw0 p.zw2 p.zw3 0 p.zw5)

variable (p : L42P)

/-! ## L46-1, L46-2 -/

/-- `c1 = Phi - V` (ring in `a0 … t`). -/
theorem l46_c1_eq : p.c1 = p.Phi - p.V := by
  simp only [L42P.c1, L42P.Phi, L41P.V, L41P.S, L42P.P0, L42P.P2, L42P.D234, L42P.D035, P0_sp, P2_sp, D234_sp,
    D035_sp, S_sp]
  ring

/-- **L46-1** (`RW34`): the affine dependency of `x0, x2, x4, x5, x6` at every view `u`, dotted with `G u`. -/
theorem l46_rw34 (u3 u4 u5 : ℝ) :
    p.h0 * (p.rowv p.D035 p.P0 p.h0 u3 u4 u5 - p.rowv p.P2 p.D234 p.h2 u3 u4 u5) +
      (p.h2 - p.h0) * (p.rowv p.D035 p.P0 p.h0 u3 u4 u5 - p.S * p.ge5 u3 u4 u5) -
      (p.Phi - p.V) * p.ge5 u3 u4 u5 + p.Phi * p.ge4 u3 u4 u5 = 0 := by
  rw [← l46_c1_eq p]
  simp only [L42P.rowv, L42P.ge3, L42P.ge4, L42P.ge5, L42P.c1, L42P.Phi]
  ring

/-- **L46-2** (`phi_KY_identity`). -/
theorem l46_phi_KY : p.del2 * p.C35 * p.Phi =
    (p.C35 - A35_sp p.a0 p.b0 p.h0 p.a2 p.b2 p.h2) * p.KY +
      (-A35_sp p.a0 p.b0 p.h0 p.a2 p.b2 p.h2) * (p.h2 - p.h0) * p.del2 * p.D035 := by
  simp only [L42P.Phi, L42P.KY, L42P.C35, L42P.del2, L42P.P2, L42P.D035, KY_sp, L_sp, C35_sp, A35_sp, DG4_sp,
    D0_sp, G4_sp, P2_sp, D035_sp]
  ring

/-- **L46-2** (`phi_pos`): `Phi > 0` on `K_Y ≥ 0`. -/
theorem l46_phi_pos (hKY : 0 ≤ p.KY) (hC : 0 < p.C35) (hA : A35_sp p.a0 p.b0 p.h0 p.a2 p.b2 p.h2 < 0)
    (hd : 0 < p.del2) (hD : 0 < p.D035) (hh : p.h0 < p.h2) : 0 < p.Phi := by
  have h := l46_phi_KY p
  have h1 : 0 ≤ (p.C35 - A35_sp p.a0 p.b0 p.h0 p.a2 p.b2 p.h2) * p.KY :=
    mul_nonneg (by linarith) hKY
  have h2 : 0 < (-A35_sp p.a0 p.b0 p.h0 p.a2 p.b2 p.h2) * (p.h2 - p.h0) * p.del2 * p.D035 :=
    mul_pos (mul_pos (mul_pos (by linarith) (by linarith)) hd) hD
  have h3 : 0 < p.del2 * p.C35 * p.Phi := by linarith
  by_contra hn
  push Not at hn
  have := mul_nonpos_of_nonneg_of_nonpos (mul_pos hd hC).le hn
  linarith

/-! ## L46-3, L46-4: the pure order lemmas -/

/-- **L46-3**: `z4 > 0 = z6`, `z5 < 0` and a failing rim `(z0, z2, z4, 0, z5)` force `z2 ≤ z0` and `z5 ≤ z0`. -/
theorem l46_order_56 {z0 z2 z4 z5 : ℝ} (h4 : 0 < z4) (h5 : z5 < 0)
    (h : ¬ RobUni (rim5w z0 z2 z4 0 z5)) : z2 ≤ z0 ∧ z5 ≤ z0 := by
  simp only [RobUni, rim5w, not_forall, not_not] at h
  obtain ⟨B, b, c, d, hb, hbc, hcd, hd, e1, e2, e3, e4⟩ := h
  have hb2 : b ≤ 2 := by omega
  have hc3 : c ≤ 3 := by omega
  interval_cases b <;> interval_cases c <;> interval_cases d
  all_goals
    have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := zmod5_all B
    rcases hB with rfl | rfl | rfl | rfl | rfl <;> norm_num [Fin.isValue] at e1 e2 e3 e4 <;>
      exact ⟨by linarith, by linarith⟩

/-- **L46-4**: `z3 < 0 = z6`, `z2 < z0` and a failing rim `(z0, z2, z3, 0, z5)` force `z5 ≤ z0` and `z5 ≤ 0`. -/
theorem l46_order_20 {z0 z2 z3 z5 : ℝ} (h3 : z3 < 0) (h20 : z2 < z0)
    (h : ¬ RobUni (rim5w z0 z2 z3 0 z5)) : z5 ≤ z0 ∧ z5 ≤ 0 := by
  simp only [RobUni, rim5w, not_forall, not_not] at h
  obtain ⟨B, b, c, d, hb, hbc, hcd, hd, e1, e2, e3, e4⟩ := h
  have hb2 : b ≤ 2 := by omega
  have hc3 : c ≤ 3 := by omega
  interval_cases b <;> interval_cases c <;> interval_cases d
  all_goals
    have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := zmod5_all B
    rcases hB with rfl | rfl | rfl | rfl | rfl <;> norm_num [Fin.isValue] at e1 e2 e3 e4 <;>
      exact ⟨by linarith, by linarith⟩

/-! ## L46-5, L46-6, L46-7: the `w34` rows -/

theorem l46_rowv0 (hS : 0 < p.S) : p.rowv p.D035 p.P0 p.h0 (-1) 1 0 = p.S * p.zw0 := by
  simp only [L42P.zw0]; field_simp

theorem l46_rowv2 (hS : 0 < p.S) : p.rowv p.P2 p.D234 p.h2 (-1) 1 0 = p.S * p.zw2 := by
  simp only [L42P.zw2]; field_simp

/-- `Z20w = S (z2 - z0)(w34)`. -/
theorem l46_Z20w_eq (hS : 0 < p.S) : p.Z20w = p.S * (p.zw2 - p.zw0) := by
  rw [mul_sub, ← l46_rowv0 p hS, ← l46_rowv2 p hS]
  simp only [L42P.Z20w, L42P.rowv]; ring

/-- `RW34` at `u = w34` in the depths `z_i`: `S h0 (z0 - z2) + S (h2 - h0)(z0 - z5) - (Phi - V) z5 + Phi z4 = 0`. -/
theorem l46_rw34_z (hS : 0 < p.S) :
    p.S * p.h0 * (p.zw0 - p.zw2) + p.S * (p.h2 - p.h0) * (p.zw0 - p.zw5) - (p.Phi - p.V) * p.zw5 +
      p.Phi * p.zw4 = 0 := by
  have e := l46_rw34 p (-1) 1 0
  rw [l46_rowv0 p hS, l46_rowv2 p hS] at e
  linear_combination e

/-- **L46-5**: `W34_56 = z5(w34) ≥ 0` from the rim `(0,2,4,6,5)`. -/
theorem l46_w34_56_nonneg (hS : 0 < p.S) (hh0 : 0 < p.h0) (hh : p.h0 < p.h2) (hV : p.V < 0) (hPhi : 0 < p.Phi)
    (hG44 : 0 < p.G44) (hg34 : p.g34 ≤ 0) (hrim : ¬ RobUni (rim5w p.zw0 p.zw2 p.zw4 0 p.zw5)) :
    0 ≤ p.W34_56 := by
  by_contra hn
  push Not at hn
  have h5 : p.zw5 < 0 := hn
  have h4 : 0 < p.zw4 := by simp only [L42P.zw4, L42P.ge4]; linarith
  obtain ⟨h20, h50⟩ := l46_order_56 h4 h5 hrim
  have e := l46_rw34_z p hS
  have t1 := mul_nonneg (mul_nonneg hS.le hh0.le) (sub_nonneg.2 h20)
  have t2 := mul_nonneg (mul_nonneg hS.le (sub_nonneg.2 hh.le)) (sub_nonneg.2 h50)
  have t3 := mul_pos (show 0 < p.Phi - p.V by linarith) (neg_pos.2 h5)
  have t4 := mul_pos hPhi h4
  nlinarith

/-- **L46-6**: `Z20w = S (z2 - z0)(w34) ≥ 0` from the rim `(0,2,3,6,5)`. -/
theorem l46_z20_nonneg (hS : 0 < p.S) (hh0 : 0 < p.h0) (hh : p.h0 < p.h2) (hV : p.V < 0) (hPhi : 0 < p.Phi)
    (hG33 : 0 < p.G33) (hG44 : 0 < p.G44) (hg34 : p.g34 ≤ 0)
    (hrim : ¬ RobUni (rim5w p.zw0 p.zw2 p.zw3 0 p.zw5)) : 0 ≤ p.Z20w := by
  by_contra hn
  push Not at hn
  rw [l46_Z20w_eq p hS] at hn
  have h20 : p.zw2 < p.zw0 := by
    by_contra hc
    push Not at hc
    have := mul_nonneg hS.le (sub_nonneg.2 hc)
    linarith
  have h3 : p.zw3 < 0 := by simp only [L42P.zw3, L42P.ge3]; linarith
  have h4 : 0 < p.zw4 := by simp only [L42P.zw4, L42P.ge4]; linarith
  obtain ⟨h50, h5⟩ := l46_order_20 h3 h20 hrim
  have e := l46_rw34_z p hS
  have t1 := mul_pos (mul_pos hS hh0) (sub_pos.2 h20)
  have t2 := mul_nonneg (mul_nonneg hS.le (sub_nonneg.2 hh.le)) (sub_nonneg.2 h50)
  have t3 := mul_nonneg (show 0 ≤ p.Phi - p.V by linarith) (neg_nonneg.2 h5)
  have t4 := mul_pos hPhi h4
  nlinarith

/-- **L46-7**: `W34Rows` (`Type29CellII45`) on `K_Y ≥ 0`, given the rim step at `w34`. -/
theorem l46_w34Rows (allRimsFail : Prop) (hS : 0 < p.S) (hh0 : 0 < p.h0) (hh : p.h0 < p.h2) (hV : p.V < 0)
    (hKY : 0 ≤ p.KY) (hC : 0 < p.C35) (hA : A35_sp p.a0 p.b0 p.h0 p.a2 p.b2 p.h2 < 0) (hd : 0 < p.del2)
    (hD : 0 < p.D035) (hG33 : 0 < p.G33) (hG44 : 0 < p.G44) (hg34 : p.g34 ≤ 0)
    (hstep : RimStepW34 p allRimsFail) : W34Rows p allRimsFail := by
  have hPhi := l46_phi_pos p hKY hC hA hd hD hh
  intro hf
  obtain ⟨r1, r2⟩ := hstep hf
  exact ⟨l46_w34_56_nonneg p hS hh0 hh hV hPhi hG44 hg34 r1,
    l46_z20_nonneg p hS hh0 hh hV hPhi hG33 hG44 hg34 r2⟩

/-! ## L46-8: the forms and identities of cell `C5-` -/

/-- `U4 = (1 - h0) P2 + (h2 - 1) D035`. -/
theorem l46_U4_eq : p.U4 = (1 - p.h0) * p.P2 + (p.h2 - 1) * p.D035 := by
  simp only [L41P.U4, U4_sp, L42P.P2, L42P.D035, D023_sp, DG5_sp, D0_sp, G4_sp, G5_sp, P2_sp, D035_sp]
  ring

/-- `U5 = (1 - h0) D234 + (h2 - 1) P0`. -/
theorem l46_U5_eq : p.U5 = (1 - p.h0) * p.D234 + (p.h2 - 1) * p.P0 := by
  simp only [L41P.U5, U5_sp, L42P.D234, L42P.P0, D023_sp, DG4_sp, D0_sp, G4_sp, G5_sp, D234_sp, P0_sp]
  ring

/-- `U4 v5 - U5 v4 = Del`. -/
theorem l46_Del_eq : p.U4 * p.v5 - p.U5 * p.v4 = p.Del := by
  simp only [L41P.U4, L41P.U5, L42P.v4, L42P.v5, L42P.Del, L41P.S, L41P.D0, U4_sp, U5_sp, v4_sp, v5_sp, D023_sp,
    DG5_sp, DG4_sp, D0_sp, G4_sp, G5_sp, S_sp, P4C_sp, P5C_sp]
  ring

/-- `U4 D234 - U5 P2 = -S (h2 - 1) D023`. -/
theorem l46_U4D_eq : p.U4 * p.D234 - p.U5 * p.P2 =
    -p.S * (p.h2 - 1) * D023_sp p.a0 p.b0 p.h0 p.a2 p.b2 p.h2 p.s p.t := by
  simp only [L41P.U4, L41P.U5, L42P.D234, L42P.P2, L41P.S, U4_sp, U5_sp, D023_sp, DG5_sp, DG4_sp, D0_sp, G4_sp,
    G5_sp, S_sp, D234_sp, P2_sp]
  ring

/-- `U4 F55' + m U5 = -Phi Del S (h2 - 1) D023`. -/
theorem l46_F55_m : p.U4 * p.F55p + p.mC5 * p.U5 =
    -p.Phi * p.Del * p.S * (p.h2 - 1) * D023_sp p.a0 p.b0 p.h0 p.a2 p.b2 p.h2 p.s p.t := by
  have h1 := l46_Del_eq p
  have h2 := l46_U4D_eq p
  simp only [L42P.F55p, L42P.mC5]
  have : p.U4 * (p.Phi * p.U4 * p.D234 * p.v5 - p.P2 * (-p.v4) * p.c1 * p.U5) +
      ((-p.v4) * p.U4 * (p.P2 * p.c1 + p.D234 * p.Phi) - p.P2 * p.Phi * p.Del) * p.U5 =
      p.Phi * p.Del * (p.U4 * p.D234 - p.U5 * p.P2) := by
    rw [← h1]; ring
  rw [this, h2]; ring

/-- `-F55' = Phi [U4 D234 (P4 - P5) + (-v4) S (h2 - 1) D023] + (-V) U5 (-v4) P2`. -/
theorem l46_negF55 : -p.F55p = p.Phi * (p.U4 * p.D234 * (p.P4 - p.P5) +
    (-p.v4) * p.S * (p.h2 - 1) * D023_sp p.a0 p.b0 p.h0 p.a2 p.b2 p.h2 p.s p.t) +
    (-p.V) * p.U5 * (-p.v4) * p.P2 := by
  have hV := l46_c1_eq p
  have h4 : p.v4 + p.v5 = p.P5 - p.P4 := by
    simp only [L42P.v4, L42P.v5, L41P.P4, L41P.P5, v4_sp, v5_sp, P4C_sp, P5C_sp]; ring
  have h2 := l46_U4D_eq p
  have h5 : p.v5 = p.P5 - p.P4 - p.v4 := by linarith
  simp only [L42P.F55p]
  rw [hV, h5]
  have : -p.S * (p.h2 - 1) * D023_sp p.a0 p.b0 p.h0 p.a2 p.b2 p.h2 p.s p.t = p.U4 * p.D234 - p.U5 * p.P2 := h2.symm
  linear_combination (p.Phi * (-p.v4)) * this

/-- **L46-8**: the entries of `P`, `Rq`, `Q5neg`. -/
theorem l46_P_form : p.FA23 + (p.h2 - 1) * p.FA3 =
    (p.P2 * p.v4) * p.G44 + (p.D234 * p.v5) * p.G55 + (p.P2 * p.v5 + p.D234 * p.v4) * p.g45 := by
  simp only [L42P.FA23, L42P.FA3, L42P.rowv, L42P.ge3, L42P.ge4, L42P.ge5]; ring

theorem l46_Rq_form : p.h0 * p.Q02 + (p.h2 - p.h0) * p.Q05 =
    (p.Phi * p.U4) * p.G44 + (-p.c1 * p.U5) * p.G55 + (p.Phi * p.U5 - p.c1 * p.U4) * p.g45 := by
  simp only [L41P.Q02, L41P.Q05, L41P.row, Row_sp, L42P.Phi, L42P.c1, L42P.P2, L42P.D234, L42P.D035, L42P.P0,
    L41P.S]
  ring

theorem l46_Q5n_form : p.Q5n = (p.S * p.U4) * p.g45 + (p.S * p.U5) * p.G55 := by
  simp only [L41P.Q5n, L41P.row, Row_sp]; ring

/-! ## L46-9: the `C5-` certificate -/

/-- Core of the `C5-` certificate: five rows `≥ 0`, region facts, and `0 ≤ m` or `F55' < 0 ∧ m < 0`. -/
theorem l46_cert_C5_core (hS : 0 < p.S) (hh0 : 0 < p.h0) (hh : p.h0 < p.h2) (h1 : 1 < p.h2) (hP2 : 0 < p.P2)
    (hv4 : p.v4 < 0) (hU4 : 0 < p.U4) (hPhi : 0 < p.Phi) (hD : 0 < p.D0)
    (hD023 : 0 < D023_sp p.a0 p.b0 p.h0 p.a2 p.b2 p.h2 p.s p.t)
    (hG55 : 0 < p.G55) (hg45 : p.g45 ≤ 0)
    (hFA23 : 0 ≤ p.FA23) (hFA3 : 0 ≤ p.FA3) (hQ02 : 0 ≤ p.Q02) (hQ05 : 0 ≤ p.Q05) (hQ5n : 0 ≤ p.Q5n)
    (hm : 0 ≤ p.mC5 ∨ (p.mC5 < 0 ∧ p.F55p < 0)) : False := by
  have hSU : 0 < p.S * p.U4 := mul_pos hS hU4
  have hPU : 0 ≤ p.Phi * p.U4 := (mul_pos hPhi hU4).le
  have hPv : 0 ≤ p.P2 * (-p.v4) := mul_nonneg hP2.le (by linarith)
  have hRq : 0 ≤ p.h0 * p.Q02 + (p.h2 - p.h0) * p.Q05 :=
    add_nonneg (mul_nonneg hh0.le hQ02) (mul_nonneg (by linarith) hQ05)
  have hP : 0 ≤ p.FA23 + (p.h2 - 1) * p.FA3 := add_nonneg hFA23 (mul_nonneg (by linarith) hFA3)
  have hPF := l46_P_form p
  have hRF := l46_Rq_form p
  have hQF := l46_Q5n_form p
  rcases hm with hm | ⟨hm, hF⟩
  · -- m ≥ 0: multiplier m / (S U4) on Q5neg
    have hmu : 0 ≤ p.mC5 / (p.S * p.U4) := div_nonneg hm hSU.le
    have hF0 : 0 ≤ (p.Phi * p.U4) * (p.FA23 + (p.h2 - 1) * p.FA3) +
        (p.P2 * (-p.v4)) * (p.h0 * p.Q02 + (p.h2 - p.h0) * p.Q05) + p.mC5 / (p.S * p.U4) * p.Q5n :=
      add_nonneg (add_nonneg (mul_nonneg hPU hP) (mul_nonneg hPv hRq)) (mul_nonneg hmu hQ5n)
    have hq1 : p.mC5 * p.U5 / p.U4 * p.U4 = p.mC5 * p.U5 := div_mul_cancel₀ _ hU4.ne'
    have hneg : p.F55p + p.mC5 * p.U5 / p.U4 < 0 := by
      have e := l46_F55_m p
      have hDel : 0 < p.Del := mul_pos (mul_pos hS (by linarith)) hD
      have hpos := mul_pos (mul_pos (mul_pos (mul_pos hPhi hDel) hS) (sub_pos.2 h1)) hD023
      by_contra hc
      push Not at hc
      nlinarith [mul_nonneg hc hU4.le]
    have hq : p.mC5 / (p.S * p.U4) * (p.S * p.U4) = p.mC5 := div_mul_cancel₀ _ hSU.ne'
    have hq2 : p.mC5 / (p.S * p.U4) * (p.S * p.U5) = p.mC5 * p.U5 / p.U4 := by
      field_simp
    have hid : (p.Phi * p.U4) * (p.FA23 + (p.h2 - 1) * p.FA3) +
        (p.P2 * (-p.v4)) * (p.h0 * p.Q02 + (p.h2 - p.h0) * p.Q05) + p.mC5 / (p.S * p.U4) * p.Q5n =
        (p.F55p + p.mC5 * p.U5 / p.U4) * p.G55 := by
      rw [hPF, hRF, hQF]
      simp only [L42P.F55p, L42P.mC5, L42P.Del] at hq hq2 ⊢
      have hDel := l46_Del_eq p
      simp only [L42P.Del] at hDel
      linear_combination p.g45 * hq + p.G55 * hq2 + (p.g45 * p.Phi * p.P2) * hDel
    rw [hid] at hF0
    nlinarith
  · -- m < 0 and F55' < 0
    have hF0 : 0 ≤ (p.Phi * p.U4) * (p.FA23 + (p.h2 - 1) * p.FA3) +
        (p.P2 * (-p.v4)) * (p.h0 * p.Q02 + (p.h2 - p.h0) * p.Q05) :=
      add_nonneg (mul_nonneg hPU hP) (mul_nonneg hPv hRq)
    have hid : (p.Phi * p.U4) * (p.FA23 + (p.h2 - 1) * p.FA3) +
        (p.P2 * (-p.v4)) * (p.h0 * p.Q02 + (p.h2 - p.h0) * p.Q05) =
        p.F55p * p.G55 + (-p.mC5) * p.g45 := by
      rw [hPF, hRF]
      have hDel := l46_Del_eq p
      simp only [L42P.F55p, L42P.mC5, L42P.Del] at hDel ⊢
      linear_combination (p.g45 * p.Phi * p.P2) * hDel
    rw [hid] at hF0
    nlinarith

/-- **L46-9** (`cert_C5_false`): the proved sub-cases of `C5-`: `m ≥ 0`, or `m < 0` with `P4 ≥ P5`. -/
theorem l46_cert_C5_false (hS : 0 < p.S) (hh0 : 0 < p.h0) (hh : p.h0 < p.h2) (h1 : 1 < p.h2) (hP2 : 0 < p.P2)
    (hv4 : p.v4 < 0) (hU4 : 0 < p.U4) (hU5 : 0 ≤ p.U5) (hD234 : 0 < p.D234) (hPhi : 0 < p.Phi) (hV : p.V < 0)
    (hD : 0 < p.D0) (hD023 : 0 < D023_sp p.a0 p.b0 p.h0 p.a2 p.b2 p.h2 p.s p.t)
    (hG55 : 0 < p.G55) (hg45 : p.g45 ≤ 0)
    (hFA23 : 0 ≤ p.FA23) (hFA3 : 0 ≤ p.FA3) (hQ02 : 0 ≤ p.Q02) (hQ05 : 0 ≤ p.Q05) (hQ5n : 0 ≤ p.Q5n)
    (hm : 0 ≤ p.mC5 ∨ (p.mC5 < 0 ∧ p.P5 ≤ p.P4)) : False := by
  refine l46_cert_C5_core p hS hh0 hh h1 hP2 hv4 hU4 hPhi hD hD023 hG55 hg45 hFA23 hFA3 hQ02 hQ05 hQ5n ?_
  rcases hm with hm | ⟨hm, hP⟩
  · exact Or.inl hm
  · refine Or.inr ⟨hm, ?_⟩
    have e := l46_negF55 p
    have t1 : 0 ≤ p.U4 * p.D234 * (p.P4 - p.P5) := mul_nonneg (mul_pos hU4 hD234).le (sub_nonneg.2 hP)
    have t2 : 0 < (-p.v4) * p.S * (p.h2 - 1) * D023_sp p.a0 p.b0 p.h0 p.a2 p.b2 p.h2 p.s p.t :=
      mul_pos (mul_pos (mul_pos (by linarith) hS) (sub_pos.2 h1)) hD023
    have t3 := mul_pos hPhi (add_pos_of_nonneg_of_pos t1 t2)
    have t4 : 0 ≤ (-p.V) * p.U5 * (-p.v4) * p.P2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hU5) (by linarith)) hP2.le
    linarith

/-- **L46-9** (`cert_C5_res_false`): `m < 0` with `P5 > P4`, with the CENSUS fact `F55' < 0` as a named hypothesis
(20 of 20 instances; not proved). -/
theorem l46_cert_C5_res_false (hS : 0 < p.S) (hh0 : 0 < p.h0) (hh : p.h0 < p.h2) (h1 : 1 < p.h2) (hP2 : 0 < p.P2)
    (hv4 : p.v4 < 0) (hU4 : 0 < p.U4) (hPhi : 0 < p.Phi) (hD : 0 < p.D0)
    (hD023 : 0 < D023_sp p.a0 p.b0 p.h0 p.a2 p.b2 p.h2 p.s p.t)
    (hG55 : 0 < p.G55) (hg45 : p.g45 ≤ 0)
    (hFA23 : 0 ≤ p.FA23) (hFA3 : 0 ≤ p.FA3) (hQ02 : 0 ≤ p.Q02) (hQ05 : 0 ≤ p.Q05) (hQ5n : 0 ≤ p.Q5n)
    (hm : p.mC5 < 0) (hC5Res : p.F55p < 0) : False :=
  l46_cert_C5_core p hS hh0 hh h1 hP2 hv4 hU4 hPhi hD hD023 hG55 hg45 hFA23 hFA3 hQ02 hQ05 hQ5n (Or.inr ⟨hm, hC5Res⟩)

end Minimality.NF29
