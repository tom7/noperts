module

public import Minimality.Type29CellII42

@[expose] public section

/-!
# Type 29, `K1a ∩ G* ∩ Cell II`, Task L44 (`A44-REFEREE`)

* `L44-1` `m_cone_rows`: the cone-`M` weak-order lemma at `035 × 234` (pure order + one balanced identity), and its
  instance `l44_cone_M_rows` (`ID16`-`ID18` as a ring identity in the `(e3, e4, e5)` frame).
* `L44-2` `l44_rows_4rim`: the rows `W21', W23, W51, W53 ≥ 0` of the failing `(-,-)` 4-rim `(5,1,2,3)` at `v14`
  (`ID15` as a ring identity).  The rim step itself (`not LexAny29 → Alt4 …`) is a hypothesis.
* `L44-3` the ring identities `ID1`-`ID12`.
* `L44-4`, `L44-5` `branchA_slt1_false`, `branchC_false`, `branchB_false` (the TRUE 5-rim `(2,3,5,6,4)` at `v14 - ε d1`
  has a branch D that is NOT closed; A44's A/B/C cover is false and is not wired).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.Gen Minimality.GenQuad Minimality.LexCell Minimality.H21 Minimality.H29

namespace Minimality.NF29

/-! ## L44-1: the cone-`M` lemma -/

/-- **L44-1** (`m_cone_rows`): if the weak alternating 4-cycle `(z1, z4, z3, z5)` has the balanced identity
`wa (z4 - z1) + wb (z4 - z3) + wc (z5 - z1) + wd (z5 - z3) + W n = 0` with positive weights, then the cone `M`
holds: `{z1, z3} ≥ {z4, z5}`.  The opposite alternation `M'` is killed by the identity (ties included). -/
theorem m_cone_rows {z1 z3 z4 z5 wa wb wc wd W n : ℝ} (hwa : 0 < wa) (hwb : 0 < wb) (hwc : 0 < wc)
    (hwd : 0 < wd) (hW : 0 < W) (hn : 0 < n)
    (hid : wa * (z4 - z1) + wb * (z4 - z3) + wc * (z5 - z1) + wd * (z5 - z3) + W * n = 0)
    (h : Alt4 z1 z4 z3 z5) : z4 ≤ z1 ∧ z5 ≤ z1 ∧ z4 ≤ z3 ∧ z5 ≤ z3 := by
  rcases h with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · exact ⟨h1, h2, h3, h4⟩
  · exfalso
    have e1 := mul_nonneg hwa.le (sub_nonneg.2 h1)
    have e2 := mul_nonneg hwb.le (sub_nonneg.2 h2)
    have e3 := mul_nonneg hwc.le (sub_nonneg.2 h3)
    have e4 := mul_nonneg hwd.le (sub_nonneg.2 h4)
    have e5 := mul_pos hW hn
    nlinarith

/-- The `RobUni` form of a failing 4-cycle: `¬ RobUni z` gives the weak alternating quadruple (`robUni_four_of_mixed`
is the converse). -/
theorem alt4_of_not_robUni_four {z : ZMod 4 → ℝ} (h : ¬ RobUni z) : Alt4 (z 0) (z 1) (z 2) (z 3) := by
  simp only [RobUni, not_forall, not_not] at h
  obtain ⟨B, b, c, d, hb, hbc, hcd, hd, e1, e2, e3, e4⟩ := h
  have hb1 : b = 1 := by omega
  have hc2 : c = 2 := by omega
  have hd3 : d = 3 := by omega
  subst hb1 hc2 hd3
  unfold Alt4
  fin_cases B <;> simp at e1 e2 e3 e4 <;> first
    | (left; refine ⟨?_, ?_, ?_, ?_⟩ <;> assumption)
    | (right; refine ⟨?_, ?_, ?_, ?_⟩ <;> assumption)


/-! ## Rows of `W14` and the cone `M` in the `G` entries -/

section L44Rows

namespace L42P

variable (p : L42P)

/-- `⟪u, G u⟫` for `u = u3 e3 + u4 e4 + u5 e5`. -/
abbrev nrm (u3 u4 u5 : ℝ) : ℝ := u3 * p.ge3 u3 u4 u5 + u4 * p.ge4 u3 u4 u5 + u5 * p.ge5 u3 u4 u5

/-- `W51 = S (z5 - z1)(v14)`, `W53 = S (z5 - z3)(v14)`, `v14 = (0, 1 - t, t)`. -/
abbrev W51 : ℝ := p.rowv (-p.s) (p.s - 1) 0 0 (1 - p.t) p.t
abbrev W53 : ℝ := p.rowv 0 p.S (-1) 0 (1 - p.t) p.t
/-- `W14_34 = (z3 - z4)(v14)`, `W14_5m = -z5(v14)`, `W14_4 = z4(v14)`, `W34_56 = (z5 - z6)(w34)`. -/
abbrev W14_34 : ℝ := p.ge3 0 (1 - p.t) p.t - p.ge4 0 (1 - p.t) p.t
abbrev W14_5m : ℝ := -p.ge5 0 (1 - p.t) p.t
abbrev W14_4 : ℝ := p.ge4 0 (1 - p.t) p.t
abbrev W34_56 : ℝ := p.ge5 (-1) 1 0
/-- `‖v14‖_G^2`. -/
abbrev nrm14 : ℝ := p.nrm 0 (1 - p.t) p.t
/-- `P_B`, `W_B`, `p_{B,45}` of branch B. -/
abbrev pB45 : ℝ := p.t * p.P2 * p.v5 - p.S * p.P4 * p.D234
abbrev PB : ℝ := p.t * (p.FA23 + (p.h2 - 1) * p.FA3) + p.D234 * p.v5 * p.W14_5m
abbrev WB : ℝ := p.W23' + p.S * (p.h2 - 1) * p.t * p.W34_56 + p.D234 * p.W14_5m
abbrev CertB : ℝ := p.t * (p.P2 + p.S * (p.h2 - 1)) * p.PB + (-p.pB45) * p.WB
/-- The cone-`M` data at `u35 = (S C35, del2 D035, del0 D234)`. -/
abbrev u35n : ℝ := p.nrm (p.S * p.C35) (p.del2 * p.D035) (p.del0 * p.D234)
abbrev Z34 : ℝ := p.ge3 (p.S * p.C35) (p.del2 * p.D035) (p.del0 * p.D234) -
  p.ge4 (p.S * p.C35) (p.del2 * p.D035) (p.del0 * p.D234)
abbrev Z35 : ℝ := p.ge3 (p.S * p.C35) (p.del2 * p.D035) (p.del0 * p.D234) -
  p.ge5 (p.S * p.C35) (p.del2 * p.D035) (p.del0 * p.D234)
abbrev M14 : ℝ := p.rowv (1 - p.t) p.t 0 (p.S * p.C35) (p.del2 * p.D035) (p.del0 * p.D234)

end L42P

variable (p : L42P)

/-! ### L44-3: ring identities `ID1`-`ID12` -/

/-- `ID1` (key): `t W51 + S W14_4 + (1 - s) ‖v14‖^2 = 0`. -/
theorem l44_ID1 : p.t * p.W51 + p.S * p.W14_4 + (1 - p.s) * p.nrm14 = 0 := by
  simp only [L42P.W51, L42P.W14_4, L42P.nrm14, L42P.nrm, L42P.rowv, L42P.ge3, L42P.ge4, L42P.ge5, L41P.S, S_sp]
  ring

/-- `ID2`: the entries of `W51`. -/
theorem l44_ID2 : p.W51 = (-p.s * (1 - p.t)) * p.G44 + ((p.s - 1) * p.t) * p.G55 +
    (-(p.s * p.t + (1 - p.s) * (1 - p.t))) * p.g45 := by
  simp only [L42P.W51, L42P.rowv, L42P.ge3, L42P.ge4, L42P.ge5]; ring

/-- `ID3`: `W14_34 = -(1-t) G44 + (1-t) g34 + t g35 - t g45`. -/
theorem l44_ID3 : p.W14_34 = (-(1 - p.t)) * p.G44 + (1 - p.t) * p.g34 + p.t * p.g35 - p.t * p.g45 := by
  simp only [L42P.W14_34, L42P.ge3, L42P.ge4]; ring

/-- `ID4`: `W14_5m = -t G55 - (1-t) g45`. -/
theorem l44_ID4 : p.W14_5m = -p.t * p.G55 - (1 - p.t) * p.g45 := by
  simp only [L42P.W14_5m, L42P.ge5]; ring

/-- `ID5`: `W14_4 = (1-t) G44 + t g45`. -/
theorem l44_ID5 : p.W14_4 = (1 - p.t) * p.G44 + p.t * p.g45 := by
  simp only [L42P.W14_4, L42P.ge4]; ring

/-- `ID6`: `(1-t) D234 - t P2 = S [b2 + t (h2 - 1)]`. -/
theorem l44_ID6 : (1 - p.t) * p.D234 - p.t * p.P2 = p.S * (p.b2 + p.t * (p.h2 - 1)) := by
  simp only [L42P.D234, L42P.P2, L41P.S, D234_sp, P2_sp, S_sp]; ring

/-- `ID8`: `t (-v4) + (1-t) v5 = S P4`. -/
theorem l44_ID8 : p.t * (-p.v4) + (1 - p.t) * p.v5 = p.S * p.P4 := by
  simp only [L42P.v4, L42P.v5, L41P.P4, L41P.S, v4_sp, v5_sp, S_sp, P4C_sp, P5C_sp]; ring

/-- `ID12`: `W14_34 + t W34_56 = -(1-t) G44 + (1-t) g34`. -/
theorem l44_ID12 : p.W14_34 + p.t * p.W34_56 = (-(1 - p.t)) * p.G44 + (1 - p.t) * p.g34 := by
  simp only [L42P.W14_34, L42P.W34_56, L42P.ge3, L42P.ge4, L42P.ge5]; ring

/-- `ID9`: `P_B = t P2 v4 G44 + p_{B,45} g45`. -/
theorem l44_ID9 : p.PB = (p.t * p.P2 * p.v4) * p.G44 + p.pB45 * p.g45 := by
  have h8 := l44_ID8 p
  have h7 := l42_PFA_form p
  have h4 := l44_ID4 p
  simp only [L42P.PB, L42P.pB45]
  rw [h7, h4]
  linear_combination (-p.D234 * p.g45) * h8

/-- `ID10`: `W_B = P2 (1-t) G44 + S (h2-1)(1-t) g34 + t (P2 + S (h2-1)) g45`. -/
theorem l44_ID10 : p.WB = (p.P2 * (1 - p.t)) * p.G44 + (p.S * (p.h2 - 1) * (1 - p.t)) * p.g34 +
    (p.t * (p.P2 + p.S * (p.h2 - 1))) * p.g45 := by
  simp only [L42P.WB, L42P.W23', L42P.W34_56, L42P.W14_5m, L42P.rowv, L42P.ge3, L42P.ge4, L42P.ge5]; ring

/-- `ID11` (`Cert-BranchB`): the entries (`G33 = G55 = g35 = g45 = 0`). -/
theorem l44_ID11 : p.CertB = (p.S * p.P2 * (p.S * p.P4 * (p.b2 + p.t * (p.h2 - 1)) +
      p.t ^ 2 * (p.h2 - 1) * p.v4)) * p.G44 +
    ((-p.pB45) * p.S * (p.h2 - 1) * (1 - p.t)) * p.g34 := by
  have h9 := l44_ID9 p
  have h10 := l44_ID10 p
  have h6 := l44_ID6 p
  have h8 := l44_ID8 p
  simp only [L42P.CertB]
  rw [h9, h10]
  simp only [L42P.pB45]
  linear_combination (p.S * p.P2 * p.P4 * p.G44) * h6 + (-(p.t * p.P2 ^ 2 * p.G44)) * h8

end L44Rows

/-! ## L44-4, L44-5: the closing lemmas (branches A with `s < 1`, B, C of the `W14` split) -/

section L44Close

variable (p : L42P)

/-- Metric positivity of `G` on the `(e3, e4, e5)` frame. -/
def L44PD (p : L42P) : Prop :=
  ∀ u3 u4 u5 : ℝ, (u3 ≠ 0 ∨ u4 ≠ 0 ∨ u5 ≠ 0) → 0 < p.nrm u3 u4 u5

theorem l44_nrm14_pos {p : L42P} (hPD : L44PD p) (ht : 0 < p.t) : 0 < p.nrm14 :=
  hPD 0 (1 - p.t) p.t (Or.inr (Or.inr ht.ne'))

/-- **L44-4** (`branchA_slt1_false`): `s < 1`, `W51 ≥ 0`, `W14_4 ≥ 0` is impossible for every PD metric
(`t W51 + S W14_4 = -(1-s) ‖v14‖^2 < 0`). -/
theorem branchA_slt1_false {p : L42P} (hs : p.s < 1) (ht : 0 < p.t) (hS : 0 < p.S) (hPD : L44PD p)
    (hW51 : 0 ≤ p.W51) (hW4 : 0 ≤ p.W14_4) : False := by
  have h1 := l44_ID1 p
  have hn := l44_nrm14_pos hPD ht
  nlinarith [mul_nonneg ht.le hW51, mul_nonneg hS.le hW4, mul_pos (sub_pos.2 hs) hn]

/-- **L44-5** (`branchC_false`): `W14_34 + t W34_56 = -(1-t)(G44 - g34) < 0`. -/
theorem branchC_false {p : L42P} (ht : 0 < p.t) (ht1 : p.t < 1) (hG44 : 0 < p.G44) (hg34 : p.g34 ≤ 0)
    (hW34 : 0 ≤ p.W14_34) (hW56 : 0 ≤ p.W34_56) : False := by
  have h := l44_ID12 p
  nlinarith [mul_nonneg ht.le hW56, mul_pos (sub_pos.2 ht1) hG44,
    mul_nonneg (sub_pos.2 ht1).le (neg_nonneg.2 hg34)]

/-- **L44-5** (`branchB_false`): the five rows `FA23, FA3, W23, W14_5m, W34_56` (`pB45 ≥ 0`: three of them suffice). -/
theorem branchB_false {p : L42P} (hS : 0 < p.S) (ht : 0 < p.t) (ht1 : p.t < 1) (hh2 : 1 < p.h2)
    (hb : p.h2 - 1 < -p.b2) (hP2 : 0 < p.P2) (hP4 : 0 < p.P4) (hD : 0 < p.D234) (hv4 : p.v4 < 0)
    (hv5 : 0 < p.v5) (hG44 : 0 < p.G44) (hg34 : p.g34 ≤ 0) (hg45 : p.g45 ≤ 0)
    (hFA23 : 0 ≤ p.FA23) (hFA3 : 0 ≤ p.FA3) (hW23 : 0 ≤ p.W23') (hW5 : 0 ≤ p.W14_5m)
    (hW56 : 0 ≤ p.W34_56) : False := by
  have hPFA : 0 ≤ p.FA23 + (p.h2 - 1) * p.FA3 :=
    add_nonneg hFA23 (mul_nonneg (by linarith) hFA3)
  have hPB : 0 ≤ p.PB :=
    add_nonneg (mul_nonneg ht.le hPFA) (mul_nonneg (mul_nonneg hD.le hv5.le) hW5)
  have hWB : 0 ≤ p.WB :=
    add_nonneg (add_nonneg hW23 (mul_nonneg (mul_nonneg (mul_nonneg hS.le (by linarith)) ht.le) hW56))
      (mul_nonneg hD.le hW5)
  have h9 := l44_ID9 p
  have h44 : 0 < p.t * p.P2 * (-p.v4) * p.G44 := by
    have := neg_pos.2 hv4
    positivity
  by_cases hpB : 0 ≤ p.pB45
  · have e2 : p.pB45 * p.g45 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpB hg45
    nlinarith
  · have hpB := not_le.mp hpB
    have hCert : 0 ≤ p.CertB := by
      have hc : 0 < p.t * (p.P2 + p.S * (p.h2 - 1)) := by
        have : 0 < p.S * (p.h2 - 1) := mul_pos hS (by linarith)
        positivity
      exact add_nonneg (mul_nonneg hc.le hPB) (mul_nonneg (neg_nonneg.2 hpB.le) hWB)
    rw [l44_ID11] at hCert
    have hb2 : p.b2 + p.t * (p.h2 - 1) < 0 := by nlinarith
    have hc44 : p.S * p.P2 * (p.S * p.P4 * (p.b2 + p.t * (p.h2 - 1)) + p.t ^ 2 * (p.h2 - 1) * p.v4) < 0 := by
      have h1 : p.S * p.P4 * (p.b2 + p.t * (p.h2 - 1)) < 0 := mul_neg_of_pos_of_neg (mul_pos hS hP4) hb2
      have h2 : p.t ^ 2 * (p.h2 - 1) * p.v4 < 0 :=
        mul_neg_of_pos_of_neg (mul_pos (by positivity) (by linarith)) hv4
      exact mul_neg_of_pos_of_neg (mul_pos hS hP2) (by linarith)
    have e1 : (p.S * p.P2 * (p.S * p.P4 * (p.b2 + p.t * (p.h2 - 1)) + p.t ^ 2 * (p.h2 - 1) * p.v4)) * p.G44 < 0 :=
      mul_neg_of_neg_of_pos hc44 hG44
    have e2 : ((-p.pB45) * p.S * (p.h2 - 1) * (1 - p.t)) * p.g34 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (mul_nonneg (mul_nonneg (neg_nonneg.2 hpB.le) hS.le) (by linarith)) (by linarith)) hg34
    linarith

end L44Close

/-! ## L44-1 instance and L44-2: the cone `M` rows and the 4-rim rows -/

section L44Cone

variable (p : L42P)

/-- `ID16`-`ID18` as one ring identity: weights `A C, A D, B C, B D, A + B` with `A = -a0 del2`, `B = -b2 del0`,
`C = del0 del2`, `D = C35` (the `S` factors of the vector identity cancel against the row scaling). -/
theorem l44_cone_M_identity :
    (-p.a0 * p.del2 * (p.del0 * p.del2)) *
        (p.rowv p.S 0 0 (p.S * p.C35) (p.del2 * p.D035) (p.del0 * p.D234) -
          p.rowv p.s p.t 0 (p.S * p.C35) (p.del2 * p.D035) (p.del0 * p.D234)) +
      (-p.a0 * p.del2 * p.C35) *
        (p.rowv p.S 0 0 (p.S * p.C35) (p.del2 * p.D035) (p.del0 * p.D234) -
          p.rowv 0 0 1 (p.S * p.C35) (p.del2 * p.D035) (p.del0 * p.D234)) +
      (-p.b2 * p.del0 * (p.del0 * p.del2)) *
        (p.rowv 0 p.S 0 (p.S * p.C35) (p.del2 * p.D035) (p.del0 * p.D234) -
          p.rowv p.s p.t 0 (p.S * p.C35) (p.del2 * p.D035) (p.del0 * p.D234)) +
      (-p.b2 * p.del0 * p.C35) *
        (p.rowv 0 p.S 0 (p.S * p.C35) (p.del2 * p.D035) (p.del0 * p.D234) -
          p.rowv 0 0 1 (p.S * p.C35) (p.del2 * p.D035) (p.del0 * p.D234)) +
      (-p.a0 * p.del2 - p.b2 * p.del0) * p.u35n = 0 := by
  have r1 : p.D035 = p.S * p.a0 + p.del0 * p.s := by
    simp only [L42P.D035, L42P.del0, L41P.S, D035_sp, S_sp]; ring
  have r2 : p.D234 = p.S * p.b2 + p.del2 * p.t := by
    simp only [L42P.D234, L42P.del2, L41P.S, D234_sp, S_sp]; ring
  have r3 : p.C35 = -(p.a0 * p.del2 + p.b2 * p.del0 + p.del0 * p.del2) := by
    simp only [L42P.C35, L42P.del0, L42P.del2, C35_sp, DG4_sp, D0_sp, G4_sp]; ring
  simp only [L42P.u35n, L42P.nrm, L42P.rowv, L42P.ge3, L42P.ge4, L42P.ge5]
  rw [r1, r2, r3]
  ring

/-- **L44-1 instance** (`l44_cone_M_rows`): on `{S, -a0, -b2, del0, del2, C35 > 0}` and `‖u35‖_G^2 > 0`, the weak
alternation of the 4-cycle `(1, 4, 3, 5)` at `u35` gives the cone `M`: `M15, M14, Z34, Z35 ≥ 0`. -/
theorem l44_cone_M_rows {p : L42P} (hS : 0 < p.S) (ha0 : p.a0 < 0) (hb2 : p.b2 < 0) (hd0 : 0 < p.del0)
    (hd2 : 0 < p.del2) (hC : 0 < p.C35) (hn : 0 < p.u35n)
    (h : Alt4 (p.rowv p.s p.t 0 (p.S * p.C35) (p.del2 * p.D035) (p.del0 * p.D234))
      (p.rowv p.S 0 0 (p.S * p.C35) (p.del2 * p.D035) (p.del0 * p.D234))
      (p.rowv 0 0 1 (p.S * p.C35) (p.del2 * p.D035) (p.del0 * p.D234))
      (p.rowv 0 p.S 0 (p.S * p.C35) (p.del2 * p.D035) (p.del0 * p.D234))) :
    0 ≤ p.M15 ∧ 0 ≤ p.M14 ∧ 0 ≤ p.Z34 ∧ 0 ≤ p.Z35 := by
  have hA : 0 < -p.a0 * p.del2 := mul_pos (neg_pos.2 ha0) hd2
  have hB : 0 < -p.b2 * p.del0 := mul_pos (neg_pos.2 hb2) hd0
  have hCC : 0 < p.del0 * p.del2 := mul_pos hd0 hd2
  have hid := l44_cone_M_identity p
  obtain ⟨e1, e2, e3, e4⟩ := m_cone_rows (mul_pos hA hCC) (mul_pos hA hC) (mul_pos hB hCC) (mul_pos hB hC)
    (by linarith) hn hid h
  have f1 : p.M15 = p.rowv p.s p.t 0 (p.S * p.C35) (p.del2 * p.D035) (p.del0 * p.D234) -
      p.rowv 0 p.S 0 (p.S * p.C35) (p.del2 * p.D035) (p.del0 * p.D234) := by
    simp only [L42P.M15, L42P.rowv, L42P.ge3, L42P.ge4, L42P.ge5, L41P.S, S_sp]; ring
  have f2 : p.M14 = p.rowv p.s p.t 0 (p.S * p.C35) (p.del2 * p.D035) (p.del0 * p.D234) -
      p.rowv p.S 0 0 (p.S * p.C35) (p.del2 * p.D035) (p.del0 * p.D234) := by
    simp only [L42P.M14, L42P.rowv, L42P.ge3, L42P.ge4, L42P.ge5, L41P.S, S_sp]; ring
  have f3 : p.S * p.Z34 = p.rowv 0 0 1 (p.S * p.C35) (p.del2 * p.D035) (p.del0 * p.D234) -
      p.rowv p.S 0 0 (p.S * p.C35) (p.del2 * p.D035) (p.del0 * p.D234) := by
    simp only [L42P.Z34, L42P.rowv, L42P.ge3, L42P.ge4, L42P.ge5]; ring
  have f4 : p.S * p.Z35 = p.rowv 0 0 1 (p.S * p.C35) (p.del2 * p.D035) (p.del0 * p.D234) -
      p.rowv 0 p.S 0 (p.S * p.C35) (p.del2 * p.D035) (p.del0 * p.D234) := by
    simp only [L42P.Z35, L42P.rowv, L42P.ge3, L42P.ge4, L42P.ge5]; ring
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · exact (mul_nonneg_iff_of_pos_left hS).1 (by linarith)
  · exact (mul_nonneg_iff_of_pos_left hS).1 (by linarith)

/-- `ID15` at `v14 = (0, 1-t, t)`: `R2 + (-b2) R5 = (-a2) ‖v14‖^2 + h2 R3 + (1-b2-h2) R1`
(`R_i = ⟪S (x_i - x_6), G v14⟫`). -/
theorem l44_ID15 :
    p.rowv p.P2 p.D234 p.h2 0 (1 - p.t) p.t + (-p.b2) * p.rowv 0 p.S 0 0 (1 - p.t) p.t =
      (-p.a2) * p.nrm14 + p.h2 * p.rowv 0 0 1 0 (1 - p.t) p.t +
        (1 - p.b2 - p.h2) * p.rowv p.s p.t 0 0 (1 - p.t) p.t := by
  simp only [L42P.nrm14, L42P.nrm, L42P.rowv, L42P.ge3, L42P.ge4, L42P.ge5, L42P.P2, L42P.D234, L41P.S,
    P2_sp, D234_sp, S_sp]
  ring

/-- Pure order core of `L44-2`: the alternation `M'` is killed by `ID15` (ties included). -/
theorem l44_4rim_pure {R1 R2 R3 R5 n a2 b2 h2 : ℝ} (ha2 : a2 < 0) (hb2 : b2 < 0) (hh2 : 0 < h2)
    (hb : h2 - 1 < -b2) (hn : 0 < n)
    (hid : R2 + (-b2) * R5 = (-a2) * n + h2 * R3 + (1 - b2 - h2) * R1) (h : Alt4 R5 R1 R2 R3) :
    R1 ≤ R5 ∧ R3 ≤ R5 ∧ R1 ≤ R2 ∧ R3 ≤ R2 := by
  rcases h with ⟨h1, h2', h3, h4⟩ | ⟨h1, h2', h3, h4⟩
  · exact ⟨h1, h2', h3, h4⟩
  · exfalso
    have hx : 0 < 1 - b2 - h2 := by linarith
    have hna : 0 < -a2 * n := mul_pos (neg_pos.2 ha2) hn
    rcases le_or_gt (-b2) h2 with hc | hc
    · have e1 := mul_nonneg hx.le (sub_nonneg.2 h2')
      have e2 := mul_nonneg (show 0 ≤ b2 + h2 by linarith) (sub_nonneg.2 h4)
      have e3 := mul_nonneg (neg_pos.2 hb2).le (sub_nonneg.2 h3)
      linarith
    · have e1 := sub_nonneg.2 h2'
      have e2 := mul_nonneg (show 0 ≤ -b2 - h2 by linarith) (sub_nonneg.2 h1)
      have e3 := mul_nonneg hh2.le (sub_nonneg.2 h3)
      linarith

/-- **L44-2** (`l44_rows_4rim`): the failing `(-,-)` 4-rim `(5, 1, 2, 3)` at `v14` gives `W21', W23, W51, W53 ≥ 0`
(the opposite alternation is killed by `ID15`, ties included).  The rim step `¬ LexAny29 → Alt4 …` is the
hypothesis `h`. -/
theorem l44_rows_4rim {p : L42P} (ha2 : p.a2 < 0) (hb2 : p.b2 < 0) (hh2 : 0 < p.h2) (hb : p.h2 - 1 < -p.b2)
    (hn : 0 < p.nrm14)
    (h : Alt4 (p.rowv 0 p.S 0 0 (1 - p.t) p.t) (p.rowv p.s p.t 0 0 (1 - p.t) p.t)
      (p.rowv p.P2 p.D234 p.h2 0 (1 - p.t) p.t) (p.rowv 0 0 1 0 (1 - p.t) p.t)) :
    0 ≤ p.W21' ∧ 0 ≤ p.W23' ∧ 0 ≤ p.W51 ∧ 0 ≤ p.W53 := by
  have hid := l44_ID15 p
  have f1 : p.W21' = p.rowv p.P2 p.D234 p.h2 0 (1 - p.t) p.t - p.rowv p.s p.t 0 0 (1 - p.t) p.t := by
    simp only [L42P.W21', L42P.rowv, L42P.ge3, L42P.ge4, L42P.ge5]; ring
  have f2 : p.W23' = p.rowv p.P2 p.D234 p.h2 0 (1 - p.t) p.t - p.rowv 0 0 1 0 (1 - p.t) p.t := by
    simp only [L42P.W23', L42P.rowv, L42P.ge3, L42P.ge4, L42P.ge5]; ring
  have f3 : p.W51 = p.rowv 0 p.S 0 0 (1 - p.t) p.t - p.rowv p.s p.t 0 0 (1 - p.t) p.t := by
    simp only [L42P.W51, L42P.rowv, L42P.ge3, L42P.ge4, L42P.ge5, L41P.S, S_sp]; ring
  have f4 : p.W53 = p.rowv 0 p.S 0 0 (1 - p.t) p.t - p.rowv 0 0 1 0 (1 - p.t) p.t := by
    simp only [L42P.W53, L42P.rowv, L42P.ge3, L42P.ge4, L42P.ge5]; ring
  obtain ⟨h1, h2, h3, h4⟩ := l44_4rim_pure ha2 hb2 hh2 hb hn hid h
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

end L44Cone

end Minimality.NF29
