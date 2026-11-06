module

public import Minimality.Generic.CayleyJet
public import Minimality.PolygonHalfPlanes
public import Minimality.Generic.WaistJet

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace
open Polynomial Minimality Waist Filter Topology
namespace WaistW

noncomputable def cc (B P Q W Y : ℝ) : ZMod 4 → ℝ² :=
  ![!₂[0,0], !₂[B,0], !₂[P,Q], !₂[W,Y]]

lemma cc0 : cc B P Q W Y 0 = !₂[0,0] := rfl
lemma cc1 : cc B P Q W Y 1 = !₂[B,0] := rfl
lemma cc2 : cc B P Q W Y 2 = !₂[P,Q] := rfl
lemma cc3 : cc B P Q W Y 3 = !₂[W,Y] := rfl
lemma z01 : (0 : ZMod 4) + 1 = 1 := by decide
lemma z12 : (1 : ZMod 4) + 1 = 2 := by decide
lemma z23 : (2 : ZMod 4) + 1 = 3 := by decide
lemma z30 : (3 : ZMod 4) + 1 = 0 := by decide
lemma zc4 (i : ZMod 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide

noncomputable def nq (B P Q W Y : ℝ) : Fin 4 → ℝ² :=
  ![!₂[0,-B], !₂[Q,B-P], !₂[Y-Q,P-W], !₂[-Y,W]]
noncomputable def hq (B P Q W Y : ℝ) : Fin 4 → ℝ := ![0, Q*B, P*Y-W*Q, 0]

open Classical in
noncomputable def VV (B P Q W Y dx dz cx cz ex ey ez : ℝ) : Finset ℝ³ :=
  {!₂[0,0,0], !₂[B,0,0], !₂[P,Q,0], !₂[W,Y,0], !₂[dx,0,dz], !₂[cx,0,cz], !₂[ex,ey,ez]}

lemma waistW_reduce (B P Q W Y dx dz cx cz ex ey ez : ℝ) (hB : 0 < B) (hQ : 0 < Q) (hY : 0 < Y)
    (hW : W ≤ 0) (hBP : B ≤ P)
    (z t2 u2 : ℝ)
    (hlex : ∀ v ∈ VV B P Q W Y dx dz cx cz ex ey ez, ∀ e : Fin 4,
      (pj (jc ((nq B P Q W Y e) 0) ((nq B P Q W Y e) 1) (hq B P Q W Y e) (v 0) (v 1) (v 2) z t2 0 0 u2 0 0)).trailingCoeff < 0) :
    IsRupert (VV B P Q W Y dx dz cx cz ex ey ez) := by
  classical
  have hP : 0 < P := by linarith
  have hccw : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      0 < cross2 (cc B P Q W Y (i + 1) - cc B P Q W Y i) (cc B P Q W Y j - cc B P Q W Y i) := by
    intro i j h1 h2
    rcases zc4 i with rfl | rfl | rfl | rfl <;> rcases zc4 j with rfl | rfl | rfl | rfl <;>
      first | (exfalso; apply h1; rfl) | (exfalso; apply h2; decide) | skip
    all_goals
      simp [cross2, z01, z12, z23, z30, cc0, cc1, cc2, cc3]
      nlinarith [mul_pos hB hQ, mul_pos hP hY, mul_pos hY hB, mul_nonneg (neg_nonneg.2 hW) hQ.le,
        mul_nonneg (sub_nonneg.2 hBP) hY.le, mul_nonneg (sub_nonneg.2 hBP) hQ.le, mul_nonneg (neg_nonneg.2 hW) hY.le,
        mul_pos hP hQ]
  obtain ⟨hp1, -⟩ := halfPlanes_of_ccwPolygon (cc B P Q W Y) (by norm_num) hccw
  have hsub : convexHull ℝ (Set.range (cc B P Q W Y)) ⊆
      proj_xy '' convexHull ℝ (VV B P Q W Y dx dz cx cz ex ey ez : Set ℝ³) := by
    refine convexHull_min ?_ ((convex_convexHull ℝ _).linear_image projL)
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨!₂[0,0,0], subset_convexHull ℝ _ (by simp [VV]), by ext a; fin_cases a <;> simp [cc, proj_xy]⟩
    · exact ⟨!₂[B,0,0], subset_convexHull ℝ _ (by simp [VV]), by ext a; fin_cases a <;> simp [cc, proj_xy]⟩
    · exact ⟨!₂[P,Q,0], subset_convexHull ℝ _ (by simp [VV]), by ext a; fin_cases a <;> simp [cc, proj_xy]⟩
    · exact ⟨!₂[W,Y,0], subset_convexHull ℝ _ (by simp [VV]), by ext a; fin_cases a <;> simp [cc, proj_xy]⟩
  have hpoly : {y : ℝ² | ∀ e : Fin 4, ⟪nq B P Q W Y e, y⟫ < hq B P Q W Y e} ⊆
      proj_xy '' convexHull ℝ (VV B P Q W Y dx dz cx cz ex ey ez : Set ℝ³) := by
    intro y hy
    apply hsub; apply hp1
    intro i
    have := hy (i : Fin 4)
    rcases zc4 i with rfl | rfl | rfl | rfl <;> simp [nq, hq, rot90, z01, z12, z23, z30, cc0, cc1, cc2, cc3, PiLp.inner_apply, Fin.sum_univ_two] at this ⊢ <;> linarith
  refine isRupert_of_cayleyPolyJet _ (nq B P Q W Y) (hq B P Q W Y) hpoly ![0, X, C z * X^2]
    ![C t2 * X^2 + C 0 * X^3 + C 0 * X^4, C u2 * X^2 + C 0 * X^3 + C 0 * X^4] ?_
  intro v hv e
  rw [N_eq]
  exact hlex v hv e

syntax "tcm " num " [" term,* "]" : tactic
macro_rules
  | `(tactic| tcm $m [$ts,*]) => `(tactic|
      (refine pj_tc _ $m (by norm_num) (fun i hi => by interval_cases i <;> simp [jc, nq, hq] <;> ring) ?_
       simp [jc, nq, hq]
       nlinarith [$ts,*]))

noncomputable def R0 (u : ℝ) : ℝ := -u
noncomputable def R1 (B z u : ℝ) : ℝ := -(2*B*z+u)
noncomputable def R2 (Y W t u : ℝ) : ℝ := -(Y*t - W*u)
noncomputable def R3 (W Y z t u : ℝ) : ℝ := 2*(W^2+Y^2)*z + 2*W*Y - (Y*t - W*u)
noncomputable def R4 (B P Q z t u : ℝ) : ℝ := Q*t + (B-P)*u + 2*B*(B-P)*z - 2*B*Q
noncomputable def R5 (B P Q z t u : ℝ) : ℝ := Q*t + (B-P)*u + 2*(B*P-P^2-Q^2)*z - 2*P*Q
noncomputable def R6 (P Q W Y z t u : ℝ) : ℝ := (Y-Q)*t + (P-W)*u + 2*(P^2+Q^2-P*W-Q*Y)*z - 2*P*(Y-Q)
noncomputable def R7 (P Q W Y z t u : ℝ) : ℝ := (Y-Q)*t + (P-W)*u + 2*(P*W+Q*Y-W^2-Y^2)*z - 2*W*(Y-Q)

set_option maxHeartbeats 16000000 in
lemma waistW_core (B P Q W Y dx dz cx cz ex ey ez : ℝ) (hB : 0 < B) (hQ : 0 < Q) (hY : 0 < Y)
    (hW : W ≤ 0) (hBP : B ≤ P)
    (hk : 0 < P*Y - Q*W) (hk2 : 0 < (P-B)*Y + Q*(B-W))
    (hd0 : 0 < dx) (hd1 : dx < B) (hc0 : 0 < cx) (hc1 : cx < B)
    (hdd : (Y-Q)*dx < P*Y - Q*W) (hcc : (Y-Q)*cx < P*Y - Q*W)
    (hin1 : 0 < ey) (hin3 : Q * ex + (B - P) * ey < Q * B)
    (hin4 : (Y - Q) * ex + (P-W) * ey < P * Y - W*Q) (hin5 : -Y*ex + W*ey < 0)
    (z t u : ℝ)
    (r0 : R0 u < 0) (r1 : R1 B z u < 0) (r2 : R2 Y W t u < 0) (r3 : R3 W Y z t u < 0)
    (r4 : R4 B P Q z t u < 0) (r5 : R5 B P Q z t u < 0) (r6 : R6 P Q W Y z t u < 0)
    (r7 : R7 P Q W Y z t u < 0)
    (r8 : R1 dx z u < 0) (r9 : R1 cx z u < 0) :
    IsRupert (VV B P Q W Y dx dz cx cz ex ey ez) := by
  refine waistW_reduce B P Q W Y dx dz cx cz ex ey ez hB hQ hY hW hBP z t u ?_
  intro v hv e
  simp only [VV, Finset.mem_insert, Finset.mem_singleton] at hv
  simp only [R0, R1, R2, R3, R4, R5, R6, R7] at *
  have hBY := mul_pos hB hY
  have hBQ := mul_pos hB hQ
  have b0 := mul_neg_of_pos_of_neg hB r0
  have b1 := mul_neg_of_pos_of_neg hB r1
  have b8 := mul_neg_of_pos_of_neg hB r8
  have b9 := mul_neg_of_pos_of_neg hB r9
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> fin_cases e
  · tcm 2 [b0]
  · tcm 0 [hBQ]
  · tcm 0 [hk]
  · tcm 2 [r2]
  · tcm 2 [b1]
  · tcm 2 [r4]
  · tcm 0 [hk2]
  · tcm 0 [hBY]
  · tcm 0 [hBQ]
  · tcm 2 [r5]
  · tcm 2 [r6]
  · tcm 0 [hk]
  · tcm 0 [hBY]
  · tcm 0 [hk2]
  · tcm 2 [r7]
  · tcm 2 [r3]
  · tcm 2 [b8]
  · tcm 0 [mul_pos hQ (sub_pos.2 hd1)]
  · tcm 0 [hdd]
  · tcm 0 [mul_pos hY hd0]
  · tcm 2 [b9]
  · tcm 0 [mul_pos hQ (sub_pos.2 hc1)]
  · tcm 0 [hcc]
  · tcm 0 [mul_pos hY hc0]
  · tcm 0 [mul_pos hB hin1]
  · tcm 0 [hin3]
  · tcm 0 [hin4]
  · tcm 0 [hin5]


lemma k84_exist (P Q Y W : ℝ) (hP : 0 < P) (hQ : 0 < Q) (hY : Q < Y) (hW : W < 0) :
    ∃ z eps : ℝ, 0 < z ∧ 0 < eps ∧ z * (W^2 + Y^2) < -W * Y ∧
      eps * (P - W) < 2*P*(Y-Q) - 2*(P^2+Q^2-P*W-Q*Y) * z ∧
      eps * (P - W) < 2*W*(Y-Q) + 2*(W^2+Y^2-P*W-Q*Y) * z := by
  have hYQ : 0 < Y - Q := by linarith
  have hw : 0 < -W := by linarith
  have hY0 : 0 < Y := by linarith
  have hc : 0 < W^2+Y^2-P*W-Q*Y := by nlinarith [mul_pos hP hw, mul_pos hY0 hYQ, sq_nonneg W]
  have hs : 0 < W^2+Y^2 := by positivity
  set c := W^2+Y^2-P*W-Q*Y with hcdef
  set d := P^2+Q^2-P*W-Q*Y with hddef
  have hA7 : 0 < -W*(Y-Q)/c := by positivity
  have h73 : -W*(Y-Q)/c < -W*Y/(W^2+Y^2) := by
    rw [div_lt_div_iff₀ hc hs]; rw [hcdef]
    nlinarith [mul_pos (mul_pos hP hw) hY0, mul_pos hQ (mul_pos hw hw)]
  obtain ⟨z, hz1, hz2, hz3⟩ : ∃ z : ℝ, -W*(Y-Q)/c < z ∧ z < -W*Y/(W^2+Y^2) ∧ (0 < d → z < P*(Y-Q)/d) := by
    by_cases hd : 0 < d
    · have h76 : -W*(Y-Q)/c < P*(Y-Q)/d := by
        rw [div_lt_div_iff₀ hc hd]; rw [hcdef, hddef]
        nlinarith [mul_pos (mul_pos hP hw) hYQ, mul_pos hQ (mul_pos hw hYQ), mul_pos hP (mul_pos hP hYQ), mul_pos hY0 (mul_pos hYQ hYQ)]
      obtain ⟨z, hz1, hz2⟩ := exists_between (lt_min h73 h76)
      exact ⟨z, hz1, lt_of_lt_of_le hz2 (min_le_left _ _), fun _ => lt_of_lt_of_le hz2 (min_le_right _ _)⟩
    · obtain ⟨z, hz1, hz2⟩ := exists_between h73
      exact ⟨z, hz1, hz2, fun h => absurd h hd⟩
  have hzpos : 0 < z := lt_trans hA7 hz1
  have e1 : z * c > -W*(Y-Q) := (div_lt_iff₀ hc).1 hz1
  have e2 : z * (W^2+Y^2) < -W * Y := by rwa [lt_div_iff₀ hs] at hz2
  have R6 : 0 < 2*P*(Y-Q) - 2*d*z := by
    by_cases hd : 0 < d
    · have := hz3 hd; rw [lt_div_iff₀ hd] at this; nlinarith
    · push Not at hd; nlinarith [mul_pos hP hYQ, mul_nonneg (neg_nonneg.2 hd) hzpos.le]
  have R7 : 0 < 2*W*(Y-Q) + 2*c*z := by nlinarith
  have hPW : 0 < P - W := by linarith
  refine ⟨z, min (2*P*(Y-Q) - 2*d*z) (2*W*(Y-Q) + 2*c*z) / (2*(P-W)), hzpos, ?_, e2, ?_, ?_⟩
  · have := lt_min R6 R7; positivity
  · rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    have := min_le_left (2*P*(Y-Q) - 2*d*z) (2*W*(Y-Q) + 2*c*z)
    have := lt_min R6 R7
    nlinarith
  · rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    have := min_le_right (2*P*(Y-Q) - 2*d*z) (2*W*(Y-Q) + 2*c*z)
    have := lt_min R6 R7
    nlinarith

set_option maxHeartbeats 8000000 in
theorem waistW_thmB (B P Q W Y dx dz cx cz ex ey ez : ℝ) (hB : 0 < B) (hQ : 0 < Q) (hY : 0 < Y)
    (hW : W < 0) (hBP : B ≤ P) (hYQ : Q < Y)
    (hd0 : 0 < dx) (hd1 : dx < B) (hc0 : 0 < cx) (hc1 : cx < B)
    (hin1 : 0 < ey) (hin3 : Q * ex + (B - P) * ey < Q * B)
    (hin4 : (Y - Q) * ex + (P-W) * ey < P * Y - W*Q) (hin5 : -Y*ex + W*ey < 0)
    : IsRupert (VV B P Q W Y dx dz cx cz ex ey ez) := by
  have hP : 0 < P := by linarith
  have hQY : 0 < Y - Q := by linarith
  obtain ⟨z, eps, hz, hepos, hA3, hE6, hE7⟩ := k84_exist P Q Y W hP hQ hYQ hW
  have hk : 0 < P*Y - Q*W := by nlinarith [mul_pos hP hY, mul_pos hQ (neg_pos.2 hW)]
  have hk2 : 0 < (P-B)*Y + Q*(B-W) := by nlinarith [mul_nonneg (sub_nonneg.2 hBP) hY.le, mul_pos hQ (sub_pos.2 (lt_of_lt_of_le hW (by linarith : (0:ℝ) ≤ B)))]
  have hdd : (Y-Q)*dx < P*Y - Q*W := by
    nlinarith [mul_lt_mul_of_pos_left hd1 hQY, mul_nonneg (sub_nonneg.2 hBP) hY.le, mul_pos hQ (neg_pos.2 hW)]
  have hcc : (Y-Q)*cx < P*Y - Q*W := by
    nlinarith [mul_lt_mul_of_pos_left hc1 hQY, mul_nonneg (sub_nonneg.2 hBP) hY.le, mul_pos hQ (neg_pos.2 hW)]
  refine waistW_core B P Q W Y dx dz cx cz ex ey ez hB hQ hY hW.le hBP hk hk2 hd0 hd1 hc0 hc1 hdd hcc
    hin1 hin3 hin4 hin5 z 0 eps ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
  simp only [R0, R1, R2, R3, R4, R5, R6, R7]
  · linarith
  · nlinarith [mul_pos hB hz]
  · nlinarith [mul_pos hepos (neg_pos.2 hW)]
  · nlinarith [mul_pos hepos (neg_pos.2 hW)]
  · nlinarith [mul_nonneg (sub_nonneg.2 hBP) hepos.le, mul_nonneg (mul_nonneg hB.le (sub_nonneg.2 hBP)) hz.le]
  · nlinarith [mul_nonneg (sub_nonneg.2 hBP) hepos.le, mul_nonneg (mul_nonneg hP.le (sub_nonneg.2 hBP)) hz.le,
      mul_pos hz (mul_pos hP hP), mul_pos hz (mul_pos hQ hQ), mul_pos hP hQ]
  · linarith
  · linarith
  · nlinarith [mul_pos hd0 hz]
  · nlinarith [mul_pos hc0 hz]

noncomputable def DD (B p w Y m : ℝ) : ℝ := p*(B+p+w)+(Y+m)*m
noncomputable def zA (B p w Y m e : ℝ) : ℝ :=
  -m*p/DD B p w Y m - e*(B*m + (B+p)*Y + (Y+m)*w + 2*(Y+m) - Y)/(2*(Y+m)*DD B p w Y m)
noncomputable def tA (B p w Y m e : ℝ) : ℝ := 2*B + e*(p-1)/(Y+m)
noncomputable def uA (B p w Y m e : ℝ) : ℝ := e - 2*B*zA B p w Y m e

lemma ev_lt (f : ℝ → ℝ) (hf : Continuous f) (h : f 0 < 0) : ∀ᶠ e in 𝓝[>] (0:ℝ), f e < 0 :=
  ((hf.continuousAt.eventually_lt continuousAt_const h).filter_mono nhdsWithin_le_nhds)

set_option maxHeartbeats 32000000 in
theorem waistW_thmA (B P Q W Y dx dz cx cz ex ey ez : ℝ) (hB : 0 < B) (hQ : 0 < Q) (hY : 0 < Y)
    (hW : W ≤ 0) (hBP : B < P) (hYQ : Y < Q)
    (hd0 : 0 < dx) (hd1 : dx < B) (hc0 : 0 < cx) (hc1 : cx < B)
    (hin1 : 0 < ey) (hin3 : Q * ex + (B - P) * ey < Q * B)
    (hin4 : (Y - Q) * ex + (P-W) * ey < P * Y - W*Q) (hin5 : -Y*ex + W*ey < 0) :
    IsRupert (VV B P Q W Y dx dz cx cz ex ey ez) := by
  obtain ⟨p, hp, rfl⟩ : ∃ p, 0 < p ∧ P = B + p := ⟨P - B, by linarith, by ring⟩
  obtain ⟨m, hm, rfl⟩ : ∃ m, 0 < m ∧ Q = Y + m := ⟨Q - Y, by linarith, by ring⟩
  obtain ⟨w, hw, rfl⟩ : ∃ w, 0 ≤ w ∧ W = -w := ⟨-W, by linarith, by ring⟩
  have hD : 0 < DD B p w Y m := by unfold DD; positivity
  have hD' : DD B p w Y m ≠ 0 := hD.ne'
  have hQ' : Y + m ≠ 0 := by positivity
  have hBd : 0 < B - dx := by linarith
  have hBc : 0 < B - cx := by linarith
  have c0 : ∀ f : ℝ → ℝ, (∀ e, f e = f e) → True := fun _ _ => trivial
  have k0 : R0 (uA B p w Y m 0) = -(2*B*m*p)/DD B p w Y m := by
    simp only [R0, uA, zA, DD] at *; field_simp; ring
  have k2 : R2 Y (-w) (tA B p w Y m 0) (uA B p w Y m 0) =
      -(2*B*(B*Y*p + Y^2*m + Y*m^2 + Y*p^2 + Y*p*w + m*p*w))/DD B p w Y m := by
    simp only [R2, tA, uA, zA, DD] at *; field_simp; ring
  have k3 : R3 (-w) Y (zA B p w Y m 0) (tA B p w Y m 0) (uA B p w Y m 0) =
      -(2*(B^2*Y*p + B*Y^2*m + B*Y*m^2 + B*Y*p^2 + 2*B*Y*p*w + B*m*p*w + Y^2*m*p + Y^2*m*w + Y*m^2*w + Y*p^2*w + Y*p*w^2 + m*p*w^2))/DD B p w Y m := by
    simp only [R3, tA, uA, zA, DD] at *; field_simp; ring
  have k5 : R5 B (B+p) (Y+m) (zA B p w Y m 0) (tA B p w Y m 0) (uA B p w Y m 0) =
      -(2*p^2*(B*Y + B*m + Y*p + Y*w + m*w))/DD B p w Y m := by
    simp only [R5, tA, uA, zA, DD] at *; field_simp; ring
  have k7 : R7 (B+p) (Y+m) (-w) Y (zA B p w Y m 0) (tA B p w Y m 0) (uA B p w Y m 0) =
      -(2*m^2*(B*Y + B*m + Y*p + Y*w + m*w))/DD B p w Y m := by
    simp only [R7, tA, uA, zA, DD] at *; field_simp; ring
  have k8 : ∀ x, R1 x (zA B p w Y m 0) (uA B p w Y m 0) = -(2*(B-x)*m*p)/DD B p w Y m := by
    intro x
    simp only [R1, uA, zA, DD] at *; field_simp; ring
  have kk0 : R0 (uA B p w Y m 0) < 0 := by
    rw [k0]; exact div_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) hD
  have kk2 : R2 Y (-w) (tA B p w Y m 0) (uA B p w Y m 0) < 0 := by
    rw [k2]; exact div_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) hD
  have kk3 : R3 (-w) Y (zA B p w Y m 0) (tA B p w Y m 0) (uA B p w Y m 0) < 0 := by
    rw [k3]; exact div_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) hD
  have kk5 : R5 B (B+p) (Y+m) (zA B p w Y m 0) (tA B p w Y m 0) (uA B p w Y m 0) < 0 := by
    rw [k5]; exact div_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) hD
  have kk7 : R7 (B+p) (Y+m) (-w) Y (zA B p w Y m 0) (tA B p w Y m 0) (uA B p w Y m 0) < 0 := by
    rw [k7]; exact div_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) hD
  have kk8 : R1 dx (zA B p w Y m 0) (uA B p w Y m 0) < 0 := by
    rw [k8]; exact div_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) hD
  have kk9 : R1 cx (zA B p w Y m 0) (uA B p w Y m 0) < 0 := by
    rw [k8]; exact div_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) hD
  have ev : ∀ᶠ e in 𝓝[>] (0:ℝ),
      (R0 (uA B p w Y m e) < 0 ∧ R2 Y (-w) (tA B p w Y m e) (uA B p w Y m e) < 0 ∧
       R3 (-w) Y (zA B p w Y m e) (tA B p w Y m e) (uA B p w Y m e) < 0 ∧
       R5 B (B+p) (Y+m) (zA B p w Y m e) (tA B p w Y m e) (uA B p w Y m e) < 0 ∧
       R7 (B+p) (Y+m) (-w) Y (zA B p w Y m e) (tA B p w Y m e) (uA B p w Y m e) < 0 ∧
       R1 dx (zA B p w Y m e) (uA B p w Y m e) < 0 ∧ R1 cx (zA B p w Y m e) (uA B p w Y m e) < 0) ∧ 0 < e := by
    refine Filter.Eventually.and ?_ self_mem_nhdsWithin
    refine (ev_lt _ ?_ kk0).and ((ev_lt _ ?_ kk2).and ((ev_lt _ ?_ kk3).and ((ev_lt _ ?_ kk5).and
      ((ev_lt _ ?_ kk7).and ((ev_lt _ ?_ kk8).and (ev_lt _ ?_ kk9)))))) <;>
    simp only [R0, R1, R2, R3, R5, R7, zA, tA, uA] <;> fun_prop
  obtain ⟨e, ⟨⟨s0, s2, s3, s5, s7, s8, s9⟩, he⟩⟩ := ev.exists
  have s1 : R1 B (zA B p w Y m e) (uA B p w Y m e) < 0 := by
    have : R1 B (zA B p w Y m e) (uA B p w Y m e) = -e := by simp only [R1, uA]; ring
    rw [this]; linarith
  have s4 : R4 B (B+p) (Y+m) (zA B p w Y m e) (tA B p w Y m e) (uA B p w Y m e) < 0 := by
    have : R4 B (B+p) (Y+m) (zA B p w Y m e) (tA B p w Y m e) (uA B p w Y m e) = -e := by
      simp only [R4, tA, uA, zA, DD]; field_simp; ring
    rw [this]; linarith
  have s6 : R6 (B+p) (Y+m) (-w) Y (zA B p w Y m e) (tA B p w Y m e) (uA B p w Y m e) < 0 := by
    have : R6 (B+p) (Y+m) (-w) Y (zA B p w Y m e) (tA B p w Y m e) (uA B p w Y m e) = -e := by
      simp only [R6, tA, uA, zA, DD]; field_simp; ring
    rw [this]; linarith
  have hk : 0 < (B+p)*Y - (Y+m)*(-w) := by nlinarith [mul_pos hB hY, mul_pos hp hY, mul_nonneg hw hY.le, mul_nonneg hw hm.le]
  have hk2 : 0 < ((B+p)-B)*Y + (Y+m)*(B-(-w)) := by nlinarith [mul_pos hp hY, mul_pos hB hY, mul_pos hB hm, mul_nonneg hw hY.le, mul_nonneg hw hm.le]
  have hdd : (Y-(Y+m))*dx < (B+p)*Y - (Y+m)*(-w) := by nlinarith [mul_pos hm hd0]
  have hcc : (Y-(Y+m))*cx < (B+p)*Y - (Y+m)*(-w) := by nlinarith [mul_pos hm hc0]
  exact waistW_core B (B+p) (Y+m) (-w) Y dx dz cx cz ex ey ez hB hQ hY hW hBP.le hk hk2 hd0 hd1 hc0 hc1 hdd hcc
    hin1 hin3 hin4 hin5 _ _ _ s0 s1 s2 s3 s4 s5 s6 s7 s8 s9

end WaistW
