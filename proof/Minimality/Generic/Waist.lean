module

public import Minimality.Generic.CayleyJet
public import Minimality.PolygonHalfPlanes
public import Minimality.Generic.WaistJet

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace
open Polynomial Minimality
namespace Waist

noncomputable def cc (B P Q Y : ℝ) : ZMod 4 → ℝ² :=
  ![!₂[0,0], !₂[B,0], !₂[P,Q], !₂[0,Y]]

lemma cc0 : cc B P Q Y 0 = !₂[0,0] := rfl
lemma cc1 : cc B P Q Y 1 = !₂[B,0] := rfl
lemma cc2 : cc B P Q Y 2 = !₂[P,Q] := rfl
lemma cc3 : cc B P Q Y 3 = !₂[0,Y] := rfl
lemma z12 : (1 : ZMod 4) + 1 = 2 := by decide
lemma z23 : (2 : ZMod 4) + 1 = 3 := by decide
lemma z30 : (3 : ZMod 4) + 1 = 0 := by decide

lemma zc4 (i : ZMod 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide

noncomputable def nq (B P Q Y : ℝ) : Fin 4 → ℝ² :=
  ![!₂[0,-B], !₂[Q,B-P], !₂[Y-Q,P], !₂[-Y,0]]
noncomputable def hq (B P Q Y : ℝ) : Fin 4 → ℝ := ![0, Q*B, P*Y, 0]

noncomputable def vA : ℝ³ := !₂[0,0,0]
noncomputable def vB (B : ℝ) : ℝ³ := !₂[B,0,0]

open Classical in
noncomputable def VV (B P Q Y dx dz cx cz ex ey ez : ℝ) : Finset ℝ³ :=
  {!₂[0,0,0], !₂[B,0,0], !₂[P,Q,0], !₂[0,Y,0], !₂[dx,0,dz], !₂[cx,0,cz], !₂[ex,ey,ez]}

lemma waist_reduce (B P Q Y dx dz cx cz ex ey ez : ℝ) (hB : 0 < B) (hP : 0 < P) (hQ : 0 < Q) (hY : 0 < Y)
    (hconv : B * (Y - Q) < P * Y)
    (z t2 t3 t4 u2 u3 u4 : ℝ)
    (hlex : ∀ v ∈ VV B P Q Y dx dz cx cz ex ey ez, ∀ e : Fin 4,
      (pj (jc ((nq B P Q Y e) 0) ((nq B P Q Y e) 1) (hq B P Q Y e) (v 0) (v 1) (v 2) z t2 t3 t4 u2 u3 u4)).trailingCoeff < 0) :
    IsRupert (VV B P Q Y dx dz cx cz ex ey ez) := by
  classical
  have hccw : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      0 < cross2 (cc B P Q Y (i + 1) - cc B P Q Y i) (cc B P Q Y j - cc B P Q Y i) := by
    intro i j h1 h2
    rcases zc4 i with rfl | rfl | rfl | rfl <;> rcases zc4 j with rfl | rfl | rfl | rfl <;>
      first | (exfalso; apply h1; rfl) | (exfalso; apply h2; decide) | skip
    all_goals
      simp [cross2, z12, z23, z30, cc0, cc1, cc2, cc3]
      nlinarith [mul_pos hB hQ, mul_pos hP hY, mul_pos hY hB]
  obtain ⟨hp1, -⟩ := halfPlanes_of_ccwPolygon (cc B P Q Y) (by norm_num) hccw
  have hsub : convexHull ℝ (Set.range (cc B P Q Y)) ⊆
      proj_xy '' convexHull ℝ (VV B P Q Y dx dz cx cz ex ey ez : Set ℝ³) := by
    refine convexHull_min ?_ ((convex_convexHull ℝ _).linear_image projL)
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨!₂[0,0,0], subset_convexHull ℝ _ (by simp [VV]), by ext a; fin_cases a <;> simp [cc, proj_xy]⟩
    · exact ⟨!₂[B,0,0], subset_convexHull ℝ _ (by simp [VV]), by ext a; fin_cases a <;> simp [cc, proj_xy]⟩
    · exact ⟨!₂[P,Q,0], subset_convexHull ℝ _ (by simp [VV]), by ext a; fin_cases a <;> simp [cc, proj_xy]⟩
    · exact ⟨!₂[0,Y,0], subset_convexHull ℝ _ (by simp [VV]), by ext a; fin_cases a <;> simp [cc, proj_xy]⟩
  have hpoly : {y : ℝ² | ∀ e : Fin 4, ⟪nq B P Q Y e, y⟫ < hq B P Q Y e} ⊆
      proj_xy '' convexHull ℝ (VV B P Q Y dx dz cx cz ex ey ez : Set ℝ³) := by
    intro y hy
    apply hsub; apply hp1
    intro i
    have := hy (i : Fin 4)
    rcases zc4 i with rfl | rfl | rfl | rfl <;> simp [nq, hq, rot90, z12, z23, z30, cc0, cc1, cc2, cc3, PiLp.inner_apply, Fin.sum_univ_two] at this ⊢ <;> linarith
  refine isRupert_of_cayleyPolyJet _ (nq B P Q Y) (hq B P Q Y) hpoly ![0, X, C z * X^2]
    ![C t2 * X^2 + C t3 * X^3 + C t4 * X^4, C u2 * X^2 + C u3 * X^3 + C u4 * X^4] ?_
  intro v hv e
  rw [N_eq]
  exact hlex v hv e

syntax "tcm " num " [" term,* "]" : tactic
macro_rules
  | `(tactic| tcm $m [$ts,*]) => `(tactic|
      (refine pj_tc _ $m (by norm_num) (fun i hi => by interval_cases i <;> simp [jc, nq, hq] <;> ring) ?_
       simp [jc, nq, hq]
       nlinarith [$ts,*]))

set_option maxHeartbeats 16000000 in
lemma waist_core1 (B P Q Y dx dz cx cz ex ey ez : ℝ) (hB : 0 < B) (hP : 0 < P) (hQ : 0 < Q) (hY : 0 < Y)
    (hYQ : Q < Y) (hconv : B * (Y - Q) < P * Y)
    (hd0 : 0 < dx) (hd1 : dx < B) (hc0 : 0 < cx) (hc1 : cx < B)
    (hin1 : 0 < ey) (hin2 : 0 < ex) (hin3 : Q * ex + (B - P) * ey < Q * B)
    (hin4 : (Y - Q) * ex + P * ey < P * Y)
    (z eps : ℝ) (hz : 0 < z) (heps : 2 * (Y - Q) * eps = P * Y * z ^ 2) (hepos : 0 < eps)
    (h1 : z * (B ^ 2 - B * P + Q * Y) < Q * B)
    (h2 : z * (B * P - P ^ 2 - Q ^ 2 + Q * Y) < P * Q)
    (h3 : z * (P ^ 2 + (Q - Y) ^ 2) < P * (Y - Q)) :
    IsRupert (VV B P Q Y dx dz cx cz ex ey ez) := by
  refine waist_reduce B P Q Y dx dz cx cz ex ey ez hB hP hQ hY hconv z (2*Y*z) 0 (eps - 2*Y*z) 0 0 (Y*z^2) ?_
  intro v hv e
  simp only [VV, Finset.mem_insert, Finset.mem_singleton] at hv
  have hz2 := pow_pos hz 2
  have hBY := mul_pos hB hY
  have hBQ := mul_pos hB hQ
  have hPY := mul_pos hP hY
  have hYY := mul_pos hY hY
  have hY' : 0 < Y - Q := by linarith
  have hBd := mul_pos hY' (sub_pos.2 hd1)
  have hBc := mul_pos hY' (sub_pos.2 hc1)
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> fin_cases e
  -- a
  · tcm 4 [mul_pos hBY hz2]
  · tcm 0 [hBQ]
  · tcm 0 [hPY]
  · tcm 2 [mul_pos hYY hz]
  -- b
  · tcm 2 [mul_pos (mul_pos hB hB) hz]
  · tcm 2 [h1]
  · tcm 0 [hconv]
  · tcm 0 [hBY]
  -- a'
  · tcm 0 [hBQ]
  · tcm 2 [h2]
  · tcm 2 [h3]
  · tcm 0 [hPY]
  -- b'
  · tcm 0 [hBY]
  · tcm 0 [hconv]
  · tcm 4 [heps, mul_pos hPY hz2]
  · tcm 4 [mul_pos hY hepos]
  -- d
  · tcm 2 [mul_pos (mul_pos hB hd0) hz]
  · tcm 0 [mul_pos hQ (sub_pos.2 hd1)]
  · tcm 0 [hBd, hconv]
  · tcm 0 [mul_pos hY hd0]
  -- c'
  · tcm 2 [mul_pos (mul_pos hB hc0) hz]
  · tcm 0 [mul_pos hQ (sub_pos.2 hc1)]
  · tcm 0 [hBc, hconv]
  · tcm 0 [mul_pos hY hc0]
  -- c
  · tcm 0 [mul_pos hB hin1]
  · tcm 0 [hin3]
  · tcm 0 [hin4]
  · tcm 0 [mul_pos hY hin2]

syntax "tcz " num " [" term,* "]" : tactic
macro_rules
  | `(tactic| tcz $m [$ts,*]) => `(tactic|
      (refine pj_tc _ $m (by norm_num) (fun i hi => by interval_cases i <;> simp [jc, nq, hq] <;> (try field_simp) <;> ring) ?_
       simp [jc, nq, hq]
       nlinarith [$ts,*]))

set_option hygiene false in
syntax "tcd " num "[" term "]" "[" term,* "]" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| tcd $m [$N] [$ts,*]) => `(tactic|
      (refine pj_tc _ $m (by norm_num) (fun i hi => by interval_cases i <;> simp [jc, nq, hq] <;> (try field_simp) <;> ring) ?_
       suffices hh : ($N) / (P^2+(Q-Y)^2) < 0 by
         refine lt_of_eq_of_lt ?_ hh
         simp [jc, nq, hq]
         field_simp <;> ring
       exact div_neg_of_neg_of_pos (by nlinarith [$ts,*]) hD))

lemma z_aux (a b z : ℝ) (hz : 0 < z) (hm : z ≤ b / (|a| + 1)) : z * a < b := by
  have hp : 0 < |a| + 1 := by positivity
  rw [le_div_iff₀ hp] at hm
  nlinarith [le_abs_self a, mul_le_mul_of_nonneg_left (le_abs_self a) hz.le]

lemma exists_z3 (a1 a2 a3 b1 b2 b3 : ℝ) (h1 : 0 < b1) (h2 : 0 < b2) (h3 : 0 < b3) :
    ∃ z : ℝ, 0 < z ∧ z * a1 < b1 ∧ z * a2 < b2 ∧ z * a3 < b3 := by
  have p1 : 0 < b1/(|a1|+1) := by positivity
  have p2 : 0 < b2/(|a2|+1) := by positivity
  have p3 : 0 < b3/(|a3|+1) := by positivity
  have hz : 0 < min (min (b1/(|a1|+1)) (b2/(|a2|+1))) (b3/(|a3|+1)) := by
    simp only [lt_min_iff]; tauto
  refine ⟨_, hz, z_aux _ _ _ hz ((min_le_left _ _).trans (min_le_left _ _)),
    z_aux _ _ _ hz ((min_le_left _ _).trans (min_le_right _ _)), z_aux _ _ _ hz (min_le_right _ _)⟩

theorem waist_thm1 (B P Q Y dx dz cx cz ex ey ez : ℝ) (hB : 0 < B) (hP : 0 < P) (hQ : 0 < Q) (hY : 0 < Y)
    (hYQ : Q < Y) (hconv : B * (Y - Q) < P * Y)
    (hd0 : 0 < dx) (hd1 : dx < B) (hc0 : 0 < cx) (hc1 : cx < B)
    (hin1 : 0 < ey) (hin2 : 0 < ex) (hin3 : Q * ex + (B - P) * ey < Q * B)
    (hin4 : (Y - Q) * ex + P * ey < P * Y) :
    IsRupert (VV B P Q Y dx dz cx cz ex ey ez) := by
  obtain ⟨z, hz, h1, h2, h3⟩ := exists_z3 (B ^ 2 - B * P + Q * Y) (B * P - P ^ 2 - Q ^ 2 + Q * Y)
    (P ^ 2 + (Q - Y) ^ 2) (Q * B) (P * Q) (P * (Y - Q)) (mul_pos hQ hB) (mul_pos hP hQ)
    (mul_pos hP (by linarith))
  have hY' : 0 < Y - Q := by linarith
  obtain ⟨eps, heps⟩ : ∃ eps, 2 * (Y - Q) * eps = P * Y * z ^ 2 :=
    ⟨P * Y * z ^ 2 / (2 * (Y - Q)), by field_simp⟩
  have hepos : 0 < eps := by
    have : 0 < 2 * (Y - Q) * eps := by rw [heps]; positivity
    by_contra hc; push Not at hc; nlinarith
  exact waist_core1 B P Q Y dx dz cx cz ex ey ez hB hP hQ hY hYQ hconv hd0 hd1 hc0 hc1 hin1 hin2 hin3 hin4
    z eps hz heps hepos h1 h2 h3

end Waist
