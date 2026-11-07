module

public import Minimality.Type20IMCC
public import Minimality.Type20IMCD
public import Minimality.Type20IMCE

@[expose] public section

/-!
# Type 20, item I_MC (part F): the last corner leaves, and I_MC is Rupert

The corner leaves T and Wt, then `Frame20.imc_corner` (the corner `A = K = 0`, branch tree of the covering notes), the top-level
theorems `isRupert_IMC` (with the corner and tie hypotheses) and `isRupert_IMC_all`,
`isRupert_IMC_R` (the `R`-image, lines 279 and 285 of `CaseC20Face`), with no hypotheses beyond the
two equations.
-/

section

/-!
# C9: corner leaf T
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace Cor

/-- The last depth fact of T: `z2 < 0` or `z2 < z6`, in abstract form
(`z = z6`, `e` the quantity `kk tm - p`). -/
lemma z2_lt (sp kk sm t z e : ℝ) (sp0 : 0 < sp) (sp1 : sp < 1) (kk0 : 0 < kk) (sm0 : 0 < sm)
    (sm1 : sm < 1) (t0 : 0 < t) (hG : kk*(1-sm) - sp < 0) (hC : 0 < sm*t*e - (1-sm)*z) :
    sp*z - kk*sm*t*e < 0 ∨ sp*z - kk*sm*t*e < z := by
  have s1 : 0 < 1 - sm := by linarith
  have k1 : 0 < kk*sm*t := by positivity
  by_cases he0 : 0 ≤ e
  · by_cases hz0 : 0 < z
    · right
      have h7 : 0 ≤ kk*sm*t*e := mul_nonneg k1.le he0
      have h8 : sp*z < 1*z := mul_lt_mul_of_pos_right sp1 hz0
      linarith
    · left
      push Not at hz0
      by_cases hz1 : z < 0
      · have h7 : 0 ≤ kk*sm*t*e := mul_nonneg k1.le he0
        have h8 : sp*z < 0 := mul_neg_of_pos_of_neg sp0 hz1
        linarith
      · have hz : z = 0 := le_antisymm hz0 (not_lt.1 hz1)
        subst hz
        have h1 : 0 < e := by
          have : 0 < sm*t*e := by linarith
          exact pos_of_mul_pos_right this (by positivity)
        have : 0 < kk*sm*t*e := mul_pos k1 h1
        linarith
  · push Not at he0
    left
    have hz0 : z < 0 := by
      have h1 : sm*t*e < 0 := mul_neg_of_pos_of_neg (by positivity) he0
      by_contra hn; push Not at hn
      have := mul_nonneg s1.le hn
      linarith
    have h5 : sm*t*(-e) < (1-sm)*(-z) := by linarith
    have h6 : kk*(sm*t*(-e)) < kk*((1-sm)*(-z)) := mul_lt_mul_of_pos_left h5 kk0
    have h9 : 0 < (sp - kk*(1-sm)) * (-z) := mul_pos (by linarith) (by linarith)
    nlinarith

/-- **Leaf T**: view `u = (tp, -sp, q - kk)` (`x0 - x2`), tilt `(2 tp, -1, 2 q)`. -/
theorem leaf_T {q tm sp sm kk B : ℝ} (h : Hy q tm sp sm kk B) (hK : 0 ≤ Kc q tm sp sm kk)
    (hG : Kg sp sm kk < 0) (hBp : psiN tm sm ≤ B*(sm*(1-sm))) (hBd : Bd q tm sp sm kk ≤ 0) :
    LeafOK q tm sp sm kk B cycT patT (1-q*tm) (-sp) (q-kk) (2*(1-q*tm)) (-1) (2*q) := by
  obtain ⟨tm0, sm0, sp0, q0, tp0, kk0, t1, r1, s1, q2, tmsm⟩ := h.pf
  have hroof := h.roof
  have hQ := h.hQ
  have hBt := h.hB
  have hGs := Gs_pos h hBd
  have hC := Cone_pos h hK hBp
  have e0 : NN q tm sp sm kk (1-q*tm) (-sp) (q-kk) 0 = sm*(1-q) - tm*sp + (1-tm)*sm*kk := by
    rw [NN_0]; ring
  have e1 : NN q tm sp sm kk (1-q*tm) (-sp) (q-kk) 1 = 0 := by rw [NN_1]; ring
  have e2 : NN q tm sp sm kk (1-q*tm) (-sp) (q-kk) 2 = sp := by rw [NN_2]; ring
  have e3 : NN q tm sp sm kk (1-q*tm) (-sp) (q-kk) 3 = -(sm - tm*sp - sm*tm*kk) := by
    rw [NN_3]; ring
  have e4 : NN q tm sp sm kk (1-q*tm) (-sp) (q-kk) 4 = q*((1-sp) - kk*tm) := by rw [NN_4]; ring
  have e5 : NN q tm sp sm kk (1-q*tm) (-sp) (q-kk) 5 = 0 := by rw [NN_5]; ring
  have e6 : NN q tm sp sm kk (1-q*tm) (-sp) (q-kk) 6 = (1-sp) - q*(1+tm-sm) + (1-sm)*kk := by
    rw [NN_6]; ring
  have e7 : NN q tm sp sm kk (1-q*tm) (-sp) (q-kk) 7 = -(kk*(1-q*tm)) := by rw [NN_7]; ring
  have v1 : NN q tm sp sm kk (2*(1-q*tm)) (-1) (2*q) 1 = kk*(1-q*tm) := by rw [NN_1]; ring
  have v5 : NN q tm sp sm kk (2*(1-q*tm)) (-1) (2*q) 5 = kk*(1-q*tm) := by rw [NN_5]; ring
  have pA : 0 < sm*(1-q) - tm*sp + (1-tm)*sm*kk := by
    have : tm*sp < tm := by nlinarith
    have : 0 < (1-tm)*sm*kk := by positivity
    linarith
  have pD : 0 < sm - tm*sp - sm*tm*kk := by nlinarith
  refine ⟨⟨2, ?_⟩, ?_, ?_⟩
  · rw [e2]; exact sp0.ne'
  · intro t
    have ht : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 := by revert t; decide
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨fun _ => lp1 (by rw [e0]; exact pA), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp2 e1 (by rw [v1]; positivity), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp1 (by rw [e2]; exact sp0), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lp1 (by rw [e3]; linarith)⟩
    · exact ⟨fun _ => lp1 (by rw [e4]; exact mul_pos q0 (by linarith)), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp2 e5 (by rw [v5]; positivity), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp1 (by rw [e6]; exact hGs), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lp1 (by
        rw [e7]; have : 0 < kk*(1-q*tm) := by positivity
        linarith)⟩
  · have d35 : zN q tm sp sm kk B (1-q*tm) (-sp) (q-kk) 3 = tm * (sm*(1-q) - tm*sp + (1-tm)*sm*kk) := by
      rw [zN_3]; ring
    have d34 : zN q tm sp sm kk B (1-q*tm) (-sp) (q-kk) 3 - zN q tm sp sm kk B (1-q*tm) (-sp) (q-kk) 4 =
        (B*sm - tm^2)*sp := by rw [zN_3, zN_4]; ring
    have d46 : zN q tm sp sm kk B (1-q*tm) (-sp) (q-kk) 4 - zN q tm sp sm kk B (1-q*tm) (-sp) (q-kk) 6 =
        Cone q tm sp sm kk B := by rw [zN_4, zN_6]; unfold Cone; ring
    have z6 : zN q tm sp sm kk B (1-q*tm) (-sp) (q-kk) 6 = tm*(1-q*tm) - sp*B := by
      rw [zN_6]; ring
    have z2 : zN q tm sp sm kk B (1-q*tm) (-sp) (q-kk) 2 =
        sp*(tm*(1-q*tm) - sp*B) - kk*sm*(1-tm)*(kk*tm - q*tm) := by rw [zN_2]; ring
    refine ruT ?_ ?_ ?_ ?_
    · show zN q tm sp sm kk B _ _ _ 5 < zN q tm sp sm kk B _ _ _ 3
      rw [zN_5, d35]; positivity
    · show zN q tm sp sm kk B _ _ _ 4 < zN q tm sp sm kk B _ _ _ 3
      have : 0 < (B*sm - tm^2)*sp := by
        have : 0 < B*sm - tm^2 := by
          nlinarith [mul_le_mul_of_nonneg_right hBt sm0.le, mul_pos tm0 (sub_pos.2 tmsm)]
        positivity
      linarith
    · show zN q tm sp sm kk B _ _ _ 6 < zN q tm sp sm kk B _ _ _ 4
      linarith
    · show zN q tm sp sm kk B _ _ _ 2 < zN q tm sp sm kk B _ _ _ 5 ∨
        zN q tm sp sm kk B _ _ _ 2 < zN q tm sp sm kk B _ _ _ 6
      rw [zN_5, z6, z2]
      unfold Cone at hC
      unfold Kg at hG
      have hC' : 0 < sm*(1-tm)*(tm*kk - q*tm) - (1-sm)*(tm*(1-q*tm) - sp*B) := by
        have : kk*tm = tm*kk := mul_comm _ _
        rw [← this]; exact hC
      have := z2_lt sp kk sm (1-tm) (tm*(1-q*tm) - sp*B) (kk*tm - q*tm) sp0 h.sp_lt kk0 sm0 h.sm_lt t1 hG
        (by simpa using hC)
      have e1 : kk*sm*(1-tm)*(kk*tm - q*tm) = kk*sm*(1-tm)*(kk*tm - q*tm) := rfl
      rcases this with h1 | h1
      · left; linarith
      · right; linarith

end Cor
end Minimality.CaseC20

end

section

/-!
# C10: corner leaf Wt (`Kc = 0`, `Kg >= 0`, `Cone = 0`): cycle `(0,1,4,5,2)`
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace Cor

/-- Five-cycle shape of Wt: `z0 < z1`, `z3 < z2`, `z4 < z0`, `z4 < z3`. -/
theorem ruWt {z : ZMod 5 → ℝ} (h01 : z 0 < z 1) (h32 : z 3 < z 2) (h40 : z 4 < z 0)
    (h43 : z 4 < z 3) : RobUni z := by robuni5

/-- Negativity of the facet `F` value at the view of Wt. -/
lemma Wt_F_neg {q tm sp sm kk B : ℝ} (h : Hy q tm sp sm kk B) :
    q*tm*(1-sm)*(kk - q*(1-sp)) - (1-q*tm)*(kk*(1-sm) + (1-sp)*(1-q*tm)) < 0 := by
  obtain ⟨tm0, sm0, sp0, q0, tp0, kk0, t1, r1, s1, q2, tmsm⟩ := h.pf
  have hroof := h.roof
  have key : tm * (q*tm*(1-sm)*(kk - q*(1-sp)) - (1-q*tm)*(kk*(1-sm) + (1-sp)*(1-q*tm))) =
      (kk*tm)*(1-sm)*(2*(q*tm)-1) - (1-sp)*((q*tm)^2*(1-sm) + tm*(1-q*tm)^2) := by ring
  have hneg : 0 < (1-sp)*((q*tm)^2*(1-sm) + tm*(1-q*tm)^2) := by positivity
  have : tm * (q*tm*(1-sm)*(kk - q*(1-sp)) - (1-q*tm)*(kk*(1-sm) + (1-sp)*(1-q*tm))) < 0 := by
    rw [key]
    by_cases hp : 2*(q*tm) - 1 ≤ 0
    · have : (kk*tm)*(1-sm)*(2*(q*tm)-1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hp
      linarith
    · push Not at hp
      have h1 : (kk*tm)*(1-sm)*(2*(q*tm)-1) ≤ (1-sp)*(1-sm)*(2*(q*tm)-1) := by
        apply mul_le_mul_of_nonneg_right _ hp.le
        exact mul_le_mul_of_nonneg_right hroof.le s1.le
      have h2 : (1-sp)*(1-sm)*(2*(q*tm)-1) - (1-sp)*((q*tm)^2*(1-sm) + tm*(1-q*tm)^2) =
          -((1-sp)*(1-q*tm)^2*((1-sm) + tm)) := by ring
      have : 0 < (1-sp)*(1-q*tm)^2*((1-sm) + tm) := by positivity
      linarith
  exact neg_of_mul_neg_right this tm0.le

set_option maxHeartbeats 800000 in
/-- **Leaf Wt**: view `u = (p (1-sm), -(1-sm), -tp)`, tilt `(-(1-tm), 0, -1)` (`x3 - x1`). -/
theorem leaf_Wt {q tm sp sm kk B : ℝ} (h : Hy q tm sp sm kk B) (hK : Kc q tm sp sm kk = 0)
    (hG : 0 ≤ Kg sp sm kk) (hC : Cone q tm sp sm kk B = 0) :
    LeafOK q tm sp sm kk B cycWt patWt (q*tm*(1-sm)) (-(1-sm)) (-(1-q*tm)) (-(1-tm)) 0 (-1) := by
  obtain ⟨tm0, sm0, sp0, q0, tp0, kk0, t1, r1, s1, q2, tmsm⟩ := h.pf
  have hBt := h.hB
  have hF5 := Wt_F_neg h
  have hq1 : q < 1 := by linarith
  have g1 : 0 < 1 + tm - sm := by linarith
  have g1' : 1 + tm - sm < 1 := by linarith
  have qs : 0 < 1 - q*(1+tm-sm) := by nlinarith
  have e0 : NN q tm sp sm kk (q*tm*(1-sm)) (-(1-sm)) (-(1-q*tm)) 0 = (sm-tm)*(1-q*tm*sm) := by
    rw [NN_0]; ring
  have e1 : NN q tm sp sm kk (q*tm*(1-sm)) (-(1-sm)) (-(1-q*tm)) 1 =
      (1-q*tm)*Kg sp sm kk + q*tm*sp*(1 - q*(1+tm-sm)) := by
    rw [NN_1]; unfold Kg; ring
  have e2 : NN q tm sp sm kk (q*tm*(1-sm)) (-(1-sm)) (-(1-q*tm)) 2 = 1 - sm := by rw [NN_2]; ring
  have e3 : NN q tm sp sm kk (q*tm*(1-sm)) (-(1-sm)) (-(1-q*tm)) 3 =
      tm - q*tm*sm*(1+tm-sm) := by
    rw [NN_3]; ring
  have e4 : NN q tm sp sm kk (q*tm*(1-sm)) (-(1-sm)) (-(1-q*tm)) 4 = -((1-q*tm)*(q*((1-sm)+tm))) := by
    rw [NN_4]; ring
  have e5 : NN q tm sp sm kk (q*tm*(1-sm)) (-(1-sm)) (-(1-q*tm)) 5 =
      q*tm*(1-sm)*(kk - q*(1-sp)) - (1-q*tm)*(kk*(1-sm) + (1-sp)*(1-q*tm)) := by
    rw [NN_5]; ring
  have e6 : NN q tm sp sm kk (q*tm*(1-sm)) (-(1-sm)) (-(1-q*tm)) 6 = 0 := by rw [NN_6]; ring
  have e7 : NN q tm sp sm kk (q*tm*(1-sm)) (-(1-sm)) (-(1-q*tm)) 7 = -(kk*(q*tm*(1-sm))) := by
    rw [NN_7]; ring
  have v6 : NN q tm sp sm kk (-(1-tm)) 0 (-1) 6 = tm - sm := by rw [NN_6]; ring
  have hQ := h.hQ
  have pd : 0 < sm - tm := by linarith
  have p3 : 0 < tm - q*tm*sm*(1+tm-sm) := by
    have a1 : q*sm < 1 := mul_lt_one_of_nonneg_of_lt_one_left q0.le hq1 h.sm_lt.le
    have a2 : q*sm*(1+tm-sm) < 1 := mul_lt_one_of_nonneg_of_lt_one_left (by positivity) a1 g1'.le
    have := mul_pos tm0 (sub_pos.2 a2)
    linarith
  have pT : 0 < 1 - q*tm*sm := by
    have := mul_lt_one_of_nonneg_of_lt_one_left (mul_pos q0 tm0).le (by linarith : q*tm < 1) h.sm_lt.le
    linarith
  have hBs : (1-sm)*B = (1-sm)*tm*(1-q*tm) + sm*(1-tm)*(q*tm) := by
    have : sp * ((1-sm)*B - ((1-sm)*tm*(1-q*tm) + sm*(1-tm)*(q*tm))) = 0 := by
      unfold Cone at hC; unfold Kc at hK
      linear_combination hC - hK
    have := (mul_eq_zero.1 this).resolve_left sp0.ne'
    linarith
  have qtm : q*(1+tm) < 1 := by
    have h1 : sm*q ≤ sm - tm := by linarith
    have h2 : sm*(q*(1+tm)) ≤ (sm - tm)*(1+tm) := by nlinarith
    have h3 : (sm - tm)*(1+tm) < sm := by nlinarith
    by_contra hn; push Not at hn
    nlinarith
  have z4v : zN q tm sp sm kk B (q*tm*(1-sm)) (-(1-sm)) (-(1-q*tm)) 4 =
      sm*(sm-tm)*(tm - q*tm*(1+tm)) := by
    rw [zN_4]; linear_combination (-sm) * hBs
  have z4p : 0 < sm*(sm-tm)*(tm - q*tm*(1+tm)) := by
    have : 0 < tm - q*tm*(1+tm) := by nlinarith
    have : 0 < sm - tm := by linarith
    positivity
  have d10 : zN q tm sp sm kk B (q*tm*(1-sm)) (-(1-sm)) (-(1-q*tm)) 1 -
      zN q tm sp sm kk B (q*tm*(1-sm)) (-(1-sm)) (-(1-q*tm)) 0 = q*tm*((sm-tm)*(1-q*tm*sm)) := by
    rw [zN_1, zN_0]; ring
  have d02 : zN q tm sp sm kk B (q*tm*(1-sm)) (-(1-sm)) (-(1-q*tm)) 0 -
      zN q tm sp sm kk B (q*tm*(1-sm)) (-(1-sm)) (-(1-q*tm)) 2 = q*tm*((sm-tm)*((1-sm)*(1-q*tm) + sp*(q*tm))) := by
    rw [zN_0, zN_2]
    unfold Cone at hC; unfold Kc at hK
    linear_combination hC - (q*tm) * hK
  have z2n : zN q tm sp sm kk B (q*tm*(1-sm)) (-(1-sm)) (-(1-q*tm)) 2 < 0 := by
    have : zN q tm sp sm kk B (q*tm*(1-sm)) (-(1-sm)) (-(1-q*tm)) 2 =
        -(sp*(1-sm)*(B - tm*(q*tm)) + kk*sm*(1-tm)*tm*(1-q*tm)) := by rw [zN_2]; ring
    rw [this]
    have h1 : 0 < B - tm*(q*tm) := by
      have := mul_lt_mul_of_pos_left (by linarith : q*tm < 1) tm0
      linarith
    have k1 : 0 < sp*(1-sm)*(B - tm*(q*tm)) := mul_pos (mul_pos sp0 s1) h1
    have k2 : 0 < kk*sm*(1-tm)*tm*(1-q*tm) :=
      mul_pos (mul_pos (mul_pos (mul_pos kk0 sm0) t1) tm0) tp0
    linarith
  refine ⟨⟨2, ?_⟩, ?_, ?_⟩
  · rw [e2]; exact s1.ne'
  · intro t
    have ht : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 := by revert t; decide
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨fun _ => lp1 (by rw [e0]; positivity), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp1 (by
        rw [e1]; have := mul_nonneg tp0.le hG; have : 0 < q*tm*sp*(1 - q*(1+tm-sm)) := by positivity
        linarith), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp1 (by rw [e2]; exact s1), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp1 (by rw [e3]; exact p3), fun h => absurd h (by decide)⟩
    · have : 0 < (1-q*tm)*(q*((1-sm)+tm)) := by positivity
      exact ⟨fun h => absurd h (by decide), fun _ => lp1 (by rw [e4]; linarith)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lp1 (by rw [e5]; linarith)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lp2 (by rw [e6]; ring) (by rw [v6]; linarith)⟩
    · have : 0 < kk*(q*tm*(1-sm)) := by positivity
      exact ⟨fun h => absurd h (by decide), fun _ => lp1 (by rw [e7]; linarith)⟩
  · refine ruWt ?_ ?_ ?_ ?_
    · show zN q tm sp sm kk B _ _ _ 0 < zN q tm sp sm kk B _ _ _ 1
      have : 0 < q*tm*((sm-tm)*(1-q*tm*sm)) := by
        have : 0 < sm - tm := by linarith
        have : 0 < 1 - q*tm*sm := by nlinarith
        positivity
      linarith
    · show zN q tm sp sm kk B _ _ _ 5 < zN q tm sp sm kk B _ _ _ 4
      rw [zN_5, z4v]; exact z4p
    · show zN q tm sp sm kk B _ _ _ 2 < zN q tm sp sm kk B _ _ _ 0
      have : 0 < q*tm*((sm-tm)*((1-sm)*(1-q*tm) + sp*(q*tm))) := by
        have : 0 < sm - tm := by linarith
        positivity
      linarith
    · show zN q tm sp sm kk B _ _ _ 2 < zN q tm sp sm kk B _ _ _ 5
      rw [zN_5]; exact z2n

end Cor
end Minimality.CaseC20

end

section

/-!
# C11: the corner `A = K = 0` of I_MC (`Q >= 0`, `F15 >= 0`): the branch tree of GAPS.md section 1.3
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- **I_MC, corner `A = K = 0`**: with `Q >= 0` and `F15 >= 0` the point set is Rupert.  The proof
passes to the corner normal form (`hp = hm q`, `kp = hm kk`, `km = hm`, `tp = 1 - q tm`, depths
`b * zN`) and splits by the signs of `Kc`, `Kg`, `B - psi`, `Bd` and `(Kc, C1)` into the six leaves
L6K, W, Wt, Y, X, T. -/
theorem imc_corner (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hI : F.IMC) (hA : (F.S.hm*F.S.tp-F.S.hm+F.S.hp*F.S.tm) = 0) (hK : (F.S.km-F.S.hm) = 0) (hQ : 0 ≤ (F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm*F.S.tp)-F.S.hp*F.S.sm*(1-F.S.tm))) (hF : 0 ≤ (F.S.kp-F.S.hp*(1-F.S.sp))) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨b, q, kk, B, hb, hkm, hhp, hkp, htp, hH, hdep⟩ := Cor.corner_data F hI hA hK hQ hF
  have asm := fun {k : ℕ} [NeZero k] (hk : 3 ≤ k) {c : ZMod k → Fin 7} (hc : Function.Injective c)
      {pat : Fin 8 → Bool} (hcyc : S0xCycOK h20s_S c pat) {ux uy uz vx vy vz : ℝ}
      (L : Cor.LeafOK q F.S.tm F.S.sp F.S.sm kk B c pat ux uy uz vx vy vz) =>
    Cor.corner_assemble F hx hR hb hkm hhp hkp htp hdep hk hc hcyc L
  by_cases hk1 : Cor.Kc q F.S.tm F.S.sp F.S.sm kk < 0
  · exact asm (by norm_num) Cor.cycL_inj Cor.cycL_ok (Cor.leaf_L6K hH hk1)
  push Not at hk1
  by_cases hg : 0 ≤ Cor.Kg F.S.sp F.S.sm kk
  · by_cases hn : Cor.Kc q F.S.tm F.S.sp F.S.sm kk = 0 ∧ Cor.Cone q F.S.tm F.S.sp F.S.sm kk B = 0
    · exact asm (by norm_num) Cor.cycWt_inj Cor.cycWt_ok
        (Cor.leaf_Wt hH hn.1 hg hn.2)
    · exact asm (by norm_num) Cor.cycW_inj Cor.cycW_ok (Cor.leaf_W hH hk1 hg hn)
  push Not at hg
  by_cases hp : B*(F.S.sm*(1-F.S.sm)) < Cor.psiN F.S.tm F.S.sm
  · exact asm (by norm_num) Cor.cycY_inj Cor.cycY_ok (Cor.leaf_Y hH hg hp)
  push Not at hp
  by_cases hd : 0 < Cor.Bd q F.S.tm F.S.sp F.S.sm kk
  · exact asm (by norm_num) Cor.cycY_inj Cor.cycY_ok (Cor.leaf_X hH hd)
  push Not at hd
  exact asm (by norm_num) Cor.cycT_inj Cor.cycT_ok (Cor.leaf_T hH hk1 hg hp hd)

end Frame20
end Minimality.CaseC20


end


/-!
# D2: the top-level I_MC theorem and its `R`-image
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace
open Minimality.CaseC20.IMCT

namespace Minimality.CaseC20
namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- **I_MC is Rupert**, modulo the corner leaf `hCorner` (`imc_corner`) and the tie leaf `hZt`
(`imc_Zt`).  Case tree: `A < 0` (L1); `A = 0, Q < 0` (L3); `A > 0, Q < 0` (L2); `A >= 0, Q >= 0`
is `imc_main` (L4-L12, corner, tie). -/
theorem isRupert_IMC (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hI : F.IMC) (hCorner : F.CornerStmt) (hZt : F.ZtStmt) : IsRupert (univ.image x) := by
  rcases lt_or_ge (Aq F.S) 0 with hA | hA
  · exact F.imc_L1 hx hR hI hA
  rcases lt_or_ge (Qq F.S) 0 with hQ | hQ
  · rcases hA.eq_or_lt with h | h
    · exact imc_L3 F hx hR hI.1 hI.2 h.symm hQ
    · exact F.imc_L2 hx hR hI h hQ
  · exact F.imc_main hCorner hZt hx hR hI hA hQ

/-- **The `R`-image of I_MC** (lines 279, 285 of `CaseC20Face`): the swapped equations are Rupert,
by `isRupert_IMC` for the frame of `x ∘ rperm`, whose corner and tie leaves are the hypotheses
`hCorner`, `hZt` for `F.rFrame`. -/
theorem isRupert_IMC_R (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hO : (-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 +
      (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg = 0)
    (hL : (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * (F.a22 - F.a12) +
      (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * F.a12 + (-F.S.km*F.S.kp) * F.gg = 0)
    (hCorner : F.rFrame.CornerStmt) (hZt : F.rFrame.ZtStmt) : IsRupert (univ.image x) := by
  have h12 : F.rFrame.a12 = F.a12 := by
    show ⟪x (rperm 1) - x (rperm 5), x (rperm 6) - x (rperm 5)⟫ = _
    show ⟪x 6 - x 5, x 1 - x 5⟫ = _
    exact real_inner_comm _ _
  have hg : F.rFrame.gg = F.gg := by
    show ⟪-F.e, -F.e⟫ = ⟪F.e, F.e⟫
    simp
  have h11 : F.rFrame.a11 = F.a22 := rfl
  have h22 : F.rFrame.a22 = F.a11 := rfl
  refine rupert_of_r (F.rFrame.isRupert_IMC (hx.comp rperm_bijective.1) (realizesFaces_rperm hR)
    ?_ hCorner hZt)
  unfold Frame20.IMC
  simp only [rFrame_S, Shape20.swap, h12, h11, hg]
  constructor
  · linear_combination hO
  · linear_combination hL

end Frame20
end Minimality.CaseC20



section
open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- The tie leaf `imc_Zt` and the corner leaf `imc_corner` discharge the two hypotheses of
`isRupert_IMC`: **I_MC is Rupert** (lines 277 and 280 of `CaseC20Face`), with no further assumption. -/
theorem isRupert_IMC_all (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hI : F.IMC) : IsRupert (univ.image x) :=
  F.isRupert_IMC hx hR hI
    (fun hx hR hI hA hK hQ hF => F.imc_corner hx hR hI hA hK hQ hF)
    (fun hx hR hI hV hP hA _ hQ hT _ => F.imc_Zt hx hR hI hV hP hA hQ hT)

/-- **The `R`-image of I_MC** (lines 279 and 285 of `CaseC20Face`) is Rupert. -/
theorem isRupert_IMC_all_R (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hO : (-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 +
      (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg = 0)
    (hL : (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * (F.a22 - F.a12) +
      (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * F.a12 + (-F.S.km*F.S.kp) * F.gg = 0) :
    IsRupert (univ.image x) :=
  F.isRupert_IMC_R hx hR hO hL
    (fun hx hR hI hA hK hQ hF => F.rFrame.imc_corner hx hR hI hA hK hQ hF)
    (fun hx hR hI hV hP hA _ hQ hT _ => F.rFrame.imc_Zt hx hR hI hV hP hA hQ hT)

end Frame20
end Minimality.CaseC20
end
