module

public import Minimality.Type20IV

@[expose] public section

/-!
# Type 20, item I_Q: the metric line 286 and its R-image 283
-/

section


/-!
# I_Q (type 20): the leaves W1, W2 (view `qL = x1 - x4`... the line C inter G, `(1-sm, 0, km)`)
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace IQT
open IVT
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

def w1_pat : Fin 8 → Bool := ![false, true, true, false, true, true, false, false]
def w1_c : ZMod 5 → Fin 7 := ![3, 5, 2, 6, 1]
def w2_pat : Fin 8 → Bool := ![false, false, false, false, true, true, false, false]
def w2_c : ZMod 4 → Fin 7 := ![0, 1, 6, 2]
theorem w1_cyc : S0xCycOK h20s_S w1_c w1_pat := by decide
theorem w1_inj : Function.Injective w1_c := by decide
theorem w2_cyc : S0xCycOK h20s_S w2_c w2_pat := by decide
theorem w2_inj : Function.Injective w2_c := by decide

lemma eq_pos {a b : ℝ} (h : a = b) (hb : 0 < b) : 0 < a := h ▸ hb
lemma eq_neg {a b : ℝ} (h : a = b) (hb : b < 0) : a < 0 := h ▸ hb

/-- The facing values at the line view `qL = (1-sm, 0, km)`. -/
lemma qL_nf (S : Shape20) :
    nf S ⟨1 - S.sm, 0, S.km⟩ 0 = -S.sm * (S.km*(1-S.tm) - S.hm*(1-S.sm)) ∧
    nf S ⟨1 - S.sm, 0, S.km⟩ 1 = S.sp * (S.tp*S.km - S.hp*(1-S.sm)) ∧
    nf S ⟨1 - S.sm, 0, S.km⟩ 2 = 0 ∧
    nf S ⟨1 - S.sm, 0, S.km⟩ 3 = -S.sm * (S.hm*(1-S.sm) + S.tm*S.km) ∧
    nf S ⟨1 - S.sm, 0, S.km⟩ 4 = S.hp*(1-S.sm) + (1-S.tp)*S.km ∧
    nf S ⟨1 - S.sm, 0, S.km⟩ 5 = (S.kp-S.hp*(1-S.sp))*(1-S.sm)+S.tp*(1-S.sp)*S.km ∧
    nf S ⟨1 - S.sm, 0, S.km⟩ 6 = 0 ∧
    nf S ⟨1 - S.sm, 0, S.km⟩ 7 = -S.kp*(1-S.sm) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [nf_A]; ring
  · simp only [nf_B]; ring
  · simp only [nf_C]; ring
  · simp only [nf_D]; ring
  · simp only [nf_E]; ring
  · simp only [nf_F]; ring
  · simp only [nf_G]; ring
  · simp only [nf_H]; try ring

/-- Depths at `qL`: `z1, z2, z0, z3, z5, z6`. -/
lemma qL_dep :
    F.dep ⟨1 - F.S.sm, 0, F.S.km⟩ 0 = F.a11*F.S.tp*(1-F.S.sm) + F.gg*F.S.hp*F.S.km ∧
    F.dep ⟨1 - F.S.sm, 0, F.S.km⟩ 1 = F.a11*(1-F.S.sm) ∧
    F.dep ⟨1 - F.S.sm, 0, F.S.km⟩ 2 = F.a12*F.S.sp*(1-F.S.sm) + F.gg*F.S.kp*F.S.km ∧
    F.dep ⟨1 - F.S.sm, 0, F.S.km⟩ 3 = F.a11*F.S.tm*(1-F.S.sm) - F.gg*F.S.hm*F.S.km ∧
    F.dep ⟨1 - F.S.sm, 0, F.S.km⟩ 5 = 0 ∧
    F.dep ⟨1 - F.S.sm, 0, F.S.km⟩ 6 = F.a12*(1-F.S.sm) := by
  refine ⟨?_, ?_, ?_, ?_, Frame20.dep_5 F _, ?_⟩
  · rw [Frame20.dep_0]; ring
  · rw [Frame20.dep_1]; ring
  · rw [Frame20.dep_2]; ring
  · rw [Frame20.dep_3]; ring
  · rw [Frame20.dep_6]; ring

/-- At `qL`, `P >= 0` puts `z2` below `z6` (identity I2 and the upper roof). -/
lemma qL_z26 (hP : 0 ≤ ((1-F.S.tp)*(1-F.S.sm)*F.a12-F.gg*F.S.hp*F.S.km)) : F.a12*F.S.sp*(1-F.S.sm) + F.gg*F.S.kp*F.S.km < F.a12*(1-F.S.sm) := by
  have sp1 := F.S.sp1; have tp1 := F.S.tp1; have rp := F.S.rhop_pos
  have hg : 0 < F.gg := F.g_pos; have km0 := F.S.km_pos
  have e : (1-F.S.tp) * (F.a12*(1-F.S.sm) - (F.a12*F.S.sp*(1-F.S.sm) + F.gg*F.S.kp*F.S.km)) = (1-F.S.sp)*((1-F.S.tp)*(1-F.S.sm)*F.a12-F.gg*F.S.hp*F.S.km) + F.gg*F.S.km*(F.S.hp*(1-F.S.sp)-F.S.kp*(1-F.S.tp)) := by ring
  have h1 : 0 < (1-F.S.tp) * (F.a12*(1-F.S.sm) - (F.a12*F.S.sp*(1-F.S.sm) + F.gg*F.S.kp*F.S.km)) := by
    rw [e]; have := mul_nonneg sp1.le hP; have := mul_pos (mul_pos hg km0) rp; linarith
  have := pos_of_mul_pos_right h1 tp1.le
  linarith

/-- Shared facings at `qL` for W1, W2. -/
lemma qL_signs (hF2 : 0 < ((F.S.kp-F.S.hp*(1-F.S.sp))*(1-F.S.sm)+F.S.tp*(1-F.S.sp)*F.S.km)) :
    nf F.S ⟨1 - F.S.sm, 0, F.S.km⟩ 0 < 0 ∧ nf F.S ⟨1 - F.S.sm, 0, F.S.km⟩ 3 < 0 ∧ 0 < nf F.S ⟨1 - F.S.sm, 0, F.S.km⟩ 4 ∧
    0 < nf F.S ⟨1 - F.S.sm, 0, F.S.km⟩ 5 ∧ nf F.S ⟨1 - F.S.sm, 0, F.S.km⟩ 7 < 0 := by
  obtain ⟨uA, -, -, uD, uE, uF, -, uH⟩ := qL_nf F.S
  have sm0 := F.S.sm_pos; have sm1 := F.S.sm1; have kp0 := F.S.kp_pos; have km0 := F.S.km_pos
  have hp0 := F.S.hp_pos; have hm0 := F.S.hm_pos; have tm0 := F.S.tm_pos; have tp1 := F.S.tp1
  have rm := F.S.rhom_pos
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [uA]; have := mul_pos sm0 rm; linarith
  · rw [uD]; have := mul_pos sm0 (add_pos (mul_pos hm0 sm1) (mul_pos tm0 km0)); linarith
  · rw [uE]; have := mul_pos hp0 sm1; have := mul_pos tp1 km0; linarith
  · rw [uF]; exact hF2
  · rw [uH]; have := mul_pos kp0 sm1; linarith

/-- W1: view `qL`, tilt `x5 - x6`; needs `D1 >= 0`, `P >= 0` and `hF2`. -/
theorem iq_W1 (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hF2 : 0 < ((F.S.kp-F.S.hp*(1-F.S.sp))*(1-F.S.sm)+F.S.tp*(1-F.S.sp)*F.S.km)) (hD : 0 ≤ (F.S.tp*F.S.km-F.S.hp*(1-F.S.sm))) (hP : 0 ≤ ((1-F.S.tp)*(1-F.S.sm)*F.a12-F.gg*F.S.hp*F.S.km)) : IsRupert (univ.image x) := by
  have sm0 := F.S.sm_pos; have sm1 := F.S.sm1; have kp0 := F.S.kp_pos; have km0 := F.S.km_pos
  have hp0 := F.S.hp_pos; have hm0 := F.S.hm_pos; have tm0 := F.S.tm_pos; have tp1 := F.S.tp1
  have tp0 := F.S.tp_pos; have tm1 := F.S.tm1
  have ha : 0 < F.a12 := F.A12_pos; have hg : 0 < F.gg := F.g_pos; have h11 : F.a12 ≤ F.a11 := F.A12_le_A11
  have W0 := F.S.W_pos
  obtain ⟨uA, uB, uC, uD, uE, uF, uG, uH⟩ := qL_nf F.S
  obtain ⟨sA, sD, sE, sF, sH⟩ := qL_signs F hF2
  have vB : nf F.S ⟨0, -1, 0⟩ 1 = F.S.kp*F.S.tp := by simp only [nf_B]; ring
  have vC : nf F.S ⟨0, -1, 0⟩ 2 = (F.S.hm*F.S.tp+F.S.hp*F.S.tm) := by simp only [nf_C]; ring
  have vG : nf F.S ⟨0, -1, 0⟩ 6 = -F.S.km := by simp only [nf_G]; ring
  obtain ⟨z0, z1, z2, z3, z5, z6⟩ := qL_dep F
  refine leaf_of_view F (h20s_fac hR) hx (by norm_num) w1_inj w1_cyc ⟨1 - F.S.sm, 0, F.S.km⟩ ⟨0, -1, 0⟩ 7
    (ne_of_lt sH) ?_ ?_
  · intro t; fin_cases t
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos sA⟩
    · refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
      rcases hD.lt_or_eq with h | h
      · exact lp_pos (eq_pos uB (by have := F.S.sp_pos; positivity))
      · exact lp_zero (uB.trans (by rw [← h]; ring)) (eq_pos vB (by positivity))
    · exact ⟨fun _ => lp_zero uC (eq_pos vC W0), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos sD⟩
    · exact ⟨fun _ => lp_pos sE, fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp_pos sF, fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_zero uG (eq_neg vG (by linarith))⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos sH⟩
  · refine Minimality.H20S.robUni5_d ?_ ?_ ?_
    · show F.dep _ 5 < F.dep _ 2
      rw [z5, z2]; have := mul_pos (mul_pos ha F.S.sp_pos) sm1; have := mul_pos hg (mul_pos kp0 km0); linarith
    · show F.dep _ 2 < F.dep _ 6
      rw [z2, z6]; exact qL_z26 F hP
    · show F.dep _ 3 < F.dep _ 1
      rw [z3, z1]
      have := mul_pos (mul_pos (lt_of_lt_of_le ha h11) sm1) tm1; have := mul_pos hg (mul_pos hm0 km0)
      nlinarith [mul_nonneg (sub_nonneg.2 h11) (mul_pos sm1 tm1).le, mul_pos (mul_pos ha sm1) tm1]

/-- W2: view `qL`, tilt `x2 - x1`; needs `D1 < 0`, `Pp > 0`, `P >= 0` and `hF2`. -/
theorem iq_W2 (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hF2 : 0 < ((F.S.kp-F.S.hp*(1-F.S.sp))*(1-F.S.sm)+F.S.tp*(1-F.S.sp)*F.S.km)) (hD : (F.S.tp*F.S.km-F.S.hp*(1-F.S.sm)) < 0) (hP : 0 ≤ ((1-F.S.tp)*(1-F.S.sm)*F.a12-F.gg*F.S.hp*F.S.km)) (hPp : 0 < (((1-F.S.tp)*(1-F.S.sm)*F.a12-F.gg*F.S.hp*F.S.km)+(1-F.S.tp)*(1-F.S.sm)*(F.a11-F.a12))) : IsRupert (univ.image x) := by
  have sm0 := F.S.sm_pos; have sm1 := F.S.sm1; have kp0 := F.S.kp_pos; have km0 := F.S.km_pos
  have sp0 := F.S.sp_pos; have sp1 := F.S.sp1
  have hp0 := F.S.hp_pos; have hm0 := F.S.hm_pos; have tm0 := F.S.tm_pos; have tp1 := F.S.tp1
  have W0 := F.S.W_pos
  obtain ⟨uA, uB, uC, uD, uE, uF, uG, uH⟩ := qL_nf F.S
  obtain ⟨sA, sD, sE, sF, sH⟩ := qL_signs F hF2
  have vC : nf F.S ⟨-1, F.S.sp, F.S.kp⟩ 2 = -((F.S.hm*F.S.tp+F.S.hp*F.S.tm)*F.S.sp) := by simp only [nf_C]; ring
  have vG : nf F.S ⟨-1, F.S.sp, F.S.kp⟩ 6 = -(F.S.km*(1-F.S.sp) + (1-F.S.sm)*F.S.kp) := by simp only [nf_G]; ring
  obtain ⟨z0, z1, z2, z3, z5, z6⟩ := qL_dep F
  refine leaf_of_view F (h20s_fac hR) hx (by norm_num) w2_inj w2_cyc ⟨1 - F.S.sm, 0, F.S.km⟩ ⟨-1, F.S.sp, F.S.kp⟩ 7
    (ne_of_lt sH) ?_ ?_
  · intro t; fin_cases t
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos sA⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (eq_neg uB (by nlinarith))⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_zero uC (eq_neg vC (by have := mul_pos W0 sp0; linarith))⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos sD⟩
    · exact ⟨fun _ => lp_pos sE, fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp_pos sF, fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_zero uG (eq_neg vG (by
        have := mul_pos km0 sp1; have := mul_pos sm1 kp0; linarith))⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos sH⟩
  · refine robUni4 ?_ ?_
    · rintro ⟨a, b, c, d⟩
      have a' : F.dep ⟨1 - F.S.sm, 0, F.S.km⟩ 1 ≤ F.dep ⟨1 - F.S.sm, 0, F.S.km⟩ 0 := a
      rw [z1, z0] at a'
      have e : F.a11*(1-F.S.sm) - (F.a11*F.S.tp*(1-F.S.sm) + F.gg*F.S.hp*F.S.km) = (((1-F.S.tp)*(1-F.S.sm)*F.a12-F.gg*F.S.hp*F.S.km)+(1-F.S.tp)*(1-F.S.sm)*(F.a11-F.a12)) := by ring
      linarith
    · rintro ⟨a, b, c, d⟩
      have d' : F.dep ⟨1 - F.S.sm, 0, F.S.km⟩ 6 ≤ F.dep ⟨1 - F.S.sm, 0, F.S.km⟩ 2 := d
      rw [z6, z2] at d'
      have := qL_z26 F hP
      linarith

end IQT
end Minimality.CaseC20

end

section


/-!
# I_Q (type 20): the leaves S1, C1, C3
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace IQT
open IVT
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

def s1_pat : Fin 8 → Bool := ![false, true, true, true, false, true, false, true]
def s1_c : ZMod 5 → Fin 7 := ![1, 0, 6, 4, 3]
def c1_pat : Fin 8 → Bool := ![true, false, true, true, true, false, true, false]
def c1_c : ZMod 4 → Fin 7 := ![0, 5, 4, 6]
def c3_pat : Fin 8 → Bool := ![true, false, true, false, true, false, true, false]
def c3_c : ZMod 5 → Fin 7 := ![5, 0, 6, 4, 3]
theorem s1_cyc : S0xCycOK h20s_S s1_c s1_pat := by decide
theorem s1_inj : Function.Injective s1_c := by decide
theorem c1_cyc : S0xCycOK h20s_S c1_c c1_pat := by decide
theorem c1_inj : Function.Injective c1_c := by decide
theorem c3_cyc : S0xCycOK h20s_S c3_c c3_pat := by decide
theorem c3_inj : Function.Injective c3_c := by decide

/-- S1: view `x5 - x1 = (-1,0,0)`, tilt `x5 - x6`; needs `T > 0` and `hF1`. -/
theorem iq_S1 (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hF1 : F.S.kp < F.S.hp*(1-F.S.sp)) (hT : 0 < (F.a11*F.S.tp-F.a12)) : IsRupert (univ.image x) := by
  have sm0 := F.S.sm_pos; have kp0 := F.S.kp_pos; have km0 := F.S.km_pos
  have hp0 := F.S.hp_pos; have hm0 := F.S.hm_pos; have sp0 := F.S.sp_pos
  have ha : 0 < F.a12 := F.A12_pos; have sm1 := F.S.sm1; have tm1 := F.S.tm1
  have h11 : F.a12 ≤ F.a11 := F.A12_le_A11
  have W0 := F.S.W_pos
  have uA : nf F.S ⟨-1, 0, 0⟩ 0 = -(F.S.hm*F.S.sm) := by simp only [nf_A]; ring
  have uB : nf F.S ⟨-1, 0, 0⟩ 1 = F.S.hp*F.S.sp := by simp only [nf_B]; ring
  have uC : nf F.S ⟨-1, 0, 0⟩ 2 = 0 := by simp only [nf_C]; ring
  have uD : nf F.S ⟨-1, 0, 0⟩ 3 = F.S.hm*F.S.sm := by simp only [nf_D]; ring
  have uE : nf F.S ⟨-1, 0, 0⟩ 4 = -F.S.hp := by simp only [nf_E]; ring
  have uF : nf F.S ⟨-1, 0, 0⟩ 5 = F.S.hp*(1-F.S.sp) - F.S.kp := by simp only [nf_F]; ring
  have uG : nf F.S ⟨-1, 0, 0⟩ 6 = -F.S.km := by simp only [nf_G]; ring
  have uH : nf F.S ⟨-1, 0, 0⟩ 7 = F.S.kp := by simp only [nf_H]; ring
  have vC : nf F.S ⟨0, -1, 0⟩ 2 = (F.S.hm*F.S.tp+F.S.hp*F.S.tm) := by simp only [nf_C]; ring
  have z0 : F.dep ⟨-1, 0, 0⟩ 0 = -(F.a11*F.S.tp) := by rw [Frame20.dep_0]; ring
  have z1 : F.dep ⟨-1, 0, 0⟩ 1 = -F.a11 := by rw [Frame20.dep_1]; ring
  have z3 : F.dep ⟨-1, 0, 0⟩ 3 = -(F.a11*F.S.tm) := by rw [Frame20.dep_3]; ring
  have z4 : F.dep ⟨-1, 0, 0⟩ 4 = -(F.a12*F.S.sm) := by rw [Frame20.dep_4]; ring
  have z6 : F.dep ⟨-1, 0, 0⟩ 6 = -F.a12 := by rw [Frame20.dep_6]; ring
  refine leaf_of_view F (h20s_fac hR) hx (by norm_num) s1_inj s1_cyc ⟨-1, 0, 0⟩ ⟨0, -1, 0⟩ 7
    (by rw [uH]; exact kp0.ne') ?_ ?_
  · intro t; fin_cases t
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (eq_neg uA (by have := mul_pos hm0 sm0; linarith))⟩
    · exact ⟨fun _ => lp_pos (eq_pos uB (mul_pos hp0 sp0)), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp_zero uC (eq_pos vC W0), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp_pos (eq_pos uD (mul_pos hm0 sm0)), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (eq_neg uE (by linarith))⟩
    · exact ⟨fun _ => lp_pos (eq_pos uF (by linarith)), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (eq_neg uG (by linarith))⟩
    · exact ⟨fun _ => lp_pos (eq_pos uH kp0), fun h => absurd h (by decide)⟩
  · refine Minimality.H20S.robUni5_d ?_ ?_ ?_
    · show F.dep _ 0 < F.dep _ 6
      rw [z0, z6]; linarith
    · show F.dep _ 6 < F.dep _ 4
      rw [z6, z4]; nlinarith [mul_pos ha sm1]
    · show F.dep _ 1 < F.dep _ 3
      rw [z1, z3]
      have : 0 < F.a11 := lt_of_lt_of_le ha h11
      nlinarith [mul_pos this tm1]

/-- Facings at `q01 = x1 - x0 = (1-tp, 0, -hp)` and the tilt `v14 = (1,-sm,km)`, depths at `q01`. -/
lemma q01_data (hA : True) :
    nf F.S ⟨1 - F.S.tp, 0, -F.S.hp⟩ 0 = F.S.sm*(F.S.hm*(1-F.S.tp) + F.S.hp*(1-F.S.tm)) ∧
    nf F.S ⟨1 - F.S.tp, 0, -F.S.hp⟩ 1 = -(F.S.hp*F.S.sp) ∧
    nf F.S ⟨1 - F.S.tp, 0, -F.S.hp⟩ 2 = 0 ∧
    nf F.S ⟨1 - F.S.tp, 0, -F.S.hp⟩ 3 = F.S.sm*(F.S.hp*F.S.tm-F.S.hm*(1-F.S.tp)) ∧
    nf F.S ⟨1 - F.S.tp, 0, -F.S.hp⟩ 4 = 0 ∧
    nf F.S ⟨1 - F.S.tp, 0, -F.S.hp⟩ 5 = -(F.S.hp*(1-F.S.sp)-F.S.kp*(1-F.S.tp)) ∧
    nf F.S ⟨1 - F.S.tp, 0, -F.S.hp⟩ 6 = F.S.km*(1-F.S.tp) + (1-F.S.sm)*F.S.hp ∧
    nf F.S ⟨1 - F.S.tp, 0, -F.S.hp⟩ 7 = -(F.S.kp*(1-F.S.tp)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [nf_A]; ring
  · simp only [nf_B]; ring
  · simp only [nf_C]; ring
  · simp only [nf_D]; ring
  · simp only [nf_E]; ring
  · simp only [nf_F]; ring
  · simp only [nf_G]; ring
  · simp only [nf_H]; ring

/-- C1: view `x1 - x0`, tilt `x1 - x4`; needs `L < 0` (no hypothesis on `A1`). -/
theorem iq_C1 (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hA : 0 < (F.S.hp*F.S.tm-F.S.hm*(1-F.S.tp))) (hL : ((1-F.S.tp)*(F.a11*F.S.tp-F.a12)-F.gg*F.S.hp^2) < 0) : IsRupert (univ.image x) := by
  have sm0 := F.S.sm_pos; have kp0 := F.S.kp_pos; have km0 := F.S.km_pos; have sm1 := F.S.sm1
  have hp0 := F.S.hp_pos; have hm0 := F.S.hm_pos; have sp0 := F.S.sp_pos; have tp1 := F.S.tp1
  have tm1 := F.S.tm1; have rp := F.S.rhop_pos
  have ha : 0 < F.a12 := F.A12_pos; have hg : 0 < F.gg := F.g_pos
  have W0 := F.S.W_pos
  obtain ⟨uA, uB, uC, uD, uE, uF, uG, uH⟩ := q01_data F trivial
  have vC : nf F.S ⟨1, -F.S.sm, F.S.km⟩ 2 = F.S.sm*(F.S.hm*F.S.tp+F.S.hp*F.S.tm) := by simp only [nf_C]; ring
  have vE : nf F.S ⟨1, -F.S.sm, F.S.km⟩ 4 = F.S.hp*(1-F.S.sm) + (1-F.S.tp)*F.S.km := by simp only [nf_E]; ring
  have z0 : F.dep ⟨1 - F.S.tp, 0, -F.S.hp⟩ 0 = F.a11*F.S.tp*(1-F.S.tp) - F.gg*F.S.hp^2 := by rw [Frame20.dep_0]; ring
  have z4 : F.dep ⟨1 - F.S.tp, 0, -F.S.hp⟩ 4 = F.a12*F.S.sm*(1-F.S.tp) + F.gg*F.S.hp*F.S.km := by rw [Frame20.dep_4]; ring
  have z5 : F.dep ⟨1 - F.S.tp, 0, -F.S.hp⟩ 5 = 0 := Frame20.dep_5 F _
  have z6 : F.dep ⟨1 - F.S.tp, 0, -F.S.hp⟩ 6 = F.a12*(1-F.S.tp) := by rw [Frame20.dep_6]; ring
  refine leaf_of_view F (h20s_fac hR) hx (by norm_num) c1_inj c1_cyc ⟨1 - F.S.tp, 0, -F.S.hp⟩ ⟨1, -F.S.sm, F.S.km⟩ 7
    (by rw [uH]; have := mul_pos kp0 tp1; intro h; linarith) ?_ ?_
  · intro t; fin_cases t
    · exact ⟨fun _ => lp_pos (eq_pos uA (by positivity)), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (eq_neg uB (by have := mul_pos hp0 sp0; linarith))⟩
    · exact ⟨fun _ => lp_zero uC (eq_pos vC (by positivity)), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp_pos (eq_pos uD (by positivity)), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp_zero uE (eq_pos vE (by positivity)), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (eq_neg uF (by linarith))⟩
    · exact ⟨fun _ => lp_pos (eq_pos uG (by positivity)), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (eq_neg uH (by have := mul_pos kp0 tp1; linarith))⟩
  · refine robUni4 ?_ ?_
    · rintro ⟨a, b, c, d⟩
      have d' : F.dep ⟨1 - F.S.tp, 0, -F.S.hp⟩ 6 ≤ F.dep ⟨1 - F.S.tp, 0, -F.S.hp⟩ 0 := c
      rw [z0, z6] at d'
      have e : F.a12*(1-F.S.tp) - (F.a11*F.S.tp*(1-F.S.tp) - F.gg*F.S.hp^2) = -((1-F.S.tp)*(F.a11*F.S.tp-F.a12)-F.gg*F.S.hp^2) := by ring
      linarith
    · rintro ⟨a, b, c, d⟩
      have c' : F.dep ⟨1 - F.S.tp, 0, -F.S.hp⟩ 4 ≤ F.dep ⟨1 - F.S.tp, 0, -F.S.hp⟩ 5 := c
      rw [z4, z5] at c'
      have := mul_pos (mul_pos ha sm0) tp1; have := mul_pos (mul_pos hg hp0) km0
      nlinarith

/-- C3: view `x1 - x0`, tilt `x1 - x4`, with `D` edge-on at `A1 = 0` (decided by the tilt);
needs `A1 <= 0`, `L < 0`, `P < 0`. -/
theorem iq_C3 (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hA : (F.S.hp*F.S.tm-F.S.hm*(1-F.S.tp)) ≤ 0) (hL : ((1-F.S.tp)*(F.a11*F.S.tp-F.a12)-F.gg*F.S.hp^2) < 0) (hP : ((1-F.S.tp)*(1-F.S.sm)*F.a12-F.gg*F.S.hp*F.S.km) < 0) : IsRupert (univ.image x) := by
  have sm0 := F.S.sm_pos; have kp0 := F.S.kp_pos; have km0 := F.S.km_pos; have sm1 := F.S.sm1
  have hp0 := F.S.hp_pos; have hm0 := F.S.hm_pos; have sp0 := F.S.sp_pos; have tp1 := F.S.tp1
  have tm1 := F.S.tm1; have tm0 := F.S.tm_pos; have rp := F.S.rhop_pos
  have ha : 0 < F.a12 := F.A12_pos; have hg : 0 < F.gg := F.g_pos
  have h11 : F.a12 ≤ F.a11 := F.A12_le_A11
  have W0 := F.S.W_pos
  obtain ⟨uA, uB, uC, uD, uE, uF, uG, uH⟩ := q01_data F trivial
  have vC : nf F.S ⟨1, -F.S.sm, F.S.km⟩ 2 = F.S.sm*(F.S.hm*F.S.tp+F.S.hp*F.S.tm) := by simp only [nf_C]; ring
  have vD : nf F.S ⟨1, -F.S.sm, F.S.km⟩ 3 = -(F.S.hm*F.S.sm) := by simp only [nf_D]; ring
  have vE : nf F.S ⟨1, -F.S.sm, F.S.km⟩ 4 = F.S.hp*(1-F.S.sm) + (1-F.S.tp)*F.S.km := by simp only [nf_E]; ring
  have z0 : F.dep ⟨1 - F.S.tp, 0, -F.S.hp⟩ 0 = F.a11*F.S.tp*(1-F.S.tp) - F.gg*F.S.hp^2 := by rw [Frame20.dep_0]; ring
  have z3 : F.dep ⟨1 - F.S.tp, 0, -F.S.hp⟩ 3 = F.a11*F.S.tm*(1-F.S.tp) + F.gg*F.S.hp*F.S.hm := by rw [Frame20.dep_3]; ring
  have z4 : F.dep ⟨1 - F.S.tp, 0, -F.S.hp⟩ 4 = F.a12*F.S.sm*(1-F.S.tp) + F.gg*F.S.hp*F.S.km := by rw [Frame20.dep_4]; ring
  have z5 : F.dep ⟨1 - F.S.tp, 0, -F.S.hp⟩ 5 = 0 := Frame20.dep_5 F _
  have z6 : F.dep ⟨1 - F.S.tp, 0, -F.S.hp⟩ 6 = F.a12*(1-F.S.tp) := by rw [Frame20.dep_6]; ring
  refine leaf_of_view F (h20s_fac hR) hx (by norm_num) c3_inj c3_cyc ⟨1 - F.S.tp, 0, -F.S.hp⟩ ⟨1, -F.S.sm, F.S.km⟩ 7
    (by rw [uH]; have := mul_pos kp0 tp1; intro h; linarith) ?_ ?_
  · intro t; fin_cases t
    · exact ⟨fun _ => lp_pos (eq_pos uA (by positivity)), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (eq_neg uB (by have := mul_pos hp0 sp0; linarith))⟩
    · exact ⟨fun _ => lp_zero uC (eq_pos vC (by positivity)), fun h => absurd h (by decide)⟩
    · refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
      rcases hA.lt_or_eq with h | h
      · exact lpn_pos (eq_neg uD (by have := mul_neg_of_pos_of_neg sm0 h; linarith))
      · exact lpn_zero (uD.trans (by rw [h]; ring)) (eq_neg vD (by have := mul_pos hm0 sm0; linarith))
    · exact ⟨fun _ => lp_zero uE (eq_pos vE (by positivity)), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (eq_neg uF (by linarith))⟩
    · exact ⟨fun _ => lp_pos (eq_pos uG (by positivity)), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (eq_neg uH (by have := mul_pos kp0 tp1; linarith))⟩
  · refine Minimality.H20S.robUni5_d ?_ ?_ ?_
    · show F.dep _ 0 < F.dep _ 6
      rw [z0, z6]
      have e : F.a12*(1-F.S.tp) - (F.a11*F.S.tp*(1-F.S.tp) - F.gg*F.S.hp^2) = -((1-F.S.tp)*(F.a11*F.S.tp-F.a12)-F.gg*F.S.hp^2) := by ring
      linarith
    · show F.dep _ 6 < F.dep _ 4
      rw [z6, z4]
      have e : (F.a12*F.S.sm*(1-F.S.tp) + F.gg*F.S.hp*F.S.km) - F.a12*(1-F.S.tp) = -((1-F.S.tp)*(1-F.S.sm)*F.a12-F.gg*F.S.hp*F.S.km) := by ring
      linarith
    · show F.dep _ 5 < F.dep _ 3
      rw [z5, z3]
      have := mul_pos (mul_pos (lt_of_lt_of_le ha h11) tm0) tp1; have := mul_pos (mul_pos hg hp0) hm0
      nlinarith [mul_nonneg (sub_nonneg.2 h11) (mul_pos tm0 tp1).le]

end IQT
end Minimality.CaseC20

end

section


/-!
# I_Q (type 20): the case tree and the theorems

`Frame20.isRupert_of_F`: Rupert for every metric whenever facet `F` points down along `x1 - x5`
(`hF1`) and up at the line view (`hF2`).  `Frame20.isRupert_IQ`: line 286 of `CaseC20Face.lean`
(copied verbatim) gives both; `Frame20.isRupert_IQ_R`: its `R`-image, line 283.
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- **Type 20, stronger form of item I_Q**: Rupert for every metric of the frame, given `hF1` and `hF2`. -/
theorem isRupert_of_F (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hF1 : F.S.kp < F.S.hp*(1 - F.S.sp))
    (hF2 : 0 < (F.S.kp - F.S.hp*(1-F.S.sp))*(1-F.S.sm) + F.S.tp*(1-F.S.sp)*F.S.km) :
    IsRupert (Finset.univ.image x) := by
  have h11 : F.a12 ≤ F.a11 := F.A12_le_A11
  have ha : 0 < F.a12 := F.A12_pos; have hg : 0 < F.gg := F.g_pos
  have tp1 := F.S.tp1; have sm1 := F.S.sm1; have hp0 := F.S.hp_pos
  by_cases hP : 0 ≤ ((1-F.S.tp)*(1-F.S.sm)*F.a12-F.gg*F.S.hp*F.S.km)
  · by_cases hD : 0 ≤ (F.S.tp*F.S.km-F.S.hp*(1-F.S.sm))
    · exact IQT.iq_W1 F hx hR hF2 hD hP
    · by_cases hPp : 0 < (((1-F.S.tp)*(1-F.S.sm)*F.a12-F.gg*F.S.hp*F.S.km)+(1-F.S.tp)*(1-F.S.sm)*(F.a11-F.a12))
      · exact IQT.iq_W2 F hx hR hF2 (not_le.1 hD) hP hPp
      · -- corner: `Pp <= 0` forces `P = 0` and `a12 = a11`
        have hPp' : (((1-F.S.tp)*(1-F.S.sm)*F.a12-F.gg*F.S.hp*F.S.km)+(1-F.S.tp)*(1-F.S.sm)*(F.a11-F.a12)) ≤ 0 := not_lt.1 hPp
        have hnn : 0 ≤ (1-F.S.tp)*(1-F.S.sm)*(F.a11-F.a12) := mul_nonneg (mul_pos tp1 sm1).le (sub_nonneg.2 h11)
        have hP0 : ((1-F.S.tp)*(1-F.S.sm)*F.a12-F.gg*F.S.hp*F.S.km) = 0 := by
          have : (((1-F.S.tp)*(1-F.S.sm)*F.a12-F.gg*F.S.hp*F.S.km)+(1-F.S.tp)*(1-F.S.sm)*(F.a11-F.a12)) = ((1-F.S.tp)*(1-F.S.sm)*F.a12-F.gg*F.S.hp*F.S.km) + (1-F.S.tp)*(1-F.S.sm)*(F.a11-F.a12) := rfl
          linarith
        have hz : (1-F.S.tp)*(1-F.S.sm)*(F.a11-F.a12) = 0 := by
          have : (((1-F.S.tp)*(1-F.S.sm)*F.a12-F.gg*F.S.hp*F.S.km)+(1-F.S.tp)*(1-F.S.sm)*(F.a11-F.a12)) = ((1-F.S.tp)*(1-F.S.sm)*F.a12-F.gg*F.S.hp*F.S.km) + (1-F.S.tp)*(1-F.S.sm)*(F.a11-F.a12) := rfl
          linarith
        have hq : F.a11 - F.a12 = 0 := (mul_eq_zero.1 hz).resolve_left (mul_pos tp1 sm1).ne'
        refine F.faceA11 (by linarith) (fun hh => ?_)
        have h2 := hh.2.2
        have h1 := hh.2.1
        have : (1 - F.S.tp)*(1 - F.S.sm)*F.a12 - F.gg*F.S.hp*F.S.km = ((1-F.S.tp)*(1-F.S.sm)*F.a12-F.gg*F.S.hp*F.S.km) := by ring
        linarith
  · have hP' : ((1-F.S.tp)*(1-F.S.sm)*F.a12-F.gg*F.S.hp*F.S.km) < 0 := not_le.1 hP
    by_cases hL : 0 ≤ ((1-F.S.tp)*(F.a11*F.S.tp-F.a12)-F.gg*F.S.hp^2)
    · have hT : 0 < (F.a11*F.S.tp-F.a12) := by
        have e : (1-F.S.tp) * (F.a11*F.S.tp-F.a12) = ((1-F.S.tp)*(F.a11*F.S.tp-F.a12)-F.gg*F.S.hp^2) + F.gg*F.S.hp^2 := by ring
        have h1 : 0 < (1-F.S.tp) * (F.a11*F.S.tp-F.a12) := by rw [e]; have := mul_pos hg (pow_pos hp0 2); linarith
        exact pos_of_mul_pos_right h1 tp1.le
      exact IQT.iq_S1 F hx hR hF1 hT
    · by_cases hA : 0 < (F.S.hp*F.S.tm-F.S.hm*(1-F.S.tp))
      · exact IQT.iq_C1 F hx hR hA (not_le.1 hL)
      · exact IQT.iq_C3 F hx hR (not_lt.1 hA) (not_le.1 hL) hP'

/-- **Type 20, item I_Q** (line 286 of `CaseC20Face.lean`, copied verbatim): Rupert for every metric. -/
theorem isRupert_IQ (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hQ : F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.sp - F.S.hp*F.S.tm + F.S.hp + F.S.kp*F.S.tm - F.S.kp = 0) :
    IsRupert (Finset.univ.image x) := by
  have tm1 := F.S.tm1; have sp1 := F.S.sp1; have tp0 := F.S.tp_pos; have hm0 := F.S.hm_pos
  have rm := F.S.rhom_pos
  have J1 : (1-F.S.tm)*(F.S.hp*(1-F.S.sp) - F.S.kp) = (1-F.S.sp)*F.S.tp*F.S.hm := by linear_combination hQ
  have J2 : (1-F.S.tm)*((F.S.kp-F.S.hp*(1-F.S.sp))*(1-F.S.sm)+F.S.tp*(1-F.S.sp)*F.S.km) = (1-F.S.sp)*F.S.tp*(F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm)) := by
    linear_combination (-(1-F.S.sm)) * hQ
  refine F.isRupert_of_F hx hR ?_ ?_
  · have h : 0 < (1-F.S.tm)*(F.S.hp*(1-F.S.sp) - F.S.kp) := by rw [J1]; positivity
    have := pos_of_mul_pos_right h tm1.le
    linarith
  · have h : 0 < (1-F.S.tm)*((F.S.kp-F.S.hp*(1-F.S.sp))*(1-F.S.sm)+F.S.tp*(1-F.S.sp)*F.S.km) := by rw [J2]; positivity
    exact pos_of_mul_pos_right h tm1.le

/-- **The `R`-image of I_Q** (line 283 of `CaseC20Face.lean`, copied verbatim): Rupert, by
`isRupert_IQ` for the frame of `x ∘ R`. -/
theorem isRupert_IQ_R (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hQ : F.S.hm*F.S.sp - F.S.hm + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp - F.S.km*F.S.tm + F.S.km + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm = 0) :
    IsRupert (Finset.univ.image x) := by
  refine rupert_of_r (F.rFrame.isRupert_IQ (hx.comp rperm_bijective.1) (realizesFaces_rperm hR) ?_)
  simp only [rFrame_S, Shape20.swap]; linear_combination hQ

end Frame20
end Minimality.CaseC20

end

