module

public import Minimality.Type20IA1
public import Minimality.Type20IQ

@[expose] public section

/-!
# Type 20, item I_A (part 2): the cases and the theorems
-/

section


/-!
# I_A, leaves E1, S56, U2, U1
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace IAT
open IVT
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

def e1_pat : Fin 8 → Bool := ![false, true, true, false, true, true, false, false]
def e1_c : ZMod 5 → Fin 7 := ![1, 3, 5, 2, 6]
theorem e1_cyc : S0xCycOK h20s_S e1_c e1_pat := by decide
theorem e1_inj : Function.Injective e1_c := by decide

def u2_pat : Fin 8 → Bool := ![true, false, false, false, true, false, true, false]
def u2_c : ZMod 5 → Fin 7 := ![0, 1, 3, 4, 6]
theorem u2_cyc : S0xCycOK h20s_S u2_c u2_pat := by decide
theorem u2_inj : Function.Injective u2_c := by decide

def u1_pat : Fin 8 → Bool := ![true, false, true, false, true, false, true, false]
def u1_c : ZMod 5 → Fin 7 := ![0, 5, 3, 4, 6]
theorem u1_cyc : S0xCycOK h20s_S u1_c u1_pat := by decide
theorem u1_inj : Function.Injective u1_c := by decide

/-- Facings at the view `u0 = (1,0,-1)` (the direction of `x1 - x0`). -/
lemma u0_nf (S : Shape20) (hN : NF S) :
    nf S ⟨1, 0, -1⟩ 0 = S.sm ∧ nf S ⟨1, 0, -1⟩ 1 = -S.sp ∧ nf S ⟨1, 0, -1⟩ 2 = 0 ∧
    nf S ⟨1, 0, -1⟩ 3 = 0 ∧ nf S ⟨1, 0, -1⟩ 4 = 0 ∧ nf S ⟨1, 0, -1⟩ 5 = S.kp + S.sp - 1 ∧
    nf S ⟨1, 0, -1⟩ 6 = S.km + 1 - S.sm ∧ nf S ⟨1, 0, -1⟩ 7 = -S.kp := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [nf_A, hN.1]; ring
  · simp only [nf_B, hN.2]; ring
  · simp only [nf_C]; ring
  · simp only [nf_D, hN.1]; ring
  · simp only [nf_E, hN.2]; ring
  · simp only [nf_F, hN.2]; ring
  · simp only [nf_G]; ring
  · simp only [nf_H]; ring

/-- Depths at `u0 = (1,0,-1)`. -/
lemma u0_dep (hN : NF F.S) :
    F.dep ⟨1, 0, -1⟩ 0 = F.a11 * F.S.tp - F.gg * (1-F.S.tp) ∧ F.dep ⟨1, 0, -1⟩ 1 = F.a11 ∧
    F.dep ⟨1, 0, -1⟩ 3 = F.S.tm * (F.a11 + F.gg) ∧ F.dep ⟨1, 0, -1⟩ 4 = F.a12 * F.S.sm + F.gg * F.S.km ∧
    F.dep ⟨1, 0, -1⟩ 5 = 0 ∧ F.dep ⟨1, 0, -1⟩ 6 = F.a12 := by
  refine ⟨?_, ?_, ?_, ?_, Frame20.dep_5 F _, ?_⟩
  · rw [Frame20.dep_0, hN.2]; ring
  · rw [Frame20.dep_1]; ring
  · rw [Frame20.dep_3, hN.1]; ring
  · rw [Frame20.dep_4]; ring
  · rw [Frame20.dep_6]; ring

/-- Strict facings at `u0` shared by U2 and U1 (facets `A B F G H`). -/
lemma u0_strict (hN : NF F.S) :
    0 < nf F.S ⟨1, 0, -1⟩ 0 ∧ nf F.S ⟨1, 0, -1⟩ 1 < 0 ∧ nf F.S ⟨1, 0, -1⟩ 5 < 0 ∧
    0 < nf F.S ⟨1, 0, -1⟩ 6 ∧ nf F.S ⟨1, 0, -1⟩ 7 < 0 := by
  obtain ⟨uA, uB, -, -, -, uF, uG, uH⟩ := u0_nf F.S hN
  have sm0 := F.S.sm_pos; have sm1 := F.S.sm1; have sp0 := F.S.sp_pos; have kp0 := F.S.kp_pos
  have km0 := F.S.km_pos; have rp := roofP_n F.S hN
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [uA]; exact sm0
  · rw [uB]; linarith
  · rw [uF]; linarith
  · rw [uG]; linarith
  · rw [uH]; linarith

/-- E1: line view `u = (0,-1,1)` (the line `E ∩ H`) tilted by `(1,1,0)`, cycle `13526`;
needs `km <= sm` and `ph > 0`. -/
theorem ia_E1 (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hN : NF F.S) (hk : F.S.km ≤ F.S.sm) (hph : 0 < (F.a12*(1-F.S.tm)-F.gg*F.S.tm)) : IsRupert (univ.image x) := by
  have sm0 := F.S.sm_pos; have sm1 := F.S.sm1; have tm0 := F.S.tm_pos; have tp1 := F.S.tp1
  have tm1 := F.S.tm1; have tp0 := F.S.tp_pos; have kp0 := F.S.kp_pos; have km0 := F.S.km_pos
  have sp0 := F.S.sp_pos; have sp1 := F.S.sp1
  have ha : 0 < F.a12 := F.A12_pos; have hg : 0 < F.gg := F.g_pos
  have h22 : F.a12 ≤ F.a22 := F.A12_le_A22
  have rp := roofP_n F.S hN
  have uA : nf F.S ⟨0, -1, 1⟩ 0 = -(F.S.tm + (F.S.sm-F.S.km)*(1-F.S.tm)) := by simp only [nf_A, hN.1]; ring
  have uB : nf F.S ⟨0, -1, 1⟩ 1 = F.S.tp*(F.S.kp+F.S.sp) := by simp only [nf_B, hN.2]; ring
  have uC : nf F.S ⟨0, -1, 1⟩ 2 = F.S.tm := by simp only [nf_C, hN.1, hN.2]; ring
  have uD : nf F.S ⟨0, -1, 1⟩ 3 = F.S.tm*(F.S.km-F.S.sm) := by simp only [nf_D, hN.1]; ring
  have uE : nf F.S ⟨0, -1, 1⟩ 4 = 0 := by simp only [nf_E, hN.2]; ring
  have uF : nf F.S ⟨0, -1, 1⟩ 5 = F.S.tp*(1-F.S.sp-F.S.kp) := by simp only [nf_F, hN.2]; ring
  have uG : nf F.S ⟨0, -1, 1⟩ 6 = -(F.S.km+1-F.S.sm) := by simp only [nf_G]; ring
  have uH : nf F.S ⟨0, -1, 1⟩ 7 = 0 := by simp only [nf_H]; ring
  have vD : nf F.S ⟨1, 1, 0⟩ 3 = -(F.S.tm*(F.S.sm+F.S.km)) := by simp only [nf_D, hN.1]; ring
  have vE : nf F.S ⟨1, 1, 0⟩ 4 = 2*(1-F.S.tp) := by simp only [nf_E, hN.2]; ring
  have vH : nf F.S ⟨1, 1, 0⟩ 7 = -F.S.kp := by simp only [nf_H]; ring
  refine leaf_of_view F (h20s_fac hR) hx (by norm_num) e1_inj e1_cyc ⟨0, -1, 1⟩ ⟨1, 1, 0⟩ 2
    (by rw [uC]; exact tm0.ne') ?_ ?_
  · intro t; fin_cases t
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (eq_neg uA (by nlinarith [mul_nonneg (sub_nonneg.2 hk) tm1.le]))⟩
    · exact ⟨fun _ => lp_pos (eq_pos uB (by positivity)), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp_pos (eq_pos uC tm0), fun h => absurd h (by decide)⟩
    · refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
      rcases hk.lt_or_eq with h | h
      · exact lpn_pos (eq_neg uD (mul_neg_of_pos_of_neg tm0 (by linarith)))
      · exact lpn_zero (uD.trans (by rw [h]; ring)) (eq_neg vD (by nlinarith [mul_pos tm0 sm0, mul_pos tm0 km0]))
    · exact ⟨fun _ => lp_zero uE (eq_pos vE (by linarith)), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp_pos (eq_pos uF (mul_pos tp0 (by linarith))), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (eq_neg uG (by linarith))⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_zero uH (eq_neg vH (by linarith))⟩
  · have z1 : F.dep ⟨0, -1, 1⟩ 1 = -F.a12 := by rw [Frame20.dep_1]; ring
    have z2 : F.dep ⟨0, -1, 1⟩ 2 = -F.a22*F.S.sp + F.gg*F.S.kp := by rw [Frame20.dep_2]; ring
    have z3 : F.dep ⟨0, -1, 1⟩ 3 = -F.S.tm*(F.a12+F.gg) := by rw [Frame20.dep_3, hN.1]; ring
    have z5 : F.dep ⟨0, -1, 1⟩ 5 = 0 := Frame20.dep_5 F _
    have z6 : F.dep ⟨0, -1, 1⟩ 6 = -F.a22 := by rw [Frame20.dep_6]; ring
    refine robUni5_H3 ?_ ?_ ?_ ?_
    · show F.dep _ 1 < F.dep _ 3
      rw [z1, z3]; nlinarith
    · show F.dep _ 3 < F.dep _ 5
      rw [z3, z5]; nlinarith [mul_pos tm0 (add_pos ha hg)]
    · show F.dep _ 6 ≤ F.dep _ 1
      rw [z6, z1]; linarith
    · show F.dep _ 6 < F.dep _ 2
      rw [z6, z2]; nlinarith [mul_pos hg kp0, F.A22_pos]

/-- S56: segment view `x6 - x5`, cycle `01462`; needs `A56 > 0` and `Lp >= 0`. -/
theorem ia_S56 (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hN : NF F.S) (hA : 0 < (F.S.km*(1-F.S.tm)-F.S.tm)) (hL : 0 ≤ ((1-F.S.sm)*(F.a22*F.S.sm-F.a12)-F.gg*F.S.km^2)) : IsRupert (univ.image x) := by
  have sm0 := F.S.sm_pos; have sm1 := F.S.sm1; have tm0 := F.S.tm_pos; have tp1 := F.S.tp1
  have tp0 := F.S.tp_pos; have km0 := F.S.km_pos; have sp0 := F.S.sp_pos; have sp1 := F.S.sp1
  have ha : 0 < F.a12 := F.A12_pos; have hg : 0 < F.gg := F.g_pos
  have nA : nf F.S ⟨0, 1, 0⟩ 0 < 0 := by
    have e : nf F.S ⟨0, 1, 0⟩ 0 = -(F.S.km*(1-F.S.tm)-F.S.tm) := by simp only [nf_A, hN.1]; ring
    rw [e]; linarith
  refine seg_leaf F (h20s_fac hR) hx ias_S56 ias_S56_good ⟨0, 1, 0⟩
    (seg_vec F 5 6 _ (by rw [F.ptC_6, F.ptC_5]; simp only [C3.sub]; congr 1 <;> ring)) (by ia_lits) ?_
  have z0 : F.dep ⟨0, 1, 0⟩ 0 = F.a12*F.S.tp := by rw [Frame20.dep_0]; ring
  have z1 : F.dep ⟨0, 1, 0⟩ 1 = F.a12 := by rw [Frame20.dep_1]; ring
  have z4 : F.dep ⟨0, 1, 0⟩ 4 = F.a22*F.S.sm := by rw [Frame20.dep_4]; ring
  have z6 : F.dep ⟨0, 1, 0⟩ 6 = F.a22 := by rw [Frame20.dep_6]; ring
  have h22 : 0 < F.a22 := F.A22_pos
  have cs : F.a12 < F.a22*F.S.sm := by
    have h1 : 0 < (1-F.S.sm)*(F.a22*F.S.sm - F.a12) := by nlinarith [mul_pos hg (pow_pos km0 2)]
    have := pos_of_mul_pos_right h1 sm1.le
    linarith
  refine robUni5_H1 ?_ ?_ ?_
  · show F.dep _ 0 < F.dep _ 1
    rw [z0, z1]; nlinarith
  · show F.dep _ 1 < F.dep _ 4
    rw [z1, z4]; exact cs
  · show F.dep _ 4 < F.dep _ 6
    rw [z4, z6]; nlinarith

/-- U2: the view `u0` tilted by `(1,1,0)`, cycle `01346`; needs `Phi > 0` and `Y < 0 or Z4 < 0`. -/
theorem ia_U2 (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hN : NF F.S) (hP : 0 < (F.gg*F.S.km-F.a12*(1-F.S.sm))) (hYZ : (F.a11*(1-F.S.tm)-F.gg*F.S.tm) < 0 ∨ (F.a12*F.S.sm+F.gg*(F.S.km-F.S.tm)-F.a11*F.S.tm) < 0) : IsRupert (univ.image x) := by
  have sm0 := F.S.sm_pos; have tm0 := F.S.tm_pos; have tp1 := F.S.tp1; have km0 := F.S.km_pos
  have ha : 0 < F.a12 := F.A12_pos; have hg : 0 < F.gg := F.g_pos
  have h11 : F.a12 ≤ F.a11 := F.A12_le_A11
  obtain ⟨sA, sB, sF, sG, sH⟩ := u0_strict F hN
  obtain ⟨uA, uB, uC, uD, uE, uF, uG, uH⟩ := u0_nf F.S hN
  have vC : nf F.S ⟨1, 1, 0⟩ 2 = -F.S.tm := by simp only [nf_C, hN.1, hN.2]; ring
  have vD : nf F.S ⟨1, 1, 0⟩ 3 = -(F.S.tm*(F.S.sm+F.S.km)) := by simp only [nf_D, hN.1]; ring
  have vE : nf F.S ⟨1, 1, 0⟩ 4 = 2*(1-F.S.tp) := by simp only [nf_E, hN.2]; ring
  refine leaf_of_view F (h20s_fac hR) hx (by norm_num) u2_inj u2_cyc ⟨1, 0, -1⟩ ⟨1, 1, 0⟩ 0
    sA.ne' ?_ ?_
  · intro t; fin_cases t
    · exact ⟨fun _ => lp_pos sA, fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos sB⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_zero uC (eq_neg vC (by linarith))⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_zero uD (eq_neg vD (by nlinarith [mul_pos tm0 sm0, mul_pos tm0 km0]))⟩
    · exact ⟨fun _ => lp_zero uE (eq_pos vE (by linarith)), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos sF⟩
    · exact ⟨fun _ => lp_pos sG, fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos sH⟩
  · obtain ⟨z0, z1, z3, z4, z5, z6⟩ := u0_dep F hN
    refine robUni5_H4 ?_ ?_ ?_
    · show F.dep _ 0 < F.dep _ 1
      rw [z0, z1]; nlinarith
    · show F.dep _ 6 < F.dep _ 4
      rw [z6, z4]; linarith
    · show F.dep _ 1 < F.dep _ 3 ∨ F.dep _ 4 < F.dep _ 3
      rw [z1, z3, z4]
      rcases hYZ with h | h
      · left; nlinarith
      · right; nlinarith

/-- U1: the view `u0` tilted by `(2,-1,0)`, cycle `05346`; needs `km <= sm`, `Phi > 0`, `Lq < 0`. -/
theorem ia_U1 (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hN : NF F.S) (hk : F.S.km ≤ F.S.sm) (hP : 0 < (F.gg*F.S.km-F.a12*(1-F.S.sm))) (hL : (F.a11*F.S.tp-F.a12-F.gg*(1-F.S.tp)) < 0) : IsRupert (univ.image x) := by
  have sm0 := F.S.sm_pos; have tm0 := F.S.tm_pos; have tp1 := F.S.tp1; have km0 := F.S.km_pos
  have ha : 0 < F.a12 := F.A12_pos; have hg : 0 < F.gg := F.g_pos
  have h11 : F.a12 ≤ F.a11 := F.A12_le_A11
  obtain ⟨sA, sB, sF, sG, sH⟩ := u0_strict F hN
  obtain ⟨uA, uB, uC, uD, uE, uF, uG, uH⟩ := u0_nf F.S hN
  have vC : nf F.S ⟨2, -1, 0⟩ 2 = F.S.tm := by simp only [nf_C, hN.1, hN.2]; ring
  have vD : nf F.S ⟨2, -1, 0⟩ 3 = -(F.S.tm*(2*F.S.sm-F.S.km)) := by simp only [nf_D, hN.1]; ring
  have vE : nf F.S ⟨2, -1, 0⟩ 4 = 1-F.S.tp := by simp only [nf_E, hN.2]; ring
  refine leaf_of_view F (h20s_fac hR) hx (by norm_num) u1_inj u1_cyc ⟨1, 0, -1⟩ ⟨2, -1, 0⟩ 0
    sA.ne' ?_ ?_
  · intro t; fin_cases t
    · exact ⟨fun _ => lp_pos sA, fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos sB⟩
    · exact ⟨fun _ => lp_zero uC (eq_pos vC tm0), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_zero uD (eq_neg vD (by nlinarith [mul_pos tm0 sm0, mul_nonneg tm0.le (sub_nonneg.2 hk)]))⟩
    · exact ⟨fun _ => lp_zero uE (eq_pos vE tp1), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos sF⟩
    · exact ⟨fun _ => lp_pos sG, fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos sH⟩
  · obtain ⟨z0, z1, z3, z4, z5, z6⟩ := u0_dep F hN
    refine robUni5_H5 ?_ ?_ ?_
    · show F.dep _ 0 < F.dep _ 6
      rw [z0, z6]; linarith
    · show F.dep _ 6 < F.dep _ 4
      rw [z6, z4]; linarith
    · show F.dep _ 5 < F.dep _ 3
      rw [z5, z3]; nlinarith [mul_pos tm0 (add_pos (lt_of_lt_of_le ha h11) hg)]

end IAT
end Minimality.CaseC20

end

section


/-!
# I_A, leaves LAHa, LAHb, C6, S15
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace IAT
open IVT
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

def laha_pat : Fin 8 → Bool := ![false, false, false, false, true, true, true, false]
def laha_c : ZMod 5 → Fin 7 := ![0, 1, 4, 6, 2]
theorem laha_cyc : S0xCycOK h20s_S laha_c laha_pat := by decide
theorem laha_inj : Function.Injective laha_c := by decide

def lahb_pat : Fin 8 → Bool := ![false, true, false, false, true, true, true, true]
def lahb_c : ZMod 4 → Fin 7 := ![0, 1, 4, 5]
theorem lahb_cyc : S0xCycOK h20s_S lahb_c lahb_pat := by decide
theorem lahb_inj : Function.Injective lahb_c := by decide

/-- The line view `lq = (0, sm(1-tm), -A56)` (the line `A ∩ H`). -/
noncomputable def lq (S : Shape20) : C3 := ⟨0, S.sm*(1-S.tm), -(S.km*(1-S.tm)-S.tm)⟩

/-- Facings at `lq`, with `e = sm(1-tm)`, `f = -A56`. -/
lemma lq_nf (S : Shape20) (hN : NF S) :
    nf S (lq S) 0 = 0 ∧
    nf S (lq S) 1 = S.tp * (S.sp*(S.tm-S.km*(1-S.tm))-S.kp*S.sm*(1-S.tm)) ∧
    nf S (lq S) 2 = -(S.tm*(S.sm*(1-S.tm))) ∧
    nf S (lq S) 3 = -(S.tm*(S.km*(S.sm*(1-S.tm)) + S.sm*(S.tm-S.km*(1-S.tm)))) ∧
    nf S (lq S) 4 = (1-S.tp)*(S.sm*(1-S.tm) + (S.tm-S.km*(1-S.tm))) ∧
    nf S (lq S) 5 = S.tp*(S.kp*(S.sm*(1-S.tm)) + (1-S.sp)*(S.tm-S.km*(1-S.tm))) ∧
    nf S (lq S) 6 = S.km*(1-S.tm)-S.tm*(1-S.sm) ∧
    nf S (lq S) 7 = 0 := by
  unfold lq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [nf_A, hN.1]; ring
  · simp only [nf_B, hN.2]; ring
  · simp only [nf_C, hN.1, hN.2]; ring
  · simp only [nf_D, hN.1]; ring
  · simp only [nf_E, hN.2]; ring
  · simp only [nf_F, hN.2]; ring
  · simp only [nf_G]; ring
  · simp only [nf_H]; ring

/-- Depths at `lq`. -/
lemma lq_dep (hN : NF F.S) :
    F.dep (lq F.S) 0 = F.S.tp*F.a12*(F.S.sm*(1-F.S.tm)) + F.gg*(F.S.tm-F.S.km*(1-F.S.tm))*(1-F.S.tp) ∧
    F.dep (lq F.S) 1 = F.a12*(F.S.sm*(1-F.S.tm)) ∧
    F.dep (lq F.S) 4 = F.S.sm*F.a22*(F.S.sm*(1-F.S.tm)) - F.gg*F.S.km*(F.S.tm-F.S.km*(1-F.S.tm)) ∧
    F.dep (lq F.S) 5 = 0 ∧ F.dep (lq F.S) 6 = F.a22*(F.S.sm*(1-F.S.tm)) := by
  unfold lq
  refine ⟨?_, ?_, ?_, Frame20.dep_5 F _, ?_⟩
  · rw [Frame20.dep_0, hN.2]; ring
  · rw [Frame20.dep_1]; ring
  · rw [Frame20.dep_4]; ring
  · rw [Frame20.dep_6]; ring

/-- Common facts of LAHa and LAHb at `lq`: the facings of `A C D E F G` and the three depth inequalities. -/
lemma lah_common (hN : NF F.S) (h56 : (F.S.km*(1-F.S.tm)-F.S.tm) ≤ 0) (hL : 0 ≤ ((1-F.S.sm)*(F.a22*F.S.sm-F.a12)-F.gg*F.S.km^2)) (hX : 0 < ((1-F.S.tm)*F.S.sm*F.a12+F.gg*(F.S.km*(1-F.S.tm)-F.S.tm))) :
    0 < F.dep (lq F.S) 4 - F.dep (lq F.S) 1 ∧ 0 < F.dep (lq F.S) 6 - F.dep (lq F.S) 4 ∧
    0 < F.dep (lq F.S) 1 - F.dep (lq F.S) 0 ∧ 0 < F.dep (lq F.S) 0 := by
  obtain ⟨z0, z1, z4, z5, z6⟩ := lq_dep F hN
  have sm0 := F.S.sm_pos; have sm1 := F.S.sm1; have tm0 := F.S.tm_pos; have tp1 := F.S.tp1
  have tm1 := F.S.tm1; have tp0 := F.S.tp_pos; have km0 := F.S.km_pos
  have ha : 0 < F.a12 := F.A12_pos; have hg : 0 < F.gg := F.g_pos
  have rm := rm_pos F.S hN; have h22 : 0 < F.a22 := F.A22_pos
  have hf : 0 ≤ F.S.tm - F.S.km*(1-F.S.tm) := by linarith
  have he : 0 < F.S.sm*(1-F.S.tm) := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [z4, z1]
    have e : (1-F.S.sm) * (F.S.sm*F.a22*(F.S.sm*(1-F.S.tm)) - F.gg*F.S.km*(F.S.tm-F.S.km*(1-F.S.tm)) - F.a12*(F.S.sm*(1-F.S.tm)))
        = (F.S.sm*(1-F.S.tm))*((1-F.S.sm)*(F.a22*F.S.sm-F.a12)-F.gg*F.S.km^2) + F.gg*F.S.km*(F.S.km*(1-F.S.tm)-F.S.tm*(1-F.S.sm)) := by ring
    have h1 : 0 < (1-F.S.sm) * (F.S.sm*F.a22*(F.S.sm*(1-F.S.tm)) - F.gg*F.S.km*(F.S.tm-F.S.km*(1-F.S.tm)) - F.a12*(F.S.sm*(1-F.S.tm))) := by
      rw [e]; exact add_pos_of_nonneg_of_pos (mul_nonneg he.le hL) (mul_pos (mul_pos hg km0) rm)
    exact pos_of_mul_pos_right h1 sm1.le
  · rw [z6, z4]
    have e : F.a22*(F.S.sm*(1-F.S.tm)) - (F.S.sm*F.a22*(F.S.sm*(1-F.S.tm)) - F.gg*F.S.km*(F.S.tm-F.S.km*(1-F.S.tm)))
        = F.a22*(F.S.sm*(1-F.S.tm))*(1-F.S.sm) + F.gg*F.S.km*(F.S.tm-F.S.km*(1-F.S.tm)) := by ring
    rw [e]
    exact add_pos_of_pos_of_nonneg (mul_pos (mul_pos h22 he) sm1) (mul_nonneg (mul_pos hg km0).le hf)
  · rw [z1, z0]
    have e : F.a12*(F.S.sm*(1-F.S.tm)) - (F.S.tp*F.a12*(F.S.sm*(1-F.S.tm)) + F.gg*(F.S.tm-F.S.km*(1-F.S.tm))*(1-F.S.tp)) = (1-F.S.tp)*((1-F.S.tm)*F.S.sm*F.a12+F.gg*(F.S.km*(1-F.S.tm)-F.S.tm)) := by ring
    rw [e]; exact mul_pos tp1 hX
  · rw [z0]
    exact add_pos_of_pos_of_nonneg (mul_pos (mul_pos tp0 ha) he) (mul_nonneg (mul_nonneg hg.le hf) tp1.le)

/-- LAHa: the line view `lq` tilted by `(1-tm, 0, 2tm)`, cycle `01462`; needs `Lp >= 0`, `A56 <= 0`,
`X > 0`, `a25 < 0`. -/
theorem ia_LAHa (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hN : NF F.S) (hL : 0 ≤ ((1-F.S.sm)*(F.a22*F.S.sm-F.a12)-F.gg*F.S.km^2)) (h56 : (F.S.km*(1-F.S.tm)-F.S.tm) ≤ 0) (hX : 0 < ((1-F.S.tm)*F.S.sm*F.a12+F.gg*(F.S.km*(1-F.S.tm)-F.S.tm))) (h25 : (F.S.sp*(F.S.tm-F.S.km*(1-F.S.tm))-F.S.kp*F.S.sm*(1-F.S.tm)) < 0) :
    IsRupert (univ.image x) := by
  have sm0 := F.S.sm_pos; have sm1 := F.S.sm1; have tm0 := F.S.tm_pos; have tp1 := F.S.tp1
  have tm1 := F.S.tm1; have tp0 := F.S.tp_pos; have kp0 := F.S.kp_pos; have km0 := F.S.km_pos
  have rm := rm_pos F.S hN
  obtain ⟨uA, uB, uC, uD, uE, uF, uG, uH⟩ := lq_nf F.S hN
  have hf : 0 ≤ F.S.tm - F.S.km*(1-F.S.tm) := by linarith
  have he : 0 < F.S.sm*(1-F.S.tm) := by positivity
  have vA : nf F.S ⟨1-F.S.tm, 0, 2*F.S.tm⟩ 0 = -(F.S.tm*F.S.sm*(1-F.S.tm)) := by simp only [nf_A, hN.1]; ring
  have vH : nf F.S ⟨1-F.S.tm, 0, 2*F.S.tm⟩ 7 = -(F.S.kp*(1-F.S.tm)) := by simp only [nf_H]; ring
  obtain ⟨c1, c2, c3, c4⟩ := lah_common F hN h56 hL hX
  obtain ⟨z0, z1, z4, z5, z6⟩ := lq_dep F hN
  refine leaf_of_view F (h20s_fac hR) hx (by norm_num) laha_inj laha_cyc (lq F.S) ⟨1-F.S.tm, 0, 2*F.S.tm⟩ 2
    (eq_neg uC (by linarith [mul_pos tm0 he])).ne ?_ ?_
  · intro t; fin_cases t
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_zero uA (eq_neg vA (by linarith [mul_pos (mul_pos tm0 sm0) tm1]))⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (eq_neg uB (mul_neg_of_pos_of_neg tp0 h25))⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (eq_neg uC (by linarith [mul_pos tm0 he]))⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (eq_neg uD (by linarith [mul_pos tm0 (mul_pos km0 he), mul_nonneg tm0.le (mul_nonneg sm0.le hf)]))⟩
    · exact ⟨fun _ => lp_pos (eq_pos uE (mul_pos tp1 (add_pos_of_pos_of_nonneg he hf))), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp_pos (eq_pos uF (mul_pos tp0 (add_pos_of_pos_of_nonneg (mul_pos kp0 he) (mul_nonneg F.S.sp1.le hf)))), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp_pos (eq_pos uG rm), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_zero uH (eq_neg vH (by linarith [mul_pos kp0 tm1]))⟩
  · refine robUni5_H1 ?_ ?_ ?_
    · show F.dep _ 0 < F.dep _ 1
      linarith
    · show F.dep _ 1 < F.dep _ 4
      linarith
    · show F.dep _ 4 < F.dep _ 6
      linarith

end IAT
end Minimality.CaseC20

end

section


/-!
# I_A, leaves LAHb, C6, S15
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace IAT
open IVT
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- LAHb: the line view `lq` tilted by `(-1,0,0)`, cycle `0145`; needs `Lp >= 0`, `A56 <= 0`, `X > 0`,
`a25 >= 0`. -/
theorem ia_LAHb (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hN : NF F.S) (hL : 0 ≤ ((1-F.S.sm)*(F.a22*F.S.sm-F.a12)-F.gg*F.S.km^2)) (h56 : (F.S.km*(1-F.S.tm)-F.S.tm) ≤ 0) (hX : 0 < ((1-F.S.tm)*F.S.sm*F.a12+F.gg*(F.S.km*(1-F.S.tm)-F.S.tm))) (h25 : 0 ≤ (F.S.sp*(F.S.tm-F.S.km*(1-F.S.tm))-F.S.kp*F.S.sm*(1-F.S.tm))) :
    IsRupert (univ.image x) := by
  have sm0 := F.S.sm_pos; have sm1 := F.S.sm1; have tm0 := F.S.tm_pos; have tp1 := F.S.tp1
  have tm1 := F.S.tm1; have tp0 := F.S.tp_pos; have kp0 := F.S.kp_pos; have km0 := F.S.km_pos
  have sp0 := F.S.sp_pos; have sp1 := F.S.sp1
  have rm := rm_pos F.S hN
  obtain ⟨uA, uB, uC, uD, uE, uF, uG, uH⟩ := lq_nf F.S hN
  have hf : 0 ≤ F.S.tm - F.S.km*(1-F.S.tm) := by linarith
  have he : 0 < F.S.sm*(1-F.S.tm) := by positivity
  have vA : nf F.S ⟨-1, 0, 0⟩ 0 = -(F.S.tm*F.S.sm) := by simp only [nf_A, hN.1]; ring
  have vB : nf F.S ⟨-1, 0, 0⟩ 1 = (1-F.S.tp)*F.S.sp := by simp only [nf_B, hN.2]; ring
  have vH : nf F.S ⟨-1, 0, 0⟩ 7 = F.S.kp := by simp only [nf_H]; ring
  obtain ⟨c1, c2, c3, c4⟩ := lah_common F hN h56 hL hX
  obtain ⟨z0, z1, z4, z5, z6⟩ := lq_dep F hN
  refine leaf_of_view F (h20s_fac hR) hx (by norm_num) lahb_inj lahb_cyc (lq F.S) ⟨-1, 0, 0⟩ 2
    (eq_neg uC (by have := mul_pos tm0 he; linarith)).ne ?_ ?_
  · intro t; fin_cases t
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_zero uA (eq_neg vA (by have := mul_pos tm0 sm0; linarith))⟩
    · refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
      rcases h25.lt_or_eq with h | h
      · exact lp_pos (eq_pos uB (mul_pos tp0 h))
      · exact lp_zero (uB.trans (by rw [← h]; ring)) (eq_pos vB (mul_pos tp1 sp0))
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (eq_neg uC (by have := mul_pos tm0 he; linarith))⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (eq_neg uD (by
        linarith [mul_pos tm0 (mul_pos km0 he), mul_nonneg tm0.le (mul_nonneg sm0.le hf)]))⟩
    · exact ⟨fun _ => lp_pos (eq_pos uE (mul_pos tp1 (add_pos_of_pos_of_nonneg he hf))), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp_pos (eq_pos uF (mul_pos tp0 (add_pos_of_pos_of_nonneg (mul_pos kp0 he) (mul_nonneg sp1.le hf)))), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp_pos (eq_pos uG rm), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp_zero uH (eq_pos vH kp0), fun h => absurd h (by decide)⟩
  · refine robUni4 ?_ ?_
    · rintro ⟨h1, h2, h3, h4⟩
      have h1' : F.dep (lq F.S) 1 ≤ F.dep (lq F.S) 0 := h1
      linarith
    · rintro ⟨h1, h2, h3, h4⟩
      have h2' : F.dep (lq F.S) 0 ≤ F.dep (lq F.S) 5 := h2
      rw [z5] at h2'
      linarith

/-- C6: segment view `x1 - x4`, cycle `46253`; needs `A2 > 0`, `Lp >= 0`, `B14 > 0`, `A14 > 0`. -/
theorem ia_C6 (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hN : NF F.S) (hA : 0 < (F.S.km*F.S.sp-F.S.kp*(1-F.S.sm))) (hL : 0 ≤ ((1-F.S.sm)*(F.a22*F.S.sm-F.a12)-F.gg*F.S.km^2)) (hB : 0 < (F.S.tp*(F.S.kp*F.S.sm+F.S.km*F.S.sp)-F.S.sp*(1-F.S.tp))) (hA14 : 0 < (F.S.kp*(1-F.S.tp*F.S.sm)-(1-F.S.tp)*(1-F.S.sp)+F.S.km*F.S.tp*(1-F.S.sp))) :
    IsRupert (univ.image x) := by
  have sm0 := F.S.sm_pos; have sm1 := F.S.sm1; have tm0 := F.S.tm_pos; have tp1 := F.S.tp1
  have tm1 := F.S.tm1; have tp0 := F.S.tp_pos; have kp0 := F.S.kp_pos; have km0 := F.S.km_pos
  have sp0 := F.S.sp_pos; have sp1 := F.S.sp1
  have ha : 0 < F.a12 := F.A12_pos; have hg : 0 < F.gg := F.g_pos
  have h11 : F.a12 ≤ F.a11 := F.A12_le_A11
  have s2 := S2 F hN
  have nB : 0 < nf F.S ⟨1, -F.S.sm, F.S.km⟩ 1 := by
    have e : nf F.S ⟨1, -F.S.sm, F.S.km⟩ 1 = (F.S.tp*(F.S.kp*F.S.sm+F.S.km*F.S.sp)-F.S.sp*(1-F.S.tp)) := by simp only [nf_B, hN.2]; ring
    rw [e]; exact hB
  have nF : 0 < nf F.S ⟨1, -F.S.sm, F.S.km⟩ 5 := by
    have e : nf F.S ⟨1, -F.S.sm, F.S.km⟩ 5 = (F.S.kp*(1-F.S.tp*F.S.sm)-(1-F.S.tp)*(1-F.S.sp)+F.S.km*F.S.tp*(1-F.S.sp)) := by simp only [nf_F, hN.2]; ring
    rw [e]; exact hA14
  refine seg_leaf F (h20s_fac hR) hx ias_C6 ias_C6_good ⟨1, -F.S.sm, F.S.km⟩
    (seg_vec F 4 1 _ (by rw [F.ptC_1, F.ptC_4]; simp only [C3.sub]; congr 1 <;> ring)) (by ia_lits) ?_
  set T := F.a22*F.S.sm - F.a12 with hT
  have hT0 : 0 < T := by
    have h1 : 0 < (1-F.S.sm) * T := by
      have : (1-F.S.sm) * T = ((1-F.S.sm)*(F.a22*F.S.sm-F.a12)-F.gg*F.S.km^2) + F.gg*F.S.km^2 := by rw [hT]; ring
      rw [this]; exact add_pos_of_nonneg_of_pos hL (mul_pos hg (pow_pos km0 2))
    exact pos_of_mul_pos_right h1 sm1.le
  have hY : 0 < F.a11 - F.a12*F.S.sm := by nlinarith [mul_pos ha sm1]
  have z2 : F.dep ⟨1, -F.S.sm, F.S.km⟩ 2 = -T*F.S.sp + F.gg*F.S.km*F.S.kp := by rw [Frame20.dep_2, hT]; ring
  have z3 : F.dep ⟨1, -F.S.sm, F.S.km⟩ 3 = (F.a11 - F.a12*F.S.sm)*F.S.tm - F.gg*F.S.km*F.S.tm := by
    rw [Frame20.dep_3, hN.1]; ring
  have z4 : F.dep ⟨1, -F.S.sm, F.S.km⟩ 4 = -T*F.S.sm - F.gg*F.S.km^2 := by rw [Frame20.dep_4, hT]; ring
  have z5 : F.dep ⟨1, -F.S.sm, F.S.km⟩ 5 = 0 := Frame20.dep_5 F _
  have z6 : F.dep ⟨1, -F.S.sm, F.S.km⟩ 6 = -T := by rw [Frame20.dep_6, hT]; ring
  refine robUni5_d ?_ ?_ ?_
  · show F.dep _ 6 < F.dep _ 2
    rw [z6, z2]
    have := mul_pos hT0 sp1; have := mul_pos hg (mul_pos km0 kp0)
    linarith
  · show F.dep _ 2 < F.dep _ 5
    rw [z2, z5]
    have e : (1-F.S.sm) * (-T*F.S.sp + F.gg*F.S.km*F.S.kp) = -F.gg*F.S.km*(F.S.km*F.S.sp-F.S.kp*(1-F.S.sm)) - F.S.sp*((1-F.S.sm)*(F.a22*F.S.sm-F.a12)-F.gg*F.S.km^2) := by rw [hT]; ring
    have h1 : (1-F.S.sm) * (-T*F.S.sp + F.gg*F.S.km*F.S.kp) < 0 := by
      rw [e]; nlinarith [mul_pos (mul_pos hg km0) hA, mul_nonneg sp0.le hL]
    exact neg_of_mul_neg_right h1 sm1.le
  · show F.dep _ 4 < F.dep _ 3
    rw [z4, z3]
    have e : (1-F.S.sm) * (((F.a11 - F.a12*F.S.sm)*F.S.tm - F.gg*F.S.km*F.S.tm) - (-T*F.S.sm - F.gg*F.S.km^2))
        = (1-F.S.sm)*(F.a11 - F.a12*F.S.sm)*F.S.tm + F.S.sm*((1-F.S.sm)*(F.a22*F.S.sm-F.a12)-F.gg*F.S.km^2) + F.gg*F.S.km*(F.S.km - (1-F.S.sm)*F.S.tm) := by rw [hT]; ring
    have h1 : 0 < (1-F.S.sm) * (((F.a11 - F.a12*F.S.sm)*F.S.tm - F.gg*F.S.km*F.S.tm) - (-T*F.S.sm - F.gg*F.S.km^2)) := by
      rw [e]
      have := mul_pos (mul_pos sm1 hY) tm0
      have := mul_nonneg sm0.le hL
      have := mul_pos (mul_pos hg km0) s2
      linarith
    have := pos_of_mul_pos_right h1 sm1.le
    linarith

/-- S15: segment view `x1 - x5`, cycle `01346`; needs `rho > 0` and `a12 < a11 tp`. -/
theorem ia_S15 (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hN : NF F.S) (hr : 0 < ((1-F.S.sp)*(1-F.S.tp)-F.S.kp)) (hq : F.a12 < F.a11 * F.S.tp) : IsRupert (univ.image x) := by
  have sm0 := F.S.sm_pos; have sm1 := F.S.sm1; have tm0 := F.S.tm_pos; have tp1 := F.S.tp1
  have tm1 := F.S.tm1; have tp0 := F.S.tp_pos
  have ha : 0 < F.a12 := F.A12_pos
  have h11 : 0 < F.a11 := F.A11_pos
  have nF : nf F.S ⟨1, 0, 0⟩ 5 < 0 := by
    have e : nf F.S ⟨1, 0, 0⟩ 5 = -((1-F.S.sp)*(1-F.S.tp)-F.S.kp) := by simp only [nf_F, hN.2]; ring
    rw [e]; linarith
  refine seg_leaf F (h20s_fac hR) hx h20s_s15 h20s_s15_good ⟨1, 0, 0⟩
    (seg_vec F 5 1 _ (by rw [F.ptC_1, F.ptC_5]; simp only [C3.sub]; congr 1 <;> ring)) (by ia_lits) ?_
  have z0 : F.dep ⟨1, 0, 0⟩ 0 = F.a11 * F.S.tp := by rw [Frame20.dep_0]; ring
  have z1 : F.dep ⟨1, 0, 0⟩ 1 = F.a11 := by rw [Frame20.dep_1]; ring
  have z3 : F.dep ⟨1, 0, 0⟩ 3 = F.a11 * F.S.tm := by rw [Frame20.dep_3]; ring
  have z4 : F.dep ⟨1, 0, 0⟩ 4 = F.a12 * F.S.sm := by rw [Frame20.dep_4]; ring
  have z6 : F.dep ⟨1, 0, 0⟩ 6 = F.a12 := by rw [Frame20.dep_6]; ring
  refine robUni5_H7 ?_ ?_ ?_ ?_
  · show F.dep _ 6 < F.dep _ 0
    rw [z6, z0]; exact hq
  · show F.dep _ 0 < F.dep _ 1
    rw [z0, z1]; nlinarith
  · show F.dep _ 3 < F.dep _ 1
    rw [z3, z1]; nlinarith
  · show F.dep _ 4 < F.dep _ 6
    rw [z4, z6]; nlinarith

end IAT
end Minimality.CaseC20

end

section


/-!
# I_A, leaves LCF, W
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace IAT
open IVT
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

def w_pat : Fin 8 → Bool := ![false, false, false, false, true, true, true, false]
def w_c : ZMod 5 → Fin 7 := ![0, 1, 4, 6, 2]
theorem w_cyc : S0xCycOK h20s_S w_c w_pat := by decide
theorem w_inj : Function.Injective w_c := by decide

/-- LCF: the line view `(xh, 0, rho)` (the line `C ∩ F`, `xh = tp(1-sp)`) tilted by `(0, 1-sp, -(kp+1-sp))`,
cycle `01346`; needs `rho <= 0`, `Kf > 0`, `Y >= 0`, `Lq >= 0`. -/
theorem ia_LCF (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hN : NF F.S) (hr : ((1-F.S.sp)*(1-F.S.tp)-F.S.kp) ≤ 0) (hK : 0 < ((1-F.S.sp)*F.S.tp*F.a12*(1-F.S.sm)+F.gg*F.S.km*((1-F.S.sp)*(1-F.S.tp)-F.S.kp))) (hY : 0 ≤ (F.a11*(1-F.S.tm)-F.gg*F.S.tm)) (hL : 0 ≤ (F.a11*F.S.tp-F.a12-F.gg*(1-F.S.tp))) :
    IsRupert (univ.image x) := by
  have sm0 := F.S.sm_pos; have sm1 := F.S.sm1; have tm0 := F.S.tm_pos; have tp1 := F.S.tp1
  have tm1 := F.S.tm1; have tp0 := F.S.tp_pos; have kp0 := F.S.kp_pos; have km0 := F.S.km_pos
  have sp0 := F.S.sp_pos; have sp1 := F.S.sp1
  have ha : 0 < F.a11 := F.A11_pos; have hg : 0 < F.gg := F.g_pos
  have rp := roofP_n F.S hN
  have hxh : 0 < F.S.tp*(1-F.S.sp) := mul_pos tp0 sp1
  have hw : 0 < 1 - F.S.sp - F.S.kp := by linarith
  have uA : nf F.S ⟨F.S.tp*(1-F.S.sp), 0, ((1-F.S.sp)*(1-F.S.tp)-F.S.kp)⟩ 0 = F.S.sm*(F.S.tm*(F.S.tp*(1-F.S.sp)) - (1-F.S.tm)*((1-F.S.sp)*(1-F.S.tp)-F.S.kp)) := by
    simp only [nf_A, hN.1]; ring
  have uB : nf F.S ⟨F.S.tp*(1-F.S.sp), 0, ((1-F.S.sp)*(1-F.S.tp)-F.S.kp)⟩ 1 = -(F.S.sp*F.S.tp*F.S.kp) := by simp only [nf_B, hN.2]; ring
  have uC : nf F.S ⟨F.S.tp*(1-F.S.sp), 0, ((1-F.S.sp)*(1-F.S.tp)-F.S.kp)⟩ 2 = 0 := by simp only [nf_C]; ring
  have uD : nf F.S ⟨F.S.tp*(1-F.S.sp), 0, ((1-F.S.sp)*(1-F.S.tp)-F.S.kp)⟩ 3 = -(F.S.tm*F.S.sm*(1-F.S.sp-F.S.kp)) := by simp only [nf_D, hN.1]; ring
  have uE : nf F.S ⟨F.S.tp*(1-F.S.sp), 0, ((1-F.S.sp)*(1-F.S.tp)-F.S.kp)⟩ 4 = (1-F.S.tp)*(1-F.S.sp-F.S.kp) := by simp only [nf_E, hN.2]; ring
  have uF : nf F.S ⟨F.S.tp*(1-F.S.sp), 0, ((1-F.S.sp)*(1-F.S.tp)-F.S.kp)⟩ 5 = 0 := by simp only [nf_F, hN.2]; ring
  have uG : nf F.S ⟨F.S.tp*(1-F.S.sp), 0, ((1-F.S.sp)*(1-F.S.tp)-F.S.kp)⟩ 6 = F.S.km*(F.S.tp*(1-F.S.sp)) - (1-F.S.sm)*((1-F.S.sp)*(1-F.S.tp)-F.S.kp) := by
    simp only [nf_G]; ring
  have uH : nf F.S ⟨F.S.tp*(1-F.S.sp), 0, ((1-F.S.sp)*(1-F.S.tp)-F.S.kp)⟩ 7 = -(F.S.kp*(F.S.tp*(1-F.S.sp))) := by simp only [nf_H]; ring
  have vC : nf F.S ⟨0, 1-F.S.sp, -(F.S.kp+(1-F.S.sp))⟩ 2 = -(F.S.tm*(1-F.S.sp)) := by
    simp only [nf_C, hN.1, hN.2]; ring
  have vF : nf F.S ⟨0, 1-F.S.sp, -(F.S.kp+(1-F.S.sp))⟩ 5 = -(F.S.tp*(1-F.S.sp)^2) := by
    simp only [nf_F, hN.2]; ring
  have pA : 0 < F.S.sm*(F.S.tm*(F.S.tp*(1-F.S.sp)) - (1-F.S.tm)*((1-F.S.sp)*(1-F.S.tp)-F.S.kp)) := by
    have := mul_pos tm0 hxh; have := mul_nonneg tm1.le (neg_nonneg.2 hr)
    exact mul_pos sm0 (by linarith)
  have pG : 0 < F.S.km*(F.S.tp*(1-F.S.sp)) - (1-F.S.sm)*((1-F.S.sp)*(1-F.S.tp)-F.S.kp) := by
    have := mul_pos km0 hxh; have := mul_nonneg sm1.le (neg_nonneg.2 hr)
    linarith
  refine leaf_of_view F (h20s_fac hR) hx (by norm_num) u2_inj u2_cyc ⟨F.S.tp*(1-F.S.sp), 0, ((1-F.S.sp)*(1-F.S.tp)-F.S.kp)⟩
    ⟨0, 1-F.S.sp, -(F.S.kp+(1-F.S.sp))⟩ 0 (eq_pos uA pA).ne' ?_ ?_
  · intro t; fin_cases t
    · exact ⟨fun _ => lp_pos (eq_pos uA pA), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (eq_neg uB (by
        have := mul_pos (mul_pos sp0 tp0) kp0; linarith))⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_zero uC (eq_neg vC (by
        have := mul_pos tm0 sp1; linarith))⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (eq_neg uD (by
        have := mul_pos (mul_pos tm0 sm0) hw; linarith))⟩
    · exact ⟨fun _ => lp_pos (eq_pos uE (mul_pos tp1 hw)), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_zero uF (eq_neg vF (by
        have := mul_pos tp0 (pow_pos sp1 2); linarith))⟩
    · exact ⟨fun _ => lp_pos (eq_pos uG pG), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (eq_neg uH (by
        have := mul_pos kp0 hxh; linarith))⟩
  · have z0 : F.dep ⟨F.S.tp*(1-F.S.sp), 0, ((1-F.S.sp)*(1-F.S.tp)-F.S.kp)⟩ 0 = F.a11*F.S.tp*(F.S.tp*(1-F.S.sp)) + F.gg*(1-F.S.tp)*((1-F.S.sp)*(1-F.S.tp)-F.S.kp) := by
      rw [Frame20.dep_0, hN.2]; ring
    have z1 : F.dep ⟨F.S.tp*(1-F.S.sp), 0, ((1-F.S.sp)*(1-F.S.tp)-F.S.kp)⟩ 1 = F.a11*(F.S.tp*(1-F.S.sp)) := by rw [Frame20.dep_1]; ring
    have z3 : F.dep ⟨F.S.tp*(1-F.S.sp), 0, ((1-F.S.sp)*(1-F.S.tp)-F.S.kp)⟩ 3 = F.a11*F.S.tm*(F.S.tp*(1-F.S.sp)) - F.gg*F.S.tm*((1-F.S.sp)*(1-F.S.tp)-F.S.kp) := by
      rw [Frame20.dep_3, hN.1]; ring
    have z4 : F.dep ⟨F.S.tp*(1-F.S.sp), 0, ((1-F.S.sp)*(1-F.S.tp)-F.S.kp)⟩ 4 = F.a12*F.S.sm*(F.S.tp*(1-F.S.sp)) - F.gg*F.S.km*((1-F.S.sp)*(1-F.S.tp)-F.S.kp) := by
      rw [Frame20.dep_4]; ring
    have z6 : F.dep ⟨F.S.tp*(1-F.S.sp), 0, ((1-F.S.sp)*(1-F.S.tp)-F.S.kp)⟩ 6 = F.a12*(F.S.tp*(1-F.S.sp)) := by rw [Frame20.dep_6]; ring
    refine robUni5_H7 ?_ ?_ ?_ ?_
    · show F.dep _ 6 < F.dep _ 0
      rw [z6, z0]
      have e : F.a11*F.S.tp*(F.S.tp*(1-F.S.sp)) + F.gg*(1-F.S.tp)*((1-F.S.sp)*(1-F.S.tp)-F.S.kp) - F.a12*(F.S.tp*(1-F.S.sp))
          = (F.S.tp*(1-F.S.sp))*(F.a11*F.S.tp-F.a12-F.gg*(1-F.S.tp)) + F.gg*(1-F.S.tp)*(1-F.S.sp-F.S.kp) := by ring
      have : 0 < F.a11*F.S.tp*(F.S.tp*(1-F.S.sp)) + F.gg*(1-F.S.tp)*((1-F.S.sp)*(1-F.S.tp)-F.S.kp) - F.a12*(F.S.tp*(1-F.S.sp)) := by
        rw [e]; exact add_pos_of_nonneg_of_pos (mul_nonneg hxh.le hL) (mul_pos (mul_pos hg tp1) hw)
      linarith
    · show F.dep _ 0 < F.dep _ 1
      rw [z0, z1]
      have e : F.a11*(F.S.tp*(1-F.S.sp)) - (F.a11*F.S.tp*(F.S.tp*(1-F.S.sp)) + F.gg*(1-F.S.tp)*((1-F.S.sp)*(1-F.S.tp)-F.S.kp))
          = (1-F.S.tp)*(F.a11*(F.S.tp*(1-F.S.sp)) - F.gg*((1-F.S.sp)*(1-F.S.tp)-F.S.kp)) := by ring
      rw [← sub_pos, e]
      exact mul_pos tp1 (by have := mul_pos ha hxh; have := mul_nonneg hg.le (neg_nonneg.2 hr); linarith)
    · show F.dep _ 3 < F.dep _ 1
      rw [z3, z1]
      have e : F.a11*(F.S.tp*(1-F.S.sp)) - (F.a11*F.S.tm*(F.S.tp*(1-F.S.sp)) - F.gg*F.S.tm*((1-F.S.sp)*(1-F.S.tp)-F.S.kp))
          = (F.S.tp*(1-F.S.sp))*(F.a11*(1-F.S.tm)-F.gg*F.S.tm) + F.gg*F.S.tm*(1-F.S.sp-F.S.kp) := by ring
      rw [← sub_pos, e]
      exact add_pos_of_nonneg_of_pos (mul_nonneg hxh.le hY) (mul_pos (mul_pos hg tm0) hw)
    · show F.dep _ 4 < F.dep _ 6
      rw [z4, z6]
      have e : F.a12*(F.S.tp*(1-F.S.sp)) - (F.a12*F.S.sm*(F.S.tp*(1-F.S.sp)) - F.gg*F.S.km*((1-F.S.sp)*(1-F.S.tp)-F.S.kp)) = ((1-F.S.sp)*F.S.tp*F.a12*(1-F.S.sm)+F.gg*F.S.km*((1-F.S.sp)*(1-F.S.tp)-F.S.kp)) := by ring
      rw [← sub_pos, e]; exact hK

set_option maxHeartbeats 1000000 in
/-- W: the segment view `x6 - x4` tilted by `(1,0,0)`, cycle `01462`; needs `A2 <= 0`, `Phi > 0`, `Lp >= 0`,
`Kf <= 0` and `P < km`. -/
theorem ia_W (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hN : NF F.S) (hA : (F.S.km*F.S.sp-F.S.kp*(1-F.S.sm)) ≤ 0) (hP : 0 < (F.gg*F.S.km-F.a12*(1-F.S.sm))) (hL : 0 ≤ ((1-F.S.sm)*(F.a22*F.S.sm-F.a12)-F.gg*F.S.km^2)) (hK : ((1-F.S.sp)*F.S.tp*F.a12*(1-F.S.sm)+F.gg*F.S.km*((1-F.S.sp)*(1-F.S.tp)-F.S.kp)) ≤ 0)
    (hkm : 1 - F.S.tp < F.S.km) : IsRupert (univ.image x) := by
  have sm0 := F.S.sm_pos; have sm1 := F.S.sm1; have tm0 := F.S.tm_pos; have tp1 := F.S.tp1
  have tm1 := F.S.tm1; have tp0 := F.S.tp_pos; have kp0 := F.S.kp_pos; have km0 := F.S.km_pos
  have sp0 := F.S.sp_pos; have sp1 := F.S.sp1
  have ha : 0 < F.a12 := F.A12_pos; have hg : 0 < F.gg := F.g_pos
  have h22 : 0 < F.a22 := F.A22_pos
  have rp := roofP_n F.S hN; have rm := rm_pos F.S hN
  have uA : nf F.S ⟨0, 1-F.S.sm, F.S.km⟩ 0 = -(F.S.km*(1-F.S.tm)-F.S.tm*(1-F.S.sm)) := by simp only [nf_A, hN.1]; ring
  have uB : nf F.S ⟨0, 1-F.S.sm, F.S.km⟩ 1 = F.S.tp * (F.S.km*F.S.sp-F.S.kp*(1-F.S.sm)) := by simp only [nf_B, hN.2]; ring
  have uC : nf F.S ⟨0, 1-F.S.sm, F.S.km⟩ 2 = -(F.S.tm*(1-F.S.sm)) := by simp only [nf_C, hN.1, hN.2]; ring
  have uD : nf F.S ⟨0, 1-F.S.sm, F.S.km⟩ 3 = -(F.S.tm*F.S.km) := by simp only [nf_D, hN.1]; ring
  have uE : nf F.S ⟨0, 1-F.S.sm, F.S.km⟩ 4 = (1-F.S.tp)*(1-F.S.sm+F.S.km) := by simp only [nf_E, hN.2]; ring
  have uF : nf F.S ⟨0, 1-F.S.sm, F.S.km⟩ 5 = F.S.tp*(F.S.kp*(1-F.S.sm)+(1-F.S.sp)*F.S.km) := by simp only [nf_F, hN.2]; ring
  have uG : nf F.S ⟨0, 1-F.S.sm, F.S.km⟩ 6 = 0 := by simp only [nf_G]; ring
  have uH : nf F.S ⟨0, 1-F.S.sm, F.S.km⟩ 7 = 0 := by simp only [nf_H]; ring
  have vB : nf F.S ⟨1, 0, 0⟩ 1 = -((1-F.S.tp)*F.S.sp) := by simp only [nf_B, hN.2]; ring
  have vG : nf F.S ⟨1, 0, 0⟩ 6 = F.S.km := by simp only [nf_G]; ring
  have vH : nf F.S ⟨1, 0, 0⟩ 7 = -F.S.kp := by simp only [nf_H]; ring
  refine leaf_of_view F (h20s_fac hR) hx (by norm_num) w_inj w_cyc ⟨0, 1-F.S.sm, F.S.km⟩ ⟨1, 0, 0⟩ 4
    (eq_pos uE (by positivity)).ne' ?_ ?_
  · intro t; fin_cases t
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (eq_neg uA (by linarith))⟩
    · refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
      rcases hA.lt_or_eq with h | h
      · exact lpn_pos (eq_neg uB (mul_neg_of_pos_of_neg tp0 h))
      · exact lpn_zero (uB.trans (by rw [h]; ring)) (eq_neg vB (by have := mul_pos tp1 sp0; linarith))
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (eq_neg uC (by have := mul_pos tm0 sm1; linarith))⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (eq_neg uD (by have := mul_pos tm0 km0; linarith))⟩
    · exact ⟨fun _ => lp_pos (eq_pos uE (by positivity)), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp_pos (eq_pos uF (by positivity)), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp_zero uG (eq_pos vG km0), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_zero uH (eq_neg vH (by linarith))⟩
  · have z0 : F.dep ⟨0, 1-F.S.sm, F.S.km⟩ 0 = F.a12*(1-F.S.sm)*F.S.tp + F.gg*F.S.km*(1-F.S.tp) := by
      rw [Frame20.dep_0, hN.2]; ring
    have z1 : F.dep ⟨0, 1-F.S.sm, F.S.km⟩ 1 = F.a12*(1-F.S.sm) := by rw [Frame20.dep_1]; ring
    have z2 : F.dep ⟨0, 1-F.S.sm, F.S.km⟩ 2 = F.a22*(1-F.S.sm)*F.S.sp + F.gg*F.S.km*F.S.kp := by rw [Frame20.dep_2]; ring
    have z4 : F.dep ⟨0, 1-F.S.sm, F.S.km⟩ 4 = F.a22*F.S.sm*(1-F.S.sm) - F.gg*F.S.km^2 := by rw [Frame20.dep_4]; ring
    have z6 : F.dep ⟨0, 1-F.S.sm, F.S.km⟩ 6 = F.a22*(1-F.S.sm) := by rw [Frame20.dep_6]; ring
    have hT : ((1-F.S.sm)*(F.S.tp*F.a12-F.a22)+F.gg*F.S.km*(1-F.S.tp)) < 0 := by
      have e : ((1-F.S.sm)*(F.a22*F.S.sm-F.a12)-F.gg*F.S.km^2) + F.S.sm*((1-F.S.sm)*(F.S.tp*F.a12-F.a22)+F.gg*F.S.km*(1-F.S.tp)) = -(1-F.S.sm)*(1-F.S.sm*F.S.tp)*F.a12 + F.gg*F.S.km*(F.S.sm*(1-F.S.tp)-F.S.km) := by ring
      have h1 : 0 < (1-F.S.sm)*(1-F.S.sm*F.S.tp)*F.a12 := by
        have : 0 < 1 - F.S.sm*F.S.tp := by nlinarith [mul_pos sm0 tp0]
        positivity
      have h2 : F.S.sm*(1-F.S.tp) - F.S.km < 0 := by nlinarith [mul_pos sm0 km0]
      have h3 : F.gg*F.S.km*(F.S.sm*(1-F.S.tp)-F.S.km) < 0 := mul_neg_of_pos_of_neg (mul_pos hg km0) h2
      have h4 : F.S.sm*((1-F.S.sm)*(F.S.tp*F.a12-F.a22)+F.gg*F.S.km*(1-F.S.tp)) < 0 := by linarith
      by_contra hc
      push Not at hc
      have := mul_nonneg sm0.le hc
      linarith
    refine robUni5_H8 ?_ ?_ ?_
    · show F.dep _ 1 < F.dep _ 0
      rw [z1, z0]
      have e : F.a12*(1-F.S.sm)*F.S.tp + F.gg*F.S.km*(1-F.S.tp) - F.a12*(1-F.S.sm) = (1-F.S.tp)*(F.gg*F.S.km-F.a12*(1-F.S.sm)) := by ring
      have := mul_pos tp1 hP
      linarith
    · show F.dep _ 4 < F.dep _ 6
      rw [z4, z6]
      have e : F.a22*(1-F.S.sm) - (F.a22*F.S.sm*(1-F.S.sm) - F.gg*F.S.km^2) = F.a22*(1-F.S.sm)^2 + F.gg*F.S.km^2 := by ring
      have := mul_pos h22 (pow_pos sm1 2); have := mul_pos hg (pow_pos km0 2)
      linarith
    · show F.dep _ 0 < F.dep _ 2
      rw [z0, z2]
      have e : F.a22*(1-F.S.sm)*F.S.sp + F.gg*F.S.km*F.S.kp - (F.a12*(1-F.S.sm)*F.S.tp + F.gg*F.S.km*(1-F.S.tp)) = -F.S.sp*((1-F.S.sm)*(F.S.tp*F.a12-F.a22)+F.gg*F.S.km*(1-F.S.tp)) - ((1-F.S.sp)*F.S.tp*F.a12*(1-F.S.sm)+F.gg*F.S.km*((1-F.S.sp)*(1-F.S.tp)-F.S.kp)) := by ring
      have := mul_pos sp0 (neg_pos.2 hT)
      linarith

end IAT
end Minimality.CaseC20

end

section


/-!
# I_A: the case tree on the normal form, and the theorems `Frame20.isRupert_IA`, `isRupert_IA_R`
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace IAT
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

set_option maxHeartbeats 2000000 in
/-- **The cover on the normal form** (`hm = tm`, `hp = 1 - tp`): Rupert for every metric of the closed cone. -/
theorem tree (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19)) (hN : NF F.S) :
    IsRupert (Finset.univ.image x) := by
  have sm0 := F.S.sm_pos; have sm1 := F.S.sm1; have tm0 := F.S.tm_pos; have tp1 := F.S.tp1
  have tm1 := F.S.tm1; have tp0 := F.S.tp_pos; have km0 := F.S.km_pos
  have ha : 0 < F.a12 := F.A12_pos; have hg : 0 < F.gg := F.g_pos
  have h22 : F.a12 ≤ F.a22 := F.A12_le_A22
  by_cases hPhi : (F.gg*F.S.km-F.a12*(1-F.S.sm)) < 0
  · exact ia_K F hx hR hN hPhi
  push Not at hPhi
  by_cases hk : F.S.sm < F.S.km
  · by_cases hc : F.a12 < F.a22
    · exact ia_S45 F hx hR hN hk hc
    · have hcb : F.a22 = F.a12 := le_antisymm (not_lt.1 hc) h22
      have hL : ((1-F.S.sm)*(F.a22*F.S.sm-F.a12)-F.gg*F.S.km^2) < 0 := by
        have e : ((1-F.S.sm)*(F.a22*F.S.sm-F.a12)-F.gg*F.S.km^2) = -(1-F.S.sm)^2*F.a12 - F.gg*F.S.km^2 := by rw [hcb]; ring
        rw [e]
        have := mul_pos (pow_pos sm1 2) ha; have := mul_pos hg (pow_pos km0 2)
        linarith
      by_cases hA : 0 < (F.S.km*F.S.sp-F.S.kp*(1-F.S.sm))
      · exact ia_C2a F hx hR hN hA hL
      · exact ia_C2b F hx hR hN (not_lt.1 hA) hL (hPhi.lt_or_eq.imp id (fun h => ⟨h.symm, hcb⟩))
  push Not at hk
  by_cases hph : 0 < (F.a12*(1-F.S.tm)-F.gg*F.S.tm)
  · exact ia_E1 F hx hR hN hk hph
  push Not at hph
  have hP := S1 F hN hph
  by_cases hL : ((1-F.S.sm)*(F.a22*F.S.sm-F.a12)-F.gg*F.S.km^2) < 0
  · by_cases hA : 0 < (F.S.km*F.S.sp-F.S.kp*(1-F.S.sm))
    · exact ia_C2a F hx hR hN hA hL
    · exact ia_C2b F hx hR hN (not_lt.1 hA) hL (Or.inl hP)
  push Not at hL
  by_cases h56 : 0 < (F.S.km*(1-F.S.tm)-F.S.tm)
  · exact ia_S56 F hx hR hN h56 hL
  push Not at h56
  by_cases hYZ : (F.a11*(1-F.S.tm)-F.gg*F.S.tm) < 0 ∨ (F.a12*F.S.sm+F.gg*(F.S.km-F.S.tm)-F.a11*F.S.tm) < 0
  · exact ia_U2 F hx hR hN hP hYZ
  push Not at hYZ
  obtain ⟨hY, hZ⟩ := hYZ
  have eX : ((1-F.S.tm)*F.S.sm*F.a12+F.gg*(F.S.km*(1-F.S.tm)-F.S.tm)) = F.S.tm*(F.a11*(1-F.S.tm)-F.gg*F.S.tm) + (1-F.S.tm)*(F.a12*F.S.sm+F.gg*(F.S.km-F.S.tm)-F.a11*F.S.tm) := by ring
  have hX : 0 ≤ ((1-F.S.tm)*F.S.sm*F.a12+F.gg*(F.S.km*(1-F.S.tm)-F.S.tm)) := by rw [eX]; exact add_nonneg (mul_nonneg tm0.le hY) (mul_nonneg tm1.le hZ)
  rcases hX.lt_or_eq with hX | hX
  · by_cases h25 : (F.S.sp*(F.S.tm-F.S.km*(1-F.S.tm))-F.S.kp*F.S.sm*(1-F.S.tm)) < 0
    · exact ia_LAHa F hx hR hN hL h56 hX h25
    · exact ia_LAHb F hx hR hN hL h56 hX (not_lt.1 h25)
  · -- the corner `z1 = z3 = z4` at `u0`
    have hX' : ((1-F.S.tm)*F.S.sm*F.a12+F.gg*(F.S.km*(1-F.S.tm)-F.S.tm)) = 0 := hX.symm
    have hY0 : (F.a11*(1-F.S.tm)-F.gg*F.S.tm) = 0 := by
      have h1 := mul_nonneg tm0.le hY; have h2 := mul_nonneg tm1.le hZ
      have : F.S.tm*(F.a11*(1-F.S.tm)-F.gg*F.S.tm) = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left tm0.ne'
    have hZ0 : (F.a12*F.S.sm+F.gg*(F.S.km-F.S.tm)-F.a11*F.S.tm) = 0 := by
      have h1 := mul_nonneg tm0.le hY; have h2 := mul_nonneg tm1.le hZ
      have : (1-F.S.tm)*(F.a12*F.S.sm+F.gg*(F.S.km-F.S.tm)-F.a11*F.S.tm) = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left tm1.ne'
    by_cases hLq : (F.a11*F.S.tp-F.a12-F.gg*(1-F.S.tp)) < 0
    · exact ia_U1 F hx hR hN hk hP hLq
    push Not at hLq
    have h06 := S4 F hN hY0 hZ0 hLq
    obtain ⟨hkP, -, hB, hA14⟩ := S3 F hN h56 h06
    by_cases hA : 0 < (F.S.km*F.S.sp-F.S.kp*(1-F.S.sm))
    · exact ia_C6 F hx hR hN hA hL hB hA14
    · push Not at hA
      by_cases hKf : 0 < ((1-F.S.sp)*F.S.tp*F.a12*(1-F.S.sm)+F.gg*F.S.km*((1-F.S.sp)*(1-F.S.tp)-F.S.kp))
      · by_cases hr : 0 < ((1-F.S.sp)*(1-F.S.tp)-F.S.kp)
        · refine ia_S15 F hx hR hN hr ?_
          have := mul_pos hg tp1
          linarith
        · exact ia_LCF F hx hR hN (not_lt.1 hr) hKf hY hLq
      · exact ia_W F hx hR hN hA hP hL (not_lt.1 hKf) hkP

end IAT

namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- **Type 20, item I_A** (line 273 of `CaseC20Face.lean`, copied verbatim): on `A1 = 0` the point set is Rupert
for every metric of the closed cone `a12 <= a11`, `a12 <= a22`. -/
theorem isRupert_IA (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hA : F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm = 0) : IsRupert (Finset.univ.image x) := by
  obtain ⟨F', -, -, hN, -⟩ := F.exists_normal hA
  exact IAT.tree F' hx hR hN

/-- **The `R`-image of I_A** (line 274 of `CaseC20Face.lean`, copied verbatim). -/
theorem isRupert_IA_R (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hA : F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp = 0) : IsRupert (Finset.univ.image x) := by
  refine rupert_of_r (F.rFrame.isRupert_IA (hx.comp rperm_bijective.1) (realizesFaces_rperm hR) ?_)
  simp only [rFrame_S, Shape20.swap]; linear_combination hA

end Frame20
end Minimality.CaseC20

end

section

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20

/-- Every disjunct of `CaseC20Rest2` is Rupert: the codimension-2 face residuals `m1'`, `m2'`
(`isRupert_m1'`, `isRupert_m2'`), the lines 273, 274 (`isRupert_IA`, `isRupert_IA_R`) and 283, 286
(`isRupert_IQ_R`, `isRupert_IQ`). -/
theorem caseC20Rest2_isRupert {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (hR : RealizesFaces x (sevenTypeFaces 19)) (h : CaseC20Rest2 x) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨F, h⟩ := h
  rcases h with h | h | h | h | h | h
  · exact F.isRupert_m1' hx hR h.1 h.2.1 h.2.2.1 h.2.2.2
  · exact F.isRupert_m2' hx hR h.1 h.2.1 h.2.2.1 h.2.2.2
  · exact F.isRupert_IA hx hR h
  · exact F.isRupert_IA_R hx hR h
  · exact F.isRupert_IQ_R hx hR h
  · exact F.isRupert_IQ hx hR h

/-- **The type 20 special positions are Rupert**: `CaseC20Special''` reduces to `CaseC20Rest`
(`caseC20Special''_reduce`), then to `CaseC20Rest2` (`caseC20Rest_reduce`), which is Rupert. -/
theorem caseC20Special''_isRupert {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (hR : RealizesFaces x (sevenTypeFaces 19)) (h : CaseC20Special'' x) :
    IsRupert (Finset.univ.image x) := by
  rcases caseC20Special''_reduce hx hR h with h | h
  · exact h
  rcases caseC20Rest_reduce hx hR h with h | h
  · exact h
  exact caseC20Rest2_isRupert hx hR h

end Minimality.CaseC20

end

#print axioms Minimality.CaseC20.caseC20Special''_isRupert
