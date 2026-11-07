module

public import Minimality.Type20IMCB

@[expose] public section

/-!
# Type 20, item I_MC (part C): the tilted and special-position leaves, and the dispatcher

Leaves of I_MC with an equation on the shape or a tilted view: L3 (`A = 0`), L8 (`Q = 0`), L9'
(`lam = 0`), L11 and L12 (the stratum `Vq = 0`).  Then the case tree `imc_main` of the covering notes,
which leaves the corner `A = K = 0` (`CornerStmt`) and the tie leaf (`ZtStmt`) as hypotheses.
-/

section

/-!
# Type 20, I_MC, leaf L3: `A = 0`, `Q < 0` (view `x1 - x0`, cycle `0,5,3,4,6`, tilt)
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace IMCT

/-- Pattern of `s01:05346`: up `A C E G`, down `B D F H`. -/
def pat3 : Fin 8 → Bool := ![true, false, true, false, true, false, true, false]

/-- The cycle `0,5,3,4,6`. -/
def cyc3 : ZMod 5 → Fin 7 := ![0, 5, 3, 4, 6]

theorem cyc3_ok : S0xCycOK h20s_S cyc3 pat3 := by decide

theorem cyc3_inj : Function.Injective cyc3 := by decide

variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- **L3**: on I_MC with `A = 0` and `Q < 0`, the point set is Rupert (the segment view `x1 - x0`
with facet `D` edge-on, resolved by the tilt `(0, -hm sm (1-tp), hp (hm sm + km tm))`). -/
theorem imc_L3 (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hE1 : (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 +
      (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg = 0)
    (hE2 : (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) +
      (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg = 0)
    (hA : Aq F.S = 0) (hQ : Qq F.S < 0) :
    IsRupert (univ.image x) := by
  set FF := h20s_fac hR with hFF
  have tp0 := F.S.tp_pos; have tp1 := F.S.tp_lt; have tm0 := F.S.tm_pos; have tm1 := F.S.tm_lt
  have sp0 := F.S.sp_pos; have sp1 := F.S.sp_lt; have sm0 := F.S.sm_pos; have sm1 := F.S.sm_lt
  have hp0 := F.S.hp_pos; have hm0 := F.S.hm_pos; have kp0 := F.S.kp_pos; have km0 := F.S.km_pos
  have hg := F.g_pos
  have t1 : 0 < 1 - F.S.tp := by linarith
  have t4 : 0 < 1 - F.S.tm := by linarith
  have rp := F.S.roof_p'
  have rm := F.S.roof_m'
  have m1 := imc_M1 F hE2
  have m2 := imc_M2 F hE1
  have hden := imc_den_pos F hE1
  set qu : C3 := ⟨1 - F.S.tp, 0, -F.S.hp⟩ with hqu
  set qv : C3 := ⟨0, -(F.S.hm*F.S.sm*(1-F.S.tp)), F.S.hp*(F.S.hm*F.S.sm + F.S.km*F.S.tm)⟩ with hqv
  have hA' : F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm = 0 := hA
  have uA : nf F.S qu 0 = F.S.sm * (F.S.hm*(1-F.S.tp) + F.S.hp*(1-F.S.tm)) := by
    rw [nf_A]; simp only [hqu]; ring
  have uB : nf F.S qu 1 = -(F.S.hp*F.S.sp) := by rw [nf_B]; simp only [hqu]; ring
  have uC : nf F.S qu 2 = 0 := by rw [nf_C]; simp only [hqu]; ring
  have uD : nf F.S qu 3 = F.S.sm * Aq F.S := by rw [nf_D]; simp only [hqu, Aq]; ring
  have uE : nf F.S qu 4 = 0 := by rw [nf_E]; simp only [hqu]; ring
  have uF : nf F.S qu 5 = -(F.S.hp*(1-F.S.sp) - F.S.kp*(1-F.S.tp)) := by
    rw [nf_F]; simp only [hqu]; ring
  have uG : nf F.S qu 6 = F.S.km*(1-F.S.tp) + F.S.hp*(1-F.S.sm) := by
    rw [nf_G]; simp only [hqu]; ring
  have uH : nf F.S qu 7 = -(F.S.kp*(1-F.S.tp)) := by rw [nf_H]; simp only [hqu]; ring
  have vC : nf F.S qv 2 = c0 F.S * (F.S.hm*F.S.sm*(1-F.S.tp)) := by
    rw [nf_C]; simp only [hqv, c0]; ring
  have vD : nf F.S qv 3 = -(F.S.hm^2*F.S.sm^2*(1-F.S.tp)) - F.S.sm*(F.S.hm*F.S.sm + F.S.km*F.S.tm) * Aq F.S := by
    rw [nf_D]; simp only [hqv, Aq]; ring
  have vE : nf F.S qv 4 = F.S.hp * F.S.km * F.S.tm * (1-F.S.tp) := by
    rw [nf_E]; simp only [hqv]; ring
  -- depths at the view `x1 - x0`, scaled by `1 - tm`
  have d0 : (1-F.S.tm) * F.dep qu 0 = F.S.hp * F.gg * E0 F.S := by
    rw [F.dep_0]; simp only [hqu, E0]; linear_combination F.S.tp * m1
  have d3 : (1-F.S.tm) * F.dep qu 3 = F.S.hp * F.gg * F.S.hm := by
    rw [F.dep_3]; simp only [hqu]; linear_combination F.S.tm * m1
  have d4 : (1-F.S.tm) * F.dep qu 4 = F.S.hp * F.gg * F.S.hm := by
    rw [F.dep_4]; simp only [hqu]; linear_combination m2
  have d6 : F.S.sm * (1-F.S.tm) * F.dep qu 6 = F.S.hp * F.gg * den F.S := by
    rw [F.dep_6]; simp only [hqu, den]; linear_combination m2
  have hgp : 0 < F.S.hp * F.gg := mul_pos hp0 hg
  have h1 : 0 < F.dep qu 3 := by
    have : 0 < (1-F.S.tm) * F.dep qu 3 := by rw [d3]; positivity
    exact pos_of_mul_pos_right this t4.le
  have h34 : F.dep qu 3 = F.dep qu 4 := by
    have : (1-F.S.tm) * F.dep qu 3 = (1-F.S.tm) * F.dep qu 4 := by rw [d3, d4]
    exact mul_left_cancel₀ t4.ne' this
  have h06 : F.dep qu 0 < F.dep qu 6 := by
    have hs : 0 < F.S.sm * (1-F.S.tm) := mul_pos sm0 t4
    have e0 : F.S.sm * (1-F.S.tm) * F.dep qu 0 = F.S.hp * F.gg * (F.S.sm * E0 F.S) := by
      linear_combination F.S.sm * d0
    have : F.S.sm * (1-F.S.tm) * F.dep qu 0 < F.S.sm * (1-F.S.tm) * F.dep qu 6 := by
      rw [e0, d6]
      have : F.S.sm * E0 F.S < den F.S := by
        unfold Qq at hQ; unfold E0 den; linarith
      exact mul_lt_mul_of_pos_left this hgp
    exact lt_of_mul_lt_mul_left this hs.le
  have h64 : F.dep qu 6 < F.dep qu 4 := by
    have hs : 0 < F.S.sm * (1-F.S.tm) := mul_pos sm0 t4
    have e4 : F.S.sm * (1-F.S.tm) * F.dep qu 4 = F.S.hp * F.gg * (F.S.sm * F.S.hm) := by
      linear_combination F.S.sm * d4
    have : F.S.sm * (1-F.S.tm) * F.dep qu 6 < F.S.sm * (1-F.S.tm) * F.dep qu 4 := by
      rw [e4, d6]
      have : den F.S < F.S.sm * F.S.hm := by unfold den; linarith
      exact mul_lt_mul_of_pos_left this hgp
    exact lt_of_mul_lt_mul_left this hs.le
  have hU : RobUni (fun a : ZMod 5 => F.dep qu (cyc3 a)) := by
    refine robUni5_t ?_ ?_ ?_ ?_
    · show F.dep qu 0 < F.dep qu 6
      exact h06
    · show F.dep qu 6 < F.dep qu 4
      exact h64
    · show F.dep qu 3 = F.dep qu 4
      exact h34
    · show F.dep qu 5 < F.dep qu 3
      rw [F.dep_5]; exact h1
  refine leaf_of_view F FF hx (by norm_num) cyc3_inj cyc3_ok qu qv 0 ?_ ?_ hU
  · rw [uA]; positivity
  · intro t
    have ht : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 := by
      revert t; decide
    have c0p : 0 < c0 F.S := by unfold c0; positivity
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨fun _ => Or.inl (by rw [uA]; positivity), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => Or.inl (by rw [uB]; linarith [mul_pos hp0 sp0])⟩
    · exact ⟨fun _ => Or.inr ⟨uC, by rw [vC]; positivity⟩, fun h => absurd h (by decide)⟩
    · refine ⟨fun h => absurd h (by decide), fun _ => Or.inr ⟨?_, ?_⟩⟩
      · rw [uD, hA]; ring
      · rw [vD, hA]
        have : 0 < F.S.hm^2*F.S.sm^2*(1-F.S.tp) := by positivity
        linarith
    · exact ⟨fun _ => Or.inr ⟨uE, by rw [vE]; positivity⟩, fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => Or.inl (by rw [uF]; linarith)⟩
    · exact ⟨fun _ => Or.inl (by rw [uG]; positivity), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => Or.inl (by rw [uH]; linarith [mul_pos kp0 t1])⟩

end IMCT
end Minimality.CaseC20

end

section

/-!
# Type 20, I_MC, leaf L8: `Q = 0`, `A > 0`, `VM > 0` (view `x0 - x6`, cycle `0,1,3,5,2`, tilt `x5 - x0`)
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace IMCT

/-- Pattern of `LAF`: up `B C`, down `A D E F G H`. -/
def pat8 : Fin 8 → Bool := ![false, true, true, false, false, false, false, false]

/-- The cycle `0,1,3,5,2` (boundary of `B ∪ C`). -/
def cyc8 : ZMod 5 → Fin 7 := ![0, 1, 3, 5, 2]

theorem cyc8_ok : S0xCycOK h20s_S cyc8 pat8 := by decide

theorem cyc8_inj : Function.Injective cyc8 := by decide

/-- The identity `R1 * P1 + hm * VM = - Vq * Q`. -/
lemma id_R1P1 (S : Shape20) :
    ((1-S.sp)*E0 S + (1-S.tm)*S.kp) * P1 S + S.hm * VM S = -(Vq S * Qq S) := by
  unfold E0 P1 VM Vq Mq Qq; ring

variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- **L8**: on I_MC with `Q = 0`, `A > 0`, `VM > 0` the point set is Rupert (the view `x0 - x6`
with the facets `A`, `E`, `F` edge-on, resolved by the tilt `x5 - x0`). -/
theorem imc_L8 (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hE1 : (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 +
      (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg = 0)
    (hE2 : (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) +
      (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg = 0)
    (hQ : Qq F.S = 0) (hA : 0 < Aq F.S) (hVM : 0 < VM F.S) :
    IsRupert (univ.image x) := by
  set FF := h20s_fac hR with hFF
  have tp0 := F.S.tp_pos; have tp1 := F.S.tp_lt; have tm0 := F.S.tm_pos; have tm1 := F.S.tm_lt
  have sp0 := F.S.sp_pos; have sp1 := F.S.sp_lt; have sm0 := F.S.sm_pos; have sm1 := F.S.sm_lt
  have hp0 := F.S.hp_pos; have hm0 := F.S.hm_pos; have kp0 := F.S.kp_pos; have km0 := F.S.km_pos
  have hg := F.g_pos
  have t1 : 0 < 1 - F.S.tp := by linarith
  have t4 : 0 < 1 - F.S.tm := by linarith
  have t3 : 0 < 1 - F.S.sp := by linarith
  have t2 : 0 < 1 - F.S.sm := by linarith
  have rp := F.S.roof_p'
  have m1 := imc_M1 F hE2
  have m2 := imc_M2 F hE1
  have hden := imc_den_pos F hE1
  have hQr : F.S.km*(1-F.S.tm) - F.S.hm*(1 - F.S.sm*F.S.tp) - F.S.hp*F.S.sm*(1-F.S.tm) = 0 := hQ
  have hE0 : F.S.sm * E0 F.S = den F.S := by unfold E0 den; linarith
  have E0p : 0 < E0 F.S := by
    have : 0 < F.S.sm * E0 F.S := by rw [hE0]; exact hden
    exact pos_of_mul_pos_right this sm0.le
  have c0p : 0 < c0 F.S := by unfold c0; positivity
  set qu : C3 := ⟨F.S.tp, -1, F.S.hp⟩ with hqu
  set qv : C3 := ⟨-F.S.tp, 0, -F.S.hp⟩ with hqv
  have uA : nf F.S qu 0 = Qq F.S := by rw [nf_A]; simp only [hqu, Qq]; ring
  have uB : nf F.S qu 1 = F.S.kp * F.S.tp := by rw [nf_B]; simp only [hqu]; ring
  have uC : nf F.S qu 2 = c0 F.S := by rw [nf_C]; simp only [hqu, c0]; ring
  have uD : nf F.S qu 3 = P1 F.S := by rw [nf_D]; simp only [hqu, P1]; ring
  have uE : nf F.S qu 4 = 0 := by rw [nf_E]; simp only [hqu]; ring
  have uF : nf F.S qu 5 = 0 := by rw [nf_F]; simp only [hqu]; ring
  have uG : nf F.S qu 6 = -(F.S.km*(1-F.S.tp) + F.S.hp*(1-F.S.sm)) := by
    rw [nf_G]; simp only [hqu]; ring
  have uH : nf F.S qu 7 = -(F.S.kp * F.S.tp) := by rw [nf_H]; simp only [hqu]; ring
  have vA : nf F.S qv 0 = -(F.S.sm * E0 F.S) := by rw [nf_A]; simp only [hqv, E0]; ring
  have vE : nf F.S qv 4 = -F.S.hp := by rw [nf_E]; simp only [hqv]; ring
  have vF : nf F.S qv 5 = -(F.S.tp * F.S.kp) := by rw [nf_F]; simp only [hqv]; ring
  -- P1 < 0
  have hR1 : 0 < (1-F.S.sp) * E0 F.S + (1-F.S.tm) * F.S.kp := by positivity
  have hP1 : P1 F.S < 0 := by
    have h := id_R1P1 F.S
    rw [hQ, mul_zero, neg_zero] at h
    have h2 : ((1-F.S.sp) * E0 F.S + (1-F.S.tm) * F.S.kp) * P1 F.S < 0 := by
      have := mul_pos hm0 hVM
      linarith only [h, this]
    exact neg_of_mul_neg_right h2 hR1.le
  -- depths
  have hQ' : F.S.hm*F.S.sm*F.S.tp - den F.S - F.S.sm*F.S.hp*(1-F.S.tm) = 0 := by
    unfold den; linarith
  have f1 : (1-F.S.tp) * F.dep qu 1 = F.gg * F.S.hp^2 := by
    have : F.S.sm*(1-F.S.tm) * ((1-F.S.tp) * F.dep qu 1) = F.S.sm*(1-F.S.tm) * (F.gg * F.S.hp^2) := by
      rw [F.dep_1]; simp only [hqu, den] at hQ' ⊢
      linear_combination (F.S.sm*F.S.tp) * m1 - m2 + (F.S.hp*F.gg) * hQ'
    exact mul_left_cancel₀ (mul_pos sm0 t4).ne' this
  have f0 : F.dep qu 0 = F.dep qu 1 := by
    rw [F.dep_0, F.dep_1]; simp only [hqu]
    rw [F.dep_1] at f1; simp only [hqu] at f1
    linear_combination (-1) * f1
  have f3 : (1-F.S.tp) * F.dep qu 3 = F.gg * F.S.hp * Aq F.S := by
    rw [F.dep_3]; rw [F.dep_1] at f1; simp only [hqu, Aq] at f1 ⊢
    linear_combination F.S.tm * f1
  have z31 : F.dep qu 3 < F.dep qu 1 := by
    have : (1-F.S.tp) * F.dep qu 3 < (1-F.S.tp) * F.dep qu 1 := by
      rw [f3, f1]
      unfold Aq
      have : 0 < F.gg * F.S.hp * (F.S.hp * (1 - F.S.tm) + F.S.hm * (1 - F.S.tp)) := by positivity
      linarith only [this]
    exact lt_of_mul_lt_mul_left this t1.le
  have z53 : F.dep qu 5 < F.dep qu 3 := by
    rw [F.dep_5]
    have : 0 < (1-F.S.tp) * F.dep qu 3 := by rw [f3]; positivity
    exact pos_of_mul_pos_right this t1.le
  have z21 : F.dep qu 2 < F.dep qu 1 := by
    have hL : 0 < F.S.sm * (1-F.S.tm) * (F.S.hp*(1-F.S.sp) - F.S.kp*(1-F.S.tp)) +
        F.S.sp * (den F.S * (1-F.S.tp) + F.S.sm * F.S.hp * (1-F.S.tm)) := by
      have h1 : 0 < F.S.hp*(1-F.S.sp) - F.S.kp*(1-F.S.tp) := by linarith
      have h2 : 0 < F.S.sm * F.S.hp * (1-F.S.tm) := by positivity
      exact add_pos (mul_pos (mul_pos sm0 t4) h1) (mul_pos sp0 (add_pos (mul_pos hden t1) h2))
    have hd := F.A12_le_A22
    have hd' : 0 ≤ F.a22 - F.a12 := sub_nonneg.2 hd
    have key : F.S.sm*((1-F.S.tm)*(1-F.S.tp)) * (F.dep qu 1 - F.dep qu 2) =
        F.S.hp * F.gg * (F.S.sm * (1-F.S.tm) * (F.S.hp*(1-F.S.sp) - F.S.kp*(1-F.S.tp)) +
          F.S.sp * (den F.S * (1-F.S.tp) + F.S.sm * F.S.hp * (1-F.S.tm))) +
        F.S.sm*((1-F.S.tm)*(1-F.S.tp)) * F.S.sp * (F.a22 - F.a12) := by
      rw [F.dep_1, F.dep_2]; simp only [hqu, den] at hQ' ⊢
      linear_combination (F.S.sm*F.S.tp) * m1 - (1 - F.S.sp + F.S.sp*F.S.tp) * m2 + (F.S.hp*F.gg) * hQ'
    have hpos : 0 < F.S.sm*((1-F.S.tm)*(1-F.S.tp)) := by positivity
    have : 0 < F.S.sm*((1-F.S.tm)*(1-F.S.tp)) * (F.dep qu 1 - F.dep qu 2) := by
      rw [key]
      have := mul_pos (mul_pos hp0 hg) hL
      have := mul_nonneg (mul_nonneg hpos.le sp0.le) hd'
      linarith
    have := pos_of_mul_pos_right this hpos.le
    linarith
  have hU : RobUni (fun a : ZMod 5 => F.dep qu (cyc8 a)) := by
    refine robUni5_u ?_ ?_ ?_ ?_
    · show F.dep qu 0 = F.dep qu 1
      exact f0
    · show F.dep qu 3 < F.dep qu 1
      exact z31
    · show F.dep qu 5 < F.dep qu 3
      exact z53
    · show F.dep qu 2 < F.dep qu 1
      exact z21
  refine leaf_of_view F FF hx (by norm_num) cyc8_inj cyc8_ok qu qv 1 ?_ ?_ hU
  · rw [uB]; positivity
  · intro t
    have ht : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 := by
      revert t; decide
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨fun h => absurd h (by decide), fun _ => Or.inr ⟨?_, ?_⟩⟩
      · rw [uA, hQ]; ring
      · rw [vA]; have := mul_pos sm0 E0p; linarith
    · exact ⟨fun _ => Or.inl (by rw [uB]; positivity), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => Or.inl (by rw [uC]; exact c0p), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => Or.inl (by rw [uD]; linarith)⟩
    · refine ⟨fun h => absurd h (by decide), fun _ => Or.inr ⟨?_, ?_⟩⟩
      · rw [uE]; ring
      · rw [vE]; linarith
    · refine ⟨fun h => absurd h (by decide), fun _ => Or.inr ⟨?_, ?_⟩⟩
      · rw [uF]; ring
      · rw [vF]; have := mul_pos tp0 kp0; linarith
    · have hg6 : 0 < F.S.km*(1-F.S.tp) + F.S.hp*(1-F.S.sm) := by positivity
      exact ⟨fun h => absurd h (by decide), fun _ => Or.inl (by rw [uG]; linarith)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => Or.inl (by rw [uH]; have := mul_pos kp0 tp0; linarith)⟩

end IMCT
end Minimality.CaseC20

end

section

/-!
# Type 20, I_MC, leaf L9' (special position of L9: `lam = 0` and the depth `w2` is zero)

The view of `LBD:2546` is the common line of `B` and `D`; at `lam = 0, w2 = 0` the depths of the
silhouette `2,5,4,6` are all equal (to 0), so that view is not robustly unimodal.  We move the view
by `eps` in the `-y` frame direction: then `B` and `D` face up strictly, the other facets keep their
facing, and the depths become `(sp w, 0, sm w, w)` with `w = -a22 eps < 0`.
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace IMCT

/-- A small positive `eps` with `eps * b < X` is available for each of finitely many pairs. -/
lemma eps_aux {X b e : ℝ} (hX : 0 < X) (hb : 0 < b) (he : e ≤ X / (2 * b)) : e * b < X := by
  have h1 := mul_le_mul_of_nonneg_right he hb.le
  have h2 : X / (2 * b) * b = X / 2 := by field_simp
  linarith

/-- The facing pattern of `LBD:2546`: `A..G` up, `H` down. -/
def pat9 : Fin 8 → Bool := ![true, true, true, true, true, true, true, false]

/-- The silhouette cycle `2,5,4,6` (the boundary of `H`). -/
def cyc9 : ZMod 4 → Fin 7 := ![2, 5, 4, 6]

theorem cyc9_ok : S0xCycOK h20s_S cyc9 pat9 := by decide

theorem cyc9_inj : Function.Injective cyc9 := by decide

variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- **L9'**: in the special position `lam = 0` with `a12 ux + a22 uy = 0` (the depth of `x6` at the
line view of `B`, `D` vanishes), given the strict facings `LA, LE, LF, LG > 0` of the other facets,
the point set is Rupert; the view is moved off the line of `B`, `D` by a small `eps`. -/
theorem imc_L9p (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hE1 : (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 +
      (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg = 0)
    (hLA : 0 < LA F.S) (hLE : 0 < LE F.S) (hLF : 0 < LF F.S) (hLG : 0 < LG F.S)
    (hlam : lam F.S = 0)
    (hw : F.a12 * (F.S.tm*F.S.tp*kap F.S) - F.a22 * (F.S.sm*F.S.sp*c0 F.S) = 0) :
    IsRupert (univ.image x) := by
  set FF := h20s_fac hR with hFF
  have hden : 0 < den F.S := imc_den_pos F hE1
  have tp0 := F.S.tp_pos; have tp1 := F.S.tp_lt; have tm0 := F.S.tm_pos; have tm1 := F.S.tm_lt
  have sp0 := F.S.sp_pos; have sp1 := F.S.sp_lt; have sm0 := F.S.sm_pos; have sm1 := F.S.sm_lt
  have hp0 := F.S.hp_pos; have hm0 := F.S.hm_pos; have kp0 := F.S.kp_pos; have km0 := F.S.km_pos
  have hc0 : 0 < c0 F.S := by unfold c0; positivity
  have hkap : 0 < kap F.S := by unfold kap; positivity
  have ha22 : 0 < F.a22 := F.A22_pos
  obtain ⟨eps, he0, h1, h2, h3, h4⟩ : ∃ eps : ℝ, 0 < eps ∧ eps * den F.S < F.S.hm * F.S.sm * LA F.S ∧
      eps * F.S.hp < LE F.S ∧ eps < LF F.S ∧ eps * F.S.km < LG F.S := by
    have p1 : 0 < F.S.hm * F.S.sm * LA F.S := by positivity
    have q1 : 0 < LE F.S / (2 * F.S.hp) := by positivity
    have q2 : 0 < LF F.S / 2 := by positivity
    have q3 : 0 < LG F.S / (2 * F.S.km) := by positivity
    have q0 : 0 < F.S.hm * F.S.sm * LA F.S / (2 * den F.S) := by positivity
    refine ⟨min (min (F.S.hm * F.S.sm * LA F.S / (2 * den F.S)) (LE F.S / (2 * F.S.hp)))
      (min (LF F.S / 2) (LG F.S / (2 * F.S.km))), lt_min (lt_min q0 q1) (lt_min q2 q3), ?_, ?_, ?_, ?_⟩
    · exact eps_aux p1 hden ((min_le_left _ _).trans (min_le_left _ _))
    · exact eps_aux hLE hp0 ((min_le_left _ _).trans (min_le_right _ _))
    · exact lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
    · exact eps_aux hLG km0 ((min_le_right _ _).trans (min_le_right _ _))
  set qu : C3 := ⟨F.S.tm*F.S.tp*kap F.S, -(F.S.sm*F.S.sp*c0 F.S) - eps, lam F.S⟩ with hqu
  have vA : nf F.S qu 0 = F.S.hm * F.S.sm * LA F.S - eps * den F.S := by
    rw [nf_A]; simp only [hqu, LA, kap, lam, c0, den]; ring
  have vB : nf F.S qu 1 = eps * (F.S.kp * F.S.tp) := by
    rw [nf_B]; simp only [hqu, kap, lam, c0]; ring
  have vC : nf F.S qu 2 = c0 F.S * (F.S.sm * F.S.sp * c0 F.S + eps) := by
    rw [show nf F.S qu 2 = _ from nf_C F.S qu]; simp only [hqu, c0]; ring
  have vD : nf F.S qu 3 = eps * (F.S.km * F.S.tm) := by
    rw [nf_D]; simp only [hqu, kap, lam, c0]; ring
  have vE : nf F.S qu 4 = LE F.S - eps * F.S.hp := by
    rw [nf_E]; simp only [hqu, LE, P1, Aq, kap, lam, c0]; ring
  have vF : nf F.S qu 5 = F.S.kp * F.S.tp * (LF F.S - eps) := by
    rw [nf_F]; simp only [hqu, LF, kap, lam, c0]; ring
  have vG : nf F.S qu 6 = LG F.S - eps * F.S.km := by
    rw [nf_G]; simp only [hqu, LG, D16, kap, lam, c0]; ring
  have vH : nf F.S qu 7 = -(F.S.kp * F.S.tm * F.S.tp * kap F.S) := by
    rw [nf_H]; simp only [hqu]; ring
  have hz2 : F.dep qu 2 = -(F.S.sp * F.a22 * eps) := by
    rw [F.dep_2]; simp only [hqu, hlam]; linear_combination F.S.sp * hw
  have hz4 : F.dep qu 4 = -(F.S.sm * F.a22 * eps) := by
    rw [F.dep_4]; simp only [hqu, hlam]; linear_combination F.S.sm * hw
  have hz6 : F.dep qu 6 = -(F.a22 * eps) := by
    rw [F.dep_6]; simp only [hqu]; linear_combination hw
  have hz5 : F.dep qu 5 = 0 := F.dep_5 qu
  have hw0 : 0 < F.a22 * eps := mul_pos ha22 he0
  have hU : RobUni (fun a : ZMod 4 => F.dep qu (cyc9 a)) := by
    refine robUni4 ?_ ?_
    · rintro ⟨a1, -, -, -⟩
      have : F.dep qu (cyc9 1) = 0 := hz5
      have h0 : F.dep qu (cyc9 0) = -(F.S.sp * F.a22 * eps) := hz2
      rw [this, h0] at a1
      have := mul_pos sp0 hw0
      linarith
    · rintro ⟨a1, a2, -, -⟩
      have h0 : F.dep qu (cyc9 0) = -(F.S.sp * F.a22 * eps) := hz2
      have h3 : F.dep qu (cyc9 3) = -(F.a22 * eps) := hz6
      rw [h0, h3] at a2
      have := mul_pos (sub_pos.2 sp1) hw0
      linarith
  refine leaf_of_view F FF hx (by norm_num) cyc9_inj cyc9_ok qu ⟨0, -1, 0⟩ 2 ?_ ?_ hU
  · rw [vC]; positivity
  · intro t
    have ht : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 := by
      revert t; decide
    have ec : 0 < c0 F.S * (F.S.sm * F.S.sp * c0 F.S + eps) := by positivity
    have ep : 0 < eps * (F.S.kp * F.S.tp) := by positivity
    have ed : 0 < eps * (F.S.km * F.S.tm) := by positivity
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨fun _ => Or.inl (by rw [vA]; linarith), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => Or.inl (by rw [vB]; exact ep), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => Or.inl (by rw [vC]; exact ec), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => Or.inl (by rw [vD]; exact ed), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => Or.inl (by rw [vE]; linarith), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => Or.inl (by rw [vF]; positivity), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => Or.inl (by rw [vG]; linarith), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => Or.inl (by rw [vH]; nlinarith [mul_pos kp0 (mul_pos tm0 (mul_pos tp0 hkap))])⟩

end IMCT
end Minimality.CaseC20

end

section

/-!
# Type 20, I_MC, stratum Z (`Vq = 0`): leaves L11 and L12 (view `x3 - x5`, tilt `(0, -+1, 0)`)

At `Vq = 0` the facets `C`, `D`, `F` are all edge-on at the view `x3 - x5 = fvC (tm, 0, -hm)`, and
the tilt `(0, -1, 0)` makes `C`, `D` up and `F` down (L11), the tilt `(0, 1, 0)` the opposite (L12).
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace IMCT

/-- Pattern of L11: up `A C D E G`, down `B F H`. -/
def pat11 : Fin 8 → Bool := ![true, false, true, true, true, false, true, false]
/-- The cycle `0,5,4,6`. -/
def cyc11 : ZMod 4 → Fin 7 := ![0, 5, 4, 6]
theorem cyc11_ok : S0xCycOK h20s_S cyc11 pat11 := by decide
theorem cyc11_inj : Function.Injective cyc11 := by decide

/-- Pattern of L12: up `A E F G`, down `B C D H`. -/
def pat12 : Fin 8 → Bool := ![true, false, false, false, true, true, true, false]
/-- The cycle `0,1,3,4,6,2`. -/
def cyc12 : ZMod 6 → Fin 7 := ![0, 1, 3, 4, 6, 2]
theorem cyc12_ok : S0xCycOK h20s_S cyc12 pat12 := by decide
theorem cyc12_inj : Function.Injective cyc12 := by decide

variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- The common facing values at the view `x3 - x5 = (tm, 0, -hm)` in stratum Z (`Vq = 0`). -/
lemma zfacings (hV : Vq F.S = 0) :
    nf F.S ⟨F.S.tm, 0, -F.S.hm⟩ 0 = F.S.hm * F.S.sm ∧
    nf F.S ⟨F.S.tm, 0, -F.S.hm⟩ 1 = -(F.S.sp * c0 F.S) ∧
    nf F.S ⟨F.S.tm, 0, -F.S.hm⟩ 2 = 0 ∧
    nf F.S ⟨F.S.tm, 0, -F.S.hm⟩ 3 = 0 ∧
    nf F.S ⟨F.S.tm, 0, -F.S.hm⟩ 4 = Aq F.S ∧
    nf F.S ⟨F.S.tm, 0, -F.S.hm⟩ 5 = 0 ∧
    nf F.S ⟨F.S.tm, 0, -F.S.hm⟩ 6 = F.S.km * F.S.tm + F.S.hm * (1 - F.S.sm) ∧
    nf F.S ⟨F.S.tm, 0, -F.S.hm⟩ 7 = -(F.S.kp * F.S.tm) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [nf_A]; dsimp only; ring
  · rw [nf_B]; dsimp only; unfold c0; ring
  · rw [nf_C]; dsimp only; ring
  · rw [nf_D]; dsimp only; ring
  · rw [nf_E]; dsimp only; unfold Aq; ring
  · rw [nf_F]; dsimp only; unfold Vq at hV; linear_combination (-1) * hV
  · rw [nf_G]; dsimp only; ring
  · rw [nf_H]; dsimp only; ring

/-- The depths at the view `x3 - x5` (Z, `A > 0`): `z1 - z3`, `z3 - z4` scaled by `c = (1-tm)(1-tp)`. -/
lemma zdepths (hE1 : (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 +
      (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg = 0)
    (hE2 : (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) +
      (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg = 0) :
    (1-F.S.tm)*(1-F.S.tp) * (F.dep ⟨F.S.tm, 0, -F.S.hm⟩ 1 - F.dep ⟨F.S.tm, 0, -F.S.hm⟩ 3) =
        F.gg * F.S.hm * (1-F.S.tm) * Aq F.S ∧
    (1-F.S.tm)*(1-F.S.tp) * (F.dep ⟨F.S.tm, 0, -F.S.hm⟩ 3 - F.dep ⟨F.S.tm, 0, -F.S.hm⟩ 4) =
        F.gg * Kq F.S * (1-F.S.tm) * Aq F.S ∧
    (1-F.S.tm)*(1-F.S.tp) * F.dep ⟨F.S.tm, 0, -F.S.hm⟩ 0 =
        F.S.hm * F.S.hp * F.gg * (F.S.tp + F.S.tm - 1) := by
  have m1 := imc_M1 F hE2
  have m2 := imc_M2 F hE1
  refine ⟨?_, ?_, ?_⟩
  · rw [F.dep_1, F.dep_3]; unfold Aq
    linear_combination (F.S.tm*(1-F.S.tm)) * m1
  · rw [F.dep_3, F.dep_4]; unfold Aq Kq
    linear_combination (F.S.tm^2) * m1 - F.S.tm * m2
  · rw [F.dep_0]
    linear_combination (F.S.tp*F.S.tm) * m1

/-- Common positivity and setup for L11 and L12 are inside each theorem; this is **L11**:
in stratum `Vq = 0` with `A > 0`, `Q ≥ 0`, if `z0 < z6` or `z4 < z6` at the view `x3 - x5`, the
point set is Rupert (cycle `0,5,4,6`, tilt `(0,-1,0)`). -/
theorem imc_L11 (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hE1 : (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 +
      (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg = 0)
    (hE2 : (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) +
      (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg = 0)
    (hV : Vq F.S = 0) (hA : 0 < Aq F.S) (hQ : 0 ≤ Qq F.S)
    (hlow : F.dep ⟨F.S.tm, 0, -F.S.hm⟩ 0 < F.dep ⟨F.S.tm, 0, -F.S.hm⟩ 6 ∨
      F.dep ⟨F.S.tm, 0, -F.S.hm⟩ 4 < F.dep ⟨F.S.tm, 0, -F.S.hm⟩ 6) :
    IsRupert (univ.image x) := by
  set FF := h20s_fac hR with hFF
  have tp0 := F.S.tp_pos; have tp1 := F.S.tp_lt; have tm0 := F.S.tm_pos; have tm1 := F.S.tm_lt
  have sp0 := F.S.sp_pos; have sp1 := F.S.sp_lt; have sm0 := F.S.sm_pos; have sm1 := F.S.sm_lt
  have hp0 := F.S.hp_pos; have hm0 := F.S.hm_pos; have kp0 := F.S.kp_pos; have km0 := F.S.km_pos
  have hg := F.g_pos
  have t1 : 0 < 1 - F.S.tp := by linarith
  have t4 : 0 < 1 - F.S.tm := by linarith
  have hden : 0 < den F.S := imc_den_pos F hE1
  obtain ⟨uA, uB, uC, uD, uE, uF, uG, uH⟩ := zfacings F hV
  set qu : C3 := ⟨F.S.tm, 0, -F.S.hm⟩ with hqu
  set qv : C3 := ⟨0, -1, 0⟩ with hqv
  have c0p : 0 < c0 F.S := by unfold c0; positivity
  have vC : nf F.S qv 2 = c0 F.S := by rw [nf_C]; simp only [hqv, c0]; ring
  have vD : nf F.S qv 3 = F.S.km * F.S.tm := by rw [nf_D]; simp only [hqv]; ring
  have vF : nf F.S qv 5 = -(F.S.kp * F.S.tp) := by rw [nf_F]; simp only [hqv]; ring
  -- E0 > 0 and tp + tm > 1
  have hE0 : 0 < E0 F.S := by
    have h : F.S.sm * E0 F.S = den F.S + Qq F.S := by unfold E0 den Qq; ring
    have : 0 < F.S.sm * E0 F.S := by rw [h]; linarith
    exact pos_of_mul_pos_right this sm0.le
  have hsum : 1 < F.S.tp + F.S.tm := by
    by_contra hc
    push Not at hc
    unfold E0 at hE0
    unfold Aq at hA
    have hd : 0 ≤ 1 - F.S.tm - F.S.tp := by linarith
    have h1 : 0 < (F.S.hm - F.S.hp) * F.S.tp := by nlinarith [mul_nonneg hp0.le hd]
    have h2 : 0 < (F.S.hp - F.S.hm) * F.S.tm := by nlinarith [mul_nonneg hm0.le hd]
    have h3 := pos_of_mul_pos_left h1 tp0.le
    have h4 := pos_of_mul_pos_left h2 tm0.le
    linarith
  obtain ⟨-, -, d0⟩ := zdepths F hE1 hE2
  have z0p : 0 < F.dep qu 0 := by
    have : 0 < (1-F.S.tm)*(1-F.S.tp) * F.dep qu 0 := by
      rw [d0]; have : 0 < F.S.tp + F.S.tm - 1 := by linarith
      positivity
    exact pos_of_mul_pos_right this (mul_pos t4 t1).le
  have hU : RobUni (fun a : ZMod 4 => F.dep qu (cyc11 a)) := by
    refine robUni4 ?_ ?_
    · rintro ⟨-, -, a3, a4⟩
      change F.dep qu 6 ≤ F.dep qu 0 at a3
      change F.dep qu 6 ≤ F.dep qu 4 at a4
      rcases hlow with h | h <;> linarith
    · rintro ⟨a1, -, -, -⟩
      change F.dep qu 0 ≤ F.dep qu 5 at a1
      rw [F.dep_5] at a1
      linarith
  refine leaf_of_view F FF hx (by norm_num) cyc11_inj cyc11_ok qu qv 0 ?_ ?_ hU
  · rw [uA]; positivity
  · intro t
    have ht : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 := by
      revert t; decide
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨fun _ => Or.inl (by rw [uA]; positivity), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => Or.inl (by rw [uB]; have := mul_pos sp0 c0p; linarith)⟩
    · exact ⟨fun _ => Or.inr ⟨uC, by rw [vC]; exact c0p⟩, fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => Or.inr ⟨uD, by rw [vD]; positivity⟩, fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => Or.inl (by rw [uE]; exact hA), fun h => absurd h (by decide)⟩
    · refine ⟨fun h => absurd h (by decide), fun _ => Or.inr ⟨by rw [uF]; ring, ?_⟩⟩
      rw [vF]; have := mul_pos kp0 tp0; linarith
    · exact ⟨fun _ => Or.inl (by rw [uG]; positivity), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => Or.inl (by rw [uH]; have := mul_pos kp0 tm0; linarith)⟩

/-- **L12**: in stratum `Vq = 0` with `A > 0`, `K > 0`, if `z6 < z4` and `z6 ≤ z0` at the view
`x3 - x5`, the point set is Rupert (cycle `0,1,3,4,6,2`, tilt `(0,1,0)`). -/
theorem imc_L12 (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hE1 : (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 +
      (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg = 0)
    (hE2 : (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) +
      (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg = 0)
    (hV : Vq F.S = 0) (hA : 0 < Aq F.S) (hK : 0 < Kq F.S)
    (h46 : F.dep ⟨F.S.tm, 0, -F.S.hm⟩ 6 < F.dep ⟨F.S.tm, 0, -F.S.hm⟩ 4)
    (h06 : F.dep ⟨F.S.tm, 0, -F.S.hm⟩ 6 ≤ F.dep ⟨F.S.tm, 0, -F.S.hm⟩ 0) :
    IsRupert (univ.image x) := by
  set FF := h20s_fac hR with hFF
  have tp0 := F.S.tp_pos; have tp1 := F.S.tp_lt; have tm0 := F.S.tm_pos; have tm1 := F.S.tm_lt
  have sp0 := F.S.sp_pos; have sp1 := F.S.sp_lt; have sm0 := F.S.sm_pos; have sm1 := F.S.sm_lt
  have hp0 := F.S.hp_pos; have hm0 := F.S.hm_pos; have kp0 := F.S.kp_pos; have km0 := F.S.km_pos
  have hg := F.g_pos
  have t1 : 0 < 1 - F.S.tp := by linarith
  have t4 : 0 < 1 - F.S.tm := by linarith
  have ht14 : 0 < (1-F.S.tm)*(1-F.S.tp) := mul_pos t4 t1
  obtain ⟨uA, uB, uC, uD, uE, uF, uG, uH⟩ := zfacings F hV
  set qu : C3 := ⟨F.S.tm, 0, -F.S.hm⟩ with hqu
  set qv : C3 := ⟨0, 1, 0⟩ with hqv
  have c0p : 0 < c0 F.S := by unfold c0; positivity
  have vC : nf F.S qv 2 = -c0 F.S := by rw [nf_C]; simp only [hqv, c0]; ring
  have vD : nf F.S qv 3 = -(F.S.km * F.S.tm) := by rw [nf_D]; simp only [hqv]; ring
  have vF : nf F.S qv 5 = F.S.kp * F.S.tp := by rw [nf_F]; simp only [hqv]; ring
  obtain ⟨d13, d34, -⟩ := zdepths F hE1 hE2
  have z13 : F.dep qu 3 < F.dep qu 1 := by
    have : 0 < (1-F.S.tm)*(1-F.S.tp) * (F.dep qu 1 - F.dep qu 3) := by
      rw [d13]; positivity
    have := pos_of_mul_pos_right this ht14.le
    linarith
  have z34 : F.dep qu 4 < F.dep qu 3 := by
    have : 0 < (1-F.S.tm)*(1-F.S.tp) * (F.dep qu 3 - F.dep qu 4) := by
      rw [d34]; positivity
    have := pos_of_mul_pos_right this ht14.le
    linarith
  have z01 : F.dep qu 0 < F.dep qu 1 := by
    have h11 : 0 < F.a11 := F.A11_pos
    rw [F.dep_0, F.dep_1]; simp only [hqu]
    have : 0 < F.a11 * (F.S.tm * (1 - F.S.tp)) + F.gg * (F.S.hm * F.S.hp) := by positivity
    linarith
  have z3p : 0 < F.dep qu 3 := by
    have h11 : 0 < F.a11 := F.A11_pos
    rw [F.dep_3]; simp only [hqu]
    have : 0 < F.a11 * (F.S.tm * F.S.tm) + F.gg * (F.S.hm * F.S.hm) := by positivity
    linarith
  have hV' : (1-F.S.sp)*(F.S.hm*F.S.tp + F.S.hp*F.S.tm) - F.S.kp*F.S.tm = 0 := hV
  have z20 : F.dep qu 2 < F.dep qu 0 := by
    have key : F.S.tm * (F.dep qu 0 - F.dep qu 2) = F.S.tm * F.S.sp * (F.dep qu 0 - F.dep qu 6) +
        (1 - F.S.sp) * F.S.tp * F.dep qu 3 := by
      rw [F.dep_0, F.dep_2, F.dep_3, F.dep_6]; simp only [hqu]
      linear_combination (-(F.gg * F.S.hm)) * hV'
    have : 0 < F.S.tm * (F.dep qu 0 - F.dep qu 2) := by
      rw [key]
      have h1 : 0 ≤ F.S.tm * F.S.sp * (F.dep qu 0 - F.dep qu 6) :=
        mul_nonneg (mul_pos tm0 sp0).le (by linarith)
      have h2 : 0 < (1 - F.S.sp) * F.S.tp * F.dep qu 3 :=
        mul_pos (mul_pos (by linarith) tp0) z3p
      linarith
    have := pos_of_mul_pos_right this tm0.le
    linarith
  have hU : RobUni (fun a : ZMod 6 => F.dep qu (cyc12 a)) := by
    refine robUni6_a ?_ ?_ ?_ ?_ ?_ ?_
    · show F.dep qu 3 < F.dep qu 1
      exact z13
    · show F.dep qu 4 < F.dep qu 3
      exact z34
    · show F.dep qu 6 < F.dep qu 4
      exact h46
    · show F.dep qu 0 < F.dep qu 1
      exact z01
    · show F.dep qu 6 ≤ F.dep qu 0
      exact h06
    · show F.dep qu 2 < F.dep qu 0
      exact z20
  refine leaf_of_view F FF hx (by norm_num) cyc12_inj cyc12_ok qu qv 0 ?_ ?_ hU
  · rw [uA]; positivity
  · intro t
    have ht : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 := by
      revert t; decide
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨fun _ => Or.inl (by rw [uA]; positivity), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => Or.inl (by rw [uB]; have := mul_pos sp0 c0p; linarith)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => Or.inr ⟨by rw [uC]; ring, by rw [vC]; linarith⟩⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => Or.inr ⟨by rw [uD]; ring, by rw [vD]; have := mul_pos km0 tm0; linarith⟩⟩
    · exact ⟨fun _ => Or.inl (by rw [uE]; exact hA), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => Or.inr ⟨uF, by rw [vF]; positivity⟩, fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => Or.inl (by rw [uG]; positivity), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => Or.inl (by rw [uH]; have := mul_pos kp0 tm0; linarith)⟩

end IMCT
end Minimality.CaseC20

end

section

/-!
# D1: dispatch of the I_MC leaves (COVER.md section 1 tree)

`Frame20.isRupert_IMC` assembles the leaves L1..L12 by the case tree; the two leaves still being
proved elsewhere enter as the Prop-valued defs `Frame20.CornerStmt` (`imc_corner`) and
`Frame20.ZtStmt` (`imc_Zt`).
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20

namespace IMCT
variable (S : Shape20)

/-- On `Vq <= 0` the quantity `A` is positive: `(1-tp) Vq = -(1-sp) tp A + tm roof` and `roof > 0`. -/
lemma A_pos_of_Vq (hV : Vq S ≤ 0) : 0 < Aq S := by
  have e : (1 - S.tp) * Vq S = -(1 - S.sp) * S.tp * Aq S
      + S.tm * (S.hp * (1 - S.sp) - S.kp * (1 - S.tp)) := by unfold Vq Aq; ring
  have h1 := S.tp1; have h2 := S.roofP; have h3 := S.tm_pos; have h4 := S.sp1; have h5 := S.tp_pos
  by_contra hA
  push Not at hA
  nlinarith [mul_pos h3 h2, mul_nonneg (mul_pos h4 h5).le (neg_nonneg.2 hA),
    mul_nonneg h1.le (neg_nonneg.2 hV)]

/-- If `K = 0` and `Q >= 0` then `VM > 0` (so the tree never reaches `VM <= 0` with `K = 0`). -/
lemma VM_pos_of_K0 (hK : Kq S = 0) (hQ : 0 ≤ Qq S) : 0 < VM S := by
  have hkm : S.km = S.hm := by unfold Kq at hK; linarith
  have h1 := S.tp1; have h3 := S.tm_pos; have h4 := S.sp1; have h5 := S.tp_pos
  have hsm := S.sm_pos; have hhp := S.hp_pos; have hkp := S.kp_pos; have hkm0 := S.km_pos
  have ht := S.tm1
  have hq : S.hp * S.sm * (1 - S.tm) ≤ S.km * (S.sm * S.tp - S.tm) := by
    unfold Qq at hQ; rw [hkm] at hQ ⊢; nlinarith
  have hpos : 0 < S.sm * S.tp - S.tm := by
    by_contra hc
    push Not at hc
    nlinarith [mul_pos (mul_pos hhp hsm) ht, mul_nonneg hkm0.le (neg_nonneg.2 hc)]
  have e : VM S = (1 - S.sp) * S.hp * S.tm + S.kp * (S.tp * S.sm - S.tm) := by
    unfold VM Vq Mq; rw [hkm]; ring
  rw [e]
  nlinarith [mul_pos (mul_pos h4 hhp) h3, mul_pos hkp hpos]

/-- `E0 > 0` follows from `Q >= 0` and `den > 0`, since `Q = sm E0 - den`. -/
lemma E0_pos (hden : 0 < S.hm + S.km * S.tm - S.km) (hQ : 0 ≤ Qq S) :
    0 < S.hm * S.tp - S.hp * (1 - S.tm) := by
  have e : S.sm * (S.hm * S.tp - S.hp * (1 - S.tm)) = Qq S + (S.hm + S.km * S.tm - S.km) := by
    unfold Qq; ring
  have hsm := S.sm_pos
  by_contra hc
  push Not at hc
  nlinarith [mul_nonneg hsm.le (neg_nonneg.2 hc)]

end IMCT
open IMCT

namespace Frame20
variable {x : Fin 7 → ℝ³}

/-- The view `x3 - x5` of stratum Z, as a frame vector `(tm, 0, -hm)`. -/
noncomputable def qZ (F : Frame20 x) : C3 := ⟨F.S.tm, 0, -F.S.hm⟩

/-- **The corner leaf `imc_corner`** (still being proved): on I_MC with `A = 0`, `K = 0`, `Q >= 0`,
`F15 >= 0` the point set is Rupert. -/
def CornerStmt (F : Frame20 x) : Prop :=
  Function.Injective x → RealizesFaces x (sevenTypeFaces 19) → F.IMC →
    Aq F.S = 0 → Kq F.S = 0 → 0 ≤ Qq F.S → 0 ≤ F15 F.S → IsRupert (univ.image x)

/-- **The tie leaf `imc_Zt`** (still being proved): in stratum Z (`Vq = 0 = P1`) with `A > 0`,
`K > 0`, `Q >= 0`, at the view `x3 - x5` the tie `z4 = z6` with `z6 <= z0` is Rupert. -/
def ZtStmt (F : Frame20 x) : Prop :=
  Function.Injective x → RealizesFaces x (sevenTypeFaces 19) → F.IMC →
    Vq F.S = 0 → P1 F.S = 0 → 0 < Aq F.S → 0 < Kq F.S → 0 ≤ Qq F.S →
    F.dep F.qZ 4 = F.dep F.qZ 6 → F.dep F.qZ 6 ≤ F.dep F.qZ 0 → IsRupert (univ.image x)

variable (F : Frame20 x)

/-- Leaves L7 and L8: with `Q >= 0`, `A > 0`, `F15 >= 0`, `VM > 0` the set is Rupert
(L7 when `Q > 0`, the tilted leaf L8 when `Q = 0`). -/
lemma imc_L78 (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hI : F.IMC) (hQ : 0 ≤ Qq F.S) (hA : 0 < Aq F.S) (hF : 0 ≤ F15 F.S) (hVM : 0 < VM F.S) :
    IsRupert (univ.image x) := by
  rcases hQ.eq_or_lt with h | h
  · exact imc_L8 F hx hR hI.1 hI.2 h.symm hA hVM
  · exact F.imc_L7 hx hR hI h hA hF hVM

/-- The part of the tree with `A >= 0` and `Q >= 0` (the leaves L4, L5, L6, L7-L12 and the corner). -/
lemma imc_main (hCorner : F.CornerStmt) (hZt : F.ZtStmt)
    (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hI : F.IMC) (hA : 0 ≤ Aq F.S) (hQ : 0 ≤ Qq F.S) : IsRupert (univ.image x) := by
  rcases lt_or_ge (Kq F.S) 0 with hK | hK
  · exact F.imc_L4 hx hR hI hA hQ hK
  rcases lt_or_ge (F15 F.S) 0 with hF | hF
  · exact F.imc_L5 hx hR hI hQ hK hF
  rcases hK.eq_or_lt with hK0 | hKp
  · -- K = 0: then VM > 0
    have hVM := VM_pos_of_K0 F.S hK0.symm hQ
    rcases hA.eq_or_lt with hA0 | hAp
    · exact hCorner hx hR hI hA0.symm hK0.symm hQ hF
    · exact F.imc_L78 hx hR hI hQ hAp hF hVM
  · -- K > 0
    rcases lt_or_ge 0 (Vq F.S) with hV | hV
    · exact F.imc_L6 hx hR hI hQ hKp hF hV
    have hAp := A_pos_of_Vq F.S hV
    rcases lt_or_ge 0 (VM F.S) with hVM | hVM
    · exact F.imc_L78 hx hR hI hQ hAp hF hVM
    by_cases hZ : Vq F.S = 0 ∧ P1 F.S = 0
    · -- stratum Z
      rcases lt_or_ge (F.dep F.qZ 0) (F.dep F.qZ 6) with h0 | h0
      · exact imc_L11 F hx hR hI.1 hI.2 hZ.1 hAp hQ (Or.inl h0)
      rcases lt_or_ge (F.dep F.qZ 4) (F.dep F.qZ 6) with h4 | h4
      · exact imc_L11 F hx hR hI.1 hI.2 hZ.1 hAp hQ (Or.inr h4)
      rcases h4.lt_or_eq with h4 | h4
      · exact imc_L12 F hx hR hI.1 hI.2 hZ.1 hAp hKp h4 h0
      · exact hZt hx hR hI hZ.1 hZ.2 hAp hKp hQ h4.symm h0
    · rcases lt_or_ge 0 (LG F.S) with hLG | hLG
      · by_cases hne : lam F.S = 0 ∧
            F.a12 * (F.S.tm * F.S.tp * (F.S.km*F.S.sp+F.S.kp*F.S.sm))
              + F.a22 * (-F.S.sm * F.S.sp * (F.S.hm*F.S.tp+F.S.hp*F.S.tm)) = 0
        · -- special position lam = 0, w2 = 0: perturbed view
          have hden := imc_den_pos F hI.1
          have hE0 := E0_pos F.S hden hQ
          have hP := F.S.alg_P1 hQ hV hVM
          have hLF := F.S.alg_LF hP hV hZ
          have hLE := F.S.alg_LE hP hAp
          have hLA := F.S.alg_LA hQ hE0 hP hV hLF
          exact imc_L9p F hx hR hI.1 hLA hLE hLF hLG hne.1 (by simp only [kap, c0]; linarith [hne.2])
        · exact F.imc_L9 hx hR hI hQ hAp hK hV hVM hZ hLG hne
      · exact F.imc_L10 hx hR hI hQ hAp hK hV hVM hLG

end Frame20
end Minimality.CaseC20

end

