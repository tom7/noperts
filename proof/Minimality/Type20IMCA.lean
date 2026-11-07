module

public import Minimality.Type20Leaf

@[expose] public section

/-!
# Type 20, item I_MC (part A): the I_MC equations and shared generic-leaf tools

The item I_MC is the pair of equations of lines 277 and 280 of `CaseC20Face` (and the `R`-image,
lines 279 and 285).  This module has the named shape quantities of the covering notes (`den`, `Aq`,
`Qq`, ...), the consequences `a12 < a11` of the two equations, the facet normals in frame
coordinates (`Nrm`), the parametrization of I_MC (`Frame20.par`), polynomial depths, and the
`RobUni` helpers and view lemmas used by the generic leaves of the later parts.
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace IMCT

export Minimality.CaseC20.IVT (nf nf_A nf_B nf_C nf_D nf_E nf_F nf_G nf_H core_a core_b facing_A facing_B facing_C facing_D
  facing_E facing_F facing_G facing_H facing lp_scale facOK fvC_ne_zero leaf_of_view seg_vec dep_neg)

/-! ### Named shape quantities of the COVER.md notation (`t = 1 - tm`) -/
section names
variable (S : Shape20)
noncomputable def den : ℝ := S.hm + S.km*S.tm - S.km
noncomputable def c0 : ℝ := S.hm*S.tp + S.hp*S.tm
noncomputable def Aq : ℝ := S.hm*S.tp - S.hm + S.hp*S.tm
noncomputable def Kq : ℝ := S.km - S.hm
noncomputable def E0 : ℝ := S.hm*S.tp - S.hp*(1-S.tm)
noncomputable def Qq : ℝ := S.km*(1-S.tm) - S.hm*(1 - S.sm*S.tp) - S.hp*S.sm*(1-S.tm)
noncomputable def F15 : ℝ := S.kp - S.hp*(1-S.sp)
noncomputable def Vq : ℝ := (1-S.sp)*(S.hm*S.tp + S.hp*S.tm) - S.kp*S.tm
noncomputable def Mq : ℝ := S.km*(1-S.sp) - S.kp*S.sm
noncomputable def VM : ℝ := Vq S - S.tp * Mq S
noncomputable def kap : ℝ := S.km*S.sp + S.kp*S.sm
noncomputable def lam : ℝ := S.hp*S.km*S.sp*S.tm - S.hm*S.kp*S.sm*S.tp
noncomputable def D16 : ℝ := S.km*S.tm - S.hm*S.sm
noncomputable def P1 : ℝ := S.km*S.tm - S.sm*(S.hm*S.tp + S.hp*S.tm)
noncomputable def LA : ℝ := S.tp*kap S - S.sp*(S.hm*S.tp + S.hp*S.tm)
noncomputable def LF : ℝ := S.tm*kap S - S.sm*(S.hm*S.tp + S.hp*S.tm)
noncomputable def LG : ℝ := S.tp*D16 S*kap S - lam S
noncomputable def LE : ℝ := S.hp*S.sp*P1 S + S.sm*S.tp*S.kp*Aq S
end names

variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- The I_MC equations in the form used by the leaves. -/
lemma imc_M1 (hE2 : (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) +
      (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg = 0) :
    (1 - F.S.tm) * (1 - F.S.tp) * F.a11 = F.S.hm * F.S.hp * F.gg := by linear_combination hE2

lemma imc_M2 (hE1 : (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 +
      (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg = 0) :
    F.S.sm * (1 - F.S.tm) * (1 - F.S.tp) * F.a12 =
      F.S.hp * (F.S.hm + F.S.km*F.S.tm - F.S.km) * F.gg := by linear_combination -hE1

/-- On I_MC, `den = hm + km tm - km` is positive. -/
lemma imc_den_pos (hE1 : (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 +
      (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg = 0) :
    0 < F.S.hm + F.S.km*F.S.tm - F.S.km := by
  have h := imc_M2 F hE1
  have t1 : 0 < 1 - F.S.tp := by linarith [F.S.tp_lt]
  have t4 : 0 < 1 - F.S.tm := by linarith [F.S.tm_lt]
  have hl : 0 < F.S.sm * (1 - F.S.tm) * (1 - F.S.tp) * F.a12 :=
    mul_pos (mul_pos (mul_pos F.S.sm_pos t4) t1) F.A12_pos
  rw [h] at hl
  have hg := F.g_pos
  have hp := F.S.hp_pos
  by_contra hc
  push Not at hc
  nlinarith [mul_nonneg (mul_nonneg hp.le hg.le) (neg_nonneg.2 hc)]

/-- On I_MC, `a11 den = a12 hm sm`, hence `a12 < a11`. -/
lemma imc_a12_lt (hE1 : (-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 +
      (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg = 0)
    (hE2 : (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) +
      (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg = 0) :
    F.a12 < F.a11 := by
  have hden := imc_den_pos F hE1
  have m1 := imc_M1 F hE2
  have m2 := imc_M2 F hE1
  have t1 : 0 < 1 - F.S.tp := by linarith [F.S.tp_lt]
  have t4 : 0 < 1 - F.S.tm := by linarith [F.S.tm_lt]
  have hc : 0 < (1 - F.S.tm) * (1 - F.S.tp) := mul_pos t4 t1
  have key : F.a11 * (F.S.hm + F.S.km*F.S.tm - F.S.km) = F.a12 * (F.S.hm * F.S.sm) := by
    have : (1 - F.S.tm) * (1 - F.S.tp) * (F.a11 * (F.S.hm + F.S.km*F.S.tm - F.S.km)) =
        (1 - F.S.tm) * (1 - F.S.tp) * (F.a12 * (F.S.hm * F.S.sm)) := by
      linear_combination (F.S.hm + F.S.km*F.S.tm - F.S.km) * m1 - F.S.hm * m2
    exact mul_left_cancel₀ hc.ne' this
  have hl := F.S.roof_m'
  have h12 : 0 < F.a12 := F.A12_pos
  by_contra hcon
  push Not at hcon
  have : F.a11 * (F.S.hm + F.S.km*F.S.tm - F.S.km) ≤ F.a12 * (F.S.hm + F.S.km*F.S.tm - F.S.km) :=
    mul_le_mul_of_nonneg_right hcon hden.le
  nlinarith [mul_pos h12 (show 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) by linarith)]

end IMCT
end Minimality.CaseC20

/-!
# G0a: facet normals of type 20 in frame coordinates (the eight `nrm_*` lemmas)
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x) (FF : S0xFac 8 h20s_S x)

/-- Facet `t` has outward normal with frame coordinates a positive multiple of `(a, b, d)`:
`⟪N, u1⟫ = l a`, `⟪N, u2⟫ = l b`, `⟪N, e⟫ = l d`. -/
def Nrm (t : Fin 8) (a b d : ℝ) : Prop :=
  ∃ l : ℝ, 0 < l ∧ ⟪FF.N t, x 1 - x 5⟫ = l * a ∧ ⟪FF.N t, x 6 - x 5⟫ = l * b ∧
    ⟪FF.N t, F.e⟫ = l * d

/-- Scaled coordinates `s α = m a` with `s, m > 0` give a positive multiple. -/
lemma nrm_of {α β δ a b d s m : ℝ} (hs : 0 < s) (hm : 0 < m) (h1 : s * α = m * a)
    (h2 : s * β = m * b) (h3 : s * δ = m * d) :
    ∃ l : ℝ, 0 < l ∧ α = l * a ∧ β = l * b ∧ δ = l * d := by
  refine ⟨m / s, div_pos hm hs, ?_, ?_, ?_⟩ <;> field_simp <;> linarith

/-- Facet `A = 134`: normal `(hm sm, den, -sm (1-tm))`. -/
lemma nrm_A : F.Nrm FF 0 (F.S.hm * F.S.sm) (F.S.hm + F.S.km * F.S.tm - F.S.km)
    (-(F.S.sm * (1 - F.S.tm))) := by
  obtain ⟨-, c3, -, c4⟩ := F.facet_coords (FF.f 0) (FF.N 0) (FF.hN 0)
  have z1 : FF.f 0 (x 1) = 0 := FF.zero 0 1 (by decide)
  have z3 : FF.f 0 (x 3) = 0 := FF.zero 0 3 (by decide)
  have z4 : FF.f 0 (x 4) = 0 := FF.zero 0 4 (by decide)
  have n5 : FF.f 0 (x 5) < 0 := FF.neg 0 5 (by decide)
  have hα := FF.hN 0 (x 1) (x 5)
  have hβ := FF.hN 0 (x 6) (x 5)
  simp only [hα, hβ] at c3 c4
  rw [z1] at hα
  rw [z3] at c3
  rw [z4] at c4
  have hm := F.S.hm_pos; have hs := F.S.sm_pos
  have eα : ⟪FF.N 0, x 1 - x 5⟫ = -FF.f 0 (x 5) := by linarith
  rw [eα] at c3
  have eδ : ⟪FF.N 0, F.e⟫ = FF.f 0 (x 5) * (1 - F.S.tm) / F.S.hm := by
    rw [eq_div_iff hm.ne']; linarith
  rw [eδ] at c4
  have eβ : ⟪FF.N 0, x 6 - x 5⟫ = -FF.f 0 (x 5) * (F.S.hm + F.S.km * F.S.tm - F.S.km) /
      (F.S.hm * F.S.sm) := by
    rw [eq_div_iff (mul_pos hm hs).ne']
    field_simp at c4
    nlinarith [c4]
  refine nrm_of (s := F.S.hm * F.S.sm) (m := -FF.f 0 (x 5)) (mul_pos hm hs) (by linarith) ?_ ?_ ?_
  · rw [eα]; ring
  · rw [eβ]; field_simp
  · rw [eδ]; field_simp

/-- Facet `B = 025`: normal `(-hp sp, -kp tp, sp tp)`. -/
lemma nrm_B : F.Nrm FF 1 (-(F.S.hp * F.S.sp)) (-(F.S.kp * F.S.tp)) (F.S.sp * F.S.tp) := by
  obtain ⟨c0, -, c2, -⟩ := F.facet_coords (FF.f 1) (FF.N 1) (FF.hN 1)
  have z0 : FF.f 1 (x 0) = 0 := FF.zero 1 0 (by decide)
  have z2 : FF.f 1 (x 2) = 0 := FF.zero 1 2 (by decide)
  have z5 : FF.f 1 (x 5) = 0 := FF.zero 1 5 (by decide)
  have n1 : FF.f 1 (x 1) < 0 := FF.neg 1 1 (by decide)
  have hα := FF.hN 1 (x 1) (x 5)
  have hβ := FF.hN 1 (x 6) (x 5)
  simp only [hα, hβ] at c0 c2
  rw [z5] at hα
  rw [z0, z5] at c0
  rw [z2, z5] at c2
  have hp := F.S.hp_pos; have hs := F.S.sp_pos; have hk := F.S.kp_pos
  have eα : ⟪FF.N 1, x 1 - x 5⟫ = FF.f 1 (x 1) := by linarith
  rw [eα] at c0
  have eδ : ⟪FF.N 1, F.e⟫ = -(F.S.tp * FF.f 1 (x 1)) / F.S.hp := by
    rw [eq_div_iff hp.ne']; linarith
  rw [eδ] at c2
  have eβ : ⟪FF.N 1, x 6 - x 5⟫ = F.S.kp * F.S.tp * FF.f 1 (x 1) / (F.S.sp * F.S.hp) := by
    rw [eq_div_iff (mul_pos hs hp).ne']
    field_simp at c2
    nlinarith [c2]
  refine nrm_of (s := F.S.hp * F.S.sp) (m := -FF.f 1 (x 1)) (mul_pos hp hs) (by linarith) ?_ ?_ ?_
  · rw [eα]; ring
  · rw [eβ]; field_simp
  · rw [eδ]; field_simp

/-- Facet `C = 0135`: normal `(0, -c0, 0)`, `c0 = hm tp + hp tm`. -/
lemma nrm_C : F.Nrm FF 2 0 (-(F.S.hm * F.S.tp + F.S.hp * F.S.tm)) 0 := by
  obtain ⟨c0, -, -, -⟩ := F.facet_coords (FF.f 2) (FF.N 2) (FF.hN 2)
  have z0 : FF.f 2 (x 0) = 0 := FF.zero 2 0 (by decide)
  have z1 : FF.f 2 (x 1) = 0 := FF.zero 2 1 (by decide)
  have z5 : FF.f 2 (x 5) = 0 := FF.zero 2 5 (by decide)
  have n6 : FF.f 2 (x 6) < 0 := FF.neg 2 6 (by decide)
  have hα := FF.hN 2 (x 1) (x 5)
  have hβ := FF.hN 2 (x 6) (x 5)
  simp only [hα] at c0
  rw [z1, z5] at hα
  rw [z0, z5] at c0
  rw [z5] at hβ
  have hp := F.S.hp_pos; have hm := F.S.hm_pos; have h1 := F.S.tp_pos; have h2 := F.S.tm_pos
  have eα : ⟪FF.N 2, x 1 - x 5⟫ = 0 := by linarith
  rw [eα] at c0
  have eδ : ⟪FF.N 2, F.e⟫ = 0 := by
    have : F.S.hp * ⟪FF.N 2, F.e⟫ = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hp.ne'
    · exact h
  have c0p : 0 < F.S.hm * F.S.tp + F.S.hp * F.S.tm := by positivity
  refine nrm_of (s := F.S.hm * F.S.tp + F.S.hp * F.S.tm) (m := -⟪FF.N 2, x 6 - x 5⟫) c0p
    (by linarith) ?_ ?_ ?_
  · rw [eα]; ring
  · ring
  · rw [eδ]; ring

/-- Facet `D = 345`: normal `(-hm sm, -km tm, -sm tm)`. -/
lemma nrm_D : F.Nrm FF 3 (-(F.S.hm * F.S.sm)) (-(F.S.km * F.S.tm)) (-(F.S.sm * F.S.tm)) := by
  obtain ⟨-, c3, -, c4⟩ := F.facet_coords (FF.f 3) (FF.N 3) (FF.hN 3)
  have z3 : FF.f 3 (x 3) = 0 := FF.zero 3 3 (by decide)
  have z4 : FF.f 3 (x 4) = 0 := FF.zero 3 4 (by decide)
  have z5 : FF.f 3 (x 5) = 0 := FF.zero 3 5 (by decide)
  have n1 : FF.f 3 (x 1) < 0 := FF.neg 3 1 (by decide)
  have hα := FF.hN 3 (x 1) (x 5)
  have hβ := FF.hN 3 (x 6) (x 5)
  simp only [hα, hβ] at c3 c4
  rw [z5] at hα
  rw [z3, z5] at c3
  rw [z4, z5] at c4
  have hm := F.S.hm_pos; have hs := F.S.sm_pos; have hk := F.S.km_pos
  have eα : ⟪FF.N 3, x 1 - x 5⟫ = FF.f 3 (x 1) := by linarith
  rw [eα] at c3
  have eδ : ⟪FF.N 3, F.e⟫ = F.S.tm * FF.f 3 (x 1) / F.S.hm := by
    rw [eq_div_iff hm.ne']; linarith
  rw [eδ] at c4
  have eβ : ⟪FF.N 3, x 6 - x 5⟫ = F.S.km * F.S.tm * FF.f 3 (x 1) / (F.S.hm * F.S.sm) := by
    rw [eq_div_iff (mul_pos hm hs).ne']
    field_simp at c4
    nlinarith [c4]
  refine nrm_of (s := F.S.hm * F.S.sm) (m := -FF.f 3 (x 1)) (mul_pos hm hs) (by linarith) ?_ ?_ ?_
  · rw [eα]; ring
  · rw [eβ]; field_simp
  · rw [eδ]; field_simp

/-- Facet `E = 016`: normal `(hp, hp, 1 - tp)`. -/
lemma nrm_E : F.Nrm FF 4 F.S.hp F.S.hp (1 - F.S.tp) := by
  obtain ⟨c0, -, -, -⟩ := F.facet_coords (FF.f 4) (FF.N 4) (FF.hN 4)
  have z0 : FF.f 4 (x 0) = 0 := FF.zero 4 0 (by decide)
  have z1 : FF.f 4 (x 1) = 0 := FF.zero 4 1 (by decide)
  have z6 : FF.f 4 (x 6) = 0 := FF.zero 4 6 (by decide)
  have n5 : FF.f 4 (x 5) < 0 := FF.neg 4 5 (by decide)
  have hα := FF.hN 4 (x 1) (x 5)
  have hβ := FF.hN 4 (x 6) (x 5)
  simp only [hα] at c0
  rw [z1] at hα
  rw [z0] at c0
  rw [z6] at hβ
  have hp := F.S.hp_pos
  have eα : ⟪FF.N 4, x 1 - x 5⟫ = -FF.f 4 (x 5) := by linarith
  have eβ : ⟪FF.N 4, x 6 - x 5⟫ = -FF.f 4 (x 5) := by linarith
  rw [eα] at c0
  have eδ : ⟪FF.N 4, F.e⟫ = -FF.f 4 (x 5) * (1 - F.S.tp) / F.S.hp := by
    rw [eq_div_iff hp.ne']; linarith
  refine nrm_of (s := F.S.hp) (m := -FF.f 4 (x 5)) hp (by linarith) ?_ ?_ ?_
  · rw [eα]; ring
  · rw [eβ]; ring
  · rw [eδ]; field_simp

/-- Facet `F = 026`: normal `(kp - hp (1-sp), kp tp, tp (1-sp))`. -/
lemma nrm_F : F.Nrm FF 5 (F.S.kp - F.S.hp * (1 - F.S.sp)) (F.S.kp * F.S.tp)
    (F.S.tp * (1 - F.S.sp)) := by
  obtain ⟨c0, -, c2, -⟩ := F.facet_coords (FF.f 5) (FF.N 5) (FF.hN 5)
  have z0 : FF.f 5 (x 0) = 0 := FF.zero 5 0 (by decide)
  have z2 : FF.f 5 (x 2) = 0 := FF.zero 5 2 (by decide)
  have z6 : FF.f 5 (x 6) = 0 := FF.zero 5 6 (by decide)
  have n5 : FF.f 5 (x 5) < 0 := FF.neg 5 5 (by decide)
  have hα := FF.hN 5 (x 1) (x 5)
  have hβ := FF.hN 5 (x 6) (x 5)
  simp only [hα, hβ] at c0 c2
  rw [z6] at hβ
  rw [z0] at c0
  rw [z2] at c2
  have hp := F.S.hp_pos; have hk := F.S.kp_pos; have ht := F.S.tp_pos
  have eβ : ⟪FF.N 5, x 6 - x 5⟫ = -FF.f 5 (x 5) := by linarith
  rw [eβ] at c2
  have eδ : ⟪FF.N 5, F.e⟫ = -FF.f 5 (x 5) * (1 - F.S.sp) / F.S.kp := by
    rw [eq_div_iff hk.ne']; linarith
  rw [eδ] at c0
  have eα : ⟪FF.N 5, x 1 - x 5⟫ = -FF.f 5 (x 5) * (F.S.kp - F.S.hp * (1 - F.S.sp)) /
      (F.S.kp * F.S.tp) := by
    rw [eq_div_iff (mul_pos hk ht).ne']
    field_simp at c0
    nlinarith [c0]
  refine nrm_of (s := F.S.kp * F.S.tp) (m := -FF.f 5 (x 5)) (mul_pos hk ht) (by linarith) ?_ ?_ ?_
  · rw [eα]; field_simp
  · rw [eβ]; ring
  · rw [eδ]; field_simp

/-- Facet `G = 146`: normal `(km, km, sm - 1)`. -/
lemma nrm_G : F.Nrm FF 6 F.S.km F.S.km (F.S.sm - 1) := by
  obtain ⟨-, -, -, c4⟩ := F.facet_coords (FF.f 6) (FF.N 6) (FF.hN 6)
  have z1 : FF.f 6 (x 1) = 0 := FF.zero 6 1 (by decide)
  have z4 : FF.f 6 (x 4) = 0 := FF.zero 6 4 (by decide)
  have z6 : FF.f 6 (x 6) = 0 := FF.zero 6 6 (by decide)
  have n5 : FF.f 6 (x 5) < 0 := FF.neg 6 5 (by decide)
  have hα := FF.hN 6 (x 1) (x 5)
  have hβ := FF.hN 6 (x 6) (x 5)
  simp only [hβ] at c4
  rw [z1] at hα
  rw [z6] at hβ
  rw [z4] at c4
  have hk := F.S.km_pos
  have eα : ⟪FF.N 6, x 1 - x 5⟫ = -FF.f 6 (x 5) := by linarith
  have eβ : ⟪FF.N 6, x 6 - x 5⟫ = -FF.f 6 (x 5) := by linarith
  rw [eβ] at c4
  have eδ : ⟪FF.N 6, F.e⟫ = -FF.f 6 (x 5) * (F.S.sm - 1) / F.S.km := by
    rw [eq_div_iff hk.ne']; linarith
  refine nrm_of (s := F.S.km) (m := -FF.f 6 (x 5)) hk (by linarith) ?_ ?_ ?_
  · rw [eα]; ring
  · rw [eβ]; ring
  · rw [eδ]; field_simp

/-- Facet `H = 2456`: normal `(-kp, 0, 0)`. -/
lemma nrm_H : F.Nrm FF 7 (-F.S.kp) 0 0 := by
  obtain ⟨-, -, c2, -⟩ := F.facet_coords (FF.f 7) (FF.N 7) (FF.hN 7)
  have z2 : FF.f 7 (x 2) = 0 := FF.zero 7 2 (by decide)
  have z5 : FF.f 7 (x 5) = 0 := FF.zero 7 5 (by decide)
  have z6 : FF.f 7 (x 6) = 0 := FF.zero 7 6 (by decide)
  have n1 : FF.f 7 (x 1) < 0 := FF.neg 7 1 (by decide)
  have hα := FF.hN 7 (x 1) (x 5)
  have hβ := FF.hN 7 (x 6) (x 5)
  simp only [hβ] at c2
  rw [z5] at hα
  rw [z6, z5] at hβ
  rw [z2, z5] at c2
  have hk := F.S.kp_pos
  have eβ : ⟪FF.N 7, x 6 - x 5⟫ = 0 := by linarith
  rw [eβ] at c2
  have eδ : ⟪FF.N 7, F.e⟫ = 0 := by
    have : F.S.kp * ⟪FF.N 7, F.e⟫ = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hk.ne'
    · exact h
  have eα : ⟪FF.N 7, x 1 - x 5⟫ = FF.f 7 (x 1) := by linarith
  refine nrm_of (s := F.S.kp) (m := -FF.f 7 (x 1)) hk (by linarith) ?_ ?_ ?_
  · rw [eα]; ring
  · rw [eβ]; ring
  · rw [eδ]; ring

end Frame20
end Minimality.CaseC20


/-!
# G0b: shared tools for the I_MC generic leaves

* `IMC F`: the I_MC pair of equations (lines 277/278/280/282 of `CaseC20Face`).
* `par`: the parametrization `a11 = r hm sm`, `a12 = r den`, `hp gg = r sm c`, `a22 = r B`, `B >= den`.
* `Dd`: `hp * dep = r * Dd` (polynomial depths), `dep_lt` to compare.
* RobUni helpers (negation, scaling, 5-cycle shapes).
* Facing lemmas `seg_pos/neg`, `fpos/fneg`; `line_view`: the line view as `fvC (nu w)`.
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.H20S

/-- `RobUni` is preserved by multiplication by a positive constant. -/
theorem robUni_mul_pos {k : ℕ} {z : ZMod k → ℝ} (h : RobUni z) {m : ℝ} (hm : 0 < m) :
    RobUni (fun i => m * z i) := by
  intro B b c d hb hbc hcd hd hh
  apply h B b c d hb hbc hcd hd
  simp only at hh
  obtain ⟨h1, h2, h3, h4⟩ := hh
  exact ⟨le_of_mul_le_mul_left h1 hm, le_of_mul_le_mul_left h2 hm,
    le_of_mul_le_mul_left h3 hm, le_of_mul_le_mul_left h4 hm⟩

/-- `RobUni` is preserved by multiplication by any nonzero constant. -/
theorem robUni_mul {k : ℕ} {z : ZMod k → ℝ} (h : RobUni z) {m : ℝ} (hm : m ≠ 0) :
    RobUni (fun i => m * z i) := by
  rcases lt_or_gt_of_ne hm with hn | hp
  · have := robUni_neg (robUni_mul_pos h (neg_pos.2 hn))
    convert this using 2 with i
    ring
  · exact robUni_mul_pos h hp

/-- Five-cycle shape for `L4` (positions: `z1 >= z2 > z3 > z4`, `z1 > z0`). -/
theorem robUni5_L4 {z : ZMod 5 → ℝ} (h12 : z 2 ≤ z 1) (h23 : z 3 < z 2) (h34 : z 4 < z 3)
    (h01 : z 0 < z 1) : RobUni z := by robuni5

/-- Five-cycle shape for `L5` (`z1 > z0 > z4 > z3`, `z1 > z2 >= z3`). -/
theorem robUni5_L5 {z : ZMod 5 → ℝ} (h01 : z 0 < z 1) (h40 : z 4 < z 0) (h34 : z 3 < z 4)
    (h21 : z 2 < z 1) (h32 : z 3 ≤ z 2) : RobUni z := by robuni5

/-- Five-cycle shape for `L6` (`z1 > z2 > z3`, `z1 > z0 > z4`). -/
theorem robUni5_L6 {z : ZMod 5 → ℝ} (h21 : z 2 < z 1) (h32 : z 3 < z 2) (h01 : z 0 < z 1)
    (h40 : z 4 < z 0) : RobUni z := by robuni5

/-- Five-cycle shape for `L7` (`z0 = z1 > z2 > z3`, `z1 > z4`). -/
theorem robUni5_L7 {z : ZMod 5 → ℝ} (h01 : z 0 = z 1) (h21 : z 2 < z 1) (h32 : z 3 < z 2)
    (h41 : z 4 < z 1) : RobUni z := by robuni5

end Minimality.H20S


/-!
# G0c: the I_MC equations, the parametrization, facings and line views
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x) (FF : S0xFac 8 h20s_S x)

/-- **The I_MC pair of equations** (the disjunct of `CaseC20Face`, lines 277/278/280/282), copied
verbatim: `(1-tm)(1-tp) a11 = hm hp gg` and `sm (1-tm)(1-tp) a12 = hp den gg`. -/
def IMC : Prop :=
  ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg = 0)

/-- On I_MC the Gram entries are `a11 = r hm sm`, `a12 = r den`, `hp gg = r sm c`, `a22 = r B`
with `r > 0`, `den > 0` and `B >= den` (`den = hm + km tm - km`, `c = (1-tm)(1-tp)`). -/
lemma par_aux (hI : F.IMC) : ∃ r B : ℝ, 0 < r ∧ 0 < F.S.hm + F.S.km * F.S.tm - F.S.km ∧
    F.S.hm + F.S.km * F.S.tm - F.S.km ≤ B ∧ F.a11 = r * (F.S.hm * F.S.sm) ∧
    F.a12 = r * (F.S.hm + F.S.km * F.S.tm - F.S.km) ∧
    F.S.hp * F.gg = r * (F.S.sm * ((1 - F.S.tm) * (1 - F.S.tp))) ∧ F.a22 = r * B := by
  obtain ⟨h1, h2⟩ := hI
  have ha := F.A12_pos; have hg := F.g_pos
  have ha' : F.a12 ≠ 0 := ha.ne'
  have hsm := F.S.sm_pos; have hsm1 := F.S.sm_lt
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos
  have ht := F.S.tm_lt; have ht2 := F.S.tp_lt
  have hc : 0 < (1 - F.S.tm) * (1 - F.S.tp) := mul_pos (by linarith) (by linarith)
  have e1 : F.S.hp * (F.S.hm + F.S.km * F.S.tm - F.S.km) * F.gg =
      F.S.sm * ((1 - F.S.tm) * (1 - F.S.tp)) * F.a12 := by linear_combination h1
  have e2 : (1 - F.S.tm) * (1 - F.S.tp) * F.a11 = F.S.hm * F.S.hp * F.gg := by
    linear_combination h2
  have hden : 0 < F.S.hm + F.S.km * F.S.tm - F.S.km := by
    by_contra hneg
    push Not at hneg
    have : F.S.hp * (F.S.hm + F.S.km * F.S.tm - F.S.km) * F.gg ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hhp.le hneg) hg.le
    have : 0 < F.S.sm * ((1 - F.S.tm) * (1 - F.S.tp)) * F.a12 := mul_pos (mul_pos hsm hc) ha
    linarith
  have e3 : F.a11 * (F.S.hm + F.S.km * F.S.tm - F.S.km) = F.a12 * (F.S.hm * F.S.sm) := by
    have : (1 - F.S.tm) * (1 - F.S.tp) * (F.a11 * (F.S.hm + F.S.km * F.S.tm - F.S.km) -
        F.a12 * (F.S.hm * F.S.sm)) = 0 := by
      linear_combination (F.S.hm + F.S.km * F.S.tm - F.S.km) * e2 + F.S.hm * e1
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hc.ne'
    · linarith
  have hr : 0 < F.a12 / (F.S.hm + F.S.km * F.S.tm - F.S.km) := div_pos ha hden
  refine ⟨F.a12 / (F.S.hm + F.S.km * F.S.tm - F.S.km),
    F.a22 / (F.a12 / (F.S.hm + F.S.km * F.S.tm - F.S.km)), hr, hden, ?_, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hr]
    have := F.A12_le_A22
    have h' : F.a12 ≤ F.a22 := this
    have : F.a12 / (F.S.hm + F.S.km * F.S.tm - F.S.km) * (F.S.hm + F.S.km * F.S.tm - F.S.km) =
        F.a12 := by field_simp
    nlinarith
  · field_simp; linarith
  · field_simp
  · field_simp
    nlinarith [e1]
  · field_simp

/-- The polynomial depths: `hp * dep q j = r * Dd B q j`. -/
noncomputable def Dd (B : ℝ) (q : C3) : Fin 7 → ℝ := fun j =>
  match j with
  | 0 => F.S.hp * (F.S.hm * F.S.sm * (F.S.tp * q.x) + (F.S.hm + F.S.km * F.S.tm - F.S.km) * (F.S.tp * q.y))
      + F.S.sm * ((1 - F.S.tm) * (1 - F.S.tp)) * (F.S.hp * q.z)
  | 1 => F.S.hp * (F.S.hm * F.S.sm * q.x + (F.S.hm + F.S.km * F.S.tm - F.S.km) * q.y)
  | 2 => F.S.hp * ((F.S.hm + F.S.km * F.S.tm - F.S.km) * (F.S.sp * q.x) + B * (F.S.sp * q.y))
      + F.S.sm * ((1 - F.S.tm) * (1 - F.S.tp)) * (F.S.kp * q.z)
  | 3 => F.S.hp * (F.S.hm * F.S.sm * (F.S.tm * q.x) + (F.S.hm + F.S.km * F.S.tm - F.S.km) * (F.S.tm * q.y))
      - F.S.sm * ((1 - F.S.tm) * (1 - F.S.tp)) * (F.S.hm * q.z)
  | 4 => F.S.hp * ((F.S.hm + F.S.km * F.S.tm - F.S.km) * (F.S.sm * q.x) + B * (F.S.sm * q.y))
      - F.S.sm * ((1 - F.S.tm) * (1 - F.S.tp)) * (F.S.km * q.z)
  | 5 => 0
  | 6 => F.S.hp * ((F.S.hm + F.S.km * F.S.tm - F.S.km) * q.x + B * q.y)

lemma hp_dep {r B : ℝ} (h11 : F.a11 = r * (F.S.hm * F.S.sm))
    (h12 : F.a12 = r * (F.S.hm + F.S.km * F.S.tm - F.S.km))
    (hg : F.S.hp * F.gg = r * (F.S.sm * ((1 - F.S.tm) * (1 - F.S.tp)))) (h22 : F.a22 = r * B)
    (q : C3) (j : Fin 7) : F.S.hp * F.dep q j = r * F.Dd B q j := by
  fin_cases j
  · show F.S.hp * F.dep q 0 = r * F.Dd B q 0
    simp only [dep_0, h11, h12, Dd]
    linear_combination (F.S.hp * q.z) * hg
  · show F.S.hp * F.dep q 1 = r * F.Dd B q 1
    simp only [dep_1, h11, h12, Dd]; ring
  · show F.S.hp * F.dep q 2 = r * F.Dd B q 2
    simp only [dep_2, h12, h22, Dd]
    linear_combination (F.S.kp * q.z) * hg
  · show F.S.hp * F.dep q 3 = r * F.Dd B q 3
    simp only [dep_3, h11, h12, Dd]
    linear_combination (-(F.S.hm * q.z)) * hg
  · show F.S.hp * F.dep q 4 = r * F.Dd B q 4
    simp only [dep_4, h12, h22, Dd]
    linear_combination (-(F.S.km * q.z)) * hg
  · show F.S.hp * F.dep q 5 = r * F.Dd B q 5
    simp only [dep_5, Dd]; ring
  · show F.S.hp * F.dep q 6 = r * F.Dd B q 6
    simp only [dep_6, h12, h22, Dd]; ring


/-- Bundled I_MC parametrization. -/
structure Par (r B : ℝ) : Prop where
  hr : 0 < r
  hden : 0 < F.S.hm + F.S.km * F.S.tm - F.S.km
  hB : F.S.hm + F.S.km * F.S.tm - F.S.km ≤ B
  h11 : F.a11 = r * (F.S.hm * F.S.sm)
  h12 : F.a12 = r * (F.S.hm + F.S.km * F.S.tm - F.S.km)
  hg : F.S.hp * F.gg = r * (F.S.sm * ((1 - F.S.tm) * (1 - F.S.tp)))
  h22 : F.a22 = r * B

lemma par (hI : F.IMC) : ∃ r B : ℝ, F.Par r B := by
  obtain ⟨r, B, a, b, c, d, e, f, g⟩ := F.par_aux hI
  exact ⟨r, B, ⟨a, b, c, d, e, f, g⟩⟩

/-- A comparison of polynomial depths gives the comparison of the true depths. -/
lemma Par.dep_lt {r B : ℝ} (P : F.Par r B) (q : C3) {i j : Fin 7}
    (h : F.Dd B q i < F.Dd B q j) : F.dep q i < F.dep q j := by
  have hp := F.S.hp_pos
  have a := F.hp_dep P.h11 P.h12 P.hg P.h22 q i
  have b := F.hp_dep P.h11 P.h12 P.hg P.h22 q j
  by_contra hc
  push Not at hc
  have h1 : F.S.hp * F.dep q j ≤ F.S.hp * F.dep q i := mul_le_mul_of_nonneg_left hc hp.le
  rw [a, b] at h1
  have := mul_lt_mul_of_pos_left h P.hr
  linarith

/-- Equality of polynomial depths gives equality of the true depths. -/
lemma Par.dep_eq {r B : ℝ} (P : F.Par r B) (q : C3) {i j : Fin 7}
    (h : F.Dd B q i = F.Dd B q j) : F.dep q i = F.dep q j := by
  have hp := F.S.hp_pos
  have a := F.hp_dep P.h11 P.h12 P.hg P.h22 q i
  have b := F.hp_dep P.h11 P.h12 P.hg P.h22 q j
  have : F.S.hp * F.dep q i = F.S.hp * F.dep q j := by rw [a, b, h]
  exact mul_left_cancel₀ hp.ne' this

/-- Segment view `x j - x i = fvC q` from the frame coordinates of the endpoints. -/
lemma seg_vec (i j : Fin 7) (q : C3) (hq : q = (F.toFrame7.ptC j).sub (F.toFrame7.ptC i)) :
    x j - x i = F.toFrame7.fvC q := by
  rw [hq]; exact F.toFrame7.x_sub j i

end Frame20
end Minimality.CaseC20

namespace Minimality.CaseC20
namespace Frame20
section Imp
variable {x : Fin 7 → ℝ³} {F : Frame20 x} {FF : S0xFac 8 h20s_S x}

/-- A segment-view facing is a positive multiple of the coordinate form. -/
lemma Nrm.seg_val {t : Fin 8} {a b d : ℝ} (h : F.Nrm FF t a b d) {i j : Fin 7} {q : C3}
    (hq : x j - x i = F.toFrame7.fvC q) :
    ∃ l : ℝ, 0 < l ∧ FF.f t (x j) - FF.f t (x i) = l * (q.x * a + q.y * b + q.z * d) := by
  obtain ⟨l, hl, e1, e2, e3⟩ := h
  refine ⟨l, hl, ?_⟩
  rw [FF.hN t (x j) (x i), hq, F.inner_fvC_right, e1, e2, e3]; ring

lemma Nrm.seg_pos {t : Fin 8} {a b d : ℝ} (h : F.Nrm FF t a b d) {i j : Fin 7} {q : C3}
    (hq : x j - x i = F.toFrame7.fvC q) (hp : 0 < q.x * a + q.y * b + q.z * d) :
    0 < FF.f t (x j) - FF.f t (x i) := by
  obtain ⟨l, hl, e⟩ := h.seg_val hq
  rw [e]; exact mul_pos hl hp

lemma Nrm.seg_neg {t : Fin 8} {a b d : ℝ} (h : F.Nrm FF t a b d) {i j : Fin 7} {q : C3}
    (hq : x j - x i = F.toFrame7.fvC q) (hp : q.x * a + q.y * b + q.z * d < 0) :
    FF.f t (x j) - FF.f t (x i) < 0 := by
  obtain ⟨l, hl, e⟩ := h.seg_val hq
  rw [e]; exact mul_neg_of_pos_of_neg hl hp

/-- A line-view facing is `nu * l * (w . n)` with `l > 0`. -/
lemma Nrm.line_val {t : Fin 8} {a b d : ℝ} (h : F.Nrm FF t a b d) (ν wx wy wz : ℝ) :
    ∃ l : ℝ, 0 < l ∧
      ⟪FF.N t, F.toFrame7.fvC ⟨ν * wx, ν * wy, ν * wz⟩⟫ = ν * (l * (wx * a + wy * b + wz * d)) := by
  obtain ⟨l, hl, e1, e2, e3⟩ := h
  refine ⟨l, hl, ?_⟩
  rw [F.inner_fvC_right, e1, e2, e3]; ring

lemma Nrm.fpos {t : Fin 8} {a b d : ℝ} (h : F.Nrm FF t a b d) {ν wx wy wz : ℝ} (hν : 0 < ν)
    (hw : 0 < wx * a + wy * b + wz * d) :
    0 < ⟪FF.N t, F.toFrame7.fvC ⟨ν * wx, ν * wy, ν * wz⟩⟫ := by
  obtain ⟨l, hl, e⟩ := h.line_val ν wx wy wz
  rw [e]; exact mul_pos hν (mul_pos hl hw)

lemma Nrm.fneg {t : Fin 8} {a b d : ℝ} (h : F.Nrm FF t a b d) {ν wx wy wz : ℝ} (hν : 0 < ν)
    (hw : wx * a + wy * b + wz * d < 0) :
    ⟪FF.N t, F.toFrame7.fvC ⟨ν * wx, ν * wy, ν * wz⟩⟫ < 0 := by
  obtain ⟨l, hl, e⟩ := h.line_val ν wx wy wz
  rw [e]; exact mul_neg_of_pos_of_neg hν (mul_neg_of_pos_of_neg hl hw)

lemma Nrm.fpos' {t : Fin 8} {a b d : ℝ} (h : F.Nrm FF t a b d) {ν wx wy wz : ℝ} (hν : ν < 0)
    (hw : wx * a + wy * b + wz * d < 0) :
    0 < ⟪FF.N t, F.toFrame7.fvC ⟨ν * wx, ν * wy, ν * wz⟩⟫ := by
  obtain ⟨l, hl, e⟩ := h.line_val ν wx wy wz
  rw [e]; exact mul_pos_of_neg_of_neg hν (mul_neg_of_pos_of_neg hl hw)

lemma Nrm.fneg' {t : Fin 8} {a b d : ℝ} (h : F.Nrm FF t a b d) {ν wx wy wz : ℝ} (hν : ν < 0)
    (hw : 0 < wx * a + wy * b + wz * d) :
    ⟪FF.N t, F.toFrame7.fvC ⟨ν * wx, ν * wy, ν * wz⟩⟫ < 0 := by
  obtain ⟨l, hl, e⟩ := h.line_val ν wx wy wz
  rw [e]; exact mul_neg_of_neg_of_pos hν (mul_pos hl hw)

end Imp
end Frame20
end Minimality.CaseC20

namespace Minimality.CaseC20
namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x) (FF : S0xFac 8 h20s_S x)

/-- Robust unimodality of the depths of `w` gives it for the depths along `nu * w`. -/
lemma robUni_line {k : ℕ} (c : ZMod k → Fin 7) (w : C3) {ν : ℝ} (hν : ν ≠ 0)
    (h : RobUni (fun a => F.dep w (c a))) :
    RobUni (fun a => ⟪x (c a), F.toFrame7.fvC ⟨ν * w.x, ν * w.y, ν * w.z⟩⟫) := by
  refine F.robUni_of_dep c _ ?_
  have := robUni_mul h hν
  convert this using 2 with a
  exact F.dep_scale ν w.x w.y w.z (c a)

/-- A cross product is nonzero if some pairing minor against `p, r` is. -/
lemma cross_ne_zero' (a b p r : ℝ³) (h : ⟪a, p⟫ * ⟪b, r⟫ ≠ ⟪a, r⟫ * ⟪b, p⟫) : cross a b ≠ 0 := by
  intro h0
  have := inner_cross_cross a b p r
  rw [h0] at this
  simp only [inner_zero_left] at this
  exact h (by linarith)

/-- **Line view.**  If the coordinate normals of facets `X`, `Y` have cross product `kappa * w`
(`kappa != 0`, `w != 0`), then `N_X x N_Y = fvC (nu w)` for some `nu != 0`. -/
lemma line_view (X Y : Fin 8) {aX bX dX aY bY dY wx wy wz κ : ℝ}
    (hX : F.Nrm FF X aX bX dX) (hY : F.Nrm FF Y aY bY dY) (hκ : κ ≠ 0)
    (hw : wx ≠ 0 ∨ wy ≠ 0 ∨ wz ≠ 0)
    (h1 : bX * dY - dX * bY = κ * wx) (h2 : dX * aY - aX * dY = κ * wy)
    (h3 : aX * bY - bX * aY = κ * wz) :
    ∃ ν : ℝ, ν ≠ 0 ∧ cross (FF.N X) (FF.N Y) = F.toFrame7.fvC ⟨ν * wx, ν * wy, ν * wz⟩ := by
  obtain ⟨lX, hlX, X1, X2, X3⟩ := hX
  obtain ⟨lY, hlY, Y1, Y2, Y3⟩ := hY
  have hcr : cross (FF.N X) (FF.N Y) ≠ 0 := by
    have hll : lX * lY ≠ 0 := (mul_pos hlX hlY).ne'
    rcases hw with hw | hw | hw
    · refine cross_ne_zero' _ _ (x 6 - x 5) F.e ?_
      rw [X2, X3, Y2, Y3]
      intro h
      have : (lX * lY * κ) * wx = 0 := by linear_combination h - (lX * lY) * h1
      exact mul_ne_zero (mul_ne_zero hll hκ) hw this
    · refine cross_ne_zero' _ _ F.e (x 1 - x 5) ?_
      rw [X3, X1, Y3, Y1]
      intro h
      have : (lX * lY * κ) * wy = 0 := by linear_combination h - (lX * lY) * h2
      exact mul_ne_zero (mul_ne_zero hll hκ) hw this
    · refine cross_ne_zero' _ _ (x 1 - x 5) (x 6 - x 5) ?_
      rw [X1, X2, Y1, Y2]
      intro h
      have : (lX * lY * κ) * wz = 0 := by linear_combination h - (lX * lY) * h3
      exact mul_ne_zero (mul_ne_zero hll hκ) hw this
  obtain ⟨q, hq, e1, e2⟩ := F.cross_coords (FF.N X) (FF.N Y)
  rw [X1, X2, X3] at e1
  rw [Y1, Y2, Y3] at e2
  obtain ⟨qx, qy, qz⟩ := q
  simp only at e1 e2
  have o1 : qx * aX + qy * bX + qz * dX = 0 := by
    have : lX * (qx * aX + qy * bX + qz * dX) = 0 := by linear_combination e1
    exact (mul_eq_zero.1 this).resolve_left hlX.ne'
  have o2 : qx * aY + qy * bY + qz * dY = 0 := by
    have : lY * (qx * aY + qy * bY + qz * dY) = 0 := by linear_combination e2
    exact (mul_eq_zero.1 this).resolve_left hlY.ne'
  have c1 : qy * wz = qz * wy := by
    have : κ * (qy * wz - qz * wy) = 0 := by
      linear_combination (-qy) * h3 + qz * h2 + aX * o2 - aY * o1
    have := (mul_eq_zero.1 this).resolve_left hκ
    linarith
  have c2 : qz * wx = qx * wz := by
    have : κ * (qz * wx - qx * wz) = 0 := by
      linear_combination (-qz) * h1 + qx * h3 + bX * o2 - bY * o1
    have := (mul_eq_zero.1 this).resolve_left hκ
    linarith
  have c3 : qx * wy = qy * wx := by
    have : κ * (qx * wy - qy * wx) = 0 := by
      linear_combination (-qx) * h2 + qy * h1 + dX * o2 - dY * o1
    have := (mul_eq_zero.1 this).resolve_left hκ
    linarith
  have hex : ∃ ν : ℝ, qx = ν * wx ∧ qy = ν * wy ∧ qz = ν * wz := by
    rcases hw with hw | hw | hw
    · exact ⟨qx / wx, by field_simp, by field_simp; linarith, by field_simp; linarith⟩
    · exact ⟨qy / wy, by field_simp; linarith, by field_simp, by field_simp; linarith⟩
    · exact ⟨qz / wz, by field_simp; linarith, by field_simp; linarith, by field_simp⟩
  obtain ⟨ν, hx', hy', hz'⟩ := hex
  refine ⟨ν, ?_, ?_⟩
  · intro hν
    apply hcr
    rw [hq]
    simp only [hx', hy', hz', hν, zero_mul, Frame7.fvC, zero_smul, add_zero]
  · rw [hq, hx', hy', hz']

end Frame20
end Minimality.CaseC20


/-!
# G0d: small shared facts for the I_MC leaves (positivity of the roofs, `1 - t`, ...)
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- From `0 < a` and `0 < a * b` get `0 < b`. -/
lemma pos_of_mul_pos' {a b : ℝ} (ha : 0 < a) (h : 0 < a * b) : 0 < b :=
  lt_of_not_ge fun hb => absurd h (not_lt.2 (mul_nonpos_of_nonneg_of_nonpos ha.le hb))

/-- Wrapper: compare true depths from the polynomial depths. -/
lemma dlt {r B : ℝ} (P : F.Par r B) (q : C3) {i j : Fin 7} (h : F.Dd B q i < F.Dd B q j) :
    F.dep q i < F.dep q j := Par.dep_lt F P q h

/-- Wrapper: equal true depths from equal polynomial depths. -/
lemma deq {r B : ℝ} (P : F.Par r B) (q : C3) {i j : Fin 7} (h : F.Dd B q i = F.Dd B q j) :
    F.dep q i = F.dep q j := Par.dep_eq F P q h

/-- The upper roof, `roof = hp (1-sp) - kp (1-tp) > 0`. -/
lemma roof_pos : 0 < (F.S.hp*(1-F.S.sp)-F.S.kp*(1-F.S.tp)) := by linarith [F.S.roof_p']

/-- The lower roof, `lroof = km (1-tm) - hm (1-sm) > 0`. -/
lemma lroof_pos : 0 < (F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm)) := by linarith [F.S.roof_m']

lemma one_sub_tp_pos : 0 < 1 - F.S.tp := by linarith [F.S.tp_lt]
lemma one_sub_tm_pos : 0 < 1 - F.S.tm := by linarith [F.S.tm_lt]
lemma one_sub_sp_pos : 0 < 1 - F.S.sp := by linarith [F.S.sp_lt]
lemma one_sub_sm_pos : 0 < 1 - F.S.sm := by linarith [F.S.sm_lt]

end Frame20
end Minimality.CaseC20

