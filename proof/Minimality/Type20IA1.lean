module

public import Minimality.Type20IV

@[expose] public section

/-!
# Type 20, item I_A (part 1): rescaling, the leaf K, m1', m2', shape lemmas
-/

section


/-!
# I_A, step 0: the rescaled frame

For `r > 0`, replacing `e` by `r e` keeps all the depths, the metric entries `a11 a12 a22` and the
point set, and divides the heights `hp hm kp km` by `r`.  On `A1 = 0` this gives `hm = tm`, `hp = 1 - tp`.
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20

/-- The shape with all heights divided by `r > 0`. -/
noncomputable def Shape20.rescale (S : Shape20) (r : ℝ) (hr : 0 < r) : Shape20 where
  tp := S.tp
  tm := S.tm
  sp := S.sp
  sm := S.sm
  hp := S.hp / r
  hm := S.hm / r
  kp := S.kp / r
  km := S.km / r
  tp_pos := S.tp_pos
  tp_lt := S.tp_lt
  tm_pos := S.tm_pos
  tm_lt := S.tm_lt
  sp_pos := S.sp_pos
  sp_lt := S.sp_lt
  sm_pos := S.sm_pos
  sm_lt := S.sm_lt
  hp_pos := div_pos S.hp_pos hr
  hm_pos := div_pos S.hm_pos hr
  kp_pos := div_pos S.kp_pos hr
  km_pos := div_pos S.km_pos hr
  roof_p := by
    rw [div_right_comm, div_right_comm S.hp]
    exact div_lt_div_of_pos_right S.roof_p hr
  roof_m := by
    rw [div_right_comm, div_right_comm S.km]
    exact div_lt_div_of_pos_right S.roof_m hr

namespace Frame20
variable {x : Fin 7 → ℝ³}

/-- **The rescaled frame**: the same points and metric entries, with `e` replaced by `r e`. -/
noncomputable def rescale (F : Frame20 x) (r : ℝ) (hr : 0 < r) : Frame20 x where
  e := r • F.e
  S := F.S.rescale r hr
  e_ne := smul_ne_zero hr.ne' F.e_ne
  indep := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : g 0 • (x 1 - x 5) + g 1 • (x 6 - x 5) + (g 2 * r) • F.e = 0 := by
      simpa [Fin.sum_univ_three, mul_smul] using hg
    have h := Fintype.linearIndependent_iff.mp F.indep ![g 0, g 1, g 2 * r] (by
      simpa [Fin.sum_univ_three] using hg')
    intro i
    fin_cases i
    · simpa using h 0
    · simpa using h 1
    · have := h 2
      simp only [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at this
      simpa [hr.ne'] using this
  x0_eq := by
    rw [F.x0_eq]; show _ = _ + F.S.tp • _ + (F.S.hp / r) • (r • F.e)
    rw [smul_smul, div_mul_cancel₀ _ hr.ne']
  x3_eq := by
    rw [F.x3_eq]; show _ = _ + F.S.tm • _ - (F.S.hm / r) • (r • F.e)
    rw [smul_smul, div_mul_cancel₀ _ hr.ne']
  x2_eq := by
    rw [F.x2_eq]; show _ = _ + F.S.sp • _ + (F.S.kp / r) • (r • F.e)
    rw [smul_smul, div_mul_cancel₀ _ hr.ne']
  x4_eq := by
    rw [F.x4_eq]; show _ = _ + F.S.sm • _ - (F.S.km / r) • (r • F.e)
    rw [smul_smul, div_mul_cancel₀ _ hr.ne']
  inner_u1_e := by rw [real_inner_smul_right, F.inner_u1_e, mul_zero]
  inner_u2_e := by rw [real_inner_smul_right, F.inner_u2_e, mul_zero]
  A12_pos := F.A12_pos
  A12_le_A11 := F.A12_le_A11
  A12_le_A22 := F.A12_le_A22

variable (F : Frame20 x) (r : ℝ) (hr : 0 < r)

lemma rescale_S : (F.rescale r hr).S = F.S.rescale r hr := rfl
lemma rescale_a11 : (F.rescale r hr).a11 = F.a11 := rfl
lemma rescale_a12 : (F.rescale r hr).a12 = F.a12 := rfl
lemma rescale_a22 : (F.rescale r hr).a22 = F.a22 := rfl

end Frame20
end Minimality.CaseC20

end

section


/-!
# I_A: shared helpers (lex helpers, RobUni shapes H1-H9, shape/metric lemmas S1-S5 in the normal form)

Normal form: `hm = tm`, `hp = 1 - tp` (hypotheses `hm`, `hp` below).
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.H20S

/-- H1: `z0 < z1 < z2 < z3` on a 5-cycle is robustly unimodal. -/
theorem robUni5_H1 {z : ZMod 5 → ℝ} (h01 : z 0 < z 1) (h12 : z 1 < z 2) (h23 : z 2 < z 3) :
    RobUni z := by robuni5

/-- H2: `z1 < z0`, `z2 < z3 < z4`, `z2 < z0`. -/
theorem robUni5_H2 {z : ZMod 5 → ℝ} (h10 : z 1 < z 0) (h23 : z 2 < z 3) (h34 : z 3 < z 4)
    (h20 : z 2 < z 0) : RobUni z := by robuni5

/-- H3: `z0 < z1 < z2`, `z4 <= z0`, `z4 < z3`. -/
theorem robUni5_H3 {z : ZMod 5 → ℝ} (h01 : z 0 < z 1) (h12 : z 1 < z 2) (h40 : z 4 ≤ z 0)
    (h43 : z 4 < z 3) : RobUni z := by robuni5

/-- H4: `z0 < z1`, `z4 < z3`, and `z2` above `z1` or above `z3`. -/
theorem robUni5_H4 {z : ZMod 5 → ℝ} (h01 : z 0 < z 1) (h43 : z 4 < z 3)
    (h : z 1 < z 2 ∨ z 3 < z 2) : RobUni z := by
  rcases h with h | h <;> robuni5

/-- H5: `z0 < z4 < z3` and `z1 < z2`. -/
theorem robUni5_H5 {z : ZMod 5 → ℝ} (h04 : z 0 < z 4) (h43 : z 4 < z 3) (h12 : z 1 < z 2) :
    RobUni z := by robuni5

/-- H7: `z4 < z0 < z1`, `z2 < z1`, `z3 < z4`. -/
theorem robUni5_H7 {z : ZMod 5 → ℝ} (h40 : z 4 < z 0) (h01 : z 0 < z 1) (h21 : z 2 < z 1)
    (h34 : z 3 < z 4) : RobUni z := by robuni5

/-- H8: `z1 < z0 < z4` and `z2 < z3`. -/
theorem robUni5_H8 {z : ZMod 5 → ℝ} (h10 : z 1 < z 0) (h23 : z 2 < z 3) (h04 : z 0 < z 4) :
    RobUni z := by robuni5

/-- H9: `z2 < z1`, `z3 < z0`, `z3 < z4`, and `z0` above `z1` or above `z4`. -/
theorem robUni5_H9 {z : ZMod 5 → ℝ} (h21 : z 2 < z 1) (h30 : z 3 < z 0) (h34 : z 3 < z 4)
    (h : z 1 < z 0 ∨ z 4 < z 0) : RobUni z := by
  rcases h with h | h <;> robuni5

end Minimality.H20S

namespace Minimality.CaseC20
namespace IAT
open IVT
variable {x : Fin 7 → ℝ³} (F : Frame20 x)


/-- Normal form: `hm = tm`, `hp = 1 - tp`. -/
def NF (S : Shape20) : Prop := S.hm = S.tm ∧ S.hp = 1 - S.tp

/-- The upper roof in the normal form: `kp < 1 - sp`. -/
lemma roofP_n (S : Shape20) (h : NF S) : S.kp < 1 - S.sp := by
  have := S.roof_p'; rw [h.2] at this
  have tp1 := S.tp1
  nlinarith

/-- The lower roof in the normal form: `rm > 0`. -/
lemma rm_pos (S : Shape20) (h : NF S) : 0 < (S.km*(1-S.tm)-S.tm*(1-S.sm)) := by
  have := S.roof_m'; rw [h.1] at this; linarith

end IAT
end Minimality.CaseC20

end

section


/-!
# I_A, leaf K (tilt, `u0 = (1,0,-1)`): needs only `Phi < 0`.  Closes m1'.
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace IAT
open IVT
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

def k_pat : Fin 8 → Bool := ![true, false, true, true, false, false, true, false]
def k_c : ZMod 5 → Fin 7 := ![1, 0, 5, 4, 6]
theorem k_cyc : S0xCycOK h20s_S k_c k_pat := by decide
theorem k_inj : Function.Injective k_c := by decide

/-- K: the view `x1 - x0` (frame vector `(1,0,-1)` after the rescale) tilted by `x5 - x6`; the depths
`z1, z0, z5, z4, z6` are robustly unimodal as soon as `z4 < z6`, which is `Phi < 0`.  Uses neither
`a12 = a11` nor any bound on `a22`. -/
theorem ia_K (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hN : NF F.S) (hPhi : (F.gg*F.S.km-F.a12*(1-F.S.sm)) < 0) : IsRupert (univ.image x) := by
  have sm0 := F.S.sm_pos; have sm1 := F.S.sm1; have tm0 := F.S.tm_pos; have tp1 := F.S.tp1
  have tm1 := F.S.tm1; have sp0 := F.S.sp_pos; have kp0 := F.S.kp_pos; have km0 := F.S.km_pos
  have ha : 0 < F.a12 := F.A12_pos; have hg : 0 < F.gg := F.g_pos
  have h11 : F.a12 ≤ F.a11 := F.A12_le_A11
  have rp := roofP_n F.S hN
  have uA : nf F.S ⟨1, 0, -1⟩ 0 = F.S.sm := by simp only [nf_A, hN.1]; ring
  have uB : nf F.S ⟨1, 0, -1⟩ 1 = -F.S.sp := by simp only [nf_B, hN.2]; ring
  have uC : nf F.S ⟨1, 0, -1⟩ 2 = 0 := by simp only [nf_C]; ring
  have uD : nf F.S ⟨1, 0, -1⟩ 3 = 0 := by simp only [nf_D, hN.1]; ring
  have uE : nf F.S ⟨1, 0, -1⟩ 4 = 0 := by simp only [nf_E, hN.2]; ring
  have uF : nf F.S ⟨1, 0, -1⟩ 5 = F.S.kp + F.S.sp - 1 := by simp only [nf_F, hN.2]; ring
  have uG : nf F.S ⟨1, 0, -1⟩ 6 = F.S.km + 1 - F.S.sm := by simp only [nf_G]; ring
  have uH : nf F.S ⟨1, 0, -1⟩ 7 = -F.S.kp := by simp only [nf_H]; ring
  have vC : nf F.S ⟨0, -1, 0⟩ 2 = F.S.tm := by simp only [nf_C, hN.1, hN.2]; ring
  have vD : nf F.S ⟨0, -1, 0⟩ 3 = F.S.tm * F.S.km := by simp only [nf_D]; ring
  have vE : nf F.S ⟨0, -1, 0⟩ 4 = -(1-F.S.tp) := by simp only [nf_E, hN.2]; ring
  refine leaf_of_view F (h20s_fac hR) hx (by norm_num) k_inj k_cyc ⟨1, 0, -1⟩ ⟨0, -1, 0⟩ 0
    (by rw [uA]; exact sm0.ne') ?_ ?_
  · intro t; fin_cases t
    · exact ⟨fun _ => lp_pos (eq_pos uA sm0), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (eq_neg uB (by linarith))⟩
    · exact ⟨fun _ => lp_zero uC (eq_pos vC tm0), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp_zero uD (eq_pos vD (by positivity)), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_zero uE (eq_neg vE (by linarith))⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (eq_neg uF (by linarith))⟩
    · exact ⟨fun _ => lp_pos (eq_pos uG (by linarith)), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (eq_neg uH (by linarith))⟩
  · have z0 : F.dep ⟨1, 0, -1⟩ 0 = F.a11 * F.S.tp - F.gg * (1-F.S.tp) := by
      rw [Frame20.dep_0, hN.2]; ring
    have z1 : F.dep ⟨1, 0, -1⟩ 1 = F.a11 := by rw [Frame20.dep_1]; ring
    have z4 : F.dep ⟨1, 0, -1⟩ 4 = F.a12 * F.S.sm + F.gg * F.S.km := by rw [Frame20.dep_4]; ring
    have z5 : F.dep ⟨1, 0, -1⟩ 5 = 0 := Frame20.dep_5 F _
    have z6 : F.dep ⟨1, 0, -1⟩ 6 = F.a12 := by rw [Frame20.dep_6]; ring
    refine robUni5_H2 ?_ ?_ ?_ ?_
    · show F.dep _ 0 < F.dep _ 1
      rw [z0, z1]; nlinarith
    · show F.dep _ 5 < F.dep _ 4
      rw [z5, z4]; positivity
    · show F.dep _ 4 < F.dep _ 6
      rw [z4, z6]; linarith
    · show F.dep _ 5 < F.dep _ 1
      rw [z5, z1]; linarith

end IAT
end Minimality.CaseC20

end

section


/-!
# I_A: the normal-form frame of an `A1 = 0` frame, and the consequences of leaf K for m1', m2'
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- On `A1 = 0` (line 273) the frame can be rescaled by `r = hm/tm` to the normal form `hm = tm`, `hp = 1 - tp`;
the metric entries `a11 a12 a22` are unchanged and `gg` becomes `r^2 gg`. -/
lemma exists_normal (hA : F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm = 0) :
    ∃ (F' : Frame20 x) (r : ℝ), 0 < r ∧ IAT.NF F'.S ∧ F'.a11 = F.a11 ∧ F'.a12 = F.a12 ∧
      F'.a22 = F.a22 ∧ F'.gg = r^2 * F.gg ∧ F'.S.km = F.S.km / r ∧ F'.S.hp = F.S.hp / r ∧
      F'.S.tp = F.S.tp ∧ F'.S.sm = F.S.sm := by
  have hr : 0 < F.S.hm / F.S.tm := div_pos F.S.hm_pos F.S.tm_pos
  refine ⟨F.rescale _ hr, F.S.hm / F.S.tm, hr, ⟨?_, ?_⟩, rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl⟩
  · show F.S.hm / (F.S.hm / F.S.tm) = F.S.tm
    field_simp [F.S.hm_pos.ne', F.S.tm_pos.ne']
  · show F.S.hp / (F.S.hm / F.S.tm) = 1 - F.S.tp
    have := F.S.hm_pos.ne'; have := F.S.tm_pos.ne'
    field_simp
    linarith
  · show ⟪(F.S.hm / F.S.tm) • F.e, (F.S.hm / F.S.tm) • F.e⟫ = _
    rw [real_inner_smul_left, real_inner_smul_right]
    show _ * (_ * F.gg) = _
    ring

/-- **K on an `A1 = 0` frame**: if `q = (1-tp)(1-sm) a12 - gg hp km > 0` then Rupert, with no other hypothesis
(neither `a12 = a11` nor `p <= q`).  This closes m1'. -/
theorem isRupert_of_q_pos (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hA : F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm = 0)
    (hq : 0 < (1 - F.S.tp)*(1 - F.S.sm)*F.a12 - F.gg*F.S.hp*F.S.km) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨F', r, hr, hN, h11, h12, h22, hg, hkm, hhp, htp, hsm⟩ := F.exists_normal hA
  refine IAT.ia_K F' hx hR hN ?_
  have tp1 := F.S.tp1
  have e : F'.gg * F'.S.km - F'.a12 * (1 - F'.S.sm) = - (((1 - F.S.tp)*(1 - F.S.sm)*F.a12 - F.gg*F.S.hp*F.S.km) / (1 - F.S.tp)) := by
    have hp' : F.S.hp = r * (1 - F.S.tp) := by
      have := hN.2; rw [hhp, htp] at this
      field_simp at this; linarith
    rw [hg, hkm, h12, hsm, hp']
    field_simp
    ring
  rw [e]
  have := div_pos hq tp1
  linarith

/-- **m1'** (the first disjunct of `CaseC20Special''`): `a12 = a11`, `A1 = 0`, `0 < p ≤ q` gives Rupert,
because `p ≤ q` and `0 < p` give `q > 0`. -/
theorem isRupert_m1' (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (_h1 : F.a12 = F.a11) (hA : F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm = 0)
    (hp : 0 < (1 - F.S.tp)*(1 - F.S.tm)*F.a12 - F.gg*F.S.hp*F.S.hm)
    (hpq : (1 - F.S.tp)*(1 - F.S.tm)*F.a12 - F.gg*F.S.hp*F.S.hm ≤
        (1 - F.S.tp)*(1 - F.S.sm)*F.a12 - F.gg*F.S.hp*F.S.km) :
    IsRupert (Finset.univ.image x) :=
  F.isRupert_of_q_pos hx hR hA (lt_of_lt_of_le hp hpq)

/-- **m2'** (the second disjunct of `CaseC20Special''`), the `R`-image of m1'. -/
theorem isRupert_m2' (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (h2 : F.a12 = F.a22) (hA : F.S.kp*F.S.sm - F.S.kp + F.S.km*F.S.sp = 0)
    (hp : 0 < (1 - F.S.sm)*(1 - F.S.sp)*F.a12 - F.gg*F.S.km*F.S.kp)
    (hpq : (1 - F.S.sm)*(1 - F.S.sp)*F.a12 - F.gg*F.S.km*F.S.kp ≤
        (1 - F.S.sm)*(1 - F.S.tp)*F.a12 - F.gg*F.S.km*F.S.hp) :
    IsRupert (Finset.univ.image x) := by
  have h12 : F.rFrame.a12 = F.a12 := by
    show ⟪x 6 - x 5, x 1 - x 5⟫ = _
    exact real_inner_comm _ _
  have hg : F.rFrame.gg = F.gg := by
    show ⟪-F.e, -F.e⟫ = ⟪F.e, F.e⟫
    simp
  refine rupert_of_r (F.rFrame.isRupert_m1' (hx.comp rperm_bijective.1) (realizesFaces_rperm hR) ?_ ?_ ?_ ?_)
  · exact h12.trans h2
  · simp only [rFrame_S, Shape20.swap]; linear_combination hA
  · simp only [rFrame_S, Shape20.swap, h12, hg]; linarith
  · simp only [rFrame_S, Shape20.swap, h12, hg]; linarith

end Frame20
end Minimality.CaseC20

end

section


/-!
# I_A: shape/metric lemmas S1-S5 of COVER.md in the normal form, the Std segment cells, literal macro
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.H20S

/-- S45: `s45:1346`, up `A G`, down `B C D E F H`. -/
def ias_S45 : S0xSeg 7 8 4 where
  i := 5
  j := 4
  pat := ![true, false, false, false, false, false, true, false]
  c := ![1, 3, 4, 6]

/-- S56: `s56:01462`, up `E F G`. -/
def ias_S56 : S0xSeg 7 8 5 where
  i := 5
  j := 6
  pat := ![false, false, false, false, true, true, true, false]
  c := ![0, 1, 4, 6, 2]

/-- C6 (IA): `s41:46253`, up `A B C E F G`. -/
def ias_C6 : S0xSeg 7 8 5 where
  i := 4
  j := 1
  pat := ![true, true, true, false, true, true, true, false]
  c := ![4, 6, 2, 5, 3]

theorem ias_S45_good : ias_S45.Good h20s_S := by decide
theorem ias_S56_good : ias_S56.Good h20s_S := by decide
theorem ias_C6_good : ias_C6.Good h20s_S := by decide

end Minimality.H20S

namespace Minimality.CaseC20
namespace IAT
open IVT
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- Discharges the literal part of a segment cell from named hypotheses on `nf`. -/
macro "ia_lits" : tactic => `(tactic| (intro t h0 h1; fin_cases t <;> first
  | exact absurd h0 (by decide)
  | exact absurd h1 (by decide)
  | exact ⟨fun _ => by assumption, fun h => absurd h (by decide)⟩
  | exact ⟨fun h => absurd h (by decide), fun _ => by assumption⟩))

/-- S1: if `ph <= 0` then `Phi > 0`. -/
lemma S1 (hN : NF F.S) (h : (F.a12*(1-F.S.tm)-F.gg*F.S.tm) ≤ 0) : 0 < (F.gg*F.S.km-F.a12*(1-F.S.sm)) := by
  have rm := rm_pos F.S hN
  have ha : 0 < F.a12 := F.A12_pos
  have tm0 := F.S.tm_pos; have km0 := F.S.km_pos
  have e : F.S.tm * (F.gg*F.S.km-F.a12*(1-F.S.sm)) = -F.S.km * (F.a12*(1-F.S.tm)-F.gg*F.S.tm) + F.a12 * (F.S.km*(1-F.S.tm)-F.S.tm*(1-F.S.sm)) := by ring
  have h1 : 0 < F.S.tm * (F.gg*F.S.km-F.a12*(1-F.S.sm)) := by
    rw [e]; nlinarith [mul_nonneg km0.le (neg_nonneg.2 h), mul_pos ha rm]
  exact pos_of_mul_pos_right h1 tm0.le

/-- S2: `km - (1-sm) tm > 0`. -/
lemma S2 (hN : NF F.S) : 0 < F.S.km - (1-F.S.sm)*F.S.tm := by
  have rm := rm_pos F.S hN
  have tm1 := F.S.tm1; have sm1 := F.S.sm1; have tm0 := F.S.tm_pos
  have e : (1-F.S.tm) * (F.S.km - (1-F.S.sm)*F.S.tm) = (F.S.km*(1-F.S.tm)-F.S.tm*(1-F.S.sm)) + (1-F.S.sm)*F.S.tm^2 := by ring
  have h1 : 0 < (1-F.S.tm) * (F.S.km - (1-F.S.sm)*F.S.tm) := by rw [e]; positivity
  exact pos_of_mul_pos_right h1 tm1.le

/-- S3: if `A56 <= 0` and `A06 <= 0` then `km > P`, `tp km >= P`, `B14 > 0`, `A14 > 0`. -/
lemma S3 (hN : NF F.S) (h56 : (F.S.km*(1-F.S.tm)-F.S.tm) ≤ 0) (h06 : (F.S.tm-F.S.km*(1-F.S.tm)+F.S.sm*(1-F.S.tm-F.S.tp)) ≤ 0) :
    1 - F.S.tp < F.S.km ∧ 1 - F.S.tp ≤ F.S.tp * F.S.km ∧ 0 < (F.S.tp*(F.S.kp*F.S.sm+F.S.km*F.S.sp)-F.S.sp*(1-F.S.tp)) ∧ 0 < (F.S.kp*(1-F.S.tp*F.S.sm)-(1-F.S.tp)*(1-F.S.sp)+F.S.km*F.S.tp*(1-F.S.sp)) := by
  have sm0 := F.S.sm_pos; have sm1 := F.S.sm1; have tm0 := F.S.tm_pos; have tm1 := F.S.tm1
  have tp0 := F.S.tp_pos; have tp1 := F.S.tp1; have km0 := F.S.km_pos; have kp0 := F.S.kp_pos
  have sp0 := F.S.sp_pos; have sp1 := F.S.sp1
  have j4 : F.S.sm * (F.S.tp + F.S.tm - 1) = -(F.S.km*(1-F.S.tm)-F.S.tm) - (F.S.tm-F.S.km*(1-F.S.tm)+F.S.sm*(1-F.S.tm-F.S.tp)) := by ring
  have s1 : 0 ≤ F.S.tp + F.S.tm - 1 := by
    have : 0 ≤ F.S.sm * (F.S.tp + F.S.tm - 1) := by rw [j4]; linarith
    exact nonneg_of_mul_nonneg_right this sm0
  have j5 : F.S.km*(1-F.S.tm) - (1-F.S.tp) = -(F.S.tm-F.S.km*(1-F.S.tm)+F.S.sm*(1-F.S.tm-F.S.tp)) + (1-F.S.sm)*(F.S.tp+F.S.tm-1) := by ring
  have s2 : 0 ≤ F.S.km*(1-F.S.tm) - (1-F.S.tp) := by rw [j5]; nlinarith [mul_nonneg sm1.le s1]
  have s3 : 1 - F.S.tp < F.S.km := by nlinarith [mul_pos km0 tm0]
  have j6 : F.S.tp*F.S.km - (1-F.S.tp) = (F.S.tp+F.S.tm-1)*F.S.km + (F.S.km*(1-F.S.tm) - (1-F.S.tp)) := by ring
  have s4 : 0 ≤ F.S.tp*F.S.km - (1-F.S.tp) := by rw [j6]; nlinarith [mul_nonneg s1 km0.le]
  refine ⟨s3, by linarith, ?_, ?_⟩
  · have e : (F.S.tp*(F.S.kp*F.S.sm+F.S.km*F.S.sp)-F.S.sp*(1-F.S.tp)) = F.S.tp*F.S.kp*F.S.sm + F.S.sp*(F.S.tp*F.S.km - (1-F.S.tp)) := by ring
    rw [e]; nlinarith [mul_pos (mul_pos tp0 kp0) sm0, mul_nonneg sp0.le s4]
  · have e : (F.S.kp*(1-F.S.tp*F.S.sm)-(1-F.S.tp)*(1-F.S.sp)+F.S.km*F.S.tp*(1-F.S.sp)) = F.S.kp*(1-F.S.tp*F.S.sm) + (1-F.S.sp)*(F.S.tp*F.S.km - (1-F.S.tp)) := by ring
    have : 0 < 1 - F.S.tp*F.S.sm := by nlinarith [mul_pos tp0 sm0]
    rw [e]; nlinarith [mul_pos kp0 this, mul_nonneg sp1.le s4]

/-- S4: if `Y = Z4 = 0` and `Lq >= 0` then `A06 <= 0`. -/
lemma S4 (hN : NF F.S) (hY : (F.a11*(1-F.S.tm)-F.gg*F.S.tm) = 0) (hZ : (F.a12*F.S.sm+F.gg*(F.S.km-F.S.tm)-F.a11*F.S.tm) = 0) (hL : 0 ≤ (F.a11*F.S.tp-F.a12-F.gg*(1-F.S.tp))) : (F.S.tm-F.S.km*(1-F.S.tm)+F.S.sm*(1-F.S.tm-F.S.tp)) ≤ 0 := by
  have hg : 0 < F.gg := F.g_pos
  have tm1 := F.S.tm1; have sm0 := F.S.sm_pos
  have e : (1-F.S.tm)*F.S.sm*(F.a11*F.S.tp-F.a12-F.gg*(1-F.S.tp)) + F.gg*(F.S.tm-F.S.km*(1-F.S.tm)+F.S.sm*(1-F.S.tm-F.S.tp)) = F.S.sm*F.S.tp*(F.a11*(1-F.S.tm)-F.gg*F.S.tm) - ((1-F.S.tm)*F.S.sm*F.a12 + F.gg*(F.S.km*(1-F.S.tm)-F.S.tm)) := by ring
  have eX : (1-F.S.tm)*F.S.sm*F.a12 + F.gg*(F.S.km*(1-F.S.tm)-F.S.tm) = F.S.tm*(F.a11*(1-F.S.tm)-F.gg*F.S.tm) + (1-F.S.tm)*(F.a12*F.S.sm+F.gg*(F.S.km-F.S.tm)-F.a11*F.S.tm) := by ring
  rw [eX, hY, hZ] at e
  have h1 : 0 ≤ (1-F.S.tm)*F.S.sm*(F.a11*F.S.tp-F.a12-F.gg*(1-F.S.tp)) := by positivity
  have h2 : F.gg*(F.S.tm-F.S.km*(1-F.S.tm)+F.S.sm*(1-F.S.tm-F.S.tp)) ≤ 0 := by nlinarith
  by_contra hc
  push Not at hc
  have := mul_pos hg hc
  linarith

/-- S5: `X = 0` forces `A56 < 0`. -/
lemma S5 (hN : NF F.S) (hX : ((1-F.S.tm)*F.S.sm*F.a12+F.gg*(F.S.km*(1-F.S.tm)-F.S.tm)) = 0) : (F.S.km*(1-F.S.tm)-F.S.tm) < 0 := by
  have hg : 0 < F.gg := F.g_pos
  have ha : 0 < F.a12 := F.A12_pos
  have tm1 := F.S.tm1; have sm0 := F.S.sm_pos
  have h1 : 0 < (1-F.S.tm)*F.S.sm*F.a12 := by positivity
  by_contra hc
  push Not at hc
  have := mul_nonneg hg.le hc
  nlinarith

end IAT
end Minimality.CaseC20

end

section


/-!
# I_A, leaves S45, C2a, C2b
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace IAT
open IVT
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

def c2b_pat : Fin 8 → Bool := ![false, false, false, false, true, true, true, true]
def c2b_c : ZMod 5 → Fin 7 := ![0, 1, 4, 5, 2]
theorem c2b_cyc : S0xCycOK h20s_S c2b_c c2b_pat := by decide
theorem c2b_inj : Function.Injective c2b_c := by decide


/-- S45: segment view `x4 - x5`, cycle `1346`; needs `sm < km` and `a12 < a22`. -/
theorem ia_S45 (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hN : NF F.S) (hk : F.S.sm < F.S.km) (hc : F.a12 < F.a22) : IsRupert (univ.image x) := by
  have sm0 := F.S.sm_pos; have sm1 := F.S.sm1; have tm0 := F.S.tm_pos; have tp1 := F.S.tp1
  have tm1 := F.S.tm1; have tp0 := F.S.tp_pos; have kp0 := F.S.kp_pos; have km0 := F.S.km_pos
  have ha : 0 < F.a12 := F.A12_pos; have hg : 0 < F.gg := F.g_pos
  have rp := roofP_n F.S hN; have rm := rm_pos F.S hN; have s2 := S2 F hN
  have nE : nf F.S ⟨0, F.S.sm, -F.S.km⟩ 4 < 0 := by
    have e : nf F.S ⟨0, F.S.sm, -F.S.km⟩ 4 = -(1-F.S.tp)*(F.S.km - F.S.sm) := by simp only [nf_E, hN.2]; ring
    rw [e]; nlinarith
  have nF : nf F.S ⟨0, F.S.sm, -F.S.km⟩ 5 < 0 := by
    have e : nf F.S ⟨0, F.S.sm, -F.S.km⟩ 5 = F.S.tp*(F.S.kp*F.S.sm - (1-F.S.sp)*F.S.km) := by simp only [nf_F, hN.2]; ring
    rw [e]
    have : F.S.kp*F.S.sm - (1-F.S.sp)*F.S.km < 0 := by nlinarith [mul_pos kp0 sm0]
    nlinarith
  refine seg_leaf F (h20s_fac hR) hx ias_S45 ias_S45_good ⟨0, F.S.sm, -F.S.km⟩
    (seg_vec F 5 4 _ (by rw [F.ptC_4, F.ptC_5]; simp only [C3.sub]; congr 1 <;> ring)) (by ia_lits) ?_
  have z1 : F.dep ⟨0, F.S.sm, -F.S.km⟩ 1 = F.a12 * F.S.sm := by rw [Frame20.dep_1]; ring
  have z3 : F.dep ⟨0, F.S.sm, -F.S.km⟩ 3 = F.S.tm * (F.a12 * F.S.sm + F.gg * F.S.km) := by rw [Frame20.dep_3, hN.1]; ring
  have z4 : F.dep ⟨0, F.S.sm, -F.S.km⟩ 4 = F.a22 * F.S.sm^2 + F.gg * F.S.km^2 := by rw [Frame20.dep_4]; ring
  have z6 : F.dep ⟨0, F.S.sm, -F.S.km⟩ 6 = F.a22 * F.S.sm := by rw [Frame20.dep_6]; ring
  refine robUni4 ?_ ?_
  · rintro ⟨h1, h2, h3, h4⟩
    have h3' : F.dep ⟨0, F.S.sm, -F.S.km⟩ 6 ≤ F.dep ⟨0, F.S.sm, -F.S.km⟩ 1 := h3
    rw [z6, z1] at h3'
    nlinarith [mul_pos sm0 (sub_pos.2 hc)]
  · rintro ⟨h1, h2, h3, h4⟩
    have h1' : F.dep ⟨0, F.S.sm, -F.S.km⟩ 1 ≤ F.dep ⟨0, F.S.sm, -F.S.km⟩ 3 := h1
    have h3' : F.dep ⟨0, F.S.sm, -F.S.km⟩ 4 ≤ F.dep ⟨0, F.S.sm, -F.S.km⟩ 3 := h3
    have h4' : F.dep ⟨0, F.S.sm, -F.S.km⟩ 4 ≤ F.dep ⟨0, F.S.sm, -F.S.km⟩ 6 := h4
    rw [z1, z3] at h1'; rw [z4, z3] at h3'; rw [z4, z6] at h4'
    have e : F.S.tm * (F.S.sm * ((F.a22 * F.S.sm) - (F.a22 * F.S.sm^2 + F.gg * F.S.km^2)) +
        (1-F.S.sm) * (F.S.tm * (F.a12 * F.S.sm + F.gg * F.S.km) - (F.a22 * F.S.sm^2 + F.gg * F.S.km^2))) +
        (F.S.km - (1-F.S.sm)*F.S.tm) * (F.S.tm * (F.a12 * F.S.sm + F.gg * F.S.km) - F.a12 * F.S.sm)
        = -F.a12 * F.S.sm * (F.S.km*(1-F.S.tm)-F.S.tm*(1-F.S.sm)) := by ring
    have p1 := mul_nonneg sm0.le (sub_nonneg.2 h4')
    have p2 := mul_nonneg sm1.le (sub_nonneg.2 h3')
    have p3 := mul_nonneg s2.le (sub_nonneg.2 h1')
    have p4 := mul_nonneg tm0.le (add_nonneg p1 p2)
    have p5 := mul_pos (mul_pos ha sm0) rm
    nlinarith

/-- C2a: segment view `x6 - x4`, cycle `0145`; needs `A2 > 0` and `Lp < 0`. -/
theorem ia_C2a (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hN : NF F.S) (hA : 0 < (F.S.km*F.S.sp-F.S.kp*(1-F.S.sm))) (hL : ((1-F.S.sm)*(F.a22*F.S.sm-F.a12)-F.gg*F.S.km^2) < 0) : IsRupert (univ.image x) := by
  have sm0 := F.S.sm_pos; have sm1 := F.S.sm1; have tm0 := F.S.tm_pos; have tp1 := F.S.tp1
  have tm1 := F.S.tm1; have tp0 := F.S.tp_pos; have kp0 := F.S.kp_pos; have km0 := F.S.km_pos
  have ha : 0 < F.a12 := F.A12_pos; have hg : 0 < F.gg := F.g_pos
  have nB : 0 < nf F.S ⟨0, 1-F.S.sm, F.S.km⟩ 1 := by
    have e : nf F.S ⟨0, 1-F.S.sm, F.S.km⟩ 1 = F.S.tp * (F.S.km*F.S.sp-F.S.kp*(1-F.S.sm)) := by simp only [nf_B, hN.2]; ring
    rw [e]; positivity
  have nC : nf F.S ⟨0, 1-F.S.sm, F.S.km⟩ 2 < 0 := by
    have e : nf F.S ⟨0, 1-F.S.sm, F.S.km⟩ 2 = -(F.S.tm*(1-F.S.sm)) := by simp only [nf_C, hN.1, hN.2]; ring
    rw [e]; nlinarith [mul_pos tm0 sm1]
  refine seg_leaf F (h20s_fac hR) hx ivs_C2 ivs_C2_good ⟨0, 1-F.S.sm, F.S.km⟩
    (seg_vec F 4 6 _ (by rw [F.ptC_6, F.ptC_4]; simp only [C3.sub]; congr 1 <;> ring)) (by ia_lits) ?_
  have z0 : F.dep ⟨0, 1-F.S.sm, F.S.km⟩ 0 = F.a12*(1-F.S.sm)*F.S.tp + F.gg*F.S.km*(1-F.S.tp) := by
    rw [Frame20.dep_0, hN.2]; ring
  have z1 : F.dep ⟨0, 1-F.S.sm, F.S.km⟩ 1 = F.a12*(1-F.S.sm) := by rw [Frame20.dep_1]; ring
  have z4 : F.dep ⟨0, 1-F.S.sm, F.S.km⟩ 4 = F.a22*F.S.sm*(1-F.S.sm) - F.gg*F.S.km^2 := by rw [Frame20.dep_4]; ring
  have z5 : F.dep ⟨0, 1-F.S.sm, F.S.km⟩ 5 = 0 := Frame20.dep_5 F _
  refine robUni4 ?_ ?_
  · rintro ⟨h1, h2, h3, h4⟩
    have h2' : F.dep ⟨0, 1-F.S.sm, F.S.km⟩ 1 ≤ F.dep ⟨0, 1-F.S.sm, F.S.km⟩ 4 := h2
    rw [z1, z4] at h2'
    nlinarith
  · rintro ⟨h1, h2, h3, h4⟩
    have h2' : F.dep ⟨0, 1-F.S.sm, F.S.km⟩ 0 ≤ F.dep ⟨0, 1-F.S.sm, F.S.km⟩ 5 := h2
    rw [z0, z5] at h2'
    nlinarith [mul_pos (mul_pos ha sm1) tp0, mul_pos (mul_pos hg km0) tp1]

set_option maxHeartbeats 1000000 in
/-- C2b: the same view `x6 - x4` tilted, cycle `01452`; needs `A2 <= 0`, `Lp < 0` and
(`Phi > 0` or `Phi = 0 ∧ a22 = a12`). -/
theorem ia_C2b (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hN : NF F.S) (hA : (F.S.km*F.S.sp-F.S.kp*(1-F.S.sm)) ≤ 0) (hL : ((1-F.S.sm)*(F.a22*F.S.sm-F.a12)-F.gg*F.S.km^2) < 0) (hP : 0 < (F.gg*F.S.km-F.a12*(1-F.S.sm)) ∨ ((F.gg*F.S.km-F.a12*(1-F.S.sm)) = 0 ∧ F.a22 = F.a12)) :
    IsRupert (univ.image x) := by
  have sm0 := F.S.sm_pos; have sm1 := F.S.sm1; have tm0 := F.S.tm_pos; have tp1 := F.S.tp1
  have tm1 := F.S.tm1; have tp0 := F.S.tp_pos; have kp0 := F.S.kp_pos; have km0 := F.S.km_pos
  have sp0 := F.S.sp_pos; have sp1 := F.S.sp1
  have ha : 0 < F.a12 := F.A12_pos; have hg : 0 < F.gg := F.g_pos
  have rp := roofP_n F.S hN; have rm := rm_pos F.S hN
  have uA : nf F.S ⟨0, 1-F.S.sm, F.S.km⟩ 0 = -(F.S.km*(1-F.S.tm)-F.S.tm*(1-F.S.sm)) := by simp only [nf_A, hN.1]; ring
  have uB : nf F.S ⟨0, 1-F.S.sm, F.S.km⟩ 1 = F.S.tp * (F.S.km*F.S.sp-F.S.kp*(1-F.S.sm)) := by simp only [nf_B, hN.2]; ring
  have uC : nf F.S ⟨0, 1-F.S.sm, F.S.km⟩ 2 = -(F.S.tm*(1-F.S.sm)) := by simp only [nf_C, hN.1, hN.2]; ring
  have uD : nf F.S ⟨0, 1-F.S.sm, F.S.km⟩ 3 = -(F.S.tm*F.S.km) := by simp only [nf_D, hN.1]; ring
  have uE : nf F.S ⟨0, 1-F.S.sm, F.S.km⟩ 4 = (1-F.S.tp)*(1-F.S.sm+F.S.km) := by simp only [nf_E, hN.2]; ring
  have uF : nf F.S ⟨0, 1-F.S.sm, F.S.km⟩ 5 = F.S.tp*(F.S.kp*(1-F.S.sm)+(1-F.S.sp)*F.S.km) := by simp only [nf_F, hN.2]; ring
  have uG : nf F.S ⟨0, 1-F.S.sm, F.S.km⟩ 6 = 0 := by simp only [nf_G]; ring
  have uH : nf F.S ⟨0, 1-F.S.sm, F.S.km⟩ 7 = 0 := by simp only [nf_H]; ring
  have vB : nf F.S ⟨-F.S.tp*(1-F.S.sm), 0, -(F.S.tp*F.S.km+(1-F.S.tp)*(1-F.S.sm))⟩ 1 = -(F.S.tp^2*F.S.sp*F.S.km) := by
    simp only [nf_B, hN.2]; ring
  have vG : nf F.S ⟨-F.S.tp*(1-F.S.sm), 0, -(F.S.tp*F.S.km+(1-F.S.tp)*(1-F.S.sm))⟩ 6 = (1-F.S.sm)^2*(1-F.S.tp) := by
    simp only [nf_G]; ring
  have vH : nf F.S ⟨-F.S.tp*(1-F.S.sm), 0, -(F.S.tp*F.S.km+(1-F.S.tp)*(1-F.S.sm))⟩ 7 = F.S.kp*F.S.tp*(1-F.S.sm) := by
    simp only [nf_H]; ring
  refine leaf_of_view F (h20s_fac hR) hx (by norm_num) c2b_inj c2b_cyc ⟨0, 1-F.S.sm, F.S.km⟩
    ⟨-F.S.tp*(1-F.S.sm), 0, -(F.S.tp*F.S.km+(1-F.S.tp)*(1-F.S.sm))⟩ 4
    (by rw [uE]; positivity) ?_ ?_
  · intro t; fin_cases t
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (eq_neg uA (by linarith))⟩
    · refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
      rcases hA.lt_or_eq with h | h
      · exact lpn_pos (eq_neg uB (mul_neg_of_pos_of_neg tp0 h))
      · exact lpn_zero (uB.trans (by rw [h]; ring)) (eq_neg vB (by have := mul_pos (mul_pos (pow_pos tp0 2) sp0) km0; linarith))
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (eq_neg uC (by nlinarith [mul_pos tm0 sm1]))⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (eq_neg uD (by nlinarith [mul_pos tm0 km0]))⟩
    · exact ⟨fun _ => lp_pos (eq_pos uE (by positivity)), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp_pos (eq_pos uF (by positivity)), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp_zero uG (eq_pos vG (by positivity)), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp_zero uH (eq_pos vH (by positivity)), fun h => absurd h (by decide)⟩
  · have z0 : F.dep ⟨0, 1-F.S.sm, F.S.km⟩ 0 = F.a12*(1-F.S.sm)*F.S.tp + F.gg*F.S.km*(1-F.S.tp) := by
      rw [Frame20.dep_0, hN.2]; ring
    have z1 : F.dep ⟨0, 1-F.S.sm, F.S.km⟩ 1 = F.a12*(1-F.S.sm) := by rw [Frame20.dep_1]; ring
    have z2 : F.dep ⟨0, 1-F.S.sm, F.S.km⟩ 2 = F.a22*(1-F.S.sm)*F.S.sp + F.gg*F.S.km*F.S.kp := by rw [Frame20.dep_2]; ring
    have z4 : F.dep ⟨0, 1-F.S.sm, F.S.km⟩ 4 = F.a22*F.S.sm*(1-F.S.sm) - F.gg*F.S.km^2 := by rw [Frame20.dep_4]; ring
    have z5 : F.dep ⟨0, 1-F.S.sm, F.S.km⟩ 5 = 0 := Frame20.dep_5 F _
    refine robUni5_H9 ?_ ?_ ?_ ?_
    · show F.dep _ 4 < F.dep _ 1
      rw [z4, z1]; nlinarith
    · show F.dep _ 5 < F.dep _ 0
      rw [z5, z0]; exact add_pos (mul_pos (mul_pos ha sm1) tp0) (mul_pos (mul_pos hg km0) tp1)
    · show F.dep _ 5 < F.dep _ 2
      rw [z5, z2]
      have h22 : 0 < F.a22 := F.A22_pos
      exact add_pos (mul_pos (mul_pos h22 sm1) sp0) (mul_pos (mul_pos hg km0) kp0)
    · rcases hP with h | ⟨h, hc⟩
      · left
        show F.dep _ 1 < F.dep _ 0
        rw [z1, z0]
        have e : F.a12*(1-F.S.sm)*F.S.tp + F.gg*F.S.km*(1-F.S.tp) - F.a12*(1-F.S.sm) = (1-F.S.tp)*(F.gg*F.S.km-F.a12*(1-F.S.sm)) := by ring
        have := mul_pos tp1 h
        linarith
      · right
        show F.dep _ 2 < F.dep _ 0
        rw [z2, z0, hc]
        have e : F.a12*(1-F.S.sm)*F.S.sp + F.gg*F.S.km*F.S.kp - (F.a12*(1-F.S.sm)*F.S.tp + F.gg*F.S.km*(1-F.S.tp))
            = F.a12*(1-F.S.sm)*(F.S.sp+F.S.kp-1) := by linear_combination (F.S.kp-(1-F.S.tp)) * h
        have := mul_pos (mul_pos ha sm1) (show 0 < 1 - F.S.sp - F.S.kp by linarith)
        nlinarith

end IAT
end Minimality.CaseC20

end

