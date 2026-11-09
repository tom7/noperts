module

public import Minimality.Type20IMCB

@[expose] public section

/-!
# Type 20, item I_MC (part D): the tie case `Zt`

In the stratum `Vq = 0 = P1` with `A > 0`, `Q >= 0` and the depth tie `z4 = z6` at the view `x3 - x5`:
the tie context `ZCtx`, the leaves ZW, ZWt, ZY (view `x4 - x6`) and ZT (view `x0 - x2`), the
`B16 > 0` version of L10, and the dispatcher `Frame20.imc_Zt`.
-/

section

/-!
# Type 20, I_MC, tie `Zt` inside stratum Z: shared setup (Zt0)

Stratum Z is `Vq = 0`, `P1 = 0`, i.e. `kp tm = (1-sp) c0` and `km tm = sm c0` (`c0 = hm tp + hp tm`).
The tie is `z4 = z6` at the view `x3 - x5`, which is the shape equation `sm c km hm = hp den tm (1-sm)`.
At the view `u1 = x4 - x6 = (0, -(1-sm), -km)` all depths are explicit (Dd, scaled by `hm`).
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace IMCT

variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- The view `x4 - x6` in frame coordinates. -/
def u1 (S : Shape20) : C3 := ⟨0, -(1 - S.sm), -S.km⟩

/-- The tie `z4 = z6` at `x3 - x5` is the shape equation `sm c km hm = hp den tm (1 - sm)`. -/
lemma ztie {r B : ℝ} (P : F.Par r B)
    (hT : F.dep ⟨F.S.tm, 0, -F.S.hm⟩ 4 = F.dep ⟨F.S.tm, 0, -F.S.hm⟩ 6) :
    F.S.sm * ((1 - F.S.tm) * (1 - F.S.tp)) * F.S.km * F.S.hm =
      F.S.hp * (F.S.hm + F.S.km * F.S.tm - F.S.km) * F.S.tm * (1 - F.S.sm) := by
  have a := F.hp_dep P.h11 P.h12 P.hg P.h22 ⟨F.S.tm, 0, -F.S.hm⟩ 4
  have b := F.hp_dep P.h11 P.h12 P.hg P.h22 ⟨F.S.tm, 0, -F.S.hm⟩ 6
  rw [hT] at a
  have h : r * F.Dd B ⟨F.S.tm, 0, -F.S.hm⟩ 4 = r * F.Dd B ⟨F.S.tm, 0, -F.S.hm⟩ 6 := by rw [← a, ← b]
  have h2 := mul_left_cancel₀ P.hr.ne' h
  simp only [Frame20.Dd] at h2
  linear_combination h2

/-- Polynomial depths at `x4 - x6`, scaled by `hm`, under the tie and `Vq = P1 = 0`. -/
lemma zdd_u1 (B : ℝ)
    (tie : F.S.sm * ((1 - F.S.tm) * (1 - F.S.tp)) * F.S.km * F.S.hm =
      F.S.hp * (F.S.hm + F.S.km * F.S.tm - F.S.km) * F.S.tm * (1 - F.S.sm))
    (hkm : F.S.km * F.S.tm = F.S.sm * (F.S.hm * F.S.tp + F.S.hp * F.S.tm))
    (hkp : F.S.kp * F.S.tm = (1 - F.S.sp) * (F.S.hm * F.S.tp + F.S.hp * F.S.tm)) :
    F.S.hm * F.Dd B (u1 F.S) 0 = -(F.S.hp * (F.S.hm + F.S.km * F.S.tm - F.S.km) * (1 - F.S.sm) *
        (F.S.hm * F.S.tp + F.S.hp * F.S.tm)) ∧
    F.Dd B (u1 F.S) 1 = -(F.S.hp * (F.S.hm + F.S.km * F.S.tm - F.S.km) * (1 - F.S.sm)) ∧
    F.S.hm * F.Dd B (u1 F.S) 2 = -(F.S.hp * (1 - F.S.sm) * (B * F.S.sp * F.S.hm +
        (F.S.hm + F.S.km * F.S.tm - F.S.km) * (1 - F.S.sp) * (F.S.hm * F.S.tp + F.S.hp * F.S.tm))) ∧
    F.S.hm * F.Dd B (u1 F.S) 4 = F.S.hp * (1 - F.S.sm) * F.S.sm *
        ((F.S.hm + F.S.km * F.S.tm - F.S.km) * (F.S.hm * F.S.tp + F.S.hp * F.S.tm) - F.S.hm * B) ∧
    F.Dd B (u1 F.S) 5 = 0 ∧
    F.Dd B (u1 F.S) 6 = -(F.S.hp * B * (1 - F.S.sm)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Frame20.Dd, u1]
    linear_combination (-F.S.hp) * tie
  · simp only [Frame20.Dd, u1]; ring
  · simp only [Frame20.Dd, u1]
    linear_combination (-F.S.kp) * tie + (-(F.S.hp * (F.S.hm + F.S.km * F.S.tm - F.S.km) * (1 - F.S.sm))) * hkp
  · simp only [Frame20.Dd, u1]
    linear_combination (F.S.km) * tie + (F.S.hp * (F.S.hm + F.S.km * F.S.tm - F.S.km) * (1 - F.S.sm)) * hkm
  · simp only [Frame20.Dd]
  · simp only [Frame20.Dd, u1]; ring

/-- Context of the tie case: the I_MC parametrization, stratum Z (`kp tm = (1-sp) c0`, `km tm = sm c0`),
the tie, and the region facts `A > 0`, `Q >= 0`. -/
structure ZCtx (r B : ℝ) : Prop where
  P : F.Par r B
  tie : F.S.sm * ((1 - F.S.tm) * (1 - F.S.tp)) * F.S.km * F.S.hm =
      F.S.hp * (F.S.hm + F.S.km * F.S.tm - F.S.km) * F.S.tm * (1 - F.S.sm)
  hkm : F.S.km * F.S.tm = F.S.sm * (F.S.hm * F.S.tp + F.S.hp * F.S.tm)
  hkp : F.S.kp * F.S.tm = (1 - F.S.sp) * (F.S.hm * F.S.tp + F.S.hp * F.S.tm)
  hA : 0 < F.S.hm * F.S.tp - F.S.hm + F.S.hp * F.S.tm
  hQ : 0 ≤ F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm * F.S.tp) - F.S.hp * F.S.sm * (1 - F.S.tm)

/-- Five-cycle shape of ZW: `z0 < z1`, `z3 < z2`, and `z4` strictly between `z0` and `z3`. -/
theorem robUni5_ZW {z : ZMod 5 → ℝ} (h01 : z 0 < z 1) (h32 : z 3 < z 2)
    (h4 : (z 0 < z 4 ∧ z 4 < z 3) ∨ (z 3 < z 4 ∧ z 4 < z 0)) : RobUni z := by
  rcases h4 with ⟨a, b⟩ | ⟨a, b⟩ <;> robuni5

/-- Five-cycle shape of ZWt: `z0 < z1 < z2 = z3`, `z4 = z0`. -/
theorem robUni5_ZWt {z : ZMod 5 → ℝ} (h01 : z 0 < z 1) (h12 : z 1 < z 2) (h23 : z 2 = z 3)
    (h40 : z 4 = z 0) : RobUni z := by robuni5

end IMCT
end Minimality.CaseC20

end

section

/-!
# Type 20, I_MC, tie `Zt`: the leaves ZW, ZWt, ZY (view `x4 - x6`)  (Zt1)
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace IMCT

/-- Pattern of ZW: up `A B C D H`, down `E F G`. -/
def patZW : Fin 8 → Bool := ![true, true, true, true, false, false, false, true]
/-- The cycle `0,1,4,6,2`. -/
def cycZW : ZMod 5 → Fin 7 := ![0, 1, 4, 6, 2]
theorem cycZW_ok : S0xCycOK h20s_S cycZW patZW := by decide
theorem cycZW_inj : Function.Injective cycZW := by decide

/-- Pattern of ZWt: up `A B C D`, down `E F G H`. -/
def patZWt : Fin 8 → Bool := ![true, true, true, true, false, false, false, false]
/-- The cycle `0,1,4,5,2`. -/
def cycZWt : ZMod 5 → Fin 7 := ![0, 1, 4, 5, 2]
theorem cycZWt_ok : S0xCycOK h20s_S cycZWt patZWt := by decide
theorem cycZWt_inj : Function.Injective cycZWt := by decide

/-- Pattern of ZY: up `A C D`, down `B E F G H`. -/
def patZY : Fin 8 → Bool := ![true, false, true, true, false, false, false, false]
/-- The cycle `0,1,4,5`. -/
def cycZY : ZMod 4 → Fin 7 := ![0, 1, 4, 5]
theorem cycZY_ok : S0xCycOK h20s_S cycZY patZY := by decide
theorem cycZY_inj : Function.Injective cycZY := by decide

/-- Pure-real depth order at `u1` (scaled by `hm`): `d0 < d1`. -/
lemma zc_01 {hp hm s1 den c0 d0 d1 : ℝ} (hp0 : 0 < hp) (hm0 : 0 < hm) (s10 : 0 < s1) (hden : 0 < den)
    (hA : 0 < c0 - hm) (e0 : hm * d0 = -(hp * den * s1 * c0)) (e1 : d1 = -(hp * den * s1)) : d0 < d1 := by
  have key := mul_pos (mul_pos (mul_pos hp0 hden) s10) hA
  have : hm * d0 < hm * d1 := by rw [e0, e1]; nlinarith [key]
  exact lt_of_mul_lt_mul_left this hm0.le

/-- Pure-real: `d6 < d4`. -/
lemma zc_46 {hp hm s1 sm den c0 B d4 d6 : ℝ} (hp0 : 0 < hp) (hm0 : 0 < hm) (s10 : 0 < s1) (sm0 : 0 < sm)
    (hden : 0 < den) (c0p : 0 < c0) (hB : 0 < B) (e4 : hm * d4 = hp * s1 * sm * (den * c0 - hm * B))
    (e6 : d6 = -(hp * B * s1)) (sm1 : sm < 1) : d6 < d4 := by
  have key := mul_pos (mul_pos hp0 s10) (add_pos (mul_pos sm0 (mul_pos hden c0p)) (mul_pos (sub_pos.2 sm1) (mul_pos hm0 hB)))
  have : hm * d6 < hm * d4 := by rw [e4, e6]; nlinarith [key]
  exact lt_of_mul_lt_mul_left this hm0.le

/-- Pure-real: `d2` is strictly between `d0` and `d6` when `hm B != den c0`. -/
lemma zc_2 {hp hm s1 sp den c0 B d0 d2 d6 : ℝ} (hp0 : 0 < hp) (hm0 : 0 < hm) (s10 : 0 < s1)
    (sp0 : 0 < sp) (sp1 : sp < 1)
    (hne : B * hm ≠ den * c0) (e0 : hm * d0 = -(hp * den * s1 * c0))
    (e2 : hm * d2 = -(hp * s1 * (B * sp * hm + den * (1 - sp) * c0))) (e6 : d6 = -(hp * B * s1)) :
    (d0 < d2 ∧ d2 < d6) ∨ (d6 < d2 ∧ d2 < d0) := by
  have q1 : 0 < hp * s1 * sp := by positivity
  have q2 : 0 < hp * s1 * (1 - sp) := mul_pos (mul_pos hp0 s10) (by linarith)
  rcases lt_or_gt_of_ne hne with h | h
  · left
    have g1 : 0 < den * c0 - B * hm := by linarith
    have g2 := mul_pos q1 g1
    have g3 := mul_pos q2 g1
    refine ⟨?_, ?_⟩
    · refine lt_of_mul_lt_mul_left (a := hm) ?_ hm0.le
      rw [e2, e0]; nlinarith [g2]
    · refine lt_of_mul_lt_mul_left (a := hm) ?_ hm0.le
      rw [e2, e6]; nlinarith [g3]
  · right
    have g1 : 0 < B * hm - den * c0 := by linarith
    have g2 := mul_pos q1 g1
    have g3 := mul_pos q2 g1
    refine ⟨?_, ?_⟩
    · refine lt_of_mul_lt_mul_left (a := hm) ?_ hm0.le
      rw [e2, e6]; nlinarith [g3]
    · refine lt_of_mul_lt_mul_left (a := hm) ?_ hm0.le
      rw [e2, e0]; nlinarith [g2]

variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- Basic positivity in the tie case: `c0 > 0`, `den > 0`, `B > 0`, `E0 > 0` and `hp (1-sm) < km tp`. -/
lemma zbasic {r B : ℝ} (Z : ZCtx F r B) :
    0 < F.S.hm * F.S.tp + F.S.hp * F.S.tm ∧ 0 < F.S.hm + F.S.km * F.S.tm - F.S.km ∧
    0 < B ∧ 0 < F.S.hm * F.S.tp - F.S.hp * (1 - F.S.tm) ∧
    F.S.hp * (1 - F.S.sm) < F.S.km * F.S.tp := by
  have tp0 := F.S.tp_pos; have tm0 := F.S.tm_pos; have sm0 := F.S.sm_pos; have sm1 := F.S.sm_lt
  have hp0 := F.S.hp_pos; have hm0 := F.S.hm_pos; have km0 := F.S.km_pos; have tm1 := F.S.tm_lt
  have hden := Z.P.hden
  have hE0 : 0 < F.S.hm * F.S.tp - F.S.hp * (1 - F.S.tm) := by
    have h := Z.hQ
    have e : F.S.sm * (F.S.hm * F.S.tp - F.S.hp * (1 - F.S.tm)) =
        (F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm * F.S.tp) - F.S.hp * F.S.sm * (1 - F.S.tm)) +
        (F.S.hm + F.S.km * F.S.tm - F.S.km) := by ring
    have : 0 < F.S.sm * (F.S.hm * F.S.tp - F.S.hp * (1 - F.S.tm)) := by rw [e]; linarith
    exact Frame20.pos_of_mul_pos' sm0 this
  refine ⟨by positivity, hden, by linarith [Z.P.hB], hE0, ?_⟩
  have lroof := F.lroof_pos
  have h1 : F.S.hm * (F.S.hp * (1 - F.S.sm)) < F.S.hm * (F.S.km * F.S.tp) := by
    nlinarith [mul_pos hp0 lroof, mul_pos km0 (mul_pos tm0 hE0), mul_pos km0 hE0]
  exact lt_of_mul_lt_mul_left h1 hm0.le

/-- Facing sign of `B` at `u1`: `tm * (kp (1-sm) - sp km) = c0 (1 - sm - sp)`. -/
lemma zB_u1 {r B : ℝ} (Z : ZCtx F r B) :
    F.S.tm * (F.S.kp * (1 - F.S.sm) - F.S.sp * F.S.km) =
      (F.S.hm * F.S.tp + F.S.hp * F.S.tm) * (1 - F.S.sm - F.S.sp) := by
  linear_combination (1 - F.S.sm) * Z.hkp - F.S.sp * Z.hkm

/-- Order of the polynomial depths at `u1` (scaled by `hm`), the facts shared by ZW, ZWt, ZY. -/
lemma zu1_01 {r B : ℝ} (Z : ZCtx F r B) : F.Dd B (u1 F.S) 0 < F.Dd B (u1 F.S) 1 := by
  obtain ⟨c0p, hden, -, -, -⟩ := zbasic F Z
  obtain ⟨d0, d1, -⟩ := zdd_u1 F B Z.tie Z.hkm Z.hkp
  have hm0 := F.S.hm_pos; have hp0 := F.S.hp_pos; have sm1 := F.S.sm_lt
  have s1 : 0 < 1 - F.S.sm := by linarith
  have key := mul_pos (mul_pos (mul_pos hp0 hden) s1) Z.hA
  have : F.S.hm * F.Dd B (u1 F.S) 0 < F.S.hm * F.Dd B (u1 F.S) 1 := by
    rw [d0, d1]; nlinarith [key]
  exact lt_of_mul_lt_mul_left this hm0.le

/-- Facing values at `u1 = x4 - x6` that need no case split. -/
lemma zf_u1 (S : Shape20) :
    nf S (u1 S) 0 = S.km * (1 - S.tm) - S.hm * (1 - S.sm) ∧
    nf S (u1 S) 1 = S.tp * (S.kp * (1 - S.sm) - S.sp * S.km) ∧
    nf S (u1 S) 2 = (S.hm * S.tp + S.hp * S.tm) * (1 - S.sm) ∧
    nf S (u1 S) 3 = S.km * S.tm ∧
    nf S (u1 S) 4 = -(S.hp * (1 - S.sm) + (1 - S.tp) * S.km) ∧
    nf S (u1 S) 5 = -(S.tp * (S.kp * (1 - S.sm) + (1 - S.sp) * S.km)) ∧
    nf S (u1 S) 6 = 0 ∧ nf S (u1 S) 7 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [nf_A]; simp only [u1]; ring
  · rw [nf_B]; simp only [u1]; ring
  · rw [nf_C]; simp only [u1]; ring
  · rw [nf_D]; simp only [u1]; ring
  · rw [nf_E]; simp only [u1]; ring
  · rw [nf_F]; simp only [u1]; ring
  · rw [nf_G]; simp only [u1]; ring
  · rw [nf_H]; simp only [u1]; ring

end IMCT
end Minimality.CaseC20

end

section

/-!
# Type 20, I_MC, tie `Zt`: leaves ZW (Zt2)
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace IMCT

variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- **ZW**: tie case with `sm + sp <= 1` and `a22 != beta` (`B hm != den c0`): cycle `0,1,4,6,2`
at `x4 - x6`, tilt `(-1,0,0)`; up `A B C D H`, down `E F G`. -/
theorem imc_ZW (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19)) {r B : ℝ}
    (Z : ZCtx F r B) (hs : F.S.sm + F.S.sp ≤ 1)
    (hne : B * F.S.hm ≠ (F.S.hm + F.S.km * F.S.tm - F.S.km) * (F.S.hm * F.S.tp + F.S.hp * F.S.tm)) :
    IsRupert (univ.image x) := by
  set FF := h20s_fac hR with hFF
  have tp0 := F.S.tp_pos; have tm0 := F.S.tm_pos; have sp0 := F.S.sp_pos; have sm0 := F.S.sm_pos
  have hp0 := F.S.hp_pos; have hm0 := F.S.hm_pos; have kp0 := F.S.kp_pos; have km0 := F.S.km_pos
  have sm1 := F.S.sm_lt; have tp1 := F.S.tp_lt; have sp1 := F.S.sp_lt
  have s1 : 0 < 1 - F.S.sm := by linarith
  have t1 : 0 < 1 - F.S.tp := by linarith
  have u1p : 0 < 1 - F.S.sp := by linarith
  obtain ⟨c0p, hden, hB0, -, -⟩ := zbasic F Z
  obtain ⟨d0, d1, d2, d4, d5, d6⟩ := zdd_u1 F B Z.tie Z.hkm Z.hkp
  obtain ⟨nA, nB, nC, nD, nE, nF, nG, nH⟩ := zf_u1 F.S
  have lroof := F.lroof_pos
  have hA' : 0 < (F.S.hm * F.S.tp + F.S.hp * F.S.tm) - F.S.hm := by linarith [Z.hA]
  set qu := u1 F.S with hqu
  set qv : C3 := ⟨-1, 0, 0⟩ with hqv
  have hBt := zB_u1 F Z
  have hBge : 0 ≤ F.S.kp * (1 - F.S.sm) - F.S.sp * F.S.km := by
    have : 0 ≤ F.S.tm * (F.S.kp * (1 - F.S.sm) - F.S.sp * F.S.km) := by
      rw [hBt]; exact mul_nonneg c0p.le (by linarith)
    exact nonneg_of_mul_nonneg_right this tm0
  have z01 : F.dep qu 0 < F.dep qu 1 :=
    F.dlt Z.P qu (zc_01 hp0 hm0 s1 hden hA' d0 d1)
  have z46 : F.dep qu 6 < F.dep qu 4 :=
    F.dlt Z.P qu (zc_46 hp0 hm0 s1 sm0 hden c0p hB0 d4 d6 sm1)
  have z4 : (F.dep qu 0 < F.dep qu 2 ∧ F.dep qu 2 < F.dep qu 6) ∨
      (F.dep qu 6 < F.dep qu 2 ∧ F.dep qu 2 < F.dep qu 0) := by
    rcases zc_2 hp0 hm0 s1 sp0 sp1 hne d0 d2 d6 with ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inl ⟨F.dlt Z.P qu a, F.dlt Z.P qu b⟩
    · exact Or.inr ⟨F.dlt Z.P qu a, F.dlt Z.P qu b⟩
  have hU : RobUni (fun a : ZMod 5 => F.dep qu (cycZW a)) :=
    robUni5_ZW z01 z46 z4
  have vA : nf F.S qv 0 = -(F.S.hm * F.S.sm) := by rw [nf_A]; simp only [hqv]; ring
  have vB : nf F.S qv 1 = F.S.hp * F.S.sp := by rw [nf_B]; simp only [hqv]; ring
  have vG : nf F.S qv 6 = -F.S.km := by rw [nf_G]; simp only [hqv]; ring
  have vH : nf F.S qv 7 = F.S.kp := by rw [nf_H]; simp only [hqv]; ring
  refine leaf_of_view F FF hx (by norm_num) cycZW_inj cycZW_ok qu qv 2 ?_ ?_ hU
  · rw [nC]; positivity
  · intro t
    have ht : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 := by
      revert t; decide
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨fun _ => Or.inl (by rw [nA]; exact lroof), fun h => absurd h (by decide)⟩
    · refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
      rcases lt_or_eq_of_le hBge with h | h
      · exact Or.inl (by rw [nB]; exact mul_pos tp0 h)
      · exact Or.inr ⟨by rw [nB, ← h]; ring, by rw [vB]; positivity⟩
    · exact ⟨fun _ => Or.inl (by rw [nC]; positivity), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => Or.inl (by rw [nD]; positivity), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => Or.inl (by
        rw [nE]; have := mul_pos t1 km0; have := mul_pos hp0 s1; linarith)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => Or.inl (by
        rw [nF]
        have := mul_pos tp0 (add_pos (mul_pos kp0 s1) (mul_pos u1p km0)); linarith)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => Or.inr ⟨by rw [nG]; ring, by rw [vG]; linarith⟩⟩
    · exact ⟨fun _ => Or.inr ⟨nH, by rw [vH]; exact kp0⟩, fun h => absurd h (by decide)⟩

end IMCT
end Minimality.CaseC20

end

section

/-!
# Type 20, I_MC, tie `Zt`: leaves ZWt and ZY (Zt3)
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace IMCT

/-- Pure-real: `d1 < d4` when `sm B hm < den (sm c0 + hm)`. -/
lemma zc_14 {hp hm s1 sm den c0 B d1 d4 : ℝ} (hp0 : 0 < hp) (hm0 : 0 < hm) (s10 : 0 < s1)
    (e1 : d1 = -(hp * den * s1)) (e4 : hm * d4 = hp * s1 * sm * (den * c0 - hm * B))
    (hB : sm * B * hm < den * (sm * c0 + hm)) : d1 < d4 := by
  have key := mul_pos (mul_pos hp0 s10) (sub_pos.2 hB)
  have : hm * d1 < hm * d4 := by rw [e4, e1]; nlinarith [key]
  exact lt_of_mul_lt_mul_left this hm0.le

variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- Facing values of the tilt `(1-sm, 0, 2 km)` used by ZWt and ZY. -/
lemma zf_v2 (S : Shape20) :
    nf S ⟨1 - S.sm, 0, 2 * S.km⟩ 1 = S.sp * (2 * S.km * S.tp - S.hp * (1 - S.sm)) ∧
    nf S ⟨1 - S.sm, 0, 2 * S.km⟩ 6 = -(S.km * (1 - S.sm)) ∧
    nf S ⟨1 - S.sm, 0, 2 * S.km⟩ 7 = -(S.kp * (1 - S.sm)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [nf_B]; dsimp only; ring
  · rw [nf_G]; dsimp only; ring
  · rw [nf_H]; dsimp only; ring

/-- **ZWt**: tie case with `sm + sp <= 1` and `a22 = beta` (`B hm = den c0`): cycle `0,1,4,5,2` at `x4 - x6`,
tilt `(1-sm, 0, 2km)`; up `A B C D`, down `E F G H`. -/
theorem imc_ZWt (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19)) {r B : ℝ}
    (Z : ZCtx F r B) (hs : F.S.sm + F.S.sp ≤ 1)
    (heq : B * F.S.hm = (F.S.hm + F.S.km * F.S.tm - F.S.km) * (F.S.hm * F.S.tp + F.S.hp * F.S.tm)) :
    IsRupert (univ.image x) := by
  set FF := h20s_fac hR with hFF
  have tp0 := F.S.tp_pos; have tm0 := F.S.tm_pos; have sp0 := F.S.sp_pos; have sm0 := F.S.sm_pos
  have hp0 := F.S.hp_pos; have hm0 := F.S.hm_pos; have kp0 := F.S.kp_pos; have km0 := F.S.km_pos
  have sm1 := F.S.sm_lt; have tp1 := F.S.tp_lt; have sp1 := F.S.sp_lt
  have s1 : 0 < 1 - F.S.sm := by linarith
  have t1 : 0 < 1 - F.S.tp := by linarith
  have u1p : 0 < 1 - F.S.sp := by linarith
  obtain ⟨c0p, hden, hB0, -, kmtp⟩ := zbasic F Z
  obtain ⟨d0, d1, d2, d4, d5, d6⟩ := zdd_u1 F B Z.tie Z.hkm Z.hkp
  obtain ⟨nA, nB, nC, nD, nE, nF, nG, nH⟩ := zf_u1 F.S
  have lroof := F.lroof_pos
  have hA' : 0 < (F.S.hm * F.S.tp + F.S.hp * F.S.tm) - F.S.hm := by linarith [Z.hA]
  set qu := u1 F.S with hqu
  set qv : C3 := ⟨1 - F.S.sm, 0, 2 * F.S.km⟩ with hqv
  obtain ⟨vB, vG, vH⟩ := zf_v2 F.S
  have hBt := zB_u1 F Z
  have hBge : 0 ≤ F.S.kp * (1 - F.S.sm) - F.S.sp * F.S.km := by
    have : 0 ≤ F.S.tm * (F.S.kp * (1 - F.S.sm) - F.S.sp * F.S.km) := by
      rw [hBt]; exact mul_nonneg c0p.le (by linarith)
    exact nonneg_of_mul_nonneg_right this tm0
  have z01 : F.dep qu 0 < F.dep qu 1 :=
    F.dlt Z.P qu (zc_01 hp0 hm0 s1 hden hA' d0 d1)
  -- d4 = 0, d2 = d0, d6 = d0 (scaled)
  have e4 : F.Dd B qu 4 = 0 := by
    have : F.S.hm * F.Dd B qu 4 = 0 := by
      rw [d4]
      have : F.S.hm * B = (F.S.hm + F.S.km * F.S.tm - F.S.km) * (F.S.hm * F.S.tp + F.S.hp * F.S.tm) := by
        linarith
      rw [this]; ring
    exact (mul_eq_zero.1 this).resolve_left hm0.ne'
  have z14 : F.dep qu 1 < F.dep qu 4 := by
    refine F.dlt Z.P qu ?_
    rw [e4, d1]
    have := mul_pos (mul_pos hp0 hden) s1
    linarith
  have z45 : F.dep qu 4 = F.dep qu 5 := F.deq Z.P qu (by rw [e4, d5])
  have z20 : F.dep qu 2 = F.dep qu 0 := by
    refine F.deq Z.P qu ?_
    refine mul_left_cancel₀ hm0.ne' ?_
    rw [d2, d0]
    have : F.S.hm * B = (F.S.hm + F.S.km * F.S.tm - F.S.km) * (F.S.hm * F.S.tp + F.S.hp * F.S.tm) := by
      linarith
    linear_combination (-(F.S.hp * (1 - F.S.sm) * F.S.sp)) * this
  have hU : RobUni (fun a : ZMod 5 => F.dep qu (cycZWt a)) :=
    robUni5_ZWt z01 z14 z45 z20
  refine leaf_of_view F FF hx (by norm_num) cycZWt_inj cycZWt_ok qu qv 2 ?_ ?_ hU
  · rw [nC]; positivity
  · intro t
    have ht : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 := by
      revert t; decide
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨fun _ => Or.inl (by rw [nA]; exact lroof), fun h => absurd h (by decide)⟩
    · refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
      rcases lt_or_eq_of_le hBge with h | h
      · exact Or.inl (by rw [nB]; exact mul_pos tp0 h)
      · refine Or.inr ⟨by rw [nB, ← h]; ring, ?_⟩
        rw [vB]
        have : 0 < 2 * F.S.km * F.S.tp - F.S.hp * (1 - F.S.sm) := by have := mul_pos km0 tp0; linarith
        positivity
    · exact ⟨fun _ => Or.inl (by rw [nC]; positivity), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => Or.inl (by rw [nD]; positivity), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => Or.inl (by
        rw [nE]; have := mul_pos t1 km0; have := mul_pos hp0 s1; linarith)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => Or.inl (by
        rw [nF]
        have := mul_pos tp0 (add_pos (mul_pos kp0 s1) (mul_pos u1p km0)); linarith)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => Or.inr ⟨by rw [nG]; ring, by rw [vG]; have := mul_pos km0 s1; linarith⟩⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => Or.inr ⟨by rw [nH]; ring, by rw [vH]; have := mul_pos kp0 s1; linarith⟩⟩

/-- **ZY**: tie case with `sm + sp > 1` and `a22 < psi'` (`sm B hm < den (sm c0 + hm)`): cycle `0,1,4,5` at
`x4 - x6`, tilt `(1-sm, 0, 2km)`; up `A C D`, down `B E F G H`. -/
theorem imc_ZY (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19)) {r B : ℝ}
    (Z : ZCtx F r B) (hs : 1 < F.S.sm + F.S.sp)
    (hpsi : F.S.sm * B * F.S.hm < (F.S.hm + F.S.km * F.S.tm - F.S.km) *
      (F.S.sm * (F.S.hm * F.S.tp + F.S.hp * F.S.tm) + F.S.hm)) :
    IsRupert (univ.image x) := by
  set FF := h20s_fac hR with hFF
  have tp0 := F.S.tp_pos; have tm0 := F.S.tm_pos; have sp0 := F.S.sp_pos; have sm0 := F.S.sm_pos
  have hp0 := F.S.hp_pos; have hm0 := F.S.hm_pos; have kp0 := F.S.kp_pos; have km0 := F.S.km_pos
  have sm1 := F.S.sm_lt; have tp1 := F.S.tp_lt; have sp1 := F.S.sp_lt
  have s1 : 0 < 1 - F.S.sm := by linarith
  have t1 : 0 < 1 - F.S.tp := by linarith
  have u1p : 0 < 1 - F.S.sp := by linarith
  obtain ⟨c0p, hden, hB0, -, -⟩ := zbasic F Z
  obtain ⟨d0, d1, d2, d4, d5, d6⟩ := zdd_u1 F B Z.tie Z.hkm Z.hkp
  obtain ⟨nA, nB, nC, nD, nE, nF, nG, nH⟩ := zf_u1 F.S
  have lroof := F.lroof_pos
  have hA' : 0 < (F.S.hm * F.S.tp + F.S.hp * F.S.tm) - F.S.hm := by linarith [Z.hA]
  set qu := u1 F.S with hqu
  set qv : C3 := ⟨1 - F.S.sm, 0, 2 * F.S.km⟩ with hqv
  obtain ⟨vB, vG, vH⟩ := zf_v2 F.S
  have hBt := zB_u1 F Z
  have hBlt : F.S.kp * (1 - F.S.sm) - F.S.sp * F.S.km < 0 := by
    have : F.S.tm * (F.S.kp * (1 - F.S.sm) - F.S.sp * F.S.km) < 0 := by
      rw [hBt]; exact mul_neg_of_pos_of_neg c0p (by linarith)
    by_contra hc
    push Not at hc
    have := mul_nonneg tm0.le hc
    linarith
  have z01 : F.dep qu 0 < F.dep qu 1 :=
    F.dlt Z.P qu (zc_01 hp0 hm0 s1 hden hA' d0 d1)
  have z14 : F.dep qu 1 < F.dep qu 4 :=
    F.dlt Z.P qu (zc_14 hp0 hm0 s1 d1 d4 hpsi)
  have hU : RobUni (fun a : ZMod 4 => F.dep qu (cycZY a)) := by
    refine robUni4 ?_ ?_
    · rintro ⟨a1, -, -, -⟩
      change F.dep qu 1 ≤ F.dep qu 0 at a1
      linarith
    · rintro ⟨-, -, a3, -⟩
      change F.dep qu 4 ≤ F.dep qu 1 at a3
      linarith
  refine leaf_of_view F FF hx (by norm_num) cycZY_inj cycZY_ok qu qv 2 ?_ ?_ hU
  · rw [nC]; positivity
  · intro t
    have ht : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 := by
      revert t; decide
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨fun _ => Or.inl (by rw [nA]; exact lroof), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => Or.inl (by
        rw [nB]; have := mul_pos tp0 (neg_pos.2 hBlt); linarith)⟩
    · exact ⟨fun _ => Or.inl (by rw [nC]; positivity), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => Or.inl (by rw [nD]; positivity), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => Or.inl (by
        rw [nE]; have := mul_pos t1 km0; have := mul_pos hp0 s1; linarith)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => Or.inl (by
        rw [nF]
        have := mul_pos tp0 (add_pos (mul_pos kp0 s1) (mul_pos u1p km0)); linarith)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => Or.inr ⟨by rw [nG]; ring, by rw [vG]; have := mul_pos km0 s1; linarith⟩⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => Or.inr ⟨by rw [nH]; ring, by rw [vH]; have := mul_pos kp0 s1; linarith⟩⟩

end IMCT
end Minimality.CaseC20

end

section

/-!
# Type 20, I_MC, tie `Zt`, leaf ZT: pure-real identities (Zt4)

Depths at the view `x0 - x2 = (tp, -sp, hp - kp)` in stratum Z under the tie, as polynomial identities
(coefficients found by ideal reduction; generated).
-/

open Minimality

namespace Minimality.CaseC20
namespace IMCT

/-- Polynomial depths `Dd 2,3,4,6` of the view `x0 - x2`, as functions of the shape and `B`. -/
noncomputable def ddT2 (hp hm tp tm sp sm km kp B : ℝ) : ℝ := hp*(-B*sp^2 + sp*tp*(hm + km*tm - km)) + kp*(sm*((1-tm)*(1-tp)))*(hp - kp)

noncomputable def ddT3 (hp hm tp tm sp sm km kp B : ℝ) : ℝ := -hm*(sm*((1-tm)*(1-tp)))*(hp - kp) + hp*(hm*sm*tm*tp - sp*tm*(hm + km*tm - km))

noncomputable def ddT4 (hp hm tp tm sp sm km kp B : ℝ) : ℝ := hp*(-B*sm*sp + sm*tp*(hm + km*tm - km)) - km*(sm*((1-tm)*(1-tp)))*(hp - kp)

noncomputable def ddT6 (hp hm tp tm sp sm km kp B : ℝ) : ℝ := hp*(-B*sp + tp*(hm + km*tm - km))

/-- Identity `hm (d4 - d6) = hp (1-sm) sp (hm B - den c0)` in stratum Z under the tie. -/
lemma zt_I1 (hp hm tp tm sp sm km kp B : ℝ)
    (tie : sm*((1-tm)*(1-tp))*km*hm = hp*(hm+km*tm-km)*tm*(1-sm)) (hkm : km*tm = sm*(hm*tp+hp*tm)) (hkp : kp*tm = (1-sp)*(hm*tp+hp*tm)) :
    (tm) * (hm * (ddT4 hp hm tp tm sp sm km kp B - ddT6 hp hm tp tm sp sm km kp B)) = (tm) * (hp*(1-sm)*sp*(hm*B-(hm+km*tm-km)*(hm*tp+hp*tm))) := by
  simp only [ddT4, ddT6]
  linear_combination (-hp*tm + kp*tm) * tie + (-hm*hp*sm*sp*tm*tp + hm*hp*sm*sp*tp + hm*hp*sm*tm*tp - hm*hp*sm*tp + hm*hp*sp*tm*tp - hm*hp*sp*tp - hm*hp*tm*tp + hm*hp*tp - hp^2*sm*sp*tm^2 + hp^2*sm*sp*tm + hp^2*sm*tm^2 - hp^2*sm*tm + hp^2*sp*tm^2 - hp^2*sp*tm - hp^2*tm^2 + hp^2*tm - hp*kp*sm*tm^2 + hp*kp*sm*tm + hp*kp*tm^2 - hp*kp*tm) * hkm + (-hm*hp*sm^2*tm*tp + hm*hp*sm^2*tp + hm*hp*sm*tm*tp - hm*hp*sm*tm - hm*hp*sm*tp + hm*hp*tm - hp^2*sm^2*tm^2 + hp^2*sm^2*tm + hp^2*sm*tm^2 - hp^2*sm*tm) * hkp

/-- Identity `sm km d3 = hp (sm km den tp + sm tp K lroof - den km tm sp)` in stratum Z under the tie. -/
lemma zt_I2 (hp hm tp tm sp sm km kp B : ℝ)
    (tie : sm*((1-tm)*(1-tp))*km*hm = hp*(hm+km*tm-km)*tm*(1-sm)) (hkm : km*tm = sm*(hm*tp+hp*tm)) (hkp : kp*tm = (1-sp)*(hm*tp+hp*tm)) :
    (tm) * (sm*km*ddT3 hp hm tp tm sp sm km kp B) = (tm) * (hp*(sm*km*(hm+km*tm-km)*tp+sm*tp*(km-hm)*(km*(1-tm)-hm*(1-sm))-(hm+km*tm-km)*km*tm*sp)) := by
  simp only [ddT3]
  linear_combination (-hp*sm*tm + kp*sm*tm) * tie + (-hm*hp*sm^2*sp*tm*tp + hm*hp*sm^2*sp*tp + hm*hp*sm^2*tm*tp - hm*hp*sm^2*tp + hm*hp*sm*sp*tm*tp - hm*hp*sm*sp*tm - hm*hp*sm*sp*tp - hm*hp*sm*tm*tp + hm*hp*sm*tp + hm*hp*sp*tm - hp^2*sm^2*sp*tm^2 + hp^2*sm^2*sp*tm + hp^2*sm^2*tm^2 - hp^2*sm^2*tm + hp^2*sm*sp*tm^2 - hp^2*sm*sp*tm - hp^2*sm*tm^2 + hp^2*sm*tm - hp*km*sm*sp*tm^2 + hp*km*sm*sp*tm + hp*km*sp*tm^2 - hp*km*sp*tm - hp*kp*sm^2*tm^2 + hp*kp*sm^2*tm + hp*kp*sm*tm^2 - hp*kp*sm*tm) * hkm + (-hm*hp*sm^3*tm*tp + hm*hp*sm^3*tp + hm*hp*sm^2*tm*tp - hm*hp*sm^2*tm - hm*hp*sm^2*tp + hm*hp*sm*tm - hp^2*sm^3*tm^2 + hp^2*sm^3*tm + hp^2*sm^2*tm^2 - hp^2*sm^2*tm) * hkp

/-- Identity `hm sm d2 = hp (den Cc (1-sm-sp) - sm P sp^2)` in stratum Z under the tie. -/
lemma zt_I4 (hp hm tp tm sp sm km kp B : ℝ)
    (tie : sm*((1-tm)*(1-tp))*km*hm = hp*(hm+km*tm-km)*tm*(1-sm)) (hkm : km*tm = sm*(hm*tp+hp*tm)) (hkp : kp*tm = (1-sp)*(hm*tp+hp*tm)) :
    (km*tm^2) * (hm*sm*ddT2 hp hm tp tm sp sm km kp B) = (km*tm^2) * (hp*((hm+km*tm-km)*((hm*tp+hp*tm)*sp-tp*hm)*(1-sm-sp)-sm*(B*hm-(hm+km*tm-km)*(hm*tp+hp*tm))*sp^2)) := by
  simp only [ddT2]
  linear_combination (hp*kp*sm*tm^2 - kp^2*sm*tm^2) * tie + (-hm^2*hp*sm^2*sp^2*tm*tp^2 + hm^2*hp*sm^2*sp^2*tp^2 + 2*hm^2*hp*sm^2*sp*tm*tp^2 - 2*hm^2*hp*sm^2*sp*tp^2 - hm^2*hp*sm^2*tm*tp^2 + hm^2*hp*sm^2*tp^2 + hm^2*hp*sm*sp^2*tm*tp^2 - hm^2*hp*sm*sp^2*tm*tp - hm^2*hp*sm*sp^2*tp^2 - 2*hm^2*hp*sm*sp*tm*tp^2 + 2*hm^2*hp*sm*sp*tm*tp + 2*hm^2*hp*sm*sp*tp^2 + hm^2*hp*sm*tm*tp^2 - hm^2*hp*sm*tm*tp - hm^2*hp*sm*tp^2 + hm^2*hp*sp^2*tm*tp - 2*hm^2*hp*sp*tm*tp + hm^2*hp*tm*tp - 2*hm*hp^2*sm^2*sp^2*tm^2*tp + 2*hm*hp^2*sm^2*sp^2*tm*tp + 3*hm*hp^2*sm^2*sp*tm^2*tp - 3*hm*hp^2*sm^2*sp*tm*tp - hm*hp^2*sm^2*tm^2*tp + hm*hp^2*sm^2*tm*tp + 2*hm*hp^2*sm*sp^2*tm^2*tp - hm*hp^2*sm*sp^2*tm^2 - 2*hm*hp^2*sm*sp^2*tm*tp - 3*hm*hp^2*sm*sp*tm^2*tp + hm*hp^2*sm*sp*tm^2 + 3*hm*hp^2*sm*sp*tm*tp + hm*hp^2*sm*tm^2*tp - hm*hp^2*sm*tm*tp + hm*hp^2*sp^2*tm^2 - hm*hp^2*sp*tm^2 - hm*hp*km*sm*sp^2*tm^2*tp + hm*hp*km*sm*sp^2*tm*tp + 2*hm*hp*km*sm*sp*tm^2*tp - 2*hm*hp*km*sm*sp*tm*tp - hm*hp*km*sm*tm^2*tp + hm*hp*km*sm*tm*tp + hm*hp*km*sp^2*tm^2*tp - hm*hp*km*sp^2*tm*tp - 2*hm*hp*km*sp*tm^2*tp + 2*hm*hp*km*sp*tm*tp + hm*hp*km*tm^2*tp - hm*hp*km*tm*tp - hp^3*sm^2*sp^2*tm^3 + hp^3*sm^2*sp^2*tm^2 + hp^3*sm^2*sp*tm^3 - hp^3*sm^2*sp*tm^2 + hp^3*sm*sp^2*tm^3 - hp^3*sm*sp^2*tm^2 - hp^3*sm*sp*tm^3 + hp^3*sm*sp*tm^2 - hp^2*km*sm*sp^2*tm^3 + hp^2*km*sm*sp^2*tm^2 + hp^2*km*sm*sp*tm^3 - hp^2*km*sm*sp*tm^2 + hp^2*km*sp^2*tm^3 - hp^2*km*sp^2*tm^2 - hp^2*km*sp*tm^3 + hp^2*km*sp*tm^2 - hp^2*kp*sm^2*tm^3 + hp^2*kp*sm^2*tm^2 + hp^2*kp*sm*tm^3 - hp^2*kp*sm*tm^2 + hp*kp^2*sm^2*tm^3 - hp*kp^2*sm^2*tm^2 - hp*kp^2*sm*tm^3 + hp*kp^2*sm*tm^2) * hkm + (-hm^2*hp*sm^3*sp*tm*tp^2 + hm^2*hp*sm^3*sp*tp^2 + hm^2*hp*sm^3*tm*tp^2 - hm^2*hp*sm^3*tp^2 + hm^2*hp*sm^2*sp*tm*tp^2 - hm^2*hp*sm^2*sp*tm*tp - hm^2*hp*sm^2*sp*tp^2 - hm^2*hp*sm^2*tm*tp^2 + hm^2*hp*sm^2*tm*tp + hm^2*hp*sm^2*tp^2 + hm^2*hp*sm*sp*tm*tp - hm^2*hp*sm*tm*tp - 2*hm*hp^2*sm^3*sp*tm^2*tp + 2*hm*hp^2*sm^3*sp*tm*tp + hm*hp^2*sm^3*tm^2*tp - hm*hp^2*sm^3*tm*tp + 2*hm*hp^2*sm^2*sp*tm^2*tp - hm*hp^2*sm^2*sp*tm^2 - 2*hm*hp^2*sm^2*sp*tm*tp - hm*hp^2*sm^2*tm^2*tp + hm*hp^2*sm^2*tm*tp + hm*hp^2*sm*sp*tm^2 + hm*hp*kp*sm^3*tm^2*tp - hm*hp*kp*sm^3*tm*tp - hm*hp*kp*sm^2*tm^2*tp + hm*hp*kp*sm^2*tm^2 + hm*hp*kp*sm^2*tm*tp - hm*hp*kp*sm*tm^2 - hp^3*sm^3*sp*tm^3 + hp^3*sm^3*sp*tm^2 + hp^3*sm^2*sp*tm^3 - hp^3*sm^2*sp*tm^2 + hp^2*kp*sm^3*tm^3 - hp^2*kp*sm^3*tm^2 - hp^2*kp*sm^2*tm^3 + hp^2*kp*sm^2*tm^2) * hkp

end IMCT
end Minimality.CaseC20

end

section

/-!
# Type 20, I_MC, tie `Zt`, leaf ZT: pure-real shape and depth inequalities (Zt5)

Hypotheses (all in one place): Z (`hkm`, `hkp`), the tie, `A > 0`, `Q >= 0`, `B16 <= 0`, `sm + sp > 1`,
`a22 >= psi'` (`hpsi`), and the shape facts `den > 0`, `lroof > 0`, `roof > 0`.
-/

open Minimality

namespace Minimality.CaseC20
namespace IMCT

/-- In stratum Z, `Q >= 0` reads `km - hm >= sm hp`. -/
lemma zt_K {hp hm tp tm sm km : ℝ}
    (hkm : km * tm = sm * (hm * tp + hp * tm))
    (hQ : 0 ≤ km * (1 - tm) - hm * (1 - sm * tp) - hp * sm * (1 - tm)) : sm * hp ≤ km - hm := by
  linarith [hkm]

/-- In stratum Z with `Q >= 0`: `tm <= sm tp`. -/
lemma zt_tm {hp hm tp tm sm km : ℝ} (hm0 : 0 < hm) (tm0 : 0 < tm)
    (hkm : km * tm = sm * (hm * tp + hp * tm)) (hK : sm * hp ≤ km - hm) : tm ≤ sm * tp := by
  have h := mul_le_mul_of_nonneg_left hK tm0.le
  have : 0 ≤ hm * (sm * tp - tm) := by nlinarith [h, hkm]
  have := nonneg_of_mul_nonneg_right this hm0
  linarith

/-- The facing `A` at the view `x0 - x2` is positive. -/
lemma zt_A {hp hm tp tm sp sm km kp : ℝ} (hm0 : 0 < hm) (tm0 : 0 < tm) (sp1 : sp < 1)
    (hkm : km * tm = sm * (hm * tp + hp * tm)) (hkp : kp * tm = (1 - sp) * (hm * tp + hp * tm))
    (htm : tm ≤ sm * tp) :
    0 < hm * sm * tp - (hm + km * tm - km) * sp - sm * (1 - tm) * (hp - kp) := by
  have e : tm * (hm * sm * tp - (hm + km * tm - km) * sp - sm * (1 - tm) * (hp - kp)) =
      hm * (sm * tp - sp * tm) := by
    linear_combination (sp - sp * tm) * hkm + (sm - sm * tm) * hkp
  have h1 : 0 < hm * (sm * tp - sp * tm) := by
    have := mul_pos tm0 (sub_pos.2 sp1)
    exact mul_pos hm0 (by nlinarith)
  rw [← e] at h1
  exact pos_of_mul_pos_right h1 tm0.le

/-- The facing `D` at the view `x0 - x2` vanishes (planes D and F are parallel). -/
lemma zt_D {hp hm tp tm sp sm km kp : ℝ}
    (hkm : km * tm = sm * (hm * tp + hp * tm)) (hkp : kp * tm = (1 - sp) * (hm * tp + hp * tm)) :
    -(hm * sm) * tp - km * tm * (-sp) - sm * tm * (hp - kp) = 0 := by
  linear_combination sp * hkm + sm * hkp

/-- `sp < tp` from `B16 <= 0` and the upper roof. -/
lemma zt_sp_tp {hp tp sp kp : ℝ} (hp0 : 0 < hp) (tp0 : 0 < tp) (tp1 : tp < 1)
    (hB16 : hp * sp - kp * tp ≤ 0) (roof : 0 < hp * (1 - sp) - kp * (1 - tp)) : sp < tp := by
  by_contra hc
  push Not at hc
  have h1 : hp * tp ≤ hp * sp := mul_le_mul_of_nonneg_left hc hp0.le
  have h2 : 0 ≤ tp * (kp - hp) := by nlinarith
  have h3 : hp ≤ kp := by
    have := nonneg_of_mul_nonneg_right h2 tp0
    linarith
  have h4 : hp * (1 - tp) ≤ kp * (1 - tp) := mul_le_mul_of_nonneg_right h3 (by linarith)
  nlinarith

/-- The facing `G` at the view `x0 - x2` is positive (`B16 <= 0`, `sm + sp > 1`). -/
lemma zt_G {hp hm tp tm sp sm km kp : ℝ} (hp0 : 0 < hp) (hm0 : 0 < hm) (tp0 : 0 < tp)
    (tm0 : 0 < tm) (sm1 : sm < 1) (hs : 1 < sm + sp) (hsptp : sp < tp)
    (hkm : km * tm = sm * (hm * tp + hp * tm)) (hkp : kp * tm = (1 - sp) * (hm * tp + hp * tm))
    (hB16 : hp * sp - kp * tp ≤ 0) :
    0 < km * tp + km * (-sp) + (sm - 1) * (hp - kp) := by
  have e : tm * (km * tp + km * (-sp) + (sm - 1) * (hp - kp)) =
      (hm * tp + hp * tm) * (sm * tp - sp) + hm * tp * (1 - sm) := by
    linear_combination (tp - sp) * hkm + (1 - sm) * hkp
  have hY : 0 < hm * tp := mul_pos hm0 tp0
  have hX : 0 < hp * tm := mul_pos hp0 tm0
  have s1 : 0 < 1 - sm := by linarith
  have key : 0 < (hm * tp + hp * tm) * (sm * tp - sp) + hm * tp * (1 - sm) := by
    rcases le_or_gt sp (sm * tp) with h | h
    · have : 0 ≤ (hm * tp + hp * tm) * (sm * tp - sp) :=
        mul_nonneg (by positivity) (by linarith)
      have := mul_pos hY s1
      linarith
    · -- slack from B16: X sp ≤ (1-sp) tp (X + Y)
      have hb : hp * tm * sp ≤ (1 - sp) * tp * (hm * tp + hp * tm) := by
        have := mul_le_mul_of_nonneg_right hB16 tm0.le
        nlinarith [this, hkp]
      have hD : 0 < sp - (1 - sp) * tp := by nlinarith [mul_pos tp0 (show 0 < sm - (1 - sp) by linarith)]
      have hslack : 0 ≤ (1 - sp) * tp * (hm * tp) - (sp - (1 - sp) * tp) * (hp * tm) := by nlinarith [hb]
      have h1 := mul_nonneg (sub_pos.2 h).le hslack
      have hf : 0 < (hm * tp) * ((sm + sp - 1) * (tp - sp)) :=
        mul_pos hY (mul_pos (by linarith) (by linarith))
      by_contra hc
      push Not at hc
      have h2 := mul_nonneg hD.le (neg_nonneg.2 hc)
      nlinarith [h1, hf, h2]
  rw [← e] at key
  exact pos_of_mul_pos_right key tm0.le

end IMCT
end Minimality.CaseC20

end

section

/-!
# Type 20, I_MC, tie `Zt`, leaf ZT: the depth orders at `x0 - x2` (Zt6)

`z3 > z5 = 0`, `z4 < z3`, `z6 < z4`, and `z2 < 0` or `z2 < z6`.
-/

open Minimality

namespace Minimality.CaseC20
namespace IMCT

/-- Pure-real: position of `d2` against `0` and `d6` (the case split of GAPS section 2). -/
lemma zt_z2 {hp hm sm sp den Cc P d2 d6 : ℝ} (hp0 : 0 < hp) (hm0 : 0 < hm) (hden : 0 < den)
    (hP : 0 < P) (sm0 : 0 < sm) (sm1 : sm < 1) (sp0 : 0 < sp) (sp1 : sp < 1) (hs : 1 < sm + sp)
    (e2 : hm * sm * d2 = hp * (den * Cc * (1 - sm - sp) - sm * P * sp ^ 2))
    (e6 : hm * d6 = hp * (-(den * Cc) - P * sp)) : d2 < 0 ∨ d2 < d6 := by
  have hms : 0 < hm * sm := mul_pos hm0 sm0
  have q1 : 0 < sm * P * sp ^ 2 := by positivity
  rcases le_or_gt 0 Cc with h | h
  · left
    have : den * Cc * (1 - sm - sp) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hden.le h) (by linarith)
    have : hm * sm * d2 < 0 := by
      rw [e2]; exact mul_neg_of_pos_of_neg hp0 (by linarith)
    exact neg_of_mul_neg_right this hms.le
  · rcases le_or_gt (den * (-Cc)) (P * sp) with h2 | h2
    · left
      have hm' : 0 < den * (-Cc) := mul_pos hden (by linarith)
      have h3 : sm * (den * (-Cc)) ≤ sm * (P * sp) := mul_le_mul_of_nonneg_left h2 sm0.le
      have h4 : 0 < den * (-Cc) * ((1 - sm) * (1 - sp)) := mul_pos hm' (mul_pos (by linarith) (by linarith))
      have : hm * sm * d2 < 0 := by
        rw [e2]
        refine mul_neg_of_pos_of_neg hp0 ?_
        nlinarith [mul_le_mul_of_nonneg_left h3 sp0.le]
      exact neg_of_mul_neg_right this hms.le
    · right
      have hm' : 0 < den * (-Cc) := mul_pos hden (by linarith)
      have h3 : sm * (P * sp) < den * (-Cc) := by nlinarith [mul_pos hP sp0]
      have : hm * sm * d2 < hm * sm * d6 := by
        have e : hm * sm * d6 = sm * (hp * (-(den * Cc) - P * sp)) := by rw [← e6]; ring
        rw [e2, e]
        have := mul_pos (mul_pos hp0 (sub_pos.2 sp1)) (sub_pos.2 h3)
        nlinarith [this]
      exact lt_of_mul_lt_mul_left this hms.le

/-- Cancelled forms of the three identities of Zt4. -/
lemma zt_I1c {hp hm tp tm sp sm km kp B : ℝ} (tm0 : 0 < tm)
    (tie : sm*((1-tm)*(1-tp))*km*hm = hp*(hm+km*tm-km)*tm*(1-sm))
    (hkm : km*tm = sm*(hm*tp+hp*tm)) (hkp : kp*tm = (1-sp)*(hm*tp+hp*tm)) :
    hm * (ddT4 hp hm tp tm sp sm km kp B - ddT6 hp hm tp tm sp sm km kp B) =
      hp*(1-sm)*sp*(hm*B-(hm+km*tm-km)*(hm*tp+hp*tm)) :=
  mul_left_cancel₀ tm0.ne' (zt_I1 hp hm tp tm sp sm km kp B tie hkm hkp)

lemma zt_I2c {hp hm tp tm sp sm km kp B : ℝ} (tm0 : 0 < tm)
    (tie : sm*((1-tm)*(1-tp))*km*hm = hp*(hm+km*tm-km)*tm*(1-sm))
    (hkm : km*tm = sm*(hm*tp+hp*tm)) (hkp : kp*tm = (1-sp)*(hm*tp+hp*tm)) :
    sm*km*ddT3 hp hm tp tm sp sm km kp B =
      hp*(sm*km*(hm+km*tm-km)*tp+sm*tp*(km-hm)*(km*(1-tm)-hm*(1-sm))-(hm+km*tm-km)*km*tm*sp) :=
  mul_left_cancel₀ tm0.ne' (zt_I2 hp hm tp tm sp sm km kp B tie hkm hkp)

lemma zt_I4c {hp hm tp tm sp sm km kp B : ℝ} (tm0 : 0 < tm) (km0 : 0 < km)
    (tie : sm*((1-tm)*(1-tp))*km*hm = hp*(hm+km*tm-km)*tm*(1-sm))
    (hkm : km*tm = sm*(hm*tp+hp*tm)) (hkp : kp*tm = (1-sp)*(hm*tp+hp*tm)) :
    hm*sm*ddT2 hp hm tp tm sp sm km kp B =
      hp*((hm+km*tm-km)*((hm*tp+hp*tm)*sp-tp*hm)*(1-sm-sp)-sm*(B*hm-(hm+km*tm-km)*(hm*tp+hp*tm))*sp^2) :=
  mul_left_cancel₀ (mul_pos km0 (pow_pos tm0 2)).ne' (zt_I4 hp hm tp tm sp sm km kp B tie hkm hkp)

/-- All depth orders of the leaf ZT. -/
theorem zt_depths {hp hm tp tm sp sm km kp B : ℝ} (hp0 : 0 < hp) (hm0 : 0 < hm) (tm0 : 0 < tm)
    (sp0 : 0 < sp) (sp1 : sp < 1) (sm0 : 0 < sm) (sm1 : sm < 1) (km0 : 0 < km)
    (hden : 0 < hm + km*tm - km) (lroof : 0 < km*(1-tm) - hm*(1-sm))
    (tie : sm*((1-tm)*(1-tp))*km*hm = hp*(hm+km*tm-km)*tm*(1-sm))
    (hkm : km*tm = sm*(hm*tp+hp*tm)) (hkp : kp*tm = (1-sp)*(hm*tp+hp*tm))
    (hK : sm * hp ≤ km - hm) (htm : tm ≤ sm * tp) (tp0 : 0 < tp) (hs : 1 < sm + sp)
    (hpsi : (hm+km*tm-km) * (sm*(hm*tp+hp*tm) + hm) ≤ sm*B*hm) :
    0 < ddT3 hp hm tp tm sp sm km kp B ∧
    ddT4 hp hm tp tm sp sm km kp B < ddT3 hp hm tp tm sp sm km kp B ∧
    ddT6 hp hm tp tm sp sm km kp B < ddT4 hp hm tp tm sp sm km kp B ∧
    (ddT2 hp hm tp tm sp sm km kp B < 0 ∨
      ddT2 hp hm tp tm sp sm km kp B < ddT6 hp hm tp tm sp sm km kp B) := by
  have I1 := zt_I1c (B := B) (kp := kp) tm0 tie hkm hkp
  have I2 := zt_I2c (B := B) (kp := kp) tm0 tie hkm hkp
  have I4 := zt_I4c (B := B) (kp := kp) tm0 km0 tie hkm hkp
  have hKp : 0 < km - hm := by have := mul_pos sm0 hp0; linarith
  have s1 : 0 < 1 - sm := by linarith
  have c0p : 0 < hm*tp+hp*tm := by positivity
  have hP : 0 < B*hm-(hm+km*tm-km)*(hm*tp+hp*tm) := by
    have h1 : 0 < (hm+km*tm-km) * hm := mul_pos hden hm0
    have h2 : (hm+km*tm-km) * hm ≤ sm * (B*hm-(hm+km*tm-km)*(hm*tp+hp*tm)) := by nlinarith [hpsi]
    have : 0 < sm * (B*hm-(hm+km*tm-km)*(hm*tp+hp*tm)) := lt_of_lt_of_le h1 h2
    exact pos_of_mul_pos_right this sm0.le
  have h6 : ddT6 hp hm tp tm sp sm km kp B < ddT4 hp hm tp tm sp sm km kp B := by
    have : 0 < hm * (ddT4 hp hm tp tm sp sm km kp B - ddT6 hp hm tp tm sp sm km kp B) := by
      rw [I1]; exact mul_pos (mul_pos (mul_pos hp0 s1) sp0) (by linarith [hP, mul_comm B hm])
    have := pos_of_mul_pos_right this hm0.le
    linarith
  have h3 : 0 < ddT3 hp hm tp tm sp sm km kp B := by
    have : 0 < sm * km * ddT3 hp hm tp tm sp sm km kp B := by
      rw [I2]
      refine mul_pos hp0 ?_
      have a1 : 0 < (hm+km*tm-km) * km * (sm * tp - tm * sp) := by
        refine mul_pos (mul_pos hden km0) ?_
        have := mul_pos tm0 (sub_pos.2 sp1); nlinarith
      have a2 : 0 < sm*tp*(km-hm)*(km*(1-tm)-hm*(1-sm)) := by positivity
      nlinarith [a1, a2]
    exact pos_of_mul_pos_right this (mul_pos sm0 km0).le
  refine ⟨h3, ?_, h6, ?_⟩
  · have key : sm*km*hm*(ddT3 hp hm tp tm sp sm km kp B - ddT4 hp hm tp tm sp sm km kp B) =
        hp*(hm*sm*tp*(km-hm)*(km*(1-tm)-hm*(1-sm)) + sm*sp*(hm+km*tm-km)*(hm*tp+hp*tm)*(km*(1-sm)-hm)
          + sm^2*km*hm*B*sp) := by
      simp only [ddT3, ddT4, ddT6] at I1 I2 ⊢
      linear_combination hm * I2 - sm * km * I1 + (-(hp*hm*(hm+km*tm-km)*sp)) * hkm
    have h1 : sm*sp*km*((hm+km*tm-km) * (sm*(hm*tp+hp*tm) + hm)) ≤ sm*sp*km*(sm*B*hm) :=
      mul_le_mul_of_nonneg_left hpsi (by positivity)
    have t1 : 0 < hm*sm*tp*(km-hm)*(km*(1-tm)-hm*(1-sm)) := by positivity
    have t2 : 0 < sm*sp*(hm+km*tm-km)*((hm*tp+hp*tm)*(km-hm) + km*hm) := by positivity
    have : 0 < sm*km*hm*(ddT3 hp hm tp tm sp sm km kp B - ddT4 hp hm tp tm sp sm km kp B) := by
      rw [key]
      refine mul_pos hp0 ?_
      have e : hm*sm*tp*(km-hm)*(km*(1-tm)-hm*(1-sm)) + sm*sp*(hm+km*tm-km)*(hm*tp+hp*tm)*(km*(1-sm)-hm)
          + sm^2*km*hm*B*sp = hm*sm*tp*(km-hm)*(km*(1-tm)-hm*(1-sm)) +
            sm*sp*(hm+km*tm-km)*((hm*tp+hp*tm)*(km-hm) + km*hm) +
            (sm*sp*km*(sm*B*hm) - sm*sp*km*((hm+km*tm-km) * (sm*(hm*tp+hp*tm) + hm))) := by ring
      rw [e]
      linarith [h1, t1, t2]
    have := pos_of_mul_pos_right this (by positivity : (0:ℝ) ≤ sm*km*hm)
    linarith
  · refine zt_z2 (hp := hp) (hm := hm) (sm := sm) (sp := sp) (den := hm+km*tm-km)
      (Cc := (hm*tp+hp*tm)*sp-tp*hm) (P := B*hm-(hm+km*tm-km)*(hm*tp+hp*tm)) hp0 hm0 hden hP sm0 sm1 sp0 sp1 hs
      (by rw [I4]) ?_
    simp only [ddT6]; ring

end IMCT
end Minimality.CaseC20

end

section

/-!
# Type 20, I_MC, tie `Zt`: the leaf ZT (view `x0 - x2`, tilt `2 x0 - x6`) (Zt7)
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace IMCT

/-- Pattern of ZT: up `A B C E F G`, down `D H`. -/
def patZT : Fin 8 → Bool := ![true, true, true, false, true, true, true, false]
/-- The cycle `2,5,3,4,6`. -/
def cycZT : ZMod 5 → Fin 7 := ![2, 5, 3, 4, 6]
theorem cycZT_ok : S0xCycOK h20s_S cycZT patZT := by decide
theorem cycZT_inj : Function.Injective cycZT := by decide

/-- Five-cycle shape of ZT: peak at position 2, `z3 > z4 > z6`, and `z0 < z1` or `z0 < z4`. -/
theorem robUni5_ZT {z : ZMod 5 → ℝ} (h12 : z 1 < z 2) (h32 : z 3 < z 2) (h43 : z 4 < z 3)
    (h0 : z 0 < z 1 ∨ z 0 < z 4) : RobUni z := by
  rcases h0 with a | a <;> robuni5

/-- The view `x0 - x2` in frame coordinates. -/
def uT (S : Shape20) : C3 := ⟨S.tp, -S.sp, S.hp - S.kp⟩

variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- **ZT**: tie case with `B16 <= 0`, `sm + sp > 1`, `a22 >= psi'`: cycle `2,5,3,4,6` at `x0 - x2`,
tilt `2 x0 - x6`; up `A B C E F G`, down `D H`. -/
theorem imc_ZT (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19)) {r B : ℝ}
    (Z : ZCtx F r B) (hB16 : F.S.hp * F.S.sp - F.S.kp * F.S.tp ≤ 0) (hs : 1 < F.S.sm + F.S.sp)
    (hpsi : (F.S.hm + F.S.km * F.S.tm - F.S.km) *
      (F.S.sm * (F.S.hm * F.S.tp + F.S.hp * F.S.tm) + F.S.hm) ≤ F.S.sm * B * F.S.hm) :
    IsRupert (univ.image x) := by
  set FF := h20s_fac hR with hFF
  have tp0 := F.S.tp_pos; have tm0 := F.S.tm_pos; have sp0 := F.S.sp_pos; have sm0 := F.S.sm_pos
  have hp0 := F.S.hp_pos; have hm0 := F.S.hm_pos; have kp0 := F.S.kp_pos; have km0 := F.S.km_pos
  have sm1 := F.S.sm_lt; have tp1 := F.S.tp_lt; have sp1 := F.S.sp_lt
  obtain ⟨c0p, hden, hB0, -, -⟩ := zbasic F Z
  have lroof := F.lroof_pos
  have roof := F.roof_pos
  have hK := zt_K Z.hkm Z.hQ
  have htm := zt_tm hm0 tm0 Z.hkm hK
  have hsptp := zt_sp_tp hp0 tp0 tp1 hB16 roof
  have uA := zt_A hm0 tm0 sp1 Z.hkm Z.hkp htm
  have uG := zt_G hp0 hm0 tp0 tm0 sm1 hs hsptp Z.hkm Z.hkp hB16
  obtain ⟨h3, h34, h46, h2⟩ := zt_depths hp0 hm0 tm0 sp0 sp1 sm0 sm1 km0 hden lroof Z.tie Z.hkm Z.hkp hK htm tp0 hs hpsi
  set qu := uT F.S with hqu
  set qv : C3 := ⟨2 * F.S.tp, -1, 2 * F.S.hp⟩ with hqv
  have dd2 : F.Dd B qu 2 = ddT2 F.S.hp F.S.hm F.S.tp F.S.tm F.S.sp F.S.sm F.S.km F.S.kp B := by simp only [Frame20.Dd, hqu, uT, ddT2]; ring
  have dd3 : F.Dd B qu 3 = ddT3 F.S.hp F.S.hm F.S.tp F.S.tm F.S.sp F.S.sm F.S.km F.S.kp B := by simp only [Frame20.Dd, hqu, uT, ddT3]; ring
  have dd4 : F.Dd B qu 4 = ddT4 F.S.hp F.S.hm F.S.tp F.S.tm F.S.sp F.S.sm F.S.km F.S.kp B := by simp only [Frame20.Dd, hqu, uT, ddT4]; ring
  have dd6 : F.Dd B qu 6 = ddT6 F.S.hp F.S.hm F.S.tp F.S.tm F.S.sp F.S.sm F.S.km F.S.kp B := by simp only [Frame20.Dd, hqu, uT, ddT6]; ring
  have dd5 : F.Dd B qu 5 = 0 := by simp only [Frame20.Dd]
  have z3 : 0 < F.dep qu 3 := by
    have := F.dlt Z.P qu (i := 5) (j := 3) (by rw [dd5, dd3]; exact h3)
    rwa [F.dep_5] at this
  have z34 : F.dep qu 4 < F.dep qu 3 := F.dlt Z.P qu (by rw [dd3, dd4]; exact h34)
  have z64 : F.dep qu 6 < F.dep qu 4 := F.dlt Z.P qu (by rw [dd4, dd6]; exact h46)
  have z2 : F.dep qu 2 < F.dep qu 5 ∨ F.dep qu 2 < F.dep qu 6 := by
    rcases h2 with a | a
    · left
      exact F.dlt Z.P qu (i := 2) (j := 5) (by rw [dd2, dd5]; exact a)
    · right
      exact F.dlt Z.P qu (by rw [dd2, dd6]; exact a)
  have hU : RobUni (fun a : ZMod 5 => F.dep qu (cycZT a)) := by
    refine robUni5_ZT ?_ ?_ ?_ ?_
    · show F.dep qu 5 < F.dep qu 3
      rw [F.dep_5]; exact z3
    · exact z34
    · exact z64
    · exact z2
  obtain nD := zt_D Z.hkm Z.hkp
  have fA : nf F.S qu 0 = F.S.hm * F.S.sm * F.S.tp - (F.S.hm + F.S.km * F.S.tm - F.S.km) * F.S.sp -
      F.S.sm * (1 - F.S.tm) * (F.S.hp - F.S.kp) := by rw [nf_A]; simp only [hqu, uT]; ring
  have fB : nf F.S qu 1 = 0 := by rw [nf_B]; simp only [hqu, uT]; ring
  have fC : nf F.S qu 2 = (F.S.hm * F.S.tp + F.S.hp * F.S.tm) * F.S.sp := by
    rw [nf_C]; simp only [hqu, uT]; ring
  have fD : nf F.S qu 3 = 0 := by
    rw [nf_D]; simp only [hqu, uT]; linear_combination nD
  have fE : nf F.S qu 4 = F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := by
    rw [nf_E]; simp only [hqu, uT]; ring
  have fF : nf F.S qu 5 = 0 := by rw [nf_F]; simp only [hqu, uT]; ring
  have fG : nf F.S qu 6 = F.S.km * F.S.tp + F.S.km * (-F.S.sp) + (F.S.sm - 1) * (F.S.hp - F.S.kp) := by
    rw [nf_G]; simp only [hqu, uT]
  have fH : nf F.S qu 7 = -(F.S.kp * F.S.tp) := by rw [nf_H]; simp only [hqu, uT]; ring
  have vB : nf F.S qv 1 = F.S.kp * F.S.tp := by rw [nf_B]; simp only [hqv]; ring
  have vD : nf F.S qv 3 = -(F.S.sm * (F.S.hm * F.S.tp + F.S.hp * F.S.tm)) := by
    rw [nf_D]; simp only [hqv]; linear_combination Z.hkm
  have vF : nf F.S qv 5 = F.S.kp * F.S.tp := by rw [nf_F]; simp only [hqv]; ring
  refine leaf_of_view F FF hx (by norm_num) cycZT_inj cycZT_ok qu qv 2 ?_ ?_ hU
  · rw [fC]; positivity
  · intro t
    have ht : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 := by
      revert t; decide
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨fun _ => Or.inl (by rw [fA]; exact uA), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => Or.inr ⟨fB, by rw [vB]; positivity⟩, fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => Or.inl (by rw [fC]; positivity), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => Or.inr ⟨by rw [fD]; ring, by rw [vD]; have := mul_pos sm0 c0p; linarith⟩⟩
    · exact ⟨fun _ => Or.inl (by rw [fE]; exact roof), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => Or.inr ⟨fF, by rw [vF]; positivity⟩, fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => Or.inl (by rw [fG]; exact uG), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => Or.inl (by rw [fH]; have := mul_pos kp0 tp0; linarith)⟩

end IMCT
end Minimality.CaseC20

end

section

/-!
# Type 20, I_MC, tie `Zt`: dispatch (Zt8): the `B16 > 0` version of L10 and the small fact on `K = 0`
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- L10 with the literals `B16 > 0` and `D16 > 0` as hypotheses (view `x6 - x1`, cycle `0,1,4,5`). -/
theorem imc_L10b (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hI : F.IMC) (hD : 0 < (F.S.km*F.S.tm-F.S.hm*F.S.sm)) (hB16 : 0 < (F.S.hp*F.S.sp-F.S.kp*F.S.tp)) : IsRupert (Finset.univ.image x) := by
  set FF := h20s_fac hR with hFF
  obtain ⟨r, B, P⟩ := F.par hI
  have hden := P.hden
  have ht := F.one_sub_tm_pos; have ht' := F.one_sub_tp_pos
  have tp := F.S.tp_pos; have tm := F.S.tm_pos; have hm := F.S.hm_pos; have hp := F.S.hp_pos
  have sm := F.S.sm_pos; have lroof := F.lroof_pos
  have hq := F.seg_vec 1 6 ⟨-1, 1, 0⟩ (by rw [F.ptC_1, F.ptC_6]; simp [C3.sub])
  refine h20s_I_s16 FF hx ?_ ?_ ?_
  · refine (F.nrm_B FF).seg_pos hq ?_
    simp only; linarith
  · refine (F.nrm_D FF).seg_neg hq ?_
    simp only; linarith
  · rw [hq]
    refine F.robUni_of_dep _ _ (robUni4 ?_ ?_)
    · rintro ⟨a1, a2, a3, a4⟩
      have key : F.dep ⟨-1, 1, 0⟩ 0 < F.dep ⟨-1, 1, 0⟩ 5 := by
        refine F.dlt P _ ?_
        have e : F.Dd B ⟨-1, 1, 0⟩ 5 - F.Dd B ⟨-1, 1, 0⟩ 0 = F.S.hp * F.S.tp * (F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm)) := by
          simp only [Dd]; ring
        have := mul_pos (mul_pos hp tp) lroof
        linarith
      exact absurd a3 (not_le.2 key)
    · rintro ⟨a1, a2, a3, a4⟩
      have key : F.dep ⟨-1, 1, 0⟩ 1 < F.dep ⟨-1, 1, 0⟩ 0 := by
        refine F.dlt P _ ?_
        have e : F.Dd B ⟨-1, 1, 0⟩ 0 - F.Dd B ⟨-1, 1, 0⟩ 1 = F.S.hp * (1 - F.S.tp) * (F.S.km*(1-F.S.tm)-F.S.hm*(1-F.S.sm)) := by
          simp only [Dd]; ring
        have := mul_pos (mul_pos hp ht') lroof
        linarith
      exact absurd a1 (not_le.2 key)


end Frame20
end Minimality.CaseC20

end

section

/-!
# Type 20, I_MC, tie `Zt`: the small fact on `K = 0` and the dispatcher `Frame20.imc_Zt` (Zt9)
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace IMCT

/-- COVER chain (a): `K = 0` and `Q >= 0` force `VM > 0` (hence `K = 0` never reaches `VM <= 0`). -/
theorem K0_VM_pos (S : Shape20) (hK : Kq S = 0) (hQ : 0 ≤ Qq S) : 0 < VM S := by
  unfold Kq at hK; unfold Qq at hQ; unfold VM Vq Mq
  have tp0 := S.tp_pos; have tm0 := S.tm_pos; have sp0 := S.sp_pos; have sm0 := S.sm_pos
  have hp0 := S.hp_pos; have hm0 := S.hm_pos; have kp0 := S.kp_pos; have sp1 := S.sp_lt
  have tm1 := S.tm_lt
  have hkm : S.km = S.hm := by linarith
  rw [hkm] at hQ ⊢
  have h1 : 0 < S.hp * S.sm * (1 - S.tm) := by
    have : 0 < 1 - S.tm := by linarith
    positivity
  have h2 : 0 < S.hm * (S.sm * S.tp - S.tm) := by nlinarith
  have h3 : 0 < S.sm * S.tp - S.tm := pos_of_mul_pos_right h2 hm0.le
  have h4 : 0 < (1 - S.sp) * S.hp * S.tm := by
    have : 0 < 1 - S.sp := by linarith
    positivity
  have h5 : 0 < S.kp * (S.sm * S.tp - S.tm) := mul_pos kp0 h3
  nlinarith [h4, h5]

end IMCT

namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- **I_MC tie case**: in stratum `Vq = 0`, `P1 = 0` with `A > 0`, `Q >= 0`, and the tie `z4 = z6` at the view
`x3 - x5`, the point set is Rupert. (No hypothesis on `z0` versus `z6` or on `K` is needed: `K >= sm hp > 0`
follows from `Q >= 0` in Z.) -/
theorem imc_Zt (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hI : F.IMC) (hV : IMCT.Vq F.S = 0) (hP : IMCT.P1 F.S = 0) (hA : 0 < IMCT.Aq F.S)
    (hQ : 0 ≤ IMCT.Qq F.S)
    (hT : F.dep ⟨F.S.tm, 0, -F.S.hm⟩ 4 = F.dep ⟨F.S.tm, 0, -F.S.hm⟩ 6) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨r, B, P⟩ := F.par hI
  have hkm : F.S.km * F.S.tm = F.S.sm * (F.S.hm * F.S.tp + F.S.hp * F.S.tm) := by
    unfold IMCT.P1 at hP; linarith
  have hkp : F.S.kp * F.S.tm = (1 - F.S.sp) * (F.S.hm * F.S.tp + F.S.hp * F.S.tm) := by
    unfold IMCT.Vq at hV; linarith
  have hA' : 0 < F.S.hm * F.S.tp - F.S.hm + F.S.hp * F.S.tm := by unfold IMCT.Aq at hA; exact hA
  have hQ' : 0 ≤ F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm * F.S.tp) - F.S.hp * F.S.sm * (1 - F.S.tm) := by
    unfold IMCT.Qq at hQ; exact hQ
  have Z : IMCT.ZCtx F r B := ⟨P, IMCT.ztie F P hT, hkm, hkp, hA', hQ'⟩
  have tp0 := F.S.tp_pos; have tm0 := F.S.tm_pos; have sp0 := F.S.sp_pos; have sm0 := F.S.sm_pos
  have hp0 := F.S.hp_pos; have hm0 := F.S.hm_pos; have kp0 := F.S.kp_pos; have km0 := F.S.km_pos
  have hVq : ((1-F.S.sp)*(F.S.hm*F.S.tp+F.S.hp*F.S.tm)-F.S.kp*F.S.tm) = 0 := by unfold IMCT.Vq at hV; exact hV
  by_cases hB16 : 0 < F.S.hp * F.S.sp - F.S.kp * F.S.tp
  · -- leaf L10 with B16 > 0
    have hK : 0 ≤ F.S.km - F.S.hm := by
      have := IMCT.zt_K hkm hQ'
      have := mul_pos sm0 hp0
      linarith
    have hVM0 : ((1-F.S.sp)*(F.S.hm*F.S.tp+F.S.hp*F.S.tm)-F.S.kp*F.S.tm)-F.S.tp*(F.S.km*(1-F.S.sp)-F.S.kp*F.S.sm) = 0 := by
      have e : F.S.tm * (((1-F.S.sp)*(F.S.hm*F.S.tp+F.S.hp*F.S.tm)-F.S.kp*F.S.tm)-F.S.tp*(F.S.km*(1-F.S.sp)-F.S.kp*F.S.sm)) = 0 := by
        linear_combination (F.S.tm - F.S.tp * F.S.sm) * hVq - (F.S.tp * (1 - F.S.sp)) * hkm
      exact (mul_eq_zero.1 e).resolve_left tm0.ne'
    have hD := F.S.alg_D16 hA' hK (le_of_eq hVq) hVM0.le
    exact F.imc_L10b hx hR hI hD hB16
  · push Not at hB16
    rcases le_or_gt (F.S.sm + F.S.sp) 1 with hs | hs
    · by_cases heq : B * F.S.hm = (F.S.hm + F.S.km * F.S.tm - F.S.km) * (F.S.hm * F.S.tp + F.S.hp * F.S.tm)
      · exact IMCT.imc_ZWt F hx hR Z hs heq
      · exact IMCT.imc_ZW F hx hR Z hs heq
    · by_cases hpsi : F.S.sm * B * F.S.hm < (F.S.hm + F.S.km * F.S.tm - F.S.km) *
          (F.S.sm * (F.S.hm * F.S.tp + F.S.hp * F.S.tm) + F.S.hm)
      · exact IMCT.imc_ZY F hx hR Z hs hpsi
      · push Not at hpsi
        exact IMCT.imc_ZT F hx hR Z hB16 hs hpsi

end Frame20
end Minimality.CaseC20

end

