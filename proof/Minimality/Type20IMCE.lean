module

public import Minimality.Type20IMCA

@[expose] public section

/-!
# Type 20, item I_MC (part E): the corner `A = K = 0`, normal form and first leaves

The corner normal form (`Cor.corner_data`: `hp = hm q`, `kp = hm kk`, `km = hm`, `tp = 1 - q tm`,
depths `b * zN`), the leaf assembler `Cor.corner_assemble`, and the corner leaves L6K, W, Y, X, with
the assembly of leaf T.
-/

section

/-!
# C0: corner A = K = 0 of I_MC, normal form: patterns, cycles, normals, depths, hypotheses
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace Cor

/-- Patterns: `true` = facet up. -/
def patL : Fin 8 → Bool := ![true, false, false, false, true, false, true, false]
def patW : Fin 8 → Bool := ![true, true, true, true, false, false, false, true]
def patWt : Fin 8 → Bool := ![true, true, true, true, false, false, false, false]
def patY : Fin 8 → Bool := ![true, false, true, true, false, false, false, false]
def patT : Fin 8 → Bool := ![true, true, true, false, true, true, true, false]

def cycL : ZMod 5 → Fin 7 := ![0, 1, 3, 4, 6]
def cycW : ZMod 5 → Fin 7 := ![0, 1, 4, 6, 2]
def cycWt : ZMod 5 → Fin 7 := ![0, 1, 4, 5, 2]
def cycY : ZMod 4 → Fin 7 := ![0, 1, 4, 5]
def cycT : ZMod 5 → Fin 7 := ![2, 5, 3, 4, 6]

theorem cycL_ok : S0xCycOK h20s_S cycL patL := by decide
theorem cycL_inj : Function.Injective cycL := by decide
theorem cycW_ok : S0xCycOK h20s_S cycW patW := by decide
theorem cycW_inj : Function.Injective cycW := by decide
theorem cycWt_ok : S0xCycOK h20s_S cycWt patWt := by decide
theorem cycWt_inj : Function.Injective cycWt := by decide
theorem cycY_ok : S0xCycOK h20s_S cycY patY := by decide
theorem cycY_inj : Function.Injective cycY := by decide
theorem cycT_ok : S0xCycOK h20s_S cycT patT := by decide
theorem cycT_inj : Function.Injective cycT := by decide

end Cor
end Minimality.CaseC20

end

section

/-!
# C1: corner normal form: definitions (normals NN, depths zN, hypotheses Hy), the normal-form
lemma `corner_data` and the leaf assembler `corner_assemble`.
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace Cor

/-- The eight facet normals at the scaled view `(ux, uy, uz)` (real view `(ux, uy, hm uz)`), divided
by `hm`, in the corner normal form (`hp = hm q`, `kp = hm kk`, `km = hm`, `tp = 1 - q tm`). -/
noncomputable def NN (q tm sp sm kk ux uy uz : ℝ) : Fin 8 → ℝ :=
  ![sm*ux + tm*uy - sm*(1-tm)*uz,
    -q*sp*ux - kk*(1-q*tm)*uy + sp*(1-q*tm)*uz,
    -uy,
    -sm*ux - tm*uy - sm*tm*uz,
    q*(ux+uy) + q*tm*uz,
    (kk - q*(1-sp))*ux + kk*(1-q*tm)*uy + (1-q*tm)*(1-sp)*uz,
    ux + uy - (1-sm)*uz,
    -kk*ux]

/-- The depths of the seven points at the scaled view, divided by `b = a12/tm` (metric `G~`). -/
noncomputable def zN (q tm sp sm kk B ux uy uz : ℝ) : Fin 7 → ℝ :=
  ![(1-q*tm)*(sm*ux+tm*uy) + q*(sm*(1-tm)*tm*uz),
    sm*ux+tm*uy,
    sp*(tm*ux+B*uy) + kk*(sm*(1-tm)*tm*uz),
    tm*(sm*ux+tm*uy) - sm*(1-tm)*tm*uz,
    sm*(tm*ux+B*uy) - sm*(1-tm)*tm*uz,
    0,
    tm*ux+B*uy]


section entries
variable (q tm sp sm kk B ux uy uz : ℝ)
lemma NN_0 : NN q tm sp sm kk ux uy uz 0 = sm*ux + tm*uy - sm*(1-tm)*uz := rfl
lemma NN_1 : NN q tm sp sm kk ux uy uz 1 = -q*sp*ux - kk*(1-q*tm)*uy + sp*(1-q*tm)*uz := rfl
lemma NN_2 : NN q tm sp sm kk ux uy uz 2 = -uy := rfl
lemma NN_3 : NN q tm sp sm kk ux uy uz 3 = -sm*ux - tm*uy - sm*tm*uz := rfl
lemma NN_4 : NN q tm sp sm kk ux uy uz 4 = q*(ux+uy) + q*tm*uz := rfl
lemma NN_5 : NN q tm sp sm kk ux uy uz 5 =
    (kk - q*(1-sp))*ux + kk*(1-q*tm)*uy + (1-q*tm)*(1-sp)*uz := rfl
lemma NN_6 : NN q tm sp sm kk ux uy uz 6 = ux + uy - (1-sm)*uz := rfl
lemma NN_7 : NN q tm sp sm kk ux uy uz 7 = -kk*ux := rfl
lemma zN_0 : zN q tm sp sm kk B ux uy uz 0 =
    (1-q*tm)*(sm*ux+tm*uy) + q*(sm*(1-tm)*tm*uz) := rfl
lemma zN_1 : zN q tm sp sm kk B ux uy uz 1 = sm*ux+tm*uy := rfl
lemma zN_2 : zN q tm sp sm kk B ux uy uz 2 = sp*(tm*ux+B*uy) + kk*(sm*(1-tm)*tm*uz) := rfl
lemma zN_3 : zN q tm sp sm kk B ux uy uz 3 = tm*(sm*ux+tm*uy) - sm*(1-tm)*tm*uz := rfl
lemma zN_4 : zN q tm sp sm kk B ux uy uz 4 = sm*(tm*ux+B*uy) - sm*(1-tm)*tm*uz := rfl
lemma zN_5 : zN q tm sp sm kk B ux uy uz 5 = 0 := rfl
lemma zN_6 : zN q tm sp sm kk B ux uy uz 6 = tm*ux+B*uy := rfl
end entries

/-- The real hypotheses of the corner `A = K = 0` in normal form. -/
structure Hy (q tm sp sm kk B : ℝ) : Prop where
  tm_pos : 0 < tm
  tm_sm : tm < sm
  sm_lt : sm < 1
  sp_pos : 0 < sp
  sp_lt : sp < 1
  q_pos : 0 < q
  tp_pos : 0 < 1 - q*tm
  kk_pos : 0 < kk
  hB : tm ≤ B
  hQ : tm ≤ sm*(1-q)
  hF : q*(1-sp) ≤ kk
  roof : kk*tm < 1-sp

/-- What a leaf supplies: a nonzero normal, the lex facings of the pattern at view `u` and tilt `v`,
and robust unimodality of the depths along the cycle. -/
def LeafOK (q tm sp sm kk B : ℝ) {k : ℕ} (c : ZMod k → Fin 7) (pat : Fin 8 → Bool)
    (ux uy uz vx vy vz : ℝ) : Prop :=
  (∃ t0, NN q tm sp sm kk ux uy uz t0 ≠ 0) ∧
  (∀ t, (pat t = true → h21b_LP (NN q tm sp sm kk ux uy uz t) (NN q tm sp sm kk vx vy vz t)) ∧
    (pat t = false → h21b_LP (-NN q tm sp sm kk ux uy uz t) (-NN q tm sp sm kk vx vy vz t))) ∧
  RobUni (fun a => zN q tm sp sm kk B ux uy uz (c a))

/-- Lex positivity from strict positivity of the first entry. -/
lemma lp1 {a b : ℝ} (h : 0 < a) : h21b_LP a b := Or.inl h
/-- Lex positivity from a zero first entry and positive second entry. -/
lemma lp2 {a b : ℝ} (h : a = 0) (h2 : 0 < b) : h21b_LP a b := Or.inr ⟨h, h2⟩

variable {x : Fin 7 → ℝ³}

/-- The corner `A = K = 0` of I_MC in normal form: `hp = hm q`, `kp = hm kk`, `km = hm`,
`tp = 1 - q tm`, and the depths are `b` times the polynomial depths `zN`. -/
theorem corner_data (F : Frame20 x) (hI : F.IMC)
    (hA : F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm = 0) (hK : F.S.km - F.S.hm = 0)
    (hQ : 0 ≤ F.S.km*(1-F.S.tm) - F.S.hm*(1 - F.S.sm*F.S.tp) - F.S.hp*F.S.sm*(1-F.S.tm))
    (hF : 0 ≤ F.S.kp - F.S.hp*(1-F.S.sp)) :
    ∃ b q kk B : ℝ, 0 < b ∧ F.S.km = F.S.hm ∧ F.S.hp = F.S.hm*q ∧ F.S.kp = F.S.hm*kk ∧
      F.S.tp = 1 - q*F.S.tm ∧ Hy q F.S.tm F.S.sp F.S.sm kk B ∧
      (∀ ux uy uz : ℝ, ∀ j, F.dep ⟨ux, uy, F.S.hm*uz⟩ j =
        b * zN q F.S.tm F.S.sp F.S.sm kk B ux uy uz j) := by
  obtain ⟨h1, h2⟩ := hI
  have hm0 := F.S.hm_pos; have tm0 := F.S.tm_pos; have tm1 := F.S.tm_lt
  have sm0 := F.S.sm_pos; have sm1 := F.S.sm_lt; have sp0 := F.S.sp_pos; have sp1 := F.S.sp_lt
  have hp0 := F.S.hp_pos; have kp0 := F.S.kp_pos; have tp0 := F.S.tp_pos; have tp1 := F.S.tp_lt
  have a12 : 0 < F.a12 := F.A12_pos; have a22 : F.a12 ≤ F.a22 := F.A12_le_A22
  have gg0 := F.g_pos
  have hkm : F.S.km = F.S.hm := by linarith
  obtain ⟨q, hq⟩ : ∃ q, F.S.hp = F.S.hm * q := ⟨F.S.hp / F.S.hm, by field_simp⟩
  obtain ⟨kk, hkk⟩ : ∃ kk, F.S.kp = F.S.hm * kk := ⟨F.S.kp / F.S.hm, by field_simp⟩
  have htp : F.S.tp = 1 - q * F.S.tm := by
    have : F.S.hm * (F.S.tp - (1 - q * F.S.tm)) = 0 := by rw [hq] at hA; linear_combination hA
    have := (mul_eq_zero.1 this).resolve_left hm0.ne'
    linarith
  have q0 : 0 < q := by
    have : 0 < F.S.hm * q := by rw [← hq]; exact hp0
    exact pos_of_mul_pos_right this hm0.le
  have kk0 : 0 < kk := by
    have : 0 < F.S.hm * kk := by rw [← hkk]; exact kp0
    exact pos_of_mul_pos_right this hm0.le
  -- the two equations in normal form
  have e1 : F.S.hm^2 * F.gg = F.S.sm * (1 - F.S.tm) * F.a12 := by
    have : q * F.S.tm * (F.S.hm^2 * F.gg - F.S.sm * (1 - F.S.tm) * F.a12) = 0 := by
      rw [hkm, hq, htp] at h1; linear_combination h1
    have hqt : q * F.S.tm ≠ 0 := (mul_pos q0 tm0).ne'
    have := (mul_eq_zero.1 this).resolve_left hqt
    linarith
  have e2 : F.a11 * F.S.tm = F.S.sm * F.a12 := by
    have : q * (F.a11 * F.S.tm - F.S.sm * F.a12) * (1 - F.S.tm) = 0 := by
      rw [hq, htp] at h2
      linear_combination h2 + q * e1
    have hq1 : q * (1 - F.S.tm) ≠ 0 := (mul_pos q0 (by linarith)).ne'
    have h3 : q * (1 - F.S.tm) * (F.a11 * F.S.tm - F.S.sm * F.a12) = 0 := by linear_combination this
    have := (mul_eq_zero.1 h3).resolve_left hq1
    linarith
  obtain ⟨b, hb12⟩ : ∃ b, F.a12 = b * F.S.tm := ⟨F.a12 / F.S.tm, by field_simp⟩
  have b0 : 0 < b := by rw [hb12] at a12; exact pos_of_mul_pos_left a12 tm0.le
  have hb11 : F.a11 = b * F.S.sm := by
    have : F.a11 * F.S.tm = b * F.S.sm * F.S.tm := by rw [e2, hb12]; ring
    exact mul_right_cancel₀ tm0.ne' this
  have hbg : F.S.hm^2 * F.gg = b * (F.S.sm * (1 - F.S.tm) * F.S.tm) := by rw [e1, hb12]; ring
  obtain ⟨B, hB'⟩ : ∃ B, F.a22 = b * B := ⟨F.a22 / b, by field_simp⟩
  refine ⟨b, q, kk, B, b0, hkm, hq, hkk, htp, ?_, ?_⟩
  · refine ⟨tm0, ?_, sm1, sp0, sp1, q0, by rw [← htp]; exact tp0, kk0, ?_, ?_, ?_, ?_⟩
    · have := F.lroof_pos
      rw [hkm] at this
      nlinarith
    · rw [hb12, hB'] at a22; nlinarith
    · have h3 : 0 ≤ F.S.hm * (F.S.sm*(1-q) - F.S.tm) := by
        have e : F.S.km*(1-F.S.tm) - F.S.hm*(1 - F.S.sm*F.S.tp) - F.S.hp*F.S.sm*(1-F.S.tm) =
            F.S.hm * (F.S.sm*(1-q) - F.S.tm) := by rw [hkm, hq, htp]; ring
        rw [e] at hQ; exact hQ
      have := nonneg_of_mul_nonneg_right h3 hm0
      linarith
    · have h3 : 0 ≤ F.S.hm * (kk - q*(1-F.S.sp)) := by
        have e : F.S.kp - F.S.hp*(1-F.S.sp) = F.S.hm * (kk - q*(1-F.S.sp)) := by rw [hkk, hq]; ring
        rw [e] at hF; exact hF
      have := nonneg_of_mul_nonneg_right h3 hm0
      linarith
    · have h3 := F.roof_pos
      have e : F.S.hp*(1-F.S.sp) - F.S.kp*(1-F.S.tp) = F.S.hm * q * (1 - F.S.sp - kk * F.S.tm) := by
        rw [hkk, hq, htp]; ring
      rw [e] at h3
      have := pos_of_mul_pos_right h3 (mul_pos hm0 q0).le
      linarith
  · intro ux uy uz
    have d0 : F.dep ⟨ux, uy, F.S.hm*uz⟩ 0 = b * zN q F.S.tm F.S.sp F.S.sm kk B ux uy uz 0 := by
      rw [F.dep_0, zN_0, hb11, hb12, hq, htp]
      linear_combination (q * uz) * hbg
    have d1 : F.dep ⟨ux, uy, F.S.hm*uz⟩ 1 = b * zN q F.S.tm F.S.sp F.S.sm kk B ux uy uz 1 := by
      rw [F.dep_1, zN_1, hb11, hb12]; ring
    have d2 : F.dep ⟨ux, uy, F.S.hm*uz⟩ 2 = b * zN q F.S.tm F.S.sp F.S.sm kk B ux uy uz 2 := by
      rw [F.dep_2, zN_2, hb12, hkk, hB']
      linear_combination (kk * uz) * hbg
    have d3 : F.dep ⟨ux, uy, F.S.hm*uz⟩ 3 = b * zN q F.S.tm F.S.sp F.S.sm kk B ux uy uz 3 := by
      rw [F.dep_3, zN_3, hb11, hb12]
      linear_combination (-uz) * hbg
    have d4 : F.dep ⟨ux, uy, F.S.hm*uz⟩ 4 = b * zN q F.S.tm F.S.sp F.S.sm kk B ux uy uz 4 := by
      rw [F.dep_4, zN_4, hb12, hkm, hB']
      linear_combination (-uz) * hbg
    have d5 : F.dep ⟨ux, uy, F.S.hm*uz⟩ 5 = b * zN q F.S.tm F.S.sp F.S.sm kk B ux uy uz 5 := by
      rw [F.dep_5, zN_5]; ring
    have d6 : F.dep ⟨ux, uy, F.S.hm*uz⟩ 6 = b * zN q F.S.tm F.S.sp F.S.sm kk B ux uy uz 6 := by
      rw [F.dep_6, zN_6, hb12, hB']; ring
    intro j
    fin_cases j
    exacts [d0, d1, d2, d3, d4, d5, d6]

end Cor
end Minimality.CaseC20

end

section

/-!
# C2: the leaf assembler of the corner: a `LeafOK` datum gives `IsRupert`.
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace Cor

variable {x : Fin 7 → ℝ³}

/-- In the corner normal form the facing polynomial of every facet at the view `(ux, uy, hm uz)` is
`hm` times the normal `NN`. -/
lemma nf_eq (S : Shape20) {q kk : ℝ} (hkm : S.km = S.hm) (hhp : S.hp = S.hm*q) (hkp : S.kp = S.hm*kk)
    (htp : S.tp = 1 - q*S.tm) (ux uy uz : ℝ) (t : Fin 8) :
    IMCT.nf S ⟨ux, uy, S.hm*uz⟩ t = S.hm * NN q S.tm S.sp S.sm kk ux uy uz t := by
  fin_cases t
  · show IMCT.nf S _ 0 = S.hm * NN q S.tm S.sp S.sm kk ux uy uz 0
    rw [IMCT.nf_A, NN_0, hkm]; simp only; ring
  · show IMCT.nf S _ 1 = S.hm * NN q S.tm S.sp S.sm kk ux uy uz 1
    rw [IMCT.nf_B, NN_1, hhp, hkp, htp]; simp only; ring
  · show IMCT.nf S _ 2 = S.hm * NN q S.tm S.sp S.sm kk ux uy uz 2
    rw [IMCT.nf_C, NN_2, hhp, htp]; simp only; ring
  · show IMCT.nf S _ 3 = S.hm * NN q S.tm S.sp S.sm kk ux uy uz 3
    rw [IMCT.nf_D, NN_3, hkm]; simp only; ring
  · show IMCT.nf S _ 4 = S.hm * NN q S.tm S.sp S.sm kk ux uy uz 4
    rw [IMCT.nf_E, NN_4, hhp, htp]; simp only; ring
  · show IMCT.nf S _ 5 = S.hm * NN q S.tm S.sp S.sm kk ux uy uz 5
    rw [IMCT.nf_F, NN_5, hhp, hkp, htp]; simp only; ring
  · show IMCT.nf S _ 6 = S.hm * NN q S.tm S.sp S.sm kk ux uy uz 6
    rw [IMCT.nf_G, NN_6, hkm]; simp only; ring
  · show IMCT.nf S _ 7 = S.hm * NN q S.tm S.sp S.sm kk ux uy uz 7
    rw [IMCT.nf_H, NN_7, hkp]; simp only; ring

/-- **Leaf assembler**: a cycle, a pattern, and a `LeafOK` datum for the normal form give a Rupert
passage. -/
theorem corner_assemble (F : Frame20 x) (hx : Function.Injective x)
    (hR : RealizesFaces x (sevenTypeFaces 19)) {b q kk B : ℝ} (hb : 0 < b)
    (hkm : F.S.km = F.S.hm) (hhp : F.S.hp = F.S.hm*q) (hkp : F.S.kp = F.S.hm*kk)
    (htp : F.S.tp = 1 - q*F.S.tm)
    (hdep : ∀ ux uy uz : ℝ, ∀ j, F.dep ⟨ux, uy, F.S.hm*uz⟩ j =
        b * zN q F.S.tm F.S.sp F.S.sm kk B ux uy uz j)
    {k : ℕ} [NeZero k] (hk : 3 ≤ k) {c : ZMod k → Fin 7} (hc : Function.Injective c)
    {pat : Fin 8 → Bool} (hcyc : S0xCycOK h20s_S c pat) {ux uy uz vx vy vz : ℝ}
    (L : LeafOK q F.S.tm F.S.sp F.S.sm kk B c pat ux uy uz vx vy vz) :
    IsRupert (Finset.univ.image x) := by
  set FF := h20s_fac hR with hFF
  have hm0 := F.S.hm_pos
  obtain ⟨⟨t0, ht0⟩, hL, hU⟩ := L
  refine IMCT.leaf_of_view F FF hx hk hc hcyc ⟨ux, uy, F.S.hm*uz⟩ ⟨vx, vy, F.S.hm*vz⟩ t0 ?_ ?_ ?_
  · rw [nf_eq F.S hkm hhp hkp htp]; exact mul_ne_zero hm0.ne' ht0
  · intro t
    rw [nf_eq F.S hkm hhp hkp htp, nf_eq F.S hkm hhp hkp htp]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact IMCT.lp_scale hm0 ((hL t).1 h)
    · have := IMCT.lp_scale hm0 ((hL t).2 h)
      simpa only [mul_neg] using this
  · have := robUni_mul_pos hU hb
    convert this using 2 with a
    exact hdep ux uy uz (c a)

end Cor
end Minimality.CaseC20

end

section

/-!
# C3: corner leaf L6K (`Kc < 0`): view `up A E G`, cycle `(0,1,3,4,6)`
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace Cor

/-- The corner form `(1 - sp) * Kc` of the GAPS quantity `Kc` (so `z6 - z4 = -Kc` in L6K). -/
def Kc (q tm sp sm kk : ℝ) : ℝ :=
  sm*(1-tm)*(kk*tm - q*tm*(1-sp)) - (1-sp)*(1-q*tm)*tm*(1-sm)

/-- Shape for a valley plateau: `z3 = z2` is the minimum, then `z4 < z0 < z1`. -/
theorem ruL {z : ZMod 5 → ℝ} (h01 : z 0 < z 1) (h40 : z 4 < z 0) (h34 : z 3 < z 4)
    (h23 : z 2 = z 3) : RobUni z := by robuni5

/-- Facts used everywhere: positivity of the basic quantities. -/
lemma Hy.pf {q tm sp sm kk B : ℝ} (h : Hy q tm sp sm kk B) :
    0 < tm ∧ 0 < sm ∧ 0 < sp ∧ 0 < q ∧ 0 < 1 - q*tm ∧ 0 < kk ∧ 0 < 1 - tm ∧ 0 < 1 - sp ∧
      0 < 1 - sm ∧ 0 < 1 - q ∧ tm < sm := by
  have sm0 : 0 < sm := by linarith [h.tm_pos, h.tm_sm]
  have hq : 0 < 1 - q := by
    have : 0 < sm * (1 - q) := by nlinarith [h.hQ, h.tm_pos]
    exact pos_of_mul_pos_right this sm0.le
  exact ⟨h.tm_pos, sm0, h.sp_pos, h.q_pos, h.tp_pos, h.kk_pos, by linarith [h.tm_sm, h.sm_lt],
    by linarith [h.sp_lt], by linarith [h.sm_lt], hq, h.tm_sm⟩

/-- **Leaf L6K**: `Kc < 0`; the view `u = (tp (1-sp), 0, q (1-sp) - kk)` with tilt `(0, 1-sp, -(kk+1-sp))`. -/
theorem leaf_L6K {q tm sp sm kk B : ℝ} (h : Hy q tm sp sm kk B) (hK : Kc q tm sp sm kk < 0) :
    LeafOK q tm sp sm kk B cycL patL ((1-q*tm)*(1-sp)) 0 (q*(1-sp) - kk) 0 (1-sp) (-(kk+(1-sp))) := by
  obtain ⟨tm0, sm0, sp0, q0, tp0, kk0, t1, r1, s1, q2, tmsm⟩ := h.pf
  have hF := h.hF; have hQ := h.hQ; have roof := h.roof
  have R1 : 0 < (1-sp)*(1-q) + (1-tm)*kk := by positivity
  have e0 : NN q tm sp sm kk ((1-q*tm)*(1-sp)) 0 (q*(1-sp) - kk) 0 =
      sm*((1-q*tm)*(1-sp) + (1-tm)*(kk - q*(1-sp))) := by rw [NN_0]; ring
  have e1 : NN q tm sp sm kk ((1-q*tm)*(1-sp)) 0 (q*(1-sp) - kk) 1 = -(sp*(1-q*tm)*kk) := by
    rw [NN_1]; ring
  have e2 : NN q tm sp sm kk ((1-q*tm)*(1-sp)) 0 (q*(1-sp) - kk) 2 = 0 := by rw [NN_2]; ring
  have e3 : NN q tm sp sm kk ((1-q*tm)*(1-sp)) 0 (q*(1-sp) - kk) 3 = -(sm*((1-sp) - tm*kk)) := by
    rw [NN_3]; ring
  have e4 : NN q tm sp sm kk ((1-q*tm)*(1-sp)) 0 (q*(1-sp) - kk) 4 = q*((1-sp) - tm*kk) := by
    rw [NN_4]; ring
  have e5 : NN q tm sp sm kk ((1-q*tm)*(1-sp)) 0 (q*(1-sp) - kk) 5 = 0 := by rw [NN_5]; ring
  have e6 : NN q tm sp sm kk ((1-q*tm)*(1-sp)) 0 (q*(1-sp) - kk) 6 =
      (1-q*tm)*(1-sp) + (1-sm)*(kk - q*(1-sp)) := by rw [NN_6]; ring
  have e7 : NN q tm sp sm kk ((1-q*tm)*(1-sp)) 0 (q*(1-sp) - kk) 7 = -(kk*((1-q*tm)*(1-sp))) := by
    rw [NN_7]; ring
  have v2 : NN q tm sp sm kk 0 (1-sp) (-(kk+(1-sp))) 2 = -(1-sp) := by rw [NN_2]
  have v5 : NN q tm sp sm kk 0 (1-sp) (-(kk+(1-sp))) 5 = -((1-q*tm)*(1-sp)^2) := by
    rw [NN_5]; ring
  have hkF : 0 ≤ kk - q*(1-sp) := by linarith
  refine ⟨⟨0, ?_⟩, ?_, ?_⟩
  · rw [e0]; have : 0 < (1-q*tm)*(1-sp) + (1-tm)*(kk - q*(1-sp)) := by positivity
    exact (mul_pos sm0 this).ne'
  · intro t
    have ht : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 := by revert t; decide
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨fun _ => lp1 ?_, fun h => absurd h (by decide)⟩
      rw [e0]; have : 0 < (1-q*tm)*(1-sp) + (1-tm)*(kk - q*(1-sp)) := by positivity
      exact mul_pos sm0 this
    · refine ⟨fun h => absurd h (by decide), fun _ => lp1 ?_⟩
      rw [e1]; have := mul_pos (mul_pos sp0 tp0) kk0; linarith
    · refine ⟨fun h => absurd h (by decide), fun _ => lp2 ?_ ?_⟩
      · rw [e2]; ring
      · rw [v2]; linarith
    · refine ⟨fun h => absurd h (by decide), fun _ => lp1 ?_⟩
      rw [e3]; have := mul_pos sm0 (by linarith : 0 < (1-sp) - tm*kk); linarith
    · refine ⟨fun _ => lp1 ?_, fun h => absurd h (by decide)⟩
      rw [e4]; exact mul_pos q0 (by linarith)
    · refine ⟨fun h => absurd h (by decide), fun _ => lp2 ?_ ?_⟩
      · rw [e5]; ring
      · rw [v5]; have := mul_pos tp0 (pow_pos r1 2); linarith
    · refine ⟨fun _ => lp1 ?_, fun h => absurd h (by decide)⟩
      rw [e6]; have : 0 < (1-q*tm)*(1-sp) := mul_pos tp0 r1
      nlinarith [mul_nonneg s1.le hkF]
    · refine ⟨fun h => absurd h (by decide), fun _ => lp1 ?_⟩
      rw [e7]; have := mul_pos tp0 r1; have := mul_pos kk0 this; linarith
  · -- depths
    have z1 : zN q tm sp sm kk B ((1-q*tm)*(1-sp)) 0 (q*(1-sp) - kk) 1 =
        sm*((1-q*tm)*(1-sp)) := by rw [zN_1]; ring
    have d10 : zN q tm sp sm kk B ((1-q*tm)*(1-sp)) 0 (q*(1-sp) - kk) 1 -
        zN q tm sp sm kk B ((1-q*tm)*(1-sp)) 0 (q*(1-sp) - kk) 0 =
        q*sm*tm*((1-sp)*(1-q) + (1-tm)*kk) := by rw [zN_1, zN_0]; ring
    have d06 : zN q tm sp sm kk B ((1-q*tm)*(1-sp)) 0 (q*(1-sp) - kk) 0 -
        zN q tm sp sm kk B ((1-q*tm)*(1-sp)) 0 (q*(1-sp) - kk) 6 =
        (1-q*tm)*(1-sp)*(sm*(1-q)-tm) + q*sm*(1-tm)*((1-sp) - tm*kk) := by
      rw [zN_0, zN_6]; ring
    have d64 : zN q tm sp sm kk B ((1-q*tm)*(1-sp)) 0 (q*(1-sp) - kk) 6 -
        zN q tm sp sm kk B ((1-q*tm)*(1-sp)) 0 (q*(1-sp) - kk) 4 = -Kc q tm sp sm kk := by
      rw [zN_6, zN_4]; unfold Kc; ring
    have d43 : zN q tm sp sm kk B ((1-q*tm)*(1-sp)) 0 (q*(1-sp) - kk) 4 =
        zN q tm sp sm kk B ((1-q*tm)*(1-sp)) 0 (q*(1-sp) - kk) 3 := by
      rw [zN_4, zN_3]; ring
    refine ruL ?_ ?_ ?_ ?_
    · show zN q tm sp sm kk B _ 0 (q*(1-sp) - kk) 0 < zN q tm sp sm kk B _ 0 (q*(1-sp) - kk) 1
      have : 0 < q*sm*tm*((1-sp)*(1-q) + (1-tm)*kk) := by positivity
      linarith
    · show zN q tm sp sm kk B _ 0 (q*(1-sp) - kk) 6 < zN q tm sp sm kk B _ 0 (q*(1-sp) - kk) 0
      have : 0 < (1-q*tm)*(1-sp)*(sm*(1-q)-tm) + q*sm*(1-tm)*((1-sp) - tm*kk) := by
        have h1 : 0 ≤ (1-q*tm)*(1-sp)*(sm*(1-q)-tm) :=
          mul_nonneg (mul_pos tp0 r1).le (by linarith)
        have h2 : 0 < q*sm*(1-tm)*((1-sp) - tm*kk) := by
          have : 0 < (1-sp) - tm*kk := by linarith
          positivity
        linarith
      linarith
    · show zN q tm sp sm kk B _ 0 (q*(1-sp) - kk) 4 < zN q tm sp sm kk B _ 0 (q*(1-sp) - kk) 6
      linarith
    · show zN q tm sp sm kk B _ 0 (q*(1-sp) - kk) 3 = zN q tm sp sm kk B _ 0 (q*(1-sp) - kk) 4
      linarith

end Cor
end Minimality.CaseC20

end

section

/-!
# C4: corner leaf W (`Kc >= 0`, `Kg >= 0`, not (`Kc = 0` and `C1 = 0`)): view `x4 - x6`, cycle `(0,1,4,6,2)`
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace Cor

/-- GAPS `Kg = kk (1-sm) - sp`. -/
def Kg (sp sm kk : ℝ) : ℝ := kk*(1-sm) - sp

/-- GAPS `C1(B) = sm t e - (1-sm)(tm tp - sp B)` with `e = kk tm - q tm`. -/
def Cone (q tm sp sm kk B : ℝ) : ℝ :=
  sm*(1-tm)*(kk*tm - q*tm) - (1-sm)*(tm*(1-q*tm) - sp*B)

/-- Lex positivity from a nonnegative first entry and a positive second entry. -/
lemma lp3 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) : h21b_LP a b := by
  rcases ha.lt_or_eq with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h.symm, hb⟩

/-- Five-cycle shape of W: `z0 < z1`, `z3 < z2`, and the point 4 is below 0 or below 3. -/
theorem ruW {z : ZMod 5 → ℝ} (h01 : z 0 < z 1) (h32 : z 3 < z 2) (h4 : z 4 < z 0 ∨ z 4 < z 3) :
    RobUni z := by
  rcases h4 with h4 | h4 <;> robuni5

/-- **Leaf W**: view `u = (0, -(1-sm), -1)`, tilt `(-1, 0, 0)`. -/
theorem leaf_W {q tm sp sm kk B : ℝ} (h : Hy q tm sp sm kk B) (hK : 0 ≤ Kc q tm sp sm kk)
    (hG : 0 ≤ Kg sp sm kk) (hn : ¬ (Kc q tm sp sm kk = 0 ∧ Cone q tm sp sm kk B = 0)) :
    LeafOK q tm sp sm kk B cycW patW 0 (-(1-sm)) (-1) (-1) 0 0 := by
  obtain ⟨tm0, sm0, sp0, q0, tp0, kk0, t1, r1, s1, q2, tmsm⟩ := h.pf
  have hB := h.hB
  have e0 : NN q tm sp sm kk 0 (-(1-sm)) (-1) 0 = sm - tm := by rw [NN_0]; ring
  have e1 : NN q tm sp sm kk 0 (-(1-sm)) (-1) 1 = (1-q*tm)*Kg sp sm kk := by
    rw [NN_1]; unfold Kg; ring
  have e2 : NN q tm sp sm kk 0 (-(1-sm)) (-1) 2 = 1 - sm := by rw [NN_2]; ring
  have e3 : NN q tm sp sm kk 0 (-(1-sm)) (-1) 3 = tm := by rw [NN_3]; ring
  have e4 : NN q tm sp sm kk 0 (-(1-sm)) (-1) 4 = -(q*((1-sm) + tm)) := by rw [NN_4]; ring
  have e5 : NN q tm sp sm kk 0 (-(1-sm)) (-1) 5 = -((1-q*tm)*(kk*(1-sm) + (1-sp))) := by
    rw [NN_5]; ring
  have e6 : NN q tm sp sm kk 0 (-(1-sm)) (-1) 6 = 0 := by rw [NN_6]; ring
  have e7 : NN q tm sp sm kk 0 (-(1-sm)) (-1) 7 = 0 := by rw [NN_7]; ring
  have v1 : NN q tm sp sm kk (-1) 0 0 1 = q*sp := by rw [NN_1]; ring
  have v6 : NN q tm sp sm kk (-1) 0 0 6 = -1 := by rw [NN_6]; ring
  have v7 : NN q tm sp sm kk (-1) 0 0 7 = kk := by rw [NN_7]; ring
  refine ⟨⟨0, ?_⟩, ?_, ?_⟩
  · rw [e0]; linarith
  · intro t
    have ht : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 := by revert t; decide
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨fun _ => lp1 (by rw [e0]; linarith), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp3 (by rw [e1]; exact mul_nonneg tp0.le hG) (by rw [v1]; positivity),
        fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp1 (by rw [e2]; exact s1), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp1 (by rw [e3]; exact tm0), fun h => absurd h (by decide)⟩
    · have p4 : 0 < q*((1-sm) + tm) := by positivity
      exact ⟨fun h => absurd h (by decide), fun _ => lp1 (by rw [e4]; linarith)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lp1 (by
        rw [e5]; have : 0 < (1-q*tm)*(kk*(1-sm) + (1-sp)) := by positivity
        linarith)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lp2 (by rw [e6]; ring) (by rw [v6]; norm_num)⟩
    · exact ⟨fun _ => lp2 (by rw [e7]) (by rw [v7]; exact kk0), fun h => absurd h (by decide)⟩
  · have d10 : zN q tm sp sm kk B 0 (-(1-sm)) (-1) 1 - zN q tm sp sm kk B 0 (-(1-sm)) (-1) 0 =
        q*tm*(sm-tm) := by rw [zN_1, zN_0]; ring
    have d46 : zN q tm sp sm kk B 0 (-(1-sm)) (-1) 4 - zN q tm sp sm kk B 0 (-(1-sm)) (-1) 6 =
        (1-sm)^2*B + sm*(1-tm)*tm := by rw [zN_4, zN_6]; ring
    have d2 : zN q tm sp sm kk B 0 (-(1-sm)) (-1) 2 =
        (1-sp)*zN q tm sp sm kk B 0 (-(1-sm)) (-1) 0 + sp*zN q tm sp sm kk B 0 (-(1-sm)) (-1) 6
          - Kc q tm sp sm kk := by rw [zN_2, zN_0, zN_6]; unfold Kc; ring
    have d02 : zN q tm sp sm kk B 0 (-(1-sm)) (-1) 0 - zN q tm sp sm kk B 0 (-(1-sm)) (-1) 2 =
        Cone q tm sp sm kk B := by rw [zN_2, zN_0]; unfold Cone; ring
    refine ruW ?_ ?_ ?_
    · show zN q tm sp sm kk B _ _ _ 0 < zN q tm sp sm kk B _ _ _ 1
      have hs : 0 < sm - tm := by linarith
      have : 0 < q*tm*(sm-tm) := by positivity
      linarith
    · show zN q tm sp sm kk B _ _ _ 6 < zN q tm sp sm kk B _ _ _ 4
      have : 0 < (1-sm)^2*B + sm*(1-tm)*tm := by
        have : 0 < B := by linarith
        positivity
      linarith
    · show zN q tm sp sm kk B _ _ _ 2 < zN q tm sp sm kk B _ _ _ 0 ∨
        zN q tm sp sm kk B _ _ _ 2 < zN q tm sp sm kk B _ _ _ 6
      by_contra hc
      push Not at hc
      obtain ⟨c0, c6⟩ := hc
      apply hn
      have k0 : Kc q tm sp sm kk = 0 := by
        have := mul_nonneg r1.le (sub_nonneg.2 c0)
        have := mul_nonneg sp0.le (sub_nonneg.2 c6)
        nlinarith
      refine ⟨k0, ?_⟩
      have hh : (1-sp)*(zN q tm sp sm kk B 0 (-(1-sm)) (-1) 2 - zN q tm sp sm kk B 0 (-(1-sm)) (-1) 0)
          + sp*(zN q tm sp sm kk B 0 (-(1-sm)) (-1) 2 - zN q tm sp sm kk B 0 (-(1-sm)) (-1) 6) = 0 := by
        rw [k0] at d2; linarith
      have a1 := mul_nonneg r1.le (sub_nonneg.2 c0)
      have a2 := mul_nonneg sp0.le (sub_nonneg.2 c6)
      have : (1-sp)*(zN q tm sp sm kk B 0 (-(1-sm)) (-1) 2 - zN q tm sp sm kk B 0 (-(1-sm)) (-1) 0) = 0 := by
        linarith
      have := (mul_eq_zero.1 this).resolve_left r1.ne'
      linarith

end Cor
end Minimality.CaseC20

end

section

/-!
# C5: corner leaves Y (`Kg < 0`, `B < psi`) and X (`Bd > 0`): cycle `(0,1,4,5)`
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace Cor

/-- GAPS `psi * sm * (1-sm)`: `B < psi` is `B sm (1-sm) < psiN`. -/
def psiN (tm sm : ℝ) : ℝ := tm*(1-sm) + (1-tm)*tm*sm

/-- GAPS `Bd = sp (p + tp (sm - tm)) - kk tp sm g1`, `p = q tm`, `g1 = 1 + tm - sm`. -/
def Bd (q tm sp sm kk : ℝ) : ℝ :=
  sp*(q*tm + (1-q*tm)*(sm-tm)) - kk*(1-q*tm)*sm*(1+tm-sm)

/-- Four-cycle shape: `z0 < z1 < z2` suffices. -/
theorem ru4 {z : ZMod 4 → ℝ} (h01 : z 0 < z 1) (h12 : z 1 < z 2) : RobUni z := by
  refine robUni4 ?_ ?_
  · rintro ⟨a1, a2, a3, a4⟩; linarith
  · rintro ⟨a1, a2, a3, a4⟩; linarith

/-- **Leaf Y**: `Kg < 0`, `B < psi`; view `(0, -(1-sm), -1)`, tilt `(1-sm, 0, 2)`. -/
theorem leaf_Y {q tm sp sm kk B : ℝ} (h : Hy q tm sp sm kk B) (hG : Kg sp sm kk < 0)
    (hB : B*(sm*(1-sm)) < psiN tm sm) :
    LeafOK q tm sp sm kk B cycY patY 0 (-(1-sm)) (-1) (1-sm) 0 2 := by
  obtain ⟨tm0, sm0, sp0, q0, tp0, kk0, t1, r1, s1, q2, tmsm⟩ := h.pf
  have hBt := h.hB
  have e0 : NN q tm sp sm kk 0 (-(1-sm)) (-1) 0 = sm - tm := by rw [NN_0]; ring
  have e1 : NN q tm sp sm kk 0 (-(1-sm)) (-1) 1 = (1-q*tm)*Kg sp sm kk := by
    rw [NN_1]; unfold Kg; ring
  have e2 : NN q tm sp sm kk 0 (-(1-sm)) (-1) 2 = 1 - sm := by rw [NN_2]; ring
  have e3 : NN q tm sp sm kk 0 (-(1-sm)) (-1) 3 = tm := by rw [NN_3]; ring
  have e4 : NN q tm sp sm kk 0 (-(1-sm)) (-1) 4 = -(q*((1-sm) + tm)) := by rw [NN_4]; ring
  have e5 : NN q tm sp sm kk 0 (-(1-sm)) (-1) 5 = -((1-q*tm)*(kk*(1-sm) + (1-sp))) := by
    rw [NN_5]; ring
  have e6 : NN q tm sp sm kk 0 (-(1-sm)) (-1) 6 = 0 := by rw [NN_6]; ring
  have e7 : NN q tm sp sm kk 0 (-(1-sm)) (-1) 7 = 0 := by rw [NN_7]; ring
  have v6 : NN q tm sp sm kk (1-sm) 0 2 6 = -(1-sm) := by rw [NN_6]; ring
  have v7 : NN q tm sp sm kk (1-sm) 0 2 7 = -(kk*(1-sm)) := by rw [NN_7]; ring
  refine ⟨⟨0, ?_⟩, ?_, ?_⟩
  · rw [e0]; linarith
  · intro t
    have ht : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 := by revert t; decide
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨fun _ => lp1 (by rw [e0]; linarith), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lp1 (by
        rw [e1]; have := mul_pos tp0 (neg_pos.2 hG); linarith)⟩
    · exact ⟨fun _ => lp1 (by rw [e2]; exact s1), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp1 (by rw [e3]; exact tm0), fun h => absurd h (by decide)⟩
    · have p4 : 0 < q*((1-sm) + tm) := by positivity
      exact ⟨fun h => absurd h (by decide), fun _ => lp1 (by rw [e4]; linarith)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lp1 (by
        rw [e5]; have : 0 < (1-q*tm)*(kk*(1-sm) + (1-sp)) := by positivity
        linarith)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lp2 (by rw [e6]; ring) (by rw [v6]; linarith)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lp2 (by rw [e7]; ring) (by
        rw [v7]; have := mul_pos kk0 s1; linarith)⟩
  · have d10 : zN q tm sp sm kk B 0 (-(1-sm)) (-1) 1 - zN q tm sp sm kk B 0 (-(1-sm)) (-1) 0 =
        q*tm*(sm-tm) := by rw [zN_1, zN_0]; ring
    have d41 : zN q tm sp sm kk B 0 (-(1-sm)) (-1) 4 - zN q tm sp sm kk B 0 (-(1-sm)) (-1) 1 =
        (sm*(1-sm)*(psiN tm sm - B*(sm*(1-sm))))/(sm*(1-sm)) := by
      rw [zN_4, zN_1]; unfold psiN; field_simp; ring
    refine ru4 ?_ ?_
    · show zN q tm sp sm kk B _ _ _ 0 < zN q tm sp sm kk B _ _ _ 1
      have hs : 0 < sm - tm := by linarith
      have : 0 < q*tm*(sm-tm) := by positivity
      linarith
    · show zN q tm sp sm kk B _ _ _ 1 < zN q tm sp sm kk B _ _ _ 4
      have : 0 < (sm*(1-sm)*(psiN tm sm - B*(sm*(1-sm))))/(sm*(1-sm)) := by
        apply div_pos
        · exact mul_pos (mul_pos sm0 s1) (by linarith)
        · positivity
      linarith

end Cor
end Minimality.CaseC20

end

section

/-!
# C6: corner leaf X (`Bd > 0`): view `cross(N_D, N_G)`, cycle `(0,1,4,5)`, tilt `x3 - x1`
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace Cor

/-- Four-cycle shape: `z3 < z0 < z1`. -/
theorem ru4' {z : ZMod 4 → ℝ} (h01 : z 0 < z 1) (h30 : z 3 < z 0) : RobUni z := by
  refine robUni4 ?_ ?_
  · rintro ⟨a1, a2, a3, a4⟩; linarith
  · rintro ⟨a1, a2, a3, a4⟩; linarith

/-- **Leaf X**: `Bd > 0`; view `u = (tm, -sm g1, tm - sm)`, tilt `(-(1-tm), 0, -1)`. -/
theorem leaf_X {q tm sp sm kk B : ℝ} (h : Hy q tm sp sm kk B) (hX : 0 < Bd q tm sp sm kk) :
    LeafOK q tm sp sm kk B cycY patY tm (-(sm*(1+tm-sm))) (tm - sm) (-(1-tm)) 0 (-1) := by
  obtain ⟨tm0, sm0, sp0, q0, tp0, kk0, t1, r1, s1, q2, tmsm⟩ := h.pf
  have hroof := h.roof
  have g1 : 0 < 1 + tm - sm := by linarith
  have hd : 0 < sm - tm := by linarith
  have e0 : NN q tm sp sm kk tm (-(sm*(1+tm-sm))) (tm - sm) 0 = sm*(sm-tm) := by rw [NN_0]; ring
  have e1 : NN q tm sp sm kk tm (-(sm*(1+tm-sm))) (tm - sm) 1 = -Bd q tm sp sm kk := by
    rw [NN_1]; unfold Bd; ring
  have e2 : NN q tm sp sm kk tm (-(sm*(1+tm-sm))) (tm - sm) 2 = sm*(1+tm-sm) := by rw [NN_2]; ring
  have e3 : NN q tm sp sm kk tm (-(sm*(1+tm-sm))) (tm - sm) 3 = 0 := by rw [NN_3]; ring
  have e4 : NN q tm sp sm kk tm (-(sm*(1+tm-sm))) (tm - sm) 4 = -(q*(1+tm-sm)*(sm-tm)) := by
    rw [NN_4]; ring
  have e5 : NN q tm sp sm kk tm (-(sm*(1+tm-sm))) (tm - sm) 5 < 0 := by
    have key : tm * NN q tm sp sm kk tm (-(sm*(1+tm-sm))) (tm - sm) 5 =
        (1-sp)*(1-q*tm)*(1+tm-sm)*(tm-sm) - ((1-sp) - kk*tm)*(tm - (1-q*tm)*sm*(1+tm-sm)) := by
      rw [NN_5]; ring
    have key2 : NN q tm sp sm kk tm (-(sm*(1+tm-sm))) (tm - sm) 5 =
        -(q*(1-sp)*tm) - (1-q*tm)*(1-sp)*(sm-tm) + kk*(tm - (1-q*tm)*sm*(1+tm-sm)) := by
      rw [NN_5]; ring
    have n1 : 0 < (1-sp)*(1-q*tm)*(1+tm-sm)*(sm-tm) := by positivity
    have n2 : 0 < q*(1-sp)*tm := by positivity
    have n3 : 0 < (1-q*tm)*(1-sp)*(sm-tm) := by positivity
    by_cases hc : 0 ≤ tm - (1-q*tm)*sm*(1+tm-sm)
    · have h1 := mul_nonneg (by linarith : 0 ≤ (1-sp) - kk*tm) hc
      have h2 : tm * NN q tm sp sm kk tm (-(sm*(1+tm-sm))) (tm - sm) 5 < 0 := by nlinarith
      by_contra hn; push Not at hn
      nlinarith
    · push Not at hc
      have := mul_pos kk0 (neg_pos.2 hc)
      rw [key2]; nlinarith
  have e6 : NN q tm sp sm kk tm (-(sm*(1+tm-sm))) (tm - sm) 6 = 0 := by rw [NN_6]; ring
  have e7 : NN q tm sp sm kk tm (-(sm*(1+tm-sm))) (tm - sm) 7 = -(kk*tm) := by rw [NN_7]; ring
  have v3 : NN q tm sp sm kk (-(1-tm)) 0 (-1) 3 = sm := by rw [NN_3]; ring
  have v6 : NN q tm sp sm kk (-(1-tm)) 0 (-1) 6 = tm - sm := by rw [NN_6]; ring
  refine ⟨⟨0, ?_⟩, ?_, ?_⟩
  · rw [e0]; positivity
  · intro t
    have ht : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 := by revert t; decide
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨fun _ => lp1 (by rw [e0]; positivity), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lp1 (by rw [e1]; linarith)⟩
    · exact ⟨fun _ => lp1 (by rw [e2]; positivity), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp2 e3 (by rw [v3]; exact sm0), fun h => absurd h (by decide)⟩
    · have : 0 < q*(1+tm-sm)*(sm-tm) := by positivity
      exact ⟨fun h => absurd h (by decide), fun _ => lp1 (by rw [e4]; linarith)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lp1 (by linarith)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lp2 (by rw [e6]; ring) (by rw [v6]; linarith)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lp1 (by
        rw [e7]; have := mul_pos kk0 tm0; linarith)⟩
  · have d10 : zN q tm sp sm kk B tm (-(sm*(1+tm-sm))) (tm - sm) 1 -
        zN q tm sp sm kk B tm (-(sm*(1+tm-sm))) (tm - sm) 0 = q*tm*sm*(sm-tm) := by
      rw [zN_1, zN_0]; ring
    have d05 : zN q tm sp sm kk B tm (-(sm*(1+tm-sm))) (tm - sm) 0 =
        sm*(sm-tm)*(tm - q*tm) := by rw [zN_0]; ring
    refine ru4' ?_ ?_
    · show zN q tm sp sm kk B _ _ _ 0 < zN q tm sp sm kk B _ _ _ 1
      have : 0 < q*tm*sm*(sm-tm) := by positivity
      linarith
    · show zN q tm sp sm kk B _ _ _ 5 < zN q tm sp sm kk B _ _ _ 0
      rw [zN_5, d05]
      have : 0 < tm - q*tm := by nlinarith
      positivity

end Cor
end Minimality.CaseC20

end

section

/-!
# C7: corner leaf T (`Kc >= 0`, `Kg < 0`, `B >= psi`, `Bd <= 0`): view `x0 - x2`, cycle `(2,5,3,4,6)`
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace Cor

/-- Five-cycle shape of T. -/
theorem ruT {z : ZMod 5 → ℝ} (h12 : z 1 < z 2) (h32 : z 3 < z 2) (h43 : z 4 < z 3)
    (h0 : z 0 < z 1 ∨ z 0 < z 4) : RobUni z := by
  rcases h0 with h0 | h0 <;> robuni5

/-- `Bd <= 0` forces the facing value of `G` at the view of T to be positive. -/
lemma Gs_pos {q tm sp sm kk B : ℝ} (h : Hy q tm sp sm kk B) (hBd : Bd q tm sp sm kk ≤ 0) :
    0 < (1-sp) - q*(1+tm-sm) + (1-sm)*kk := by
  obtain ⟨tm0, sm0, sp0, q0, tp0, kk0, t1, r1, s1, q2, tmsm⟩ := h.pf
  have hroof := h.roof
  by_contra hc
  push Not at hc
  have g1 : 0 < 1 + tm - sm := by linarith
  have hkq : kk < q := by
    have : kk * (1+tm-sm) < q * (1+tm-sm) := by nlinarith
    exact lt_of_mul_lt_mul_right this g1.le
  have hqg : q*(1+tm-sm) < 1 := by nlinarith
  have hP0 : 0 < q*tm + (1-q*tm)*(sm-tm) := by
    have : 0 < sm - tm := by linarith
    positivity
  have hd : 0 < sm - tm := by linarith
  -- lower bound for Bd using sp >= 1 - q g1 + s kk
  have h1 : (q*tm + (1-q*tm)*(sm-tm)) * (1 - q*(1+tm-sm) + (1-sm)*kk) ≤
      sp*(q*tm + (1-q*tm)*(sm-tm)) := by nlinarith
  have hL0 : 0 < (q*tm + (1-q*tm)*(sm-tm)) * (1 - q*(1+tm-sm)) := by
    apply mul_pos hP0; linarith
  have hLq : 0 < (1-q*tm)*(sm-tm)*(1 - q*(1+tm-sm)) := by
    have : 0 < 1 - q*(1+tm-sm) := by linarith
    positivity
  have key : q * ((q*tm + (1-q*tm)*(sm-tm)) * (1 - q*(1+tm-sm) + (1-sm)*kk)
      - kk*(1-q*tm)*sm*(1+tm-sm)) =
      ((q*tm + (1-q*tm)*(sm-tm)) * (1 - q*(1+tm-sm))) * (q - kk) +
      ((1-q*tm)*(sm-tm)*(1 - q*(1+tm-sm))) * (q * kk) / q * 1 := by
    field_simp
    ring
  have hpos : 0 < (q*tm + (1-q*tm)*(sm-tm)) * (1 - q*(1+tm-sm) + (1-sm)*kk)
      - kk*(1-q*tm)*sm*(1+tm-sm) := by
    have e1 := mul_pos hL0 (sub_pos.2 hkq)
    have e2 := mul_pos hLq kk0
    have : 0 < q * ((q*tm + (1-q*tm)*(sm-tm)) * (1 - q*(1+tm-sm) + (1-sm)*kk)
      - kk*(1-q*tm)*sm*(1+tm-sm)) := by rw [key]; nlinarith
    exact pos_of_mul_pos_right this q0.le
  unfold Bd at hBd
  nlinarith

end Cor
end Minimality.CaseC20

end

section

/-!
# C8: leaf T assembly
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace Cor

/-- `Kc >= 0` and `B >= psi` give `Cone(B) > 0`. -/
lemma Cone_pos {q tm sp sm kk B : ℝ} (h : Hy q tm sp sm kk B) (hK : 0 ≤ Kc q tm sp sm kk)
    (hBp : psiN tm sm ≤ B*(sm*(1-sm))) : 0 < Cone q tm sp sm kk B := by
  obtain ⟨tm0, sm0, sp0, q0, tp0, kk0, t1, r1, s1, q2, tmsm⟩ := h.pf
  have hQ := h.hQ
  have hp1 : sm*(q*tm) ≤ tm*(sm - tm) := by nlinarith
  have hbr : 0 < psiN tm sm - sm^2*(1-tm)*(q*tm) - sm*(1-q*tm)*tm*(1-sm) := by
    unfold psiN
    have g1 : 0 < 1 + tm - sm := by linarith
    have e : tm*(1-sm) + (1-tm)*tm*sm - sm^2*(1-tm)*(q*tm) - sm*(1-q*tm)*tm*(1-sm) =
        tm*((1-sm)^2 + sm*(1-tm)*(1+tm-sm) + sm*(q*tm)*(1-sm)) +
          sm*(1-tm)*(tm*(sm-tm) - sm*(q*tm)) := by ring
    rw [e]
    have : 0 ≤ sm*(1-tm)*(tm*(sm-tm) - sm*(q*tm)) := by
      apply mul_nonneg (by positivity); linarith
    have : 0 < tm*((1-sm)^2 + sm*(1-tm)*(1+tm-sm) + sm*(q*tm)*(1-sm)) := by positivity
    linarith
  have key : sm * Cone q tm sp sm kk B = sm * Kc q tm sp sm kk +
      sp*(psiN tm sm - sm^2*(1-tm)*(q*tm) - sm*(1-q*tm)*tm*(1-sm)) +
      sp*(B*(sm*(1-sm)) - psiN tm sm) := by
    unfold Cone Kc psiN; ring
  have : 0 < sm * Cone q tm sp sm kk B := by
    rw [key]
    have := mul_pos sp0 hbr
    have := mul_nonneg sp0.le (sub_nonneg.2 hBp)
    have := mul_nonneg sm0.le hK
    linarith
  exact pos_of_mul_pos_right this sm0.le

end Cor
end Minimality.CaseC20

end

