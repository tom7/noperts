module

public import Minimality.Type20Leaf
public import Minimality.Type20IMCF

@[expose] public section

/-!
# Type 20, item I_V: the metric line `V = 0135/026`

Line 271 of `CaseC20Face` (and its `R`-image, line 272).  Each point set on the locus is Rupert:
segment leaves along the edges (`seg_leaf`), the shape lemmas `S1`-`S7`, and the leaves `C1`-`C9`,
`K1` of the covering notes; `isRupert_IV` and `isRupert_IV_R`.
-/

section

/-!
# I_V: segment cells and the segment-leaf assembler

The segment views used by the standard leaves (C5, C2, C6, C7, C8, C9) as `S0xSeg` data, and
`seg_leaf`: a segment cell is Rupert from the facing polynomials `nf` of the facets through neither
endpoint and `RobUni` of the frame depths (either at the view or at its negative).
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.H20S

/-- C5: `s06:01352`, up `A D E F G H`, down `B C`. -/
def ivs_C5 : S0xSeg 7 8 5 where
  i := 0
  j := 6
  pat := ![true, false, false, true, true, true, true, true]
  c := ![0, 1, 3, 5, 2]

/-- C2: `s46:0145`, up `B E F G H`, down `A C D`. -/
def ivs_C2 : S0xSeg 7 8 4 where
  i := 4
  j := 6
  pat := ![false, true, false, false, true, true, true, true]
  c := ![0, 1, 4, 5]

/-- C6: `s14:25346`, up `D H`, down `A B C E F G`. -/
def ivs_C6 : S0xSeg 7 8 5 where
  i := 1
  j := 4
  pat := ![false, false, false, true, false, false, false, true]
  c := ![2, 5, 3, 4, 6]

/-- C7: `s25:01462`, up `A B C D H`, down `E F G`. -/
def ivs_C7 : S0xSeg 7 8 5 where
  i := 2
  j := 5
  pat := ![true, true, true, true, false, false, false, true]
  c := ![0, 1, 4, 6, 2]

/-- C8: `s16:0145`, up `B E F G H`, down `A C D`. -/
def ivs_C8 : S0xSeg 7 8 4 where
  i := 1
  j := 6
  pat := ![false, true, false, false, true, true, true, true]
  c := ![0, 1, 4, 5]

/-- C9: `s25:0162`, up `A B C D G H`, down `E F`. -/
def ivs_C9 : S0xSeg 7 8 4 where
  i := 2
  j := 5
  pat := ![true, true, true, true, false, false, true, true]
  c := ![0, 1, 6, 2]

theorem ivs_C5_good : ivs_C5.Good h20s_S := by decide
theorem ivs_C2_good : ivs_C2.Good h20s_S := by decide
theorem ivs_C6_good : ivs_C6.Good h20s_S := by decide
theorem ivs_C7_good : ivs_C7.Good h20s_S := by decide
theorem ivs_C8_good : ivs_C8.Good h20s_S := by decide
theorem ivs_C9_good : ivs_C9.Good h20s_S := by decide

end Minimality.H20S

namespace Minimality.CaseC20
namespace IVT
open Minimality.H20S
variable {x : Fin 7 → ℝ³} (F : Frame20 x) (FF : S0xFac 8 h20s_S x)

include FF in
/-- **Segment-cell assembler**: if `x j - x i = fvC q`, the facings `nf` of the facets through neither
endpoint follow the pattern, and the frame depths along the cycle are robustly unimodal, then Rupert. -/
theorem seg_leaf (hx : Function.Injective x) {k : ℕ} [NeZero k] (s : S0xSeg 7 8 k)
    (hg : s.Good h20s_S) (q : C3) (hq : x s.j - x s.i = F.toFrame7.fvC q)
    (hlit : ∀ t, s.i ∉ h20s_S t → s.j ∉ h20s_S t →
      (s.pat t = true → 0 < nf F.S q t) ∧ (s.pat t = false → nf F.S q t < 0))
    (hU : RobUni (fun a : ZMod k => F.dep q (s.c a))) : IsRupert (univ.image x) := by
  refine s0x_seg_rupert FF hx s hg ⟨fun t h0 h1 => ?_, ?_⟩
  · obtain ⟨l, hl, hf⟩ := facing F FF t
    have e : FF.f t (x s.j) - FF.f t (x s.i) = l * nf F.S q t := by
      rw [FF.hN t (x s.j) (x s.i), hq, hf q]
    obtain ⟨h2, h3⟩ := hlit t h0 h1
    exact ⟨fun hp => by rw [e]; exact mul_pos hl (h2 hp),
      fun hp => by rw [e]; exact mul_neg_of_pos_of_neg hl (h3 hp)⟩
  · rw [hq]; exact F.robUni_of_dep _ q hU

include FF in
/-- The same with the depths given at the opposite view `-q` (the silhouette test is invariant). -/
theorem seg_leaf_neg (hx : Function.Injective x) {k : ℕ} [NeZero k] (s : S0xSeg 7 8 k)
    (hg : s.Good h20s_S) (a b c : ℝ) (hq : x s.j - x s.i = F.toFrame7.fvC ⟨a, b, c⟩)
    (hlit : ∀ t, s.i ∉ h20s_S t → s.j ∉ h20s_S t →
      (s.pat t = true → 0 < nf F.S ⟨a, b, c⟩ t) ∧ (s.pat t = false → nf F.S ⟨a, b, c⟩ t < 0))
    (hU : RobUni (fun i : ZMod k => F.dep ⟨-a, -b, -c⟩ (s.c i))) : IsRupert (univ.image x) := by
  refine seg_leaf F FF hx s hg ⟨a, b, c⟩ hq hlit ?_
  have := robUni_neg hU
  convert this using 2 with i
  rw [dep_neg]; ring

include FF in
/-- Tilted leaf: the same as `leaf_of_view` with the depths given at `-qu`. -/
theorem leaf_of_view_neg {k : ℕ} [NeZero k] (hx : Function.Injective x) (hk : 3 ≤ k)
    {c : ZMod k → Fin 7} (hc : Function.Injective c) {pat : Fin 8 → Bool}
    (hcyc : S0xCycOK h20s_S c pat) (a b d : ℝ) (qv : C3) (t0 : Fin 8) (hu : nf F.S ⟨a, b, d⟩ t0 ≠ 0)
    (h : ∀ t, (pat t = true → h21b_LP (nf F.S ⟨a, b, d⟩ t) (nf F.S qv t)) ∧
      (pat t = false → h21b_LP (-nf F.S ⟨a, b, d⟩ t) (-nf F.S qv t)))
    (hU : RobUni (fun i : ZMod k => F.dep ⟨-a, -b, -d⟩ (c i))) : IsRupert (univ.image x) := by
  refine leaf_of_view F FF hx hk hc hcyc ⟨a, b, d⟩ qv t0 hu h ?_
  have := robUni_neg hU
  convert this using 2 with i
  rw [dep_neg]; ring

end IVT
end Minimality.CaseC20

end

section

/-!
# I_V: shape lemmas S1-S7 and the sign identities of COVER.md (pure `Shape20` algebra)

Item hypothesis `hV : Vq = 0` (the left side of CaseC20Face line 271 is `Vq` up to ring).
-/

open Minimality Minimality.CaseC20

namespace Minimality.CaseC20
namespace Shape20
variable (S : Shape20)

lemma rhop_pos : 0 < (S.hp*(1-S.sp)-S.kp*(1-S.tp)) := by linarith [S.roof_p']
lemma rhom_pos : 0 < (S.km*(1-S.tm)-S.hm*(1-S.sm)) := by linarith [S.roof_m']
lemma W_pos : 0 < (S.hm*S.tp+S.hp*S.tm) := by have := S.hm_pos; have := S.tp_pos; have := S.hp_pos; have := S.tm_pos; positivity

/-- S1: on the item, `A1 > 0` (V1 and the upper roof). -/
lemma iv_A1_pos (hV : ((1-S.sp)*(S.hm*S.tp+S.hp*S.tm)-S.kp*S.tm) = 0) : 0 < (S.hp*S.tm-S.hm*(1-S.tp)) := by
  have e : S.tm * (S.hp*(1-S.sp)-S.kp*(1-S.tp)) = (1-S.sp) * S.tp * (S.hp*S.tm-S.hm*(1-S.tp)) := by linear_combination (1-S.tp) * hV
  have h1 : 0 < S.tm * (S.hp*(1-S.sp)-S.kp*(1-S.tp)) := mul_pos S.tm_pos (S.rhop_pos)
  have h2 : 0 < (1-S.sp) * S.tp * (S.hp*S.tm-S.hm*(1-S.tp)) := by rw [← e]; exact h1
  exact pos_of_mul_pos_right h2 (by have := S.sp1; have := S.tp_pos; positivity)

/-- S2: on the item, `kp > (1-sp) hp` (V5). -/
lemma iv_S2 (hV : ((1-S.sp)*(S.hm*S.tp+S.hp*S.tm)-S.kp*S.tm) = 0) : (1-S.sp)*S.hp < S.kp := by
  have e : S.tm * (S.kp - (1-S.sp)*S.hp) = (1-S.sp) * S.tp * S.hm := by linear_combination (-1) * hV
  have h2 : 0 < (1-S.sp) * S.tp * S.hm := by
    have := S.sp1; have := S.tp_pos; have := S.hm_pos; positivity
  rw [← e] at h2
  have := pos_of_mul_pos_right h2 S.tm_pos.le
  linarith

/-- S3: outside the quadrant `A06 > 0, D06 > 0`, `kap > 0` and `km > sm hp`. -/
lemma iv_S3 (hV : ((1-S.sp)*(S.hm*S.tp+S.hp*S.tm)-S.kp*S.tm) = 0) (h : ¬ (0 < (S.hm*(1-S.sm*S.tp)-S.km*(1-S.tm)+S.hp*S.sm*(1-S.tm)) ∧ 0 < (S.sm*(S.hm*S.tp+S.hp*S.tm)-S.tm*S.km))) : 0 < (S.hm-(S.sm*(S.hm*S.tp+S.hp*S.tm)-S.tm*S.km)) ∧ S.sm * S.hp < S.km := by
  have tm1 := S.tm1; have tp0 := S.tp_pos; have tm0 := S.tm_pos; have sm0 := S.sm_pos
  have hm0 := S.hm_pos; have hp0 := S.hp_pos; have sm1 := S.sm1
  have hsmtp : S.sm * S.tp < 1 := by nlinarith [S.sm_lt, S.tp_lt]
  by_cases hD : (S.sm*(S.hm*S.tp+S.hp*S.tm)-S.tm*S.km) ≤ 0
  · refine ⟨by linarith, ?_⟩
    have e : S.tm * (S.km - S.sm*S.hp) = -(S.sm*(S.hm*S.tp+S.hp*S.tm)-S.tm*S.km) + S.sm*S.hm*S.tp := by ring
    have h2 : 0 < S.tm * (S.km - S.sm*S.hp) := by rw [e]; have := mul_pos (mul_pos sm0 hm0) tp0; linarith
    have := pos_of_mul_pos_right h2 tm0.le
    linarith
  · push Not at hD
    have hA : (S.hm*(1-S.sm*S.tp)-S.km*(1-S.tm)+S.hp*S.sm*(1-S.tm)) ≤ 0 := by
      by_contra hc; push Not at hc; exact h ⟨hc, hD⟩
    have hkm : S.sm * S.hp < S.km := by
      have e : S.km*(1-S.tm) - S.sm*S.hp*(1-S.tm) = -(S.hm*(1-S.sm*S.tp)-S.km*(1-S.tm)+S.hp*S.sm*(1-S.tm)) + S.hm*(1-S.sm*S.tp) := by ring
      have h2 : 0 < (S.km - S.sm*S.hp)*(1-S.tm) := by
        have := mul_pos hm0 (sub_pos.2 hsmtp); nlinarith
      have := pos_of_mul_pos_left h2 tm1.le
      linarith
    refine ⟨?_, hkm⟩
    by_contra hc; push Not at hc
    have hD2 : S.hm ≤ (S.sm*(S.hm*S.tp+S.hp*S.tm)-S.tm*S.km) := by linarith
    have e1 : S.tm * (S.hm*(1-S.sm*S.tp)-S.km*(1-S.tm)+S.hp*S.sm*(1-S.tm)) = (1-S.tm) * (S.sm*(S.hm*S.tp+S.hp*S.tm)-S.tm*S.km) + S.hm * (S.tm - S.sm*S.tp) := by ring
    have : 0 < S.tm * (S.hm*(1-S.sm*S.tp)-S.km*(1-S.tm)+S.hp*S.sm*(1-S.tm)) := by
      rw [e1]
      have := mul_le_mul_of_nonneg_left hD2 tm1.le
      nlinarith [mul_pos hm0 (sub_pos.2 hsmtp)]
    have := mul_nonpos_of_nonneg_of_nonpos tm0.le hA
    linarith

/-- S4: `A2 <= 0` gives `a25 < 0` (I4). -/
lemma iv_S4 (h : (S.km*S.sp-S.kp*(1-S.sm)) ≤ 0) : (S.sp*(S.hm-S.km*(1-S.tm))-S.kp*S.sm*(1-S.tm)) < 0 := by
  have e : (1-S.sm) * (S.sp*(S.hm-S.km*(1-S.tm))-S.kp*S.sm*(1-S.tm)) = -S.sp * (S.km*(1-S.tm)-S.hm*(1-S.sm)) + S.sm*(1-S.tm) * (S.km*S.sp-S.kp*(1-S.sm)) := by ring
  have h1 : (1-S.sm) * (S.sp*(S.hm-S.km*(1-S.tm))-S.kp*S.sm*(1-S.tm)) < 0 := by
    rw [e]
    have := mul_pos S.sp_pos S.rhom_pos
    have := mul_nonpos_of_nonneg_of_nonpos (mul_pos S.sm_pos S.tm1).le h
    linarith
  exact neg_of_mul_neg_right h1 S.sm1.le

/-- S5: `kap > 0` and `B14 <= 0` give `sp > sm tp` (V3). -/
lemma iv_S5 (hV : ((1-S.sp)*(S.hm*S.tp+S.hp*S.tm)-S.kp*S.tm) = 0) (hk : 0 < (S.hm-(S.sm*(S.hm*S.tp+S.hp*S.tm)-S.tm*S.km))) (hB : (S.tp*(S.kp*S.sm+S.km*S.sp)-S.sp*S.hp) ≤ 0) : S.sm * S.tp < S.sp := by
  have e : S.tm * (S.tp*(S.kp*S.sm+S.km*S.sp)-S.sp*S.hp) = (S.hm*S.tp+S.hp*S.tm) * (S.tp*S.sm - S.sp) + S.tp*S.sp*(S.hm-(S.sm*(S.hm*S.tp+S.hp*S.tm)-S.tm*S.km)) := by linear_combination (-S.sm*S.tp) * hV
  have h1 : 0 ≤ -(S.tm * (S.tp*(S.kp*S.sm+S.km*S.sp)-S.sp*S.hp)) := by
    have := mul_nonpos_of_nonneg_of_nonpos S.tm_pos.le hB; linarith
  have h2 : 0 < S.tp*S.sp*(S.hm-(S.sm*(S.hm*S.tp+S.hp*S.tm)-S.tm*S.km)) := by have := S.tp_pos; have := S.sp_pos; positivity
  have h3 : 0 < (S.hm*S.tp+S.hp*S.tm) * (S.sp - S.tp*S.sm) := by nlinarith
  have := pos_of_mul_pos_right h3 S.W_pos.le
  linarith

/-- S6: `kap > 0`, `A06 <= 0`, `B14 <= 0` give `a25 < 0`. -/
lemma iv_S6 (hV : ((1-S.sp)*(S.hm*S.tp+S.hp*S.tm)-S.kp*S.tm) = 0) (hk : 0 < (S.hm-(S.sm*(S.hm*S.tp+S.hp*S.tm)-S.tm*S.km))) (hA : (S.hm*(1-S.sm*S.tp)-S.km*(1-S.tm)+S.hp*S.sm*(1-S.tm)) ≤ 0) (hB : (S.tp*(S.kp*S.sm+S.km*S.sp)-S.sp*S.hp) ≤ 0) : (S.sp*(S.hm-S.km*(1-S.tm))-S.kp*S.sm*(1-S.tm)) < 0 := by
  have tm1 := S.tm1; have tp0 := S.tp_pos; have tm0 := S.tm_pos; have sm0 := S.sm_pos
  have hm0 := S.hm_pos; have hp0 := S.hp_pos; have sm1 := S.sm1; have sp0 := S.sp_pos
  have sp1 := S.sp1
  have hsmtp : S.sm * S.tp < 1 := by nlinarith [S.sm_lt, S.tp_lt]
  have s5 := S.iv_S5 hV hk hB
  -- I1: tm A06 = (1-tm) D06 + hm (tm - sm tp), with D06 = hm - kap
  have i1 : S.hm*(1-S.sm*S.tp) ≤ (1-S.tm) * (S.hm-(S.sm*(S.hm*S.tp+S.hp*S.tm)-S.tm*S.km)) := by
    have e1 : S.tm * (S.hm*(1-S.sm*S.tp)-S.km*(1-S.tm)+S.hp*S.sm*(1-S.tm)) = (1-S.tm) * (S.sm*(S.hm*S.tp+S.hp*S.tm)-S.tm*S.km) + S.hm * (S.tm - S.sm*S.tp) := by ring
    have := mul_nonpos_of_nonneg_of_nonpos tm0.le hA
    nlinarith
  -- V3
  have e3 : S.tm * (S.tp*(S.kp*S.sm+S.km*S.sp)-S.sp*S.hp) = (S.hm*S.tp+S.hp*S.tm) * (S.tp*S.sm - S.sp) + S.tp*S.sp*(S.hm-(S.sm*(S.hm*S.tp+S.hp*S.tm)-S.tm*S.km)) := by linear_combination (-S.sm*S.tp) * hV
  have v3 : S.tp*S.sp*(S.hm-(S.sm*(S.hm*S.tp+S.hp*S.tm)-S.tm*S.km)) ≤ (S.hm*S.tp+S.hp*S.tm) * (S.sp - S.tp*S.sm) := by
    have := mul_nonpos_of_nonneg_of_nonpos tm0.le hB; nlinarith
  -- hm sp tp (1 - sm tp) <= (1-tm) W (sp - tp sm)
  have k1 : S.hm*S.sp*S.tp*(1-S.sm*S.tp) ≤ (1-S.tm) * ((S.hm*S.tp+S.hp*S.tm) * (S.sp - S.tp*S.sm)) := by
    have a := mul_le_mul_of_nonneg_left i1 (mul_pos sp0 tp0).le
    have b := mul_le_mul_of_nonneg_left v3 tm1.le
    nlinarith
  have k2 : (1-S.tm) * ((S.hm*S.tp+S.hp*S.tm) * (S.sp - S.tp*S.sm)) < (1-S.tm) * (S.hm*S.tp+S.hp*S.tm) * (1-S.sm*S.tp) := by
    have : 0 < (1-S.tm) * (S.hm*S.tp+S.hp*S.tm) * (1 - S.sp) := mul_pos (mul_pos tm1 S.W_pos) sp1
    nlinarith
  have k3 : S.sp*S.tp*S.hm < (1-S.tm)*(S.hm*S.tp+S.hp*S.tm) := by
    have h4 : S.sp*S.tp*S.hm * (1-S.sm*S.tp) < (1-S.tm)*(S.hm*S.tp+S.hp*S.tm) * (1-S.sm*S.tp) := by nlinarith
    exact lt_of_mul_lt_mul_right h4 (sub_pos.2 hsmtp).le
  -- V4
  have e4 : S.tm * (S.sp*(S.hm-S.km*(1-S.tm))-S.kp*S.sm*(1-S.tm)) = S.tm*S.sp*(S.hm*(1-S.sm*S.tp)-S.km*(1-S.tm)+S.hp*S.sm*(1-S.tm)) - S.sm*((1-S.tm)*(S.hm*S.tp+S.hp*S.tm) - S.sp*S.tp*S.hm) := by
    linear_combination (S.sm*(1-S.tm)) * hV
  have h5 : S.tm * (S.sp*(S.hm-S.km*(1-S.tm))-S.kp*S.sm*(1-S.tm)) < 0 := by
    rw [e4]
    have := mul_nonpos_of_nonneg_of_nonpos (mul_pos tm0 sp0).le hA
    have := mul_pos sm0 (sub_pos.2 k3)
    linarith
  exact neg_of_mul_neg_right h5 tm0.le

/-- S7: `A2 >= 0` and `km > sm hp` give `br > 0`. -/
lemma iv_S7 (hV : ((1-S.sp)*(S.hm*S.tp+S.hp*S.tm)-S.kp*S.tm) = 0) (hA : 0 ≤ (S.km*S.sp-S.kp*(1-S.sm))) (hk : S.sm * S.hp < S.km) : 0 < (S.sp^2*S.km^2-S.sm*(1-S.sm)*S.kp*(S.hp-S.kp)) := by
  have s2 := S.iv_S2 hV
  have e : (S.sp^2*S.km^2-S.sm*(1-S.sm)*S.kp*(S.hp-S.kp)) = (S.km*S.sp-S.kp*(1-S.sm))*S.sp*S.km + S.kp*(1-S.sm)*S.sp*(S.km - S.sm*S.hp) + S.sm*(1-S.sm)*S.kp*(S.kp-(1-S.sp)*S.hp) := by ring
  rw [e]
  have h1 := mul_nonneg (mul_nonneg hA S.sp_pos.le) S.km_pos.le
  have h2 : 0 < S.kp*(1-S.sm)*S.sp*(S.km - S.sm*S.hp) :=
    mul_pos (by have := S.kp_pos; have := S.sm1; have := S.sp_pos; positivity) (sub_pos.2 hk)
  have h3 : 0 < S.sm*(1-S.sm)*S.kp*(S.kp-(1-S.sp)*S.hp) :=
    mul_pos (by have := S.kp_pos; have := S.sm1; have := S.sm_pos; positivity) (sub_pos.2 s2)
  linarith

/-- I3 on the item region: `A2 > 0` and `B14 <= 0` give `hp sp > tp kp`. -/
lemma iv_I3 (hA : 0 < (S.km*S.sp-S.kp*(1-S.sm))) (hB : (S.tp*(S.kp*S.sm+S.km*S.sp)-S.sp*S.hp) ≤ 0) : S.tp*S.kp < S.hp*S.sp := by
  have e : S.hp*S.sp - S.tp*S.kp = S.tp*(S.km*S.sp-S.kp*(1-S.sm)) - (S.tp*(S.kp*S.sm+S.km*S.sp)-S.sp*S.hp) := by ring
  have := mul_pos S.tp_pos hA
  linarith

/-- I2 on the item: `A1 > 0` and `D06 <= 0` give `tm km > hm sm`. -/
lemma iv_I2 (hA : 0 < (S.hp*S.tm-S.hm*(1-S.tp))) (hD : (S.sm*(S.hm*S.tp+S.hp*S.tm)-S.tm*S.km) ≤ 0) : S.hm*S.sm < S.tm*S.km := by
  have e : S.tm*S.km - S.hm*S.sm = S.sm*(S.hp*S.tm-S.hm*(1-S.tp)) - (S.sm*(S.hm*S.tp+S.hp*S.tm)-S.tm*S.km) := by ring
  have := mul_pos S.sm_pos hA
  linarith

end Shape20
end Minimality.CaseC20

end

section

/-!
# I_V: the standard leaves C1, C5, C2

Each leaf is a theorem `Frame20` of the frame `F` with the item `hV` (the left side of line 271 is
`Vq` up to ring, stated as `((1-F.S.sp)*(F.S.hm*F.S.tp+F.S.hp*F.S.tm)-F.S.kp*F.S.tm) = 0`) and its case hypotheses.
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace IVT
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- Discharges the literal part of a segment cell from named hypotheses on `nf`. -/
macro "iv_lits" : tactic => `(tactic| (intro t h0 h1; fin_cases t <;> first
  | exact absurd h0 (by decide)
  | exact absurd h1 (by decide)
  | exact ⟨fun _ => by assumption, fun h => absurd h (by decide)⟩
  | exact ⟨fun h => absurd h (by decide), fun _ => by assumption⟩))

/-- C1: `s01:0546`, needs `L < 0` (and `A1 > 0` from the item). -/
theorem iv_C1 (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hV : ((1-F.S.sp)*(F.S.hm*F.S.tp+F.S.hp*F.S.tm)-F.S.kp*F.S.tm) = 0) (hL : ((1-F.S.tp)*(F.a11*F.S.tp-F.a12)-F.gg*F.S.hp^2) < 0) : IsRupert (univ.image x) := by
  have A1 := F.S.iv_A1_pos hV
  have tp1 := F.S.tp1; have sm0 := F.S.sm_pos; have hp0 := F.S.hp_pos; have km0 := F.S.km_pos
  have ha : 0 < F.a12 := F.A12_pos; have hg : 0 < F.gg := F.g_pos
  have hD : 0 < nf F.S ⟨1 - F.S.tp, 0, -F.S.hp⟩ 3 := by
    have e : nf F.S ⟨1 - F.S.tp, 0, -F.S.hp⟩ 3 = F.S.sm * (F.S.hp*F.S.tm-F.S.hm*(1-F.S.tp)) := by simp only [nf_D]; ring
    rw [e]; positivity
  have hH : nf F.S ⟨1 - F.S.tp, 0, -F.S.hp⟩ 7 < 0 := by
    have e : nf F.S ⟨1 - F.S.tp, 0, -F.S.hp⟩ 7 = -(F.S.kp * (1 - F.S.tp)) := by simp only [nf_H]; ring
    rw [e]; have := F.S.kp_pos; have := mul_pos this tp1; linarith
  refine seg_leaf F (h20s_fac hR) hx h20s_s01 h20s_s01_good ⟨1 - F.S.tp, 0, -F.S.hp⟩
    (seg_vec F 0 1 _ (by rw [F.ptC_1, F.ptC_0]; simp only [C3.sub]; congr 1 <;> ring)) (by iv_lits) ?_
  have z0 : F.dep ⟨1 - F.S.tp, 0, -F.S.hp⟩ 0 = F.a11 * (F.S.tp * (1 - F.S.tp)) - F.gg * F.S.hp^2 := by
    rw [Frame20.dep_0]; ring
  have z5 : F.dep ⟨1 - F.S.tp, 0, -F.S.hp⟩ 5 = 0 := Frame20.dep_5 F _
  have z4 : F.dep ⟨1 - F.S.tp, 0, -F.S.hp⟩ 4 = F.a12 * (F.S.sm * (1 - F.S.tp)) + F.gg * (F.S.km * F.S.hp) := by
    rw [Frame20.dep_4]; ring
  have z6 : F.dep ⟨1 - F.S.tp, 0, -F.S.hp⟩ 6 = F.a12 * (1 - F.S.tp) := by rw [Frame20.dep_6]; ring
  have p4 : 0 < F.a12 * (F.S.sm * (1 - F.S.tp)) + F.gg * (F.S.km * F.S.hp) := add_pos (mul_pos ha (mul_pos sm0 tp1)) (mul_pos hg (mul_pos km0 hp0))
  refine robUni4 ?_ ?_
  · rintro ⟨a, b, c, d⟩
    have d' : F.dep ⟨1 - F.S.tp, 0, -F.S.hp⟩ 6 ≤ F.dep ⟨1 - F.S.tp, 0, -F.S.hp⟩ 0 := c
    rw [z0, z6] at d'
    linarith
  · rintro ⟨a, b, c, d⟩
    have c' : F.dep ⟨1 - F.S.tp, 0, -F.S.hp⟩ 4 ≤ F.dep ⟨1 - F.S.tp, 0, -F.S.hp⟩ 5 := c
    rw [z4, z5] at c'
    linarith

/-- C5: `s06:01352`, needs `A06 > 0`, `D06 > 0`, `L >= 0` (and `A1 > 0` from the item). -/
theorem iv_C5 (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hV : ((1-F.S.sp)*(F.S.hm*F.S.tp+F.S.hp*F.S.tm)-F.S.kp*F.S.tm) = 0) (hA : 0 < (F.S.hm*(1-F.S.sm*F.S.tp)-F.S.km*(1-F.S.tm)+F.S.hp*F.S.sm*(1-F.S.tm))) (hD : 0 < (F.S.sm*(F.S.hm*F.S.tp+F.S.hp*F.S.tm)-F.S.tm*F.S.km)) (hL : 0 ≤ ((1-F.S.tp)*(F.a11*F.S.tp-F.a12)-F.gg*F.S.hp^2)) : IsRupert (univ.image x) := by
  have A1 := F.S.iv_A1_pos hV
  have tp1 := F.S.tp1; have tm1 := F.S.tm1; have hp0 := F.S.hp_pos; have hm0 := F.S.hm_pos
  have tp0 := F.S.tp_pos; have sp0 := F.S.sp_pos; have kp0 := F.S.kp_pos
  have ha : 0 < F.a12 := F.A12_pos; have hg : 0 < F.gg := F.g_pos; have h22 : F.a12 ≤ F.a22 := F.A12_le_A22
  have h11 : F.a12 ≤ F.a11 := F.A12_le_A11
  have roof := F.S.rhop_pos
  have nA : 0 < nf F.S ⟨-F.S.tp, 1, -F.S.hp⟩ 0 := by
    have e : nf F.S ⟨-F.S.tp, 1, -F.S.hp⟩ 0 = (F.S.hm*(1-F.S.sm*F.S.tp)-F.S.km*(1-F.S.tm)+F.S.hp*F.S.sm*(1-F.S.tm)) := by simp only [nf_A]; ring
    rw [e]; exact hA
  have nD : 0 < nf F.S ⟨-F.S.tp, 1, -F.S.hp⟩ 3 := by
    have e : nf F.S ⟨-F.S.tp, 1, -F.S.hp⟩ 3 = (F.S.sm*(F.S.hm*F.S.tp+F.S.hp*F.S.tm)-F.S.tm*F.S.km) := by simp only [nf_D]; ring
    rw [e]; exact hD
  refine seg_leaf F (h20s_fac hR) hx ivs_C5 ivs_C5_good ⟨-F.S.tp, 1, -F.S.hp⟩
    (seg_vec F 0 6 _ (by rw [F.ptC_6, F.ptC_0]; simp only [C3.sub]; congr 1 <;> ring)) (by iv_lits) ?_
  have z0 : F.dep ⟨-F.S.tp, 1, -F.S.hp⟩ 0 = -(F.a11*F.S.tp - F.a12)*F.S.tp - F.gg*F.S.hp^2 := by rw [Frame20.dep_0]; ring
  have z1 : F.dep ⟨-F.S.tp, 1, -F.S.hp⟩ 1 = -(F.a11*F.S.tp - F.a12) := by rw [Frame20.dep_1]; ring
  have z3 : F.dep ⟨-F.S.tp, 1, -F.S.hp⟩ 3 = -(F.a11*F.S.tp - F.a12)*F.S.tm + F.gg*F.S.hp*F.S.hm := by rw [Frame20.dep_3]; ring
  have z5 : F.dep ⟨-F.S.tp, 1, -F.S.hp⟩ 5 = 0 := Frame20.dep_5 F _
  have z2 : F.dep ⟨-F.S.tp, 1, -F.S.hp⟩ 2 = (F.a22 - F.a12*F.S.tp)*F.S.sp - F.gg*F.S.hp*F.S.kp := by rw [Frame20.dep_2]; ring
  have hT : 0 < F.a11*F.S.tp - F.a12 := by
    have h1 : 0 < (1-F.S.tp) * (F.a11*F.S.tp - F.a12) := by nlinarith [mul_pos hg (pow_pos hp0 2)]
    exact pos_of_mul_pos_right h1 tp1.le
  have hY : 0 < F.a22 - F.a12*F.S.tp := by linarith [mul_pos ha tp1]
  refine Minimality.H20S.robUni5_d ?_ ?_ ?_
  · show F.dep _ 1 < F.dep _ 3
    rw [z1, z3]; nlinarith [mul_pos hT tm1, mul_pos hg (mul_pos hp0 hm0)]
  · show F.dep _ 3 < F.dep _ 5
    rw [z3, z5]
    have e : (1-F.S.tp) * (-(F.a11*F.S.tp - F.a12)*F.S.tm + F.gg*F.S.hp*F.S.hm) = -F.gg*F.S.hp*(F.S.hp*F.S.tm-F.S.hm*(1-F.S.tp)) - F.S.tm*((1-F.S.tp)*(F.a11*F.S.tp-F.a12)-F.gg*F.S.hp^2) := by ring
    have h1 : (1-F.S.tp) * (-(F.a11*F.S.tp - F.a12)*F.S.tm + F.gg*F.S.hp*F.S.hm) < 0 := by
      rw [e]; nlinarith [mul_pos hg hp0, mul_pos (mul_pos hg hp0) A1, mul_nonneg F.S.tm_pos.le hL]
    exact neg_of_mul_neg_right h1 tp1.le
  · show F.dep _ 0 < F.dep _ 2
    rw [z0, z2]
    have e : (1-F.S.tp) * (((F.a22 - F.a12*F.S.tp)*F.S.sp - F.gg*F.S.hp*F.S.kp) - (-(F.a11*F.S.tp - F.a12)*F.S.tp - F.gg*F.S.hp^2))
        = (1-F.S.tp)*(F.a22 - F.a12*F.S.tp)*F.S.sp + F.S.tp*((1-F.S.tp)*(F.a11*F.S.tp-F.a12)-F.gg*F.S.hp^2) + F.gg*F.S.hp*(F.S.hp - (1-F.S.tp)*F.S.kp) := by ring
    have h1 : 0 < (1-F.S.tp) * (((F.a22 - F.a12*F.S.tp)*F.S.sp - F.gg*F.S.hp*F.S.kp) - (-(F.a11*F.S.tp - F.a12)*F.S.tp - F.gg*F.S.hp^2)) := by
      rw [e]
      have := mul_pos (mul_pos tp1 hY) sp0
      have := mul_nonneg tp0.le hL
      have := mul_pos (mul_pos hg hp0) (show 0 < F.S.hp - (1-F.S.tp)*F.S.kp by linarith [roof, mul_pos hp0 sp0])
      linarith
    have := pos_of_mul_pos_right h1 tp1.le
    linarith

/-- C2: `s46:0145`, needs `A2 > 0`, `Lp < 0`. -/
theorem iv_C2 (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hA : 0 < (F.S.km*F.S.sp-F.S.kp*(1-F.S.sm))) (hL : ((1-F.S.sm)*(F.a22*F.S.sm-F.a12)-F.gg*F.S.km^2) < 0) : IsRupert (univ.image x) := by
  have sm1 := F.S.sm1; have tp0 := F.S.tp_pos; have hp0 := F.S.hp_pos; have km0 := F.S.km_pos
  have ha : 0 < F.a12 := F.A12_pos; have hg : 0 < F.gg := F.g_pos; have W0 := F.S.W_pos
  have nB : 0 < nf F.S ⟨0, 1 - F.S.sm, F.S.km⟩ 1 := by
    have e : nf F.S ⟨0, 1 - F.S.sm, F.S.km⟩ 1 = F.S.tp * (F.S.km*F.S.sp-F.S.kp*(1-F.S.sm)) := by simp only [nf_B]; ring
    rw [e]; exact mul_pos tp0 hA
  have nC : nf F.S ⟨0, 1 - F.S.sm, F.S.km⟩ 2 < 0 := by
    have e : nf F.S ⟨0, 1 - F.S.sm, F.S.km⟩ 2 = -((F.S.hm*F.S.tp+F.S.hp*F.S.tm) * (1 - F.S.sm)) := by simp only [nf_C]; ring
    rw [e]; have := mul_pos W0 sm1; linarith
  refine seg_leaf F (h20s_fac hR) hx ivs_C2 ivs_C2_good ⟨0, 1 - F.S.sm, F.S.km⟩
    (seg_vec F 4 6 _ (by rw [F.ptC_6, F.ptC_4]; simp only [C3.sub]; congr 1 <;> ring)) (by iv_lits) ?_
  have z0 : F.dep ⟨0, 1 - F.S.sm, F.S.km⟩ 0 = F.a12*(F.S.tp*(1-F.S.sm)) + F.gg*(F.S.hp*F.S.km) := by rw [Frame20.dep_0]; ring
  have z1 : F.dep ⟨0, 1 - F.S.sm, F.S.km⟩ 1 = F.a12*(1-F.S.sm) := by rw [Frame20.dep_1]; ring
  have z4 : F.dep ⟨0, 1 - F.S.sm, F.S.km⟩ 4 = F.a22*(F.S.sm*(1-F.S.sm)) - F.gg*(F.S.km*F.S.km) := by rw [Frame20.dep_4]; ring
  have z5 : F.dep ⟨0, 1 - F.S.sm, F.S.km⟩ 5 = 0 := Frame20.dep_5 F _
  have p0 : 0 < F.a12*(F.S.tp*(1-F.S.sm)) + F.gg*(F.S.hp*F.S.km) :=
    add_pos (mul_pos ha (mul_pos tp0 sm1)) (mul_pos hg (mul_pos hp0 km0))
  refine robUni4 ?_ ?_
  · rintro ⟨a, b, c, d⟩
    have b' : F.dep ⟨0, 1 - F.S.sm, F.S.km⟩ 1 ≤ F.dep ⟨0, 1 - F.S.sm, F.S.km⟩ 4 := b
    rw [z1, z4] at b'
    nlinarith
  · rintro ⟨a, b, c, d⟩
    have b' : F.dep ⟨0, 1 - F.S.sm, F.S.km⟩ 0 ≤ F.dep ⟨0, 1 - F.S.sm, F.S.km⟩ 5 := b
    rw [z0, z5] at b'
    linarith

end IVT
end Minimality.CaseC20

end

section

/-!
# I_V: the standard leaves C6, C7, C8, C9

(Note on C6: COVER.md says `robUni5_d` after rotating to `(z6,z2,z5,z3,z4)`; the rotation that makes the
shape `d` is `(z4,z6,z2,z5,z3)`.  In the cycle order `![2,5,3,4,6]` the shape is `z4<z0<z1`, `z3<z2`,
stated here as `robUni5_g`.)
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.H20S

/-- Five-cycle shape G (a rotation of shape D): `z4 < z0 < z1` and `z3 < z2`. -/
theorem robUni5_g {z : ZMod 5 → ℝ} (h40 : z 4 < z 0) (h01 : z 0 < z 1) (h32 : z 3 < z 2) :
    RobUni z := by robuni5

end Minimality.H20S

namespace Minimality.CaseC20
namespace IVT
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- C6: `s14:25346`, needs `A2 > 0`, `B14 > 0`, `kap > 0`, `Lp >= 0`. -/
theorem iv_C6 (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hV : ((1-F.S.sp)*(F.S.hm*F.S.tp+F.S.hp*F.S.tm)-F.S.kp*F.S.tm) = 0) (hA : 0 < (F.S.km*F.S.sp-F.S.kp*(1-F.S.sm))) (hB : 0 < (F.S.tp*(F.S.kp*F.S.sm+F.S.km*F.S.sp)-F.S.sp*F.S.hp)) (hK : 0 < (F.S.hm-(F.S.sm*(F.S.hm*F.S.tp+F.S.hp*F.S.tm)-F.S.tm*F.S.km))) (hL : 0 ≤ ((1-F.S.sm)*(F.a22*F.S.sm-F.a12)-F.gg*F.S.km^2)) :
    IsRupert (univ.image x) := by
  have sm1 := F.S.sm1; have sp1 := F.S.sp1; have tm1 := F.S.tm1; have tp0 := F.S.tp_pos
  have sp0 := F.S.sp_pos; have sm0 := F.S.sm_pos; have tm0 := F.S.tm_pos
  have kp0 := F.S.kp_pos; have km0 := F.S.km_pos; have hm0 := F.S.hm_pos
  have ha : 0 < F.a12 := F.A12_pos; have hg : 0 < F.gg := F.g_pos; have h22 : F.a12 ≤ F.a22 := F.A12_le_A22
  have h11 : F.a12 ≤ F.a11 := F.A12_le_A11
  have A14 : 0 < (F.S.kp*(1-F.S.tp*F.S.sm)-F.S.hp*(1-F.S.sp)+F.S.km*F.S.tp*(1-F.S.sp)) := by
    have e : F.S.tm * (F.S.kp*(1-F.S.tp*F.S.sm)-F.S.hp*(1-F.S.sp)+F.S.km*F.S.tp*(1-F.S.sp)) = (1-F.S.sp) * F.S.tp * (F.S.hm-(F.S.sm*(F.S.hm*F.S.tp+F.S.hp*F.S.tm)-F.S.tm*F.S.km)) := by linear_combination (F.S.sm*F.S.tp - 1) * hV
    have h1 : 0 < F.S.tm * (F.S.kp*(1-F.S.tp*F.S.sm)-F.S.hp*(1-F.S.sp)+F.S.km*F.S.tp*(1-F.S.sp)) := by rw [e]; positivity
    exact pos_of_mul_pos_right h1 tm0.le
  have nB : nf F.S ⟨-1, F.S.sm, -F.S.km⟩ 1 < 0 := by
    have e : nf F.S ⟨-1, F.S.sm, -F.S.km⟩ 1 = -(F.S.tp*(F.S.kp*F.S.sm+F.S.km*F.S.sp)-F.S.sp*F.S.hp) := by simp only [nf_B]; ring
    rw [e]; linarith
  have nF : nf F.S ⟨-1, F.S.sm, -F.S.km⟩ 5 < 0 := by
    have e : nf F.S ⟨-1, F.S.sm, -F.S.km⟩ 5 = -(F.S.kp*(1-F.S.tp*F.S.sm)-F.S.hp*(1-F.S.sp)+F.S.km*F.S.tp*(1-F.S.sp)) := by simp only [nf_F]; ring
    rw [e]; linarith
  refine seg_leaf_neg F (h20s_fac hR) hx ivs_C6 ivs_C6_good (-1) F.S.sm (-F.S.km)
    (seg_vec F 1 4 _ (by rw [F.ptC_4, F.ptC_1]; simp only [C3.sub]; congr 1 <;> ring)) (by iv_lits) ?_
  have e1 : (⟨-(-1), -F.S.sm, -(-F.S.km)⟩ : C3) = ⟨1, -F.S.sm, F.S.km⟩ := by congr 1 <;> ring
  rw [e1]
  set T := F.a22*F.S.sm - F.a12 with hT
  have hT0 : 0 < T := by
    have h1 : 0 < (1-F.S.sm) * T := by nlinarith [mul_pos hg (pow_pos km0 2)]
    exact pos_of_mul_pos_right h1 sm1.le
  have hY : 0 < F.a11 - F.a12*F.S.sm := by linarith [mul_pos ha sm1]
  have z2 : F.dep ⟨1, -F.S.sm, F.S.km⟩ 2 = -T*F.S.sp + F.gg*F.S.km*F.S.kp := by rw [Frame20.dep_2, hT]; ring
  have z3 : F.dep ⟨1, -F.S.sm, F.S.km⟩ 3 = (F.a11 - F.a12*F.S.sm)*F.S.tm - F.gg*F.S.km*F.S.hm := by rw [Frame20.dep_3]; ring
  have z4 : F.dep ⟨1, -F.S.sm, F.S.km⟩ 4 = -T*F.S.sm - F.gg*F.S.km^2 := by rw [Frame20.dep_4, hT]; ring
  have z5 : F.dep ⟨1, -F.S.sm, F.S.km⟩ 5 = 0 := Frame20.dep_5 F _
  have z6 : F.dep ⟨1, -F.S.sm, F.S.km⟩ 6 = -T := by rw [Frame20.dep_6, hT]; ring
  refine Minimality.H20S.robUni5_g ?_ ?_ ?_
  · show F.dep _ 6 < F.dep _ 2
    rw [z6, z2]; nlinarith [mul_pos hT0 sp1, mul_pos hg (mul_pos km0 kp0)]
  · show F.dep _ 2 < F.dep _ 5
    rw [z2, z5]
    have e : (1-F.S.sm) * (-T*F.S.sp + F.gg*F.S.km*F.S.kp) = -F.gg*F.S.km*(F.S.km*F.S.sp-F.S.kp*(1-F.S.sm)) - F.S.sp*((1-F.S.sm)*(F.a22*F.S.sm-F.a12)-F.gg*F.S.km^2) := by rw [hT]; ring
    have h1 : (1-F.S.sm) * (-T*F.S.sp + F.gg*F.S.km*F.S.kp) < 0 := by
      rw [e]; nlinarith [mul_pos (mul_pos hg km0) hA, mul_nonneg sp0.le hL]
    exact neg_of_mul_neg_right h1 sm1.le
  · show F.dep _ 4 < F.dep _ 3
    rw [z4, z3]
    have e : (1-F.S.sm) * (((F.a11 - F.a12*F.S.sm)*F.S.tm - F.gg*F.S.km*F.S.hm) - (-T*F.S.sm - F.gg*F.S.km^2))
        = (1-F.S.sm)*(F.a11 - F.a12*F.S.sm)*F.S.tm + F.S.sm*((1-F.S.sm)*(F.a22*F.S.sm-F.a12)-F.gg*F.S.km^2) + F.gg*F.S.km*(F.S.km - (1-F.S.sm)*F.S.hm) := by rw [hT]; ring
    have h1 : 0 < (1-F.S.sm) * (((F.a11 - F.a12*F.S.sm)*F.S.tm - F.gg*F.S.km*F.S.hm) - (-T*F.S.sm - F.gg*F.S.km^2)) := by
      rw [e]
      have := mul_pos (mul_pos sm1 hY) tm0
      have := mul_nonneg sm0.le hL
      have := mul_pos (mul_pos hg km0) (show 0 < F.S.km - (1-F.S.sm)*F.S.hm by
        linarith [F.S.rhom_pos, mul_pos km0 tm0])
      linarith
    have := pos_of_mul_pos_right h1 sm1.le
    linarith

/-- C7: `s25:01462`, needs `A2 > 0`, `B14 <= 0`, `A06 <= 0`, `kap > 0`, `km > sm hp`, `Lp >= 0`. -/
theorem iv_C7 (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hV : ((1-F.S.sp)*(F.S.hm*F.S.tp+F.S.hp*F.S.tm)-F.S.kp*F.S.tm) = 0) (hA : 0 < (F.S.km*F.S.sp-F.S.kp*(1-F.S.sm))) (hB : (F.S.tp*(F.S.kp*F.S.sm+F.S.km*F.S.sp)-F.S.sp*F.S.hp) ≤ 0) (hA06 : (F.S.hm*(1-F.S.sm*F.S.tp)-F.S.km*(1-F.S.tm)+F.S.hp*F.S.sm*(1-F.S.tm)) ≤ 0) (hK : 0 < (F.S.hm-(F.S.sm*(F.S.hm*F.S.tp+F.S.hp*F.S.tm)-F.S.tm*F.S.km)))
    (hkm : F.S.sm * F.S.hp < F.S.km) (hL : 0 ≤ ((1-F.S.sm)*(F.a22*F.S.sm-F.a12)-F.gg*F.S.km^2)) : IsRupert (univ.image x) := by
  have sm1 := F.S.sm1; have sp1 := F.S.sp1; have tm1 := F.S.tm1; have tp0 := F.S.tp_pos
  have sp0 := F.S.sp_pos; have sm0 := F.S.sm_pos; have tm0 := F.S.tm_pos
  have kp0 := F.S.kp_pos; have km0 := F.S.km_pos; have hm0 := F.S.hm_pos; have hp0 := F.S.hp_pos
  have ha : 0 < F.a12 := F.A12_pos; have hg : 0 < F.gg := F.g_pos; have h22 : F.a12 ≤ F.a22 := F.A12_le_A22
  have s5 := F.S.iv_S5 hV hK hB
  have s6 := F.S.iv_S6 hV hK hA06 hB
  have s7 := F.S.iv_S7 hV hA.le hkm
  have nA : 0 < nf F.S ⟨0, -F.S.sp, -F.S.kp⟩ 0 := by
    have e : nf F.S ⟨0, -F.S.sp, -F.S.kp⟩ 0 = -(F.S.sp*(F.S.hm-F.S.km*(1-F.S.tm))-F.S.kp*F.S.sm*(1-F.S.tm)) := by simp only [nf_A]; ring
    rw [e]; linarith
  have nE : nf F.S ⟨0, -F.S.sp, -F.S.kp⟩ 4 < 0 := by
    have e : nf F.S ⟨0, -F.S.sp, -F.S.kp⟩ 4 = -(F.S.hp*F.S.sp + (1-F.S.tp)*F.S.kp) := by simp only [nf_E]; ring
    rw [e]; have := mul_pos hp0 sp0; have := mul_pos F.S.tp1 kp0; linarith
  have nG : nf F.S ⟨0, -F.S.sp, -F.S.kp⟩ 6 < 0 := by
    have e : nf F.S ⟨0, -F.S.sp, -F.S.kp⟩ 6 = -(F.S.km*F.S.sp-F.S.kp*(1-F.S.sm)) := by simp only [nf_G]; ring
    rw [e]; linarith
  refine seg_leaf_neg F (h20s_fac hR) hx ivs_C7 ivs_C7_good 0 (-F.S.sp) (-F.S.kp)
    (seg_vec F 2 5 _ (by rw [F.ptC_5, F.ptC_2]; simp only [C3.sub]; congr 1 <;> ring)) (by iv_lits) ?_
  have e1 : (⟨-(0:ℝ), -(-F.S.sp), -(-F.S.kp)⟩ : C3) = ⟨0, F.S.sp, F.S.kp⟩ := by congr 1 <;> ring
  rw [e1]
  have z0 : F.dep ⟨0, F.S.sp, F.S.kp⟩ 0 = F.a12*F.S.sp*F.S.tp + F.gg*F.S.hp*F.S.kp := by rw [Frame20.dep_0]; ring
  have z1 : F.dep ⟨0, F.S.sp, F.S.kp⟩ 1 = F.a12*F.S.sp := by rw [Frame20.dep_1]; ring
  have z2 : F.dep ⟨0, F.S.sp, F.S.kp⟩ 2 = F.a22*F.S.sp^2 + F.gg*F.S.kp^2 := by rw [Frame20.dep_2]; ring
  have z4 : F.dep ⟨0, F.S.sp, F.S.kp⟩ 4 = F.a22*F.S.sp*F.S.sm - F.gg*F.S.km*F.S.kp := by rw [Frame20.dep_4]; ring
  have z6 : F.dep ⟨0, F.S.sp, F.S.kp⟩ 6 = F.a22*F.S.sp := by rw [Frame20.dep_6]; ring
  refine Minimality.H20S.robUni5_d ?_ ?_ ?_
  · show F.dep _ 1 < F.dep _ 4
    rw [z1, z4]
    have e : (1-F.S.sm) * (F.a22*F.S.sp*F.S.sm - F.gg*F.S.km*F.S.kp - F.a12*F.S.sp) = F.S.sp*((1-F.S.sm)*(F.a22*F.S.sm-F.a12)-F.gg*F.S.km^2) + F.gg*F.S.km*(F.S.km*F.S.sp-F.S.kp*(1-F.S.sm)) := by ring
    have h1 : 0 < (1-F.S.sm) * (F.a22*F.S.sp*F.S.sm - F.gg*F.S.km*F.S.kp - F.a12*F.S.sp) := by
      rw [e]; nlinarith [mul_nonneg sp0.le hL, mul_pos (mul_pos hg km0) hA]
    have := pos_of_mul_pos_right h1 sm1.le
    linarith
  · show F.dep _ 4 < F.dep _ 6
    rw [z4, z6]; nlinarith [mul_pos (mul_pos (lt_of_lt_of_le ha h22) sp0) sm1, mul_pos hg (mul_pos km0 kp0)]
  · show F.dep _ 0 < F.dep _ 2
    rw [z0, z2]
    have e : F.S.sm*(1-F.S.sm) * ((F.a22*F.S.sp^2 + F.gg*F.S.kp^2) - (F.a12*F.S.sp*F.S.tp + F.gg*F.S.hp*F.S.kp))
        = F.S.sp^2*((1-F.S.sm)*(F.a22*F.S.sm-F.a12)-F.gg*F.S.km^2) + (1-F.S.sm)*F.a12*F.S.sp*(F.S.sp - F.S.sm*F.S.tp) + F.gg*(F.S.sp^2*F.S.km^2-F.S.sm*(1-F.S.sm)*F.S.kp*(F.S.hp-F.S.kp)) := by ring
    have h1 : 0 < F.S.sm*(1-F.S.sm) * ((F.a22*F.S.sp^2 + F.gg*F.S.kp^2) - (F.a12*F.S.sp*F.S.tp + F.gg*F.S.hp*F.S.kp)) := by
      rw [e]
      have := mul_nonneg (pow_pos sp0 2).le hL
      have := mul_pos (mul_pos (mul_pos sm1 ha) sp0) (sub_pos.2 s5)
      have := mul_pos hg s7
      linarith
    have := pos_of_mul_pos_right h1 (mul_pos sm0 sm1).le
    linarith

/-- C8: `s16:0145`, needs `a12 < a11`, `tp kp < hp sp`, `hm sm < tm km`. -/
theorem iv_C8 (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (h11 : F.a12 < F.a11) (hB : F.S.tp*F.S.kp < F.S.hp*F.S.sp) (hD : F.S.hm*F.S.sm < F.S.tm*F.S.km) :
    IsRupert (univ.image x) := by
  have tp0 := F.S.tp_pos; have tp1 := F.S.tp1
  have nB : 0 < nf F.S ⟨-1, 1, 0⟩ 1 := by
    have e : nf F.S ⟨-1, 1, 0⟩ 1 = F.S.hp*F.S.sp - F.S.tp*F.S.kp := by simp only [nf_B]; ring
    rw [e]; linarith
  have nD : nf F.S ⟨-1, 1, 0⟩ 3 < 0 := by
    have e : nf F.S ⟨-1, 1, 0⟩ 3 = F.S.hm*F.S.sm - F.S.tm*F.S.km := by simp only [nf_D]; ring
    rw [e]; linarith
  refine seg_leaf F (h20s_fac hR) hx ivs_C8 ivs_C8_good ⟨-1, 1, 0⟩
    (seg_vec F 1 6 _ (by rw [F.ptC_6, F.ptC_1]; simp only [C3.sub]; congr 1 <;> ring)) (by iv_lits) ?_
  have z0 : F.dep ⟨-1, 1, 0⟩ 0 = -(F.a11 - F.a12)*F.S.tp := by rw [Frame20.dep_0]; ring
  have z1 : F.dep ⟨-1, 1, 0⟩ 1 = -(F.a11 - F.a12) := by rw [Frame20.dep_1]; ring
  have z5 : F.dep ⟨-1, 1, 0⟩ 5 = 0 := Frame20.dep_5 F _
  refine robUni4 ?_ ?_
  · rintro ⟨a, b, c, d⟩
    have c' : F.dep ⟨-1, 1, 0⟩ 5 ≤ F.dep ⟨-1, 1, 0⟩ 0 := c
    rw [z5, z0] at c'
    nlinarith [mul_pos (sub_pos.2 h11) tp0]
  · rintro ⟨a, b, c, d⟩
    have a' : F.dep ⟨-1, 1, 0⟩ 0 ≤ F.dep ⟨-1, 1, 0⟩ 1 := a
    rw [z0, z1] at a'
    nlinarith [mul_pos (sub_pos.2 h11) tp1]

/-- C9: `s25:0162`, needs `A2 < 0`, `a12 < a22`, `Phi >= 0`. -/
theorem iv_C9 (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hV : ((1-F.S.sp)*(F.S.hm*F.S.tp+F.S.hp*F.S.tm)-F.S.kp*F.S.tm) = 0) (hA : (F.S.km*F.S.sp-F.S.kp*(1-F.S.sm)) < 0) (h22 : F.a12 < F.a22) (hP : 0 ≤ (F.gg*F.S.hm*F.S.km-F.a12*F.S.tm*(1-F.S.sm))) : IsRupert (univ.image x) := by
  have sm1 := F.S.sm1; have sp1 := F.S.sp1; have tm1 := F.S.tm1; have tp0 := F.S.tp_pos
  have sp0 := F.S.sp_pos; have sm0 := F.S.sm_pos; have tm0 := F.S.tm_pos
  have kp0 := F.S.kp_pos; have km0 := F.S.km_pos; have hm0 := F.S.hm_pos; have hp0 := F.S.hp_pos
  have ha : 0 < F.a12 := F.A12_pos; have hg : 0 < F.gg := F.g_pos
  have s4 := F.S.iv_S4 hA.le
  have nA : 0 < nf F.S ⟨0, -F.S.sp, -F.S.kp⟩ 0 := by
    have e : nf F.S ⟨0, -F.S.sp, -F.S.kp⟩ 0 = -(F.S.sp*(F.S.hm-F.S.km*(1-F.S.tm))-F.S.kp*F.S.sm*(1-F.S.tm)) := by simp only [nf_A]; ring
    rw [e]; linarith
  have nE : nf F.S ⟨0, -F.S.sp, -F.S.kp⟩ 4 < 0 := by
    have e : nf F.S ⟨0, -F.S.sp, -F.S.kp⟩ 4 = -(F.S.hp*F.S.sp + (1-F.S.tp)*F.S.kp) := by simp only [nf_E]; ring
    rw [e]; have := mul_pos hp0 sp0; have := mul_pos F.S.tp1 kp0; linarith
  have nG : 0 < nf F.S ⟨0, -F.S.sp, -F.S.kp⟩ 6 := by
    have e : nf F.S ⟨0, -F.S.sp, -F.S.kp⟩ 6 = -(F.S.km*F.S.sp-F.S.kp*(1-F.S.sm)) := by simp only [nf_G]; ring
    rw [e]; linarith
  refine seg_leaf_neg F (h20s_fac hR) hx ivs_C9 ivs_C9_good 0 (-F.S.sp) (-F.S.kp)
    (seg_vec F 2 5 _ (by rw [F.ptC_5, F.ptC_2]; simp only [C3.sub]; congr 1 <;> ring)) (by iv_lits) ?_
  have e1 : (⟨-(0:ℝ), -(-F.S.sp), -(-F.S.kp)⟩ : C3) = ⟨0, F.S.sp, F.S.kp⟩ := by congr 1 <;> ring
  rw [e1]
  have hPsi : 0 < (F.gg*F.S.hm*F.S.kp-F.a12*F.S.tm*F.S.sp) := by
    have e : (1-F.S.sm) * (F.gg*F.S.hm*F.S.kp-F.a12*F.S.tm*F.S.sp) = F.S.sp * (F.gg*F.S.hm*F.S.km-F.a12*F.S.tm*(1-F.S.sm)) - F.gg*F.S.hm*(F.S.km*F.S.sp-F.S.kp*(1-F.S.sm)) := by ring
    have h1 : 0 < (1-F.S.sm) * (F.gg*F.S.hm*F.S.kp-F.a12*F.S.tm*F.S.sp) := by
      rw [e]; nlinarith [mul_nonneg sp0.le hP, mul_pos (mul_pos hg hm0) (neg_pos.2 hA)]
    exact pos_of_mul_pos_right h1 sm1.le
  have z0 : F.dep ⟨0, F.S.sp, F.S.kp⟩ 0 = F.a12*F.S.sp*F.S.tp + F.gg*F.S.hp*F.S.kp := by rw [Frame20.dep_0]; ring
  have z1 : F.dep ⟨0, F.S.sp, F.S.kp⟩ 1 = F.a12*F.S.sp := by rw [Frame20.dep_1]; ring
  have z2 : F.dep ⟨0, F.S.sp, F.S.kp⟩ 2 = F.a22*F.S.sp^2 + F.gg*F.S.kp^2 := by rw [Frame20.dep_2]; ring
  have z6 : F.dep ⟨0, F.S.sp, F.S.kp⟩ 6 = F.a22*F.S.sp := by rw [Frame20.dep_6]; ring
  refine robUni4 ?_ ?_
  · rintro ⟨a, b, c, d⟩
    have c' : F.dep ⟨0, F.S.sp, F.S.kp⟩ 2 ≤ F.dep ⟨0, F.S.sp, F.S.kp⟩ 0 := c
    have d' : F.dep ⟨0, F.S.sp, F.S.kp⟩ 2 ≤ F.dep ⟨0, F.S.sp, F.S.kp⟩ 6 := d
    rw [z2, z0] at c'
    rw [z2, z6] at d'
    have key : F.S.tm * (F.S.sp * (F.a22*F.S.sp - (F.a22*F.S.sp^2 + F.gg*F.S.kp^2)) +
        (1-F.S.sp) * ((F.a12*F.S.sp*F.S.tp + F.gg*F.S.hp*F.S.kp) - (F.a22*F.S.sp^2 + F.gg*F.S.kp^2))) = -(1-F.S.sp)*F.S.tp*(F.gg*F.S.hm*F.S.kp-F.a12*F.S.tm*F.S.sp) := by
      linear_combination (F.gg*F.S.kp) * hV
    have h1 : 0 ≤ F.S.tm * (F.S.sp * (F.a22*F.S.sp - (F.a22*F.S.sp^2 + F.gg*F.S.kp^2)) +
        (1-F.S.sp) * ((F.a12*F.S.sp*F.S.tp + F.gg*F.S.hp*F.S.kp) - (F.a22*F.S.sp^2 + F.gg*F.S.kp^2))) := by
      have := mul_nonneg sp0.le (sub_nonneg.2 d')
      have := mul_nonneg sp1.le (sub_nonneg.2 c')
      positivity
    have h2 : 0 < (1-F.S.sp)*F.S.tp*(F.gg*F.S.hm*F.S.kp-F.a12*F.S.tm*F.S.sp) := by positivity
    linarith
  · rintro ⟨a, b, c, d⟩
    have c' : F.dep ⟨0, F.S.sp, F.S.kp⟩ 6 ≤ F.dep ⟨0, F.S.sp, F.S.kp⟩ 1 := c
    rw [z6, z1] at c'
    nlinarith [mul_pos (sub_pos.2 h22) sp0]

end IVT
end Minimality.CaseC20

end

section

/-!
# I_V: the tilted leaves K1, C7', C2'

All three use `leaf_of_view_neg` (`s0x_seg_rupert_tilt` in disguise: the lex facings at `(u, v)`, the
cycle a silhouette of the pattern, the frame depths at `-u` robustly unimodal).  The facets that are
edge-on at `u` and contain neither endpoint (`F` in K1, `G` in C7', C2') are decided by the tilt.
No distinctness of screen points is asked: in C2' the points `x5`, `x2` share one.
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace IVT
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

lemma lp_pos {a b : ℝ} (h : 0 < a) : h21b_LP a b := Or.inl h
lemma lp_zero {a b : ℝ} (h : a = 0) (h2 : 0 < b) : h21b_LP a b := Or.inr ⟨h, h2⟩
lemma lpn_pos {a b : ℝ} (h : a < 0) : h21b_LP (-a) (-b) := Or.inl (neg_pos.2 h)
lemma lpn_zero {a b : ℝ} (h : a = 0) (h2 : b < 0) : h21b_LP (-a) (-b) :=
  Or.inr ⟨by rw [h, neg_zero], neg_pos.2 h2⟩

def ivt_K1_pat : Fin 8 → Bool := ![false, true, false, false, false, true, false, true]
def ivt_K1_c : ZMod 4 → Fin 7 := ![0, 5, 4, 6]
def ivt_C7p_pat : Fin 8 → Bool := ![true, true, true, true, false, false, false, true]
def ivt_C7p_c : ZMod 5 → Fin 7 := ![0, 1, 4, 6, 2]
def ivt_C2p_pat : Fin 8 → Bool := ![true, true, true, true, false, false, false, false]
def ivt_C2p_c : ZMod 5 → Fin 7 := ![0, 1, 4, 5, 2]

theorem ivt_K1_cyc : S0xCycOK h20s_S ivt_K1_c ivt_K1_pat := by decide
theorem ivt_K1_inj : Function.Injective ivt_K1_c := by decide
theorem ivt_C7p_cyc : S0xCycOK h20s_S ivt_C7p_c ivt_C7p_pat := by decide
theorem ivt_C7p_inj : Function.Injective ivt_C7p_c := by decide
theorem ivt_C2p_cyc : S0xCycOK h20s_S ivt_C2p_c ivt_C2p_pat := by decide
theorem ivt_C2p_inj : Function.Injective ivt_C2p_c := by decide

/-- K1: `s35:0546[CvDvF^]`, tilted leaf (`F` is edge-on at `x5 - x3`): needs `A1 > 0` (item), `Phi < 0`. -/
theorem iv_K1 (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hV : ((1-F.S.sp)*(F.S.hm*F.S.tp+F.S.hp*F.S.tm)-F.S.kp*F.S.tm) = 0) (hP : (F.gg*F.S.hm*F.S.km-F.a12*F.S.tm*(1-F.S.sm)) < 0) : IsRupert (univ.image x) := by
  have A1 := F.S.iv_A1_pos hV
  have sm0 := F.S.sm_pos; have tm0 := F.S.tm_pos; have hm0 := F.S.hm_pos; have sp0 := F.S.sp_pos
  have kp0 := F.S.kp_pos; have km0 := F.S.km_pos; have tp0 := F.S.tp_pos; have hp0 := F.S.hp_pos
  have sm1 := F.S.sm1; have W0 := F.S.W_pos
  have ha : 0 < F.a12 := F.A12_pos; have hg : 0 < F.gg := F.g_pos
  have uA : nf F.S ⟨-F.S.tm, 0, F.S.hm⟩ 0 = -(F.S.hm*F.S.sm) := by simp only [nf_A]; ring
  have uB : nf F.S ⟨-F.S.tm, 0, F.S.hm⟩ 1 = F.S.sp * (F.S.hm*F.S.tp+F.S.hp*F.S.tm) := by simp only [nf_B]; ring
  have uC : nf F.S ⟨-F.S.tm, 0, F.S.hm⟩ 2 = 0 := by simp only [nf_C]; ring
  have uD : nf F.S ⟨-F.S.tm, 0, F.S.hm⟩ 3 = 0 := by simp only [nf_D]; ring
  have uE : nf F.S ⟨-F.S.tm, 0, F.S.hm⟩ 4 = -(F.S.hp*F.S.tm-F.S.hm*(1-F.S.tp)) := by simp only [nf_E]; ring
  have uF : nf F.S ⟨-F.S.tm, 0, F.S.hm⟩ 5 = 0 := by simp only [nf_F]; linear_combination hV
  have uG : nf F.S ⟨-F.S.tm, 0, F.S.hm⟩ 6 = -(F.S.km*F.S.tm + (1-F.S.sm)*F.S.hm) := by simp only [nf_G]; ring
  have uH : nf F.S ⟨-F.S.tm, 0, F.S.hm⟩ 7 = F.S.kp * F.S.tm := by simp only [nf_H]; ring
  have vC : nf F.S ⟨0, 1, 0⟩ 2 = -(F.S.hm*F.S.tp+F.S.hp*F.S.tm) := by simp only [nf_C]; ring
  have vD : nf F.S ⟨0, 1, 0⟩ 3 = -(F.S.km*F.S.tm) := by simp only [nf_D]; ring
  have vF : nf F.S ⟨0, 1, 0⟩ 5 = F.S.kp * F.S.tp := by simp only [nf_F]; ring
  refine leaf_of_view_neg F (h20s_fac hR) hx (by norm_num) ivt_K1_inj ivt_K1_cyc (-F.S.tm) 0 F.S.hm ⟨0, 1, 0⟩ 1
    (by rw [uB]; positivity) ?_ ?_
  · intro t; fin_cases t
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (lt_of_eq_of_lt uA (by have := mul_pos hm0 sm0; linarith))⟩
    · exact ⟨fun _ => lp_pos (lt_of_lt_of_eq (by positivity) uB.symm), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_zero uC (lt_of_eq_of_lt vC (by linarith))⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_zero uD (lt_of_eq_of_lt vD (by have := mul_pos km0 tm0; linarith))⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (lt_of_eq_of_lt uE (by linarith))⟩
    · exact ⟨fun _ => lp_zero uF (lt_of_lt_of_eq (by positivity) vF.symm), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (lt_of_eq_of_lt uG (by have := mul_pos km0 tm0; have := mul_pos sm1 hm0; linarith))⟩
    · exact ⟨fun _ => lp_pos (lt_of_lt_of_eq (by positivity) uH.symm), fun h => absurd h (by decide)⟩
  · have e1 : (⟨-(-F.S.tm), -(0:ℝ), -F.S.hm⟩ : C3) = ⟨F.S.tm, 0, -F.S.hm⟩ := by congr 1 <;> ring
    rw [e1]
    have z4 : F.dep ⟨F.S.tm, 0, -F.S.hm⟩ 4 = F.a12*F.S.tm*F.S.sm + F.gg*F.S.hm*F.S.km := by rw [Frame20.dep_4]; ring
    have z5 : F.dep ⟨F.S.tm, 0, -F.S.hm⟩ 5 = 0 := Frame20.dep_5 F _
    have z6 : F.dep ⟨F.S.tm, 0, -F.S.hm⟩ 6 = F.a12*F.S.tm := by rw [Frame20.dep_6]; ring
    have p4 : 0 < F.a12*F.S.tm*F.S.sm + F.gg*F.S.hm*F.S.km := by positivity
    refine robUni4 ?_ ?_
    · rintro ⟨a, b, c, d⟩
      have d' : F.dep ⟨F.S.tm, 0, -F.S.hm⟩ 6 ≤ F.dep ⟨F.S.tm, 0, -F.S.hm⟩ 4 := d
      rw [z6, z4] at d'
      linarith
    · rintro ⟨a, b, c, d⟩
      have c' : F.dep ⟨F.S.tm, 0, -F.S.hm⟩ 4 ≤ F.dep ⟨F.S.tm, 0, -F.S.hm⟩ 5 := c
      rw [z4, z5] at c'
      linarith

end IVT
end Minimality.CaseC20

end

section

/-!
# I_V: the tilted leaves C7' and C2' (`A2 = 0`, facet `G` edge-on at `x5 - x2`)
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace IVT
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- At `A2 = 0` and `Phi >= 0`, `Psi >= 0` (I5). -/
lemma iv_Psi_nonneg (hA : (F.S.km*F.S.sp-F.S.kp*(1-F.S.sm)) = 0) (hP : 0 ≤ (F.gg*F.S.hm*F.S.km-F.a12*F.S.tm*(1-F.S.sm))) : 0 ≤ (F.gg*F.S.hm*F.S.kp-F.a12*F.S.tm*F.S.sp) := by
  have e : (1-F.S.sm) * (F.gg*F.S.hm*F.S.kp-F.a12*F.S.tm*F.S.sp) = F.S.sp * (F.gg*F.S.hm*F.S.km-F.a12*F.S.tm*(1-F.S.sm)) - F.gg*F.S.hm*(F.S.km*F.S.sp-F.S.kp*(1-F.S.sm)) := by ring
  have h1 : 0 ≤ (1-F.S.sm) * (F.gg*F.S.hm*F.S.kp-F.a12*F.S.tm*F.S.sp) := by
    rw [e, hA]; have := mul_nonneg F.S.sp_pos.le hP; linarith
  exact nonneg_of_mul_nonneg_right h1 F.S.sm1

/-- The facings at `u = x5 - x2 = (0, -sp, -kp)` shared by C7' and C2'. -/
lemma iv_tilt_u (hA : (F.S.km*F.S.sp-F.S.kp*(1-F.S.sm)) = 0) (hA06 : (F.S.sp*(F.S.hm-F.S.km*(1-F.S.tm))-F.S.kp*F.S.sm*(1-F.S.tm)) < 0) :
    nf F.S ⟨0, -F.S.sp, -F.S.kp⟩ 0 = -(F.S.sp*(F.S.hm-F.S.km*(1-F.S.tm))-F.S.kp*F.S.sm*(1-F.S.tm)) ∧ nf F.S ⟨0, -F.S.sp, -F.S.kp⟩ 1 = 0 ∧
    nf F.S ⟨0, -F.S.sp, -F.S.kp⟩ 2 = F.S.sp * (F.S.hm*F.S.tp+F.S.hp*F.S.tm) ∧ nf F.S ⟨0, -F.S.sp, -F.S.kp⟩ 3 = F.S.tm*(F.S.km*F.S.sp + F.S.sm*F.S.kp) ∧
    nf F.S ⟨0, -F.S.sp, -F.S.kp⟩ 4 = -(F.S.hp*F.S.sp + (1-F.S.tp)*F.S.kp) ∧ nf F.S ⟨0, -F.S.sp, -F.S.kp⟩ 5 = -(F.S.kp*F.S.tp) ∧
    nf F.S ⟨0, -F.S.sp, -F.S.kp⟩ 6 = 0 ∧ nf F.S ⟨0, -F.S.sp, -F.S.kp⟩ 7 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [nf_A]; ring
  · simp only [nf_B]; ring
  · simp only [nf_C]; ring
  · simp only [nf_D]; ring
  · simp only [nf_E]; ring
  · simp only [nf_F]; ring
  · simp only [nf_G]; linear_combination (-1 : ℝ) * hA
  · simp only [nf_H]; ring

set_option maxHeartbeats 1000000 in
/-- C7': `s25:01462` with `G` edge-on (`A2 = 0`), tilt `v = x5 - x1`. -/
theorem iv_C7p (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hV : ((1-F.S.sp)*(F.S.hm*F.S.tp+F.S.hp*F.S.tm)-F.S.kp*F.S.tm) = 0) (hA : (F.S.km*F.S.sp-F.S.kp*(1-F.S.sm)) = 0) (hP : 0 ≤ (F.gg*F.S.hm*F.S.km-F.a12*F.S.tm*(1-F.S.sm))) (hL : 0 ≤ ((1-F.S.sm)*(F.a22*F.S.sm-F.a12)-F.gg*F.S.km^2)) (hK : 0 < (F.S.hm-(F.S.sm*(F.S.hm*F.S.tp+F.S.hp*F.S.tm)-F.S.tm*F.S.km))) :
    IsRupert (univ.image x) := by
  have A1 := F.S.iv_A1_pos hV
  have sm1 := F.S.sm1; have sp1 := F.S.sp1; have tm1 := F.S.tm1; have tp1 := F.S.tp1
  have sp0 := F.S.sp_pos; have sm0 := F.S.sm_pos; have tm0 := F.S.tm_pos; have tp0 := F.S.tp_pos
  have kp0 := F.S.kp_pos; have km0 := F.S.km_pos; have hm0 := F.S.hm_pos; have hp0 := F.S.hp_pos
  have W0 := F.S.W_pos
  have ha : 0 < F.a12 := F.A12_pos; have hg : 0 < F.gg := F.g_pos; have h22 : F.a12 ≤ F.a22 := F.A12_le_A22
  have s4 := F.S.iv_S4 hA.le
  have Psi0 := iv_Psi_nonneg F hA hP
  obtain ⟨uA, uB, uC, uD, uE, uF, uG, uH⟩ := iv_tilt_u F hA s4
  have vB : nf F.S ⟨-1, 0, 0⟩ 1 = F.S.hp*F.S.sp := by simp only [nf_B]; ring
  have vG : nf F.S ⟨-1, 0, 0⟩ 6 = -F.S.km := by simp only [nf_G]; ring
  have vH : nf F.S ⟨-1, 0, 0⟩ 7 = F.S.kp := by simp only [nf_H]; ring
  refine leaf_of_view_neg F (h20s_fac hR) hx (by norm_num) ivt_C7p_inj ivt_C7p_cyc 0 (-F.S.sp) (-F.S.kp)
    ⟨-1, 0, 0⟩ 2 (by rw [uC]; positivity) ?_ ?_
  · intro t; fin_cases t
    · exact ⟨fun _ => lp_pos (lt_of_lt_of_eq (by linarith) uA.symm), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp_zero uB (lt_of_lt_of_eq (by positivity) vB.symm), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp_pos (lt_of_lt_of_eq (by positivity) uC.symm), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp_pos (lt_of_lt_of_eq (by positivity) uD.symm), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (lt_of_eq_of_lt uE (by
        have := mul_pos hp0 sp0; have := mul_pos tp1 kp0; linarith))⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (lt_of_eq_of_lt uF (by
        have := mul_pos kp0 tp0; linarith))⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_zero uG (lt_of_eq_of_lt vG (by linarith))⟩
    · exact ⟨fun _ => lp_zero uH (lt_of_lt_of_eq kp0 vH.symm), fun h => absurd h (by decide)⟩
  · have e1 : (⟨-(0:ℝ), -(-F.S.sp), -(-F.S.kp)⟩ : C3) = ⟨0, F.S.sp, F.S.kp⟩ := by congr 1 <;> ring
    rw [e1]
    have z0 : F.dep ⟨0, F.S.sp, F.S.kp⟩ 0 = F.a12*F.S.sp*F.S.tp + F.gg*F.S.hp*F.S.kp := by rw [Frame20.dep_0]; ring
    have z1 : F.dep ⟨0, F.S.sp, F.S.kp⟩ 1 = F.a12*F.S.sp := by rw [Frame20.dep_1]; ring
    have z2 : F.dep ⟨0, F.S.sp, F.S.kp⟩ 2 = F.a22*F.S.sp^2 + F.gg*F.S.kp^2 := by rw [Frame20.dep_2]; ring
    have z4 : F.dep ⟨0, F.S.sp, F.S.kp⟩ 4 = F.a22*F.S.sp*F.S.sm - F.gg*F.S.km*F.S.kp := by rw [Frame20.dep_4]; ring
    have z6 : F.dep ⟨0, F.S.sp, F.S.kp⟩ 6 = F.a22*F.S.sp := by rw [Frame20.dep_6]; ring
    refine Minimality.H20S.robUni5_e ?_ ?_ ?_
    · show F.dep _ 1 < F.dep _ 0
      rw [z1, z0]
      have e : F.S.hm * ((F.a12*F.S.sp*F.S.tp + F.gg*F.S.hp*F.S.kp) - F.a12*F.S.sp) = F.S.hp * (F.gg*F.S.hm*F.S.kp-F.a12*F.S.tm*F.S.sp) + F.a12*F.S.sp*(F.S.hp*F.S.tm-F.S.hm*(1-F.S.tp)) := by ring
      have h1 : 0 < F.S.hm * ((F.a12*F.S.sp*F.S.tp + F.gg*F.S.hp*F.S.kp) - F.a12*F.S.sp) := by
        rw [e]; have := mul_nonneg hp0.le Psi0; have := mul_pos (mul_pos ha sp0) A1; linarith
      have := pos_of_mul_pos_right h1 hm0.le
      linarith
    · show F.dep _ 4 < F.dep _ 6
      rw [z4, z6]; nlinarith [mul_pos (mul_pos (lt_of_lt_of_le ha h22) sp0) sm1, mul_pos hg (mul_pos km0 kp0)]
    · show ¬ (F.dep _ 2 ≤ F.dep _ 0 ∧ F.dep _ 2 ≤ F.dep _ 6)
      rintro ⟨c', d'⟩
      rw [z2, z0] at c'
      rw [z2, z6] at d'
      have key : F.S.tm * (F.S.sp * (F.a22*F.S.sp - (F.a22*F.S.sp^2 + F.gg*F.S.kp^2)) +
          (1-F.S.sp) * ((F.a12*F.S.sp*F.S.tp + F.gg*F.S.hp*F.S.kp) - (F.a22*F.S.sp^2 + F.gg*F.S.kp^2))) = -(1-F.S.sp)*F.S.tp*(F.gg*F.S.hm*F.S.kp-F.a12*F.S.tm*F.S.sp) := by
        linear_combination (F.gg*F.S.kp) * hV
      have q1 := mul_nonneg sp0.le (sub_nonneg.2 d')
      have q2 := mul_nonneg sp1.le (sub_nonneg.2 c')
      have h1 : 0 ≤ F.S.tm * (F.S.sp * (F.a22*F.S.sp - (F.a22*F.S.sp^2 + F.gg*F.S.kp^2)) +
          (1-F.S.sp) * ((F.a12*F.S.sp*F.S.tp + F.gg*F.S.hp*F.S.kp) - (F.a22*F.S.sp^2 + F.gg*F.S.kp^2))) := by positivity
      have hPsi : (F.gg*F.S.hm*F.S.kp-F.a12*F.S.tm*F.S.sp) = 0 := by
        have h2 : 0 ≤ (1-F.S.sp)*F.S.tp*(F.gg*F.S.hm*F.S.kp-F.a12*F.S.tm*F.S.sp) := by positivity
        have h3 : (1-F.S.sp)*F.S.tp*(F.gg*F.S.hm*F.S.kp-F.a12*F.S.tm*F.S.sp) ≤ 0 := by linarith
        have h4 : (1-F.S.sp)*F.S.tp*(F.gg*F.S.hm*F.S.kp-F.a12*F.S.tm*F.S.sp) = 0 := le_antisymm h3 h2
        rcases mul_eq_zero.1 h4 with h | h
        · exact absurd h (mul_pos sp1 tp0).ne'
        · exact h
      -- then both differences vanish
      have e6 : F.a22*F.S.sp - (F.a22*F.S.sp^2 + F.gg*F.S.kp^2) = 0 := by
        have h5 : F.S.tm * (F.S.sp * (F.a22*F.S.sp - (F.a22*F.S.sp^2 + F.gg*F.S.kp^2)) +
          (1-F.S.sp) * ((F.a12*F.S.sp*F.S.tp + F.gg*F.S.hp*F.S.kp) - (F.a22*F.S.sp^2 + F.gg*F.S.kp^2))) = 0 := by
          rw [key, hPsi]; ring
        have h6 : F.S.sp * (F.a22*F.S.sp - (F.a22*F.S.sp^2 + F.gg*F.S.kp^2)) +
          (1-F.S.sp) * ((F.a12*F.S.sp*F.S.tp + F.gg*F.S.hp*F.S.kp) - (F.a22*F.S.sp^2 + F.gg*F.S.kp^2)) = 0 := by
          rcases mul_eq_zero.1 h5 with h | h
          · exact absurd h tm0.ne'
          · exact h
        have h7 : F.S.sp * (F.a22*F.S.sp - (F.a22*F.S.sp^2 + F.gg*F.S.kp^2)) = 0 := by linarith
        rcases mul_eq_zero.1 h7 with h | h
        · exact absurd h sp0.ne'
        · exact h
      have E1 : F.gg*F.S.hm*F.S.kp - F.a12*F.S.tm*F.S.sp = 0 := hPsi
      have E3 : F.S.sp*(1-F.S.sp)*(F.a22*F.S.hm - F.a12*(F.S.hm*F.S.tp+F.S.hp*F.S.tm)) = 0 := by
        linear_combination F.S.hm * e6 + F.S.kp * E1 - F.a12*F.S.sp * hV
      have E4 : F.a22*F.S.hm - F.a12*(F.S.hm*F.S.tp+F.S.hp*F.S.tm) = 0 := by
        rcases mul_eq_zero.1 E3 with h | h
        · exact absurd h (mul_pos sp0 sp1).ne'
        · exact h
      have E5 : F.S.hm * (F.dep ⟨0, F.S.sp, F.S.kp⟩ 4 - F.dep ⟨0, F.S.sp, F.S.kp⟩ 1) = -(F.a12*F.S.sp*(F.S.hm-(F.S.sm*(F.S.hm*F.S.tp+F.S.hp*F.S.tm)-F.S.tm*F.S.km))) := by
        rw [z4, z1]
        linear_combination (F.S.sp*F.S.sm) * E4 - F.S.km * E1
      have E6 : F.dep ⟨0, F.S.sp, F.S.kp⟩ 4 - F.dep ⟨0, F.S.sp, F.S.kp⟩ 1 < 0 := by
        have : F.S.hm * (F.dep ⟨0, F.S.sp, F.S.kp⟩ 4 - F.dep ⟨0, F.S.sp, F.S.kp⟩ 1) < 0 := by
          rw [E5]; have := mul_pos (mul_pos ha sp0) hK; linarith
        exact neg_of_mul_neg_right this hm0.le
      rw [z4, z1] at E6
      have E7 : (1-F.S.sm) * (F.a22*F.S.sp*F.S.sm - F.gg*F.S.km*F.S.kp - F.a12*F.S.sp) = F.S.sp*((1-F.S.sm)*(F.a22*F.S.sm-F.a12)-F.gg*F.S.km^2) + F.gg*F.S.km*(F.S.km*F.S.sp-F.S.kp*(1-F.S.sm)) := by ring
      rw [hA] at E7
      have h9 := mul_neg_of_pos_of_neg sm1 E6
      have h10 := mul_nonneg sp0.le hL
      linarith only [E7, h9, h10]

set_option maxHeartbeats 1000000 in
/-- C2': `s25:01452` with `G` edge-on (`A2 = 0`), tilt `v = (tp (1-sm), 0, hp (1-sm) + tp km)`. -/
theorem iv_C2p (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hV : ((1-F.S.sp)*(F.S.hm*F.S.tp+F.S.hp*F.S.tm)-F.S.kp*F.S.tm) = 0) (hA : (F.S.km*F.S.sp-F.S.kp*(1-F.S.sm)) = 0) (hP : 0 ≤ (F.gg*F.S.hm*F.S.km-F.a12*F.S.tm*(1-F.S.sm))) (hL : ((1-F.S.sm)*(F.a22*F.S.sm-F.a12)-F.gg*F.S.km^2) < 0) : IsRupert (univ.image x) := by
  have A1 := F.S.iv_A1_pos hV
  have sm1 := F.S.sm1; have sp1 := F.S.sp1; have tm1 := F.S.tm1; have tp1 := F.S.tp1
  have sp0 := F.S.sp_pos; have sm0 := F.S.sm_pos; have tm0 := F.S.tm_pos; have tp0 := F.S.tp_pos
  have kp0 := F.S.kp_pos; have km0 := F.S.km_pos; have hm0 := F.S.hm_pos; have hp0 := F.S.hp_pos
  have W0 := F.S.W_pos
  have ha : 0 < F.a12 := F.A12_pos; have hg : 0 < F.gg := F.g_pos; have h22 : F.a12 ≤ F.a22 := F.A12_le_A22
  have s4 := F.S.iv_S4 hA.le
  have Psi0 := iv_Psi_nonneg F hA hP
  obtain ⟨uA, uB, uC, uD, uE, uF, uG, uH⟩ := iv_tilt_u F hA s4
  have vB : nf F.S ⟨F.S.tp*(1-F.S.sm), 0, F.S.hp*(1-F.S.sm) + F.S.tp*F.S.km⟩ 1 = F.S.sp*F.S.tp^2*F.S.km := by
    simp only [nf_B]; ring
  have vG : nf F.S ⟨F.S.tp*(1-F.S.sm), 0, F.S.hp*(1-F.S.sm) + F.S.tp*F.S.km⟩ 6 = -((1-F.S.sm)^2*F.S.hp) := by
    simp only [nf_G]; ring
  have vH : nf F.S ⟨F.S.tp*(1-F.S.sm), 0, F.S.hp*(1-F.S.sm) + F.S.tp*F.S.km⟩ 7 = -(F.S.kp*F.S.tp*(1-F.S.sm)) := by
    simp only [nf_H]; ring
  refine leaf_of_view_neg F (h20s_fac hR) hx (by norm_num) ivt_C2p_inj ivt_C2p_cyc 0 (-F.S.sp) (-F.S.kp)
    ⟨F.S.tp*(1-F.S.sm), 0, F.S.hp*(1-F.S.sm) + F.S.tp*F.S.km⟩ 2 (by rw [uC]; positivity) ?_ ?_
  · intro t; fin_cases t
    · exact ⟨fun _ => lp_pos (lt_of_lt_of_eq (by linarith) uA.symm), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp_zero uB (lt_of_lt_of_eq (by positivity) vB.symm), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp_pos (lt_of_lt_of_eq (by positivity) uC.symm), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => lp_pos (lt_of_lt_of_eq (by positivity) uD.symm), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (lt_of_eq_of_lt uE (by
        have := mul_pos hp0 sp0; have := mul_pos tp1 kp0; linarith))⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_pos (lt_of_eq_of_lt uF (by
        have := mul_pos kp0 tp0; linarith))⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_zero uG (lt_of_eq_of_lt vG (by
        have := mul_pos (pow_pos sm1 2) hp0; linarith))⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => lpn_zero uH (lt_of_eq_of_lt vH (by
        have := mul_pos (mul_pos kp0 tp0) sm1; linarith))⟩
  · have e1 : (⟨-(0:ℝ), -(-F.S.sp), -(-F.S.kp)⟩ : C3) = ⟨0, F.S.sp, F.S.kp⟩ := by congr 1 <;> ring
    rw [e1]
    have z0 : F.dep ⟨0, F.S.sp, F.S.kp⟩ 0 = F.a12*F.S.sp*F.S.tp + F.gg*F.S.hp*F.S.kp := by rw [Frame20.dep_0]; ring
    have z1 : F.dep ⟨0, F.S.sp, F.S.kp⟩ 1 = F.a12*F.S.sp := by rw [Frame20.dep_1]; ring
    have z2 : F.dep ⟨0, F.S.sp, F.S.kp⟩ 2 = F.a22*F.S.sp^2 + F.gg*F.S.kp^2 := by rw [Frame20.dep_2]; ring
    have z4 : F.dep ⟨0, F.S.sp, F.S.kp⟩ 4 = F.a22*F.S.sp*F.S.sm - F.gg*F.S.km*F.S.kp := by rw [Frame20.dep_4]; ring
    have z5 : F.dep ⟨0, F.S.sp, F.S.kp⟩ 5 = 0 := Frame20.dep_5 F _
    refine Minimality.H20S.robUni5_f ?_ ?_ ?_ ?_
    · show F.dep _ 1 < F.dep _ 0
      rw [z1, z0]
      have e : F.S.hm * ((F.a12*F.S.sp*F.S.tp + F.gg*F.S.hp*F.S.kp) - F.a12*F.S.sp) = F.S.hp * (F.gg*F.S.hm*F.S.kp-F.a12*F.S.tm*F.S.sp) + F.a12*F.S.sp*(F.S.hp*F.S.tm-F.S.hm*(1-F.S.tp)) := by ring
      have h1 : 0 < F.S.hm * ((F.a12*F.S.sp*F.S.tp + F.gg*F.S.hp*F.S.kp) - F.a12*F.S.sp) := by
        rw [e]; have := mul_nonneg hp0.le Psi0; have := mul_pos (mul_pos ha sp0) A1; linarith
      have := pos_of_mul_pos_right h1 hm0.le
      linarith
    · show F.dep _ 4 < F.dep _ 1
      rw [z4, z1]
      have e : (1-F.S.sm) * (F.a22*F.S.sp*F.S.sm - F.gg*F.S.km*F.S.kp - F.a12*F.S.sp) = F.S.sp*((1-F.S.sm)*(F.a22*F.S.sm-F.a12)-F.gg*F.S.km^2) + F.gg*F.S.km*(F.S.km*F.S.sp-F.S.kp*(1-F.S.sm)) := by ring
      rw [hA] at e
      have h1 : (1-F.S.sm) * (F.a22*F.S.sp*F.S.sm - F.gg*F.S.km*F.S.kp - F.a12*F.S.sp) < 0 := by
        rw [e]; have := mul_neg_of_pos_of_neg sp0 hL; linarith only [this]
      have := neg_of_mul_neg_right h1 sm1.le
      linarith only [this]
    · show F.dep _ 5 < F.dep _ 1
      rw [z5, z1]; exact mul_pos ha sp0
    · show F.dep _ 5 < F.dep _ 2
      rw [z5, z2]
      exact add_pos (mul_pos (lt_of_lt_of_le ha h22) (pow_pos sp0 2)) (mul_pos hg (pow_pos kp0 2))

end IVT
end Minimality.CaseC20

end

section

/-!
# I_V: the case tree and the theorem

`Frame20.isRupert_IV`: the third disjunct of `CaseC20Rest` (line 271 of `CaseC20Face.lean`, copied
verbatim) is Rupert.  `Frame20.isRupert_IV_R`: its `R`-image (line 272).  Tree of COVER.md:
T1 (C1, C5), T2 (C2, C6), T3 (C2, C7), T4 (C8), T5 (K1, C9), T6 (K1, C2', C7').
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- **Type 20, item I_V** (line 271 of `CaseC20Face.lean`): Rupert for every metric of the frame. -/
theorem isRupert_IV (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hV : -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm
      - F.S.kp*F.S.tm = 0) : IsRupert (Finset.univ.image x) := by
  have hV' : ((1-F.S.sp)*(F.S.hm*F.S.tp+F.S.hp*F.S.tm)-F.S.kp*F.S.tm) = 0 := by linear_combination hV
  have A1 := F.S.iv_A1_pos hV'
  have h11 : F.a12 ≤ F.a11 := F.A12_le_A11
  have h22 : F.a12 ≤ F.a22 := F.A12_le_A22
  by_cases T1 : 0 < (F.S.hm*(1-F.S.sm*F.S.tp)-F.S.km*(1-F.S.tm)+F.S.hp*F.S.sm*(1-F.S.tm)) ∧ 0 < (F.S.sm*(F.S.hm*F.S.tp+F.S.hp*F.S.tm)-F.S.tm*F.S.km)
  · by_cases hL : ((1-F.S.tp)*(F.a11*F.S.tp-F.a12)-F.gg*F.S.hp^2) < 0
    · exact IVT.iv_C1 F hx hR hV' hL
    · exact IVT.iv_C5 F hx hR hV' T1.1 T1.2 (not_lt.1 hL)
  obtain ⟨hK, hkm⟩ := F.S.iv_S3 hV' T1
  rcases lt_trichotomy (F.S.km*F.S.sp-F.S.kp*(1-F.S.sm)) 0 with hA | hA | hA
  · -- A2 < 0
    by_cases hP : (F.gg*F.S.hm*F.S.km-F.a12*F.S.tm*(1-F.S.sm)) < 0
    · exact IVT.iv_K1 F hx hR hV' hP
    · by_cases e22 : F.a12 = F.a22
      · exact F.faceA22 e22 (fun hh => by linarith [hh.1, hA])
      · exact IVT.iv_C9 F hx hR hV' hA (lt_of_le_of_ne h22 e22) (not_lt.1 hP)
  · -- A2 = 0
    by_cases hP : (F.gg*F.S.hm*F.S.km-F.a12*F.S.tm*(1-F.S.sm)) < 0
    · exact IVT.iv_K1 F hx hR hV' hP
    · by_cases hL : ((1-F.S.sm)*(F.a22*F.S.sm-F.a12)-F.gg*F.S.km^2) < 0
      · exact IVT.iv_C2p F hx hR hV' hA (not_lt.1 hP) hL
      · exact IVT.iv_C7p F hx hR hV' hA (not_lt.1 hP) (not_lt.1 hL) hK
  · -- A2 > 0
    by_cases hB : 0 < (F.S.tp*(F.S.kp*F.S.sm+F.S.km*F.S.sp)-F.S.sp*F.S.hp)
    · by_cases hL : ((1-F.S.sm)*(F.a22*F.S.sm-F.a12)-F.gg*F.S.km^2) < 0
      · exact IVT.iv_C2 F hx hR hA hL
      · exact IVT.iv_C6 F hx hR hV' hA hB hK (not_lt.1 hL)
    · have hB' : (F.S.tp*(F.S.kp*F.S.sm+F.S.km*F.S.sp)-F.S.sp*F.S.hp) ≤ 0 := not_lt.1 hB
      by_cases hA06 : (F.S.hm*(1-F.S.sm*F.S.tp)-F.S.km*(1-F.S.tm)+F.S.hp*F.S.sm*(1-F.S.tm)) ≤ 0
      · by_cases hL : ((1-F.S.sm)*(F.a22*F.S.sm-F.a12)-F.gg*F.S.km^2) < 0
        · exact IVT.iv_C2 F hx hR hA hL
        · exact IVT.iv_C7 F hx hR hV' hA hB' hA06 hK hkm (not_lt.1 hL)
      · have hA06' : 0 < (F.S.hm*(1-F.S.sm*F.S.tp)-F.S.km*(1-F.S.tm)+F.S.hp*F.S.sm*(1-F.S.tm)) := not_le.1 hA06
        have hD : (F.S.sm*(F.S.hm*F.S.tp+F.S.hp*F.S.tm)-F.S.tm*F.S.km) ≤ 0 := by
          by_contra hc; exact T1 ⟨hA06', not_le.1 hc⟩
        by_cases e11 : F.a12 = F.a11
        · exact F.faceA11 e11 (fun hh => by linarith [hh.1, A1])
        · exact IVT.iv_C8 F hx hR (lt_of_le_of_ne h11 e11) (F.S.iv_I3 hA hB') (F.S.iv_I2 A1 hD)

/-- **The `R`-image of I_V** (line 272 of `CaseC20Face.lean`): Rupert, by `isRupert_IV` for the frame
of `x ∘ R`. -/
theorem isRupert_IV_R (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hV : -F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm
      + F.S.kp*F.S.sm = 0) : IsRupert (Finset.univ.image x) := by
  refine rupert_of_r (F.rFrame.isRupert_IV (hx.comp rperm_bijective.1) (realizesFaces_rperm hR) ?_)
  simp only [rFrame_S, Shape20.swap]; linear_combination hV

end Frame20
end Minimality.CaseC20


end


section
open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20

/-- The special positions left after I_MC and I_V: `CaseC20Rest` without the I_V disjuncts (lines 271
and 272 of `CaseC20Face`) and the I_MC disjuncts (lines 277, 278, 280, 282 and the `R`-images 279 and
285).  What remains: the codimension-2 face residuals `m1'`, `m2'` and the lines 273, 274, 283, 286
(the items I_A and I_Q of the covering notes). -/
def CaseC20Rest2 (x : Fin 7 → ℝ³) : Prop :=
  ∃ F : Frame20 x,
    (F.a12 = F.a11 ∧ F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm = 0 ∧
      0 < (1 - F.S.tp)*(1 - F.S.tm)*F.a12 - F.gg*F.S.hp*F.S.hm ∧
      (1 - F.S.tp)*(1 - F.S.tm)*F.a12 - F.gg*F.S.hp*F.S.hm ≤
        (1 - F.S.tp)*(1 - F.S.sm)*F.a12 - F.gg*F.S.hp*F.S.km) ∨
    (F.a12 = F.a22 ∧ F.S.kp*F.S.sm - F.S.kp + F.S.km*F.S.sp = 0 ∧
      0 < (1 - F.S.sm)*(1 - F.S.sp)*F.a12 - F.gg*F.S.km*F.S.kp ∧
      (1 - F.S.sm)*(1 - F.S.sp)*F.a12 - F.gg*F.S.km*F.S.kp ≤
        (1 - F.S.sm)*(1 - F.S.tp)*F.a12 - F.gg*F.S.km*F.S.hp) ∨
    (F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm = 0) ∨
    (F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp = 0) ∨
    (F.S.hm*F.S.sp - F.S.hm + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp - F.S.km*F.S.tm + F.S.km + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm = 0) ∨
    (F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.sp - F.S.hp*F.S.tm + F.S.hp + F.S.kp*F.S.tm - F.S.kp = 0)

/-- `CaseC20Rest` reduces to Rupert or `CaseC20Rest2`: the I_V and I_MC disjuncts are Rupert
(`isRupert_IV`, `isRupert_IV_R`, `isRupert_IMC_all`, `isRupert_IMC_all_R`), the other six are kept. -/
theorem caseC20Rest_reduce {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (hR : RealizesFaces x (sevenTypeFaces 19)) (h : CaseC20Rest x) :
    IsRupert (Finset.univ.image x) ∨ CaseC20Rest2 x := by
  obtain ⟨F, h⟩ := h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inr ⟨F, Or.inl h⟩
  · exact Or.inr ⟨F, Or.inr (Or.inl h)⟩
  · exact Or.inl (F.isRupert_IV hx hR h)
  · exact Or.inl (F.isRupert_IV_R hx hR h)
  · exact Or.inr ⟨F, Or.inr (Or.inr (Or.inl h))⟩
  · exact Or.inr ⟨F, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩
  · exact Or.inl (F.isRupert_IMC_all hx hR h)
  · exact Or.inl (F.isRupert_IMC_all hx hR h)
  · exact Or.inl (F.isRupert_IMC_all_R hx hR h.1 h.2)
  · exact Or.inl (F.isRupert_IMC_all hx hR h)
  · exact Or.inl (F.isRupert_IMC_all hx hR h)
  · exact Or.inr ⟨F, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩
  · exact Or.inl (F.isRupert_IMC_all_R hx hR h.1 h.2)
  · exact Or.inr ⟨F, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))⟩

end Minimality.CaseC20
end

#print axioms Minimality.CaseC20.caseC20Rest_reduce
