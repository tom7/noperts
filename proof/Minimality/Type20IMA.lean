module

public import Minimality.Type20Bridge
public import Minimality.CaseC20Face

@[expose] public section

/-!
# Type 20, item I_MA: the metric special position `O = 0 ∧ L = 0`

In the frame coordinates of `Frame20` the item I_MA is the pair of equations
`(sm tp - sm - tp + 1) a12 - hp km gg = 0` and `km tm (a11 - a12) + (...) a12 = 0`.
Every point set on this locus (that realizes the faces of type 20) is Rupert:
* `D1 = tp km - hp (1 - sm) < 0`: the segment leaf `s05:0162[B^C^]`;
* `D1 > 0`: the line leaf `LCG:01625[CvGv]`;
* `D1 = 0`: the tilted segment leaf `s05:13526[BvCvG^]` (`s0x_seg_rupert_tilt`).
`isRupert_IMA_all` has no hypothesis on `D1`; `isRupert_IMA_R` is the `R`-image (second equation
with `a22`).  `CaseC20Rest` is `CaseC20Special''` without these disjuncts, and
`caseC20Special''_reduce` shows that `CaseC20Special''` reduces to Rupert or `CaseC20Rest`.
-/

section

/-!
# I_MA: facet forms at the two I_MA views, in Frame20 shape coordinates

Facets of type 20 (index `A..H = 0..7`): `A 134, B 025, C 0135, D 345, E 016, F 026, G 146, H 2456`.
Views: `qS = (tp, 0, hp)` (segment `x0 - x5`, `x 0 - x 5 = fvC qS`) and
`qL = (1 - sm, 0, km)` (line of facets C and G).  All facings are polynomial in the shape;
`D1 = tp*km - hp*(1-sm)` decides which of B, F (line) or A, G (segment) has the needed sign.
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20

namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x) (FF : S0xFac 8 h20s_S x)

/-- The facing of facet `t` along the view `q`, from its values at `x1, x5, x6` and `δ = ⟪N,e⟫`. -/
lemma facet_val (t : Fin 8) (q : C3) :
    ⟪FF.N t, F.toFrame7.fvC q⟫ = q.x * (FF.f t (x 1) - FF.f t (x 5)) +
      q.y * (FF.f t (x 6) - FF.f t (x 5)) + q.z * ⟪FF.N t, F.e⟫ := by
  rw [F.inner_fvC_right, ← FF.hN, ← FF.hN]

/-- Segment view, literal for facet A (`134`): `A+` holds when `D1 < 0`. -/
lemma lit_A_seg (hD : F.S.tp * F.S.km < F.S.hp * (1 - F.S.sm)) :
    0 < FF.f 0 (x 5) - FF.f 0 (x 0) := by
  obtain ⟨c0, c3, -, -⟩ := F.facet_coords (FF.f 0) (FF.N 0) (FF.hN 0)
  have z1 : FF.f 0 (x 1) = 0 := FF.zero 0 1 (by decide)
  have z3 : FF.f 0 (x 3) = 0 := FF.zero 0 3 (by decide)
  have n5 : FF.f 0 (x 5) < 0 := FF.neg 0 5 (by decide)
  have h1 := mul_lt_mul_of_pos_left F.S.roof_m' F.S.tp_pos
  have h2 := mul_lt_mul_of_pos_right hD (show 0 < 1 - F.S.tm by linarith [F.S.tm_lt])
  have hm := F.S.hm_pos
  rw [z1] at c0 c3
  rw [z3] at c3
  have key : F.S.hm * (FF.f 0 (x 0) - FF.f 0 (x 5)) =
      -FF.f 0 (x 5) * (F.S.tp * F.S.hm - F.S.hp * (1 - F.S.tm)) := by
    linear_combination F.S.hm * c0 + F.S.hp * c3
  have hs : 0 < 1 - F.S.sm := by linarith [F.S.sm_lt]
  have hQ : F.S.tp * F.S.hm - F.S.hp * (1 - F.S.tm) < 0 := by
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg hs.le hc]
  have h5 : -FF.f 0 (x 5) * (F.S.tp * F.S.hm - F.S.hp * (1 - F.S.tm)) < 0 :=
    mul_neg_of_pos_of_neg (by linarith) hQ
  by_contra hc
  push Not at hc
  nlinarith [mul_nonneg hm.le (show 0 ≤ FF.f 0 (x 0) - FF.f 0 (x 5) by linarith)]

/-- Segment view, literal for facet G (`146`): `G+` is exactly `D1 < 0`. -/
lemma lit_G_seg (hD : F.S.tp * F.S.km < F.S.hp * (1 - F.S.sm)) :
    0 < FF.f 6 (x 5) - FF.f 6 (x 0) := by
  obtain ⟨c0, -, -, c4⟩ := F.facet_coords (FF.f 6) (FF.N 6) (FF.hN 6)
  have z1 : FF.f 6 (x 1) = 0 := FF.zero 6 1 (by decide)
  have z4 : FF.f 6 (x 4) = 0 := FF.zero 6 4 (by decide)
  have z6 : FF.f 6 (x 6) = 0 := FF.zero 6 6 (by decide)
  have n5 : FF.f 6 (x 5) < 0 := FF.neg 6 5 (by decide)
  rw [z1] at c0
  rw [z4, z6] at c4
  have key : F.S.km * (FF.f 6 (x 0) - FF.f 6 (x 5)) =
      -FF.f 6 (x 5) * (F.S.tp * F.S.km - F.S.hp * (1 - F.S.sm)) := by
    linear_combination F.S.km * c0 + F.S.hp * c4
  have h5 : -FF.f 6 (x 5) * (F.S.tp * F.S.km - F.S.hp * (1 - F.S.sm)) < 0 :=
    mul_neg_of_pos_of_neg (by linarith) (by linarith)
  by_contra hc
  push Not at hc
  nlinarith [mul_nonneg F.S.km_pos.le (show 0 ≤ FF.f 6 (x 0) - FF.f 6 (x 5) by linarith)]

/-- The coordinate form of the line view `qL = (1 - sm, 0, km)` against a facet. -/
lemma facet_val_L (t : Fin 8) :
    ⟪FF.N t, F.toFrame7.fvC ⟨1 - F.S.sm, 0, F.S.km⟩⟫ =
      (1 - F.S.sm) * (FF.f t (x 1) - FF.f t (x 5)) + F.S.km * ⟪FF.N t, F.e⟫ := by
  rw [F.facet_val FF t]; dsimp only; ring

/-- Line view `L_CG`, facet A is below (`⟪N_A, w⟫ < 0`), from the lower roof. -/
lemma lcg_A : ⟪FF.N 0, F.toFrame7.fvC ⟨1 - F.S.sm, 0, F.S.km⟩⟫ < 0 := by
  rw [F.facet_val_L FF]
  obtain ⟨-, c3, -, -⟩ := F.facet_coords (FF.f 0) (FF.N 0) (FF.hN 0)
  have z1 : FF.f 0 (x 1) = 0 := FF.zero 0 1 (by decide)
  have z3 : FF.f 0 (x 3) = 0 := FF.zero 0 3 (by decide)
  have n5 : FF.f 0 (x 5) < 0 := FF.neg 0 5 (by decide)
  rw [z1, z3] at c3
  rw [z1]
  have key : F.S.hm * ((1 - F.S.sm) * (0 - FF.f 0 (x 5)) + F.S.km * ⟪FF.N 0, F.e⟫) =
      FF.f 0 (x 5) * (F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm)) := by
    linear_combination F.S.km * c3
  have h5 : FF.f 0 (x 5) * (F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm)) < 0 :=
    mul_neg_of_neg_of_pos n5 (by linarith [F.S.roof_m'])
  by_contra hc
  push Not at hc
  nlinarith [mul_nonneg F.S.hm_pos.le hc]

/-- Line view `L_CG`, facet B is above exactly when `D1 > 0`. -/
lemma lcg_B (hD : F.S.hp * (1 - F.S.sm) < F.S.tp * F.S.km) :
    0 < ⟪FF.N 1, F.toFrame7.fvC ⟨1 - F.S.sm, 0, F.S.km⟩⟫ := by
  rw [F.facet_val_L FF]
  obtain ⟨c0, -, -, -⟩ := F.facet_coords (FF.f 1) (FF.N 1) (FF.hN 1)
  have z0 : FF.f 1 (x 0) = 0 := FF.zero 1 0 (by decide)
  have z5 : FF.f 1 (x 5) = 0 := FF.zero 1 5 (by decide)
  have n1 : FF.f 1 (x 1) < 0 := FF.neg 1 1 (by decide)
  rw [z0, z5] at c0
  rw [z5]
  have key : F.S.hp * ((1 - F.S.sm) * (FF.f 1 (x 1) - 0) + F.S.km * ⟪FF.N 1, F.e⟫) =
      (-FF.f 1 (x 1)) * (F.S.tp * F.S.km - F.S.hp * (1 - F.S.sm)) := by
    linear_combination (-F.S.km) * c0
  have h5 : 0 < (-FF.f 1 (x 1)) * (F.S.tp * F.S.km - F.S.hp * (1 - F.S.sm)) :=
    mul_pos (by linarith) (by linarith)
  by_contra hc
  push Not at hc
  nlinarith [mul_nonneg F.S.hp_pos.le (show 0 ≤ -((1 - F.S.sm) * (FF.f 1 (x 1) - 0) +
    F.S.km * ⟪FF.N 1, F.e⟫) by linarith)]

/-- Line view `L_CG`, facet D is below. -/
lemma lcg_D : ⟪FF.N 3, F.toFrame7.fvC ⟨1 - F.S.sm, 0, F.S.km⟩⟫ < 0 := by
  rw [F.facet_val_L FF]
  obtain ⟨-, c3, -, -⟩ := F.facet_coords (FF.f 3) (FF.N 3) (FF.hN 3)
  have z3 : FF.f 3 (x 3) = 0 := FF.zero 3 3 (by decide)
  have z5 : FF.f 3 (x 5) = 0 := FF.zero 3 5 (by decide)
  have n1 : FF.f 3 (x 1) < 0 := FF.neg 3 1 (by decide)
  rw [z3, z5] at c3
  rw [z5]
  have key : F.S.hm * ((1 - F.S.sm) * (FF.f 3 (x 1) - 0) + F.S.km * ⟪FF.N 3, F.e⟫) =
      FF.f 3 (x 1) * ((1 - F.S.sm) * F.S.hm + F.S.km * F.S.tm) := by
    linear_combination F.S.km * c3
  have h5 : FF.f 3 (x 1) * ((1 - F.S.sm) * F.S.hm + F.S.km * F.S.tm) < 0 :=
    mul_neg_of_neg_of_pos n1 (by
      have := F.S.sm_lt; have := F.S.hm_pos; have := F.S.km_pos; have := F.S.tm_pos
      positivity)
  by_contra hc
  push Not at hc
  nlinarith [mul_nonneg F.S.hm_pos.le hc]

/-- Line view `L_CG`, facet E is above. -/
lemma lcg_E : 0 < ⟪FF.N 4, F.toFrame7.fvC ⟨1 - F.S.sm, 0, F.S.km⟩⟫ := by
  rw [F.facet_val_L FF]
  obtain ⟨c0, -, -, -⟩ := F.facet_coords (FF.f 4) (FF.N 4) (FF.hN 4)
  have z0 : FF.f 4 (x 0) = 0 := FF.zero 4 0 (by decide)
  have z1 : FF.f 4 (x 1) = 0 := FF.zero 4 1 (by decide)
  have n5 : FF.f 4 (x 5) < 0 := FF.neg 4 5 (by decide)
  rw [z0, z1] at c0
  rw [z1]
  have key : F.S.hp * ((1 - F.S.sm) * (0 - FF.f 4 (x 5)) + F.S.km * ⟪FF.N 4, F.e⟫) =
      (-FF.f 4 (x 5)) * ((1 - F.S.sm) * F.S.hp + F.S.km * (1 - F.S.tp)) := by
    linear_combination (-F.S.km) * c0
  have h5 : 0 < (-FF.f 4 (x 5)) * ((1 - F.S.sm) * F.S.hp + F.S.km * (1 - F.S.tp)) :=
    mul_pos (by linarith) (by
      have := F.S.sm_lt; have := F.S.tp_lt; have := F.S.hp_pos; have := F.S.km_pos
      have : 0 < 1 - F.S.sm := by linarith
      have : 0 < 1 - F.S.tp := by linarith
      positivity)
  by_contra hc
  push Not at hc
  nlinarith [mul_nonneg F.S.hp_pos.le (show 0 ≤ -((1 - F.S.sm) * (0 - FF.f 4 (x 5)) +
    F.S.km * ⟪FF.N 4, F.e⟫) by linarith)]

/-- Line view `L_CG`, facet F is above exactly under `D1 > 0` (together with the roofs). -/
lemma lcg_F (hD : F.S.hp * (1 - F.S.sm) < F.S.tp * F.S.km) :
    0 < ⟪FF.N 5, F.toFrame7.fvC ⟨1 - F.S.sm, 0, F.S.km⟩⟫ := by
  rw [F.facet_val_L FF]
  obtain ⟨c0, -, c2, -⟩ := F.facet_coords (FF.f 5) (FF.N 5) (FF.hN 5)
  have z0 : FF.f 5 (x 0) = 0 := FF.zero 5 0 (by decide)
  have z2 : FF.f 5 (x 2) = 0 := FF.zero 5 2 (by decide)
  have z6 : FF.f 5 (x 6) = 0 := FF.zero 5 6 (by decide)
  have n5 : FF.f 5 (x 5) < 0 := FF.neg 5 5 (by decide)
  rw [z0] at c0
  rw [z2, z6] at c2
  have key : F.S.tp * F.S.kp * ((1 - F.S.sm) * (FF.f 5 (x 1) - FF.f 5 (x 5)) +
      F.S.km * ⟪FF.N 5, F.e⟫) =
      (-FF.f 5 (x 5)) * ((1 - F.S.sm) * F.S.kp +
        (1 - F.S.sp) * (F.S.tp * F.S.km - F.S.hp * (1 - F.S.sm))) := by
    linear_combination (-(F.S.kp * (1 - F.S.sm))) * c0 +
      (-(F.S.tp * F.S.km - F.S.hp * (1 - F.S.sm))) * c2
  have h5 : 0 < (-FF.f 5 (x 5)) * ((1 - F.S.sm) * F.S.kp +
        (1 - F.S.sp) * (F.S.tp * F.S.km - F.S.hp * (1 - F.S.sm))) :=
    mul_pos (by linarith) (by
      have := F.S.sm_lt; have := F.S.sp_lt; have := F.S.kp_pos
      have : 0 < 1 - F.S.sm := by linarith
      have : 0 < 1 - F.S.sp := by linarith
      have : 0 < F.S.tp * F.S.km - F.S.hp * (1 - F.S.sm) := by linarith
      positivity)
  by_contra hc
  push Not at hc
  nlinarith [mul_nonneg (mul_pos F.S.tp_pos F.S.kp_pos).le (show 0 ≤ -((1 - F.S.sm) *
    (FF.f 5 (x 1) - FF.f 5 (x 5)) + F.S.km * ⟪FF.N 5, F.e⟫) by linarith)]

/-- Line view `L_CG`, facet H is below. -/
lemma lcg_H : ⟪FF.N 7, F.toFrame7.fvC ⟨1 - F.S.sm, 0, F.S.km⟩⟫ < 0 := by
  rw [F.facet_val_L FF]
  obtain ⟨-, -, c2, -⟩ := F.facet_coords (FF.f 7) (FF.N 7) (FF.hN 7)
  have z2 : FF.f 7 (x 2) = 0 := FF.zero 7 2 (by decide)
  have z5 : FF.f 7 (x 5) = 0 := FF.zero 7 5 (by decide)
  have z6 : FF.f 7 (x 6) = 0 := FF.zero 7 6 (by decide)
  have n1 : FF.f 7 (x 1) < 0 := FF.neg 7 1 (by decide)
  rw [z2, z5, z6] at c2
  rw [z5]
  have key : F.S.kp * ((1 - F.S.sm) * (FF.f 7 (x 1) - 0) + F.S.km * ⟪FF.N 7, F.e⟫) =
      (1 - F.S.sm) * F.S.kp * FF.f 7 (x 1) := by
    linear_combination (-F.S.km) * c2
  have h5 : (1 - F.S.sm) * F.S.kp * FF.f 7 (x 1) < 0 :=
    mul_neg_of_pos_of_neg (by have := F.S.sm_lt; have := F.S.kp_pos
                              have : 0 < 1 - F.S.sm := by linarith
                              positivity) n1
  by_contra hc
  push Not at hc
  nlinarith [mul_nonneg F.S.kp_pos.le hc]

end Frame20
end Minimality.CaseC20
end

section

/-!
# I_MA: the line view `L_CG` is `l * fvC (1 - sm, 0, km)`, and its depth order
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x) (FF : S0xFac 8 h20s_S x)

/-- The line view `N_C x N_G` is a nonzero multiple `l` of the frame vector `(1-sm, 0, km)`
(whose sign `l` is the orientation of the frame). -/
lemma cross_CG : ∃ l : ℝ, l ≠ 0 ∧
    cross (FF.N 2) (FF.N 6) = F.toFrame7.fvC ⟨l * (1 - F.S.sm), 0, l * F.S.km⟩ := by
  have hs := F.S.sm_lt
  have hk := F.S.km_pos
  -- facet C (0135)
  obtain ⟨c0, -, -, -⟩ := F.facet_coords (FF.f 2) (FF.N 2) (FF.hN 2)
  have a0 : FF.f 2 (x 0) = 0 := FF.zero 2 0 (by decide)
  have a1 : FF.f 2 (x 1) = 0 := FF.zero 2 1 (by decide)
  have a5 : FF.f 2 (x 5) = 0 := FF.zero 2 5 (by decide)
  have a6 : FF.f 2 (x 6) < 0 := FF.neg 2 6 (by decide)
  rw [a0, a1, a5] at c0
  have dC : ⟪FF.N 2, F.e⟫ = 0 := by
    have := F.S.hp_pos
    have h : F.S.hp * ⟪FF.N 2, F.e⟫ = 0 := by linarith
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h this.ne'
    · exact h
  -- facet G (146)
  obtain ⟨-, -, -, g4⟩ := F.facet_coords (FF.f 6) (FF.N 6) (FF.hN 6)
  have b1 : FF.f 6 (x 1) = 0 := FF.zero 6 1 (by decide)
  have b4 : FF.f 6 (x 4) = 0 := FF.zero 6 4 (by decide)
  have b6 : FF.f 6 (x 6) = 0 := FF.zero 6 6 (by decide)
  have b5 : FF.f 6 (x 5) < 0 := FF.neg 6 5 (by decide)
  rw [b4, b6] at g4
  have hne : ⟪FF.N 2, x 6 - x 5⟫ * ⟪FF.N 6, x 1 - x 5⟫ ≠
      ⟪FF.N 2, x 1 - x 5⟫ * ⟪FF.N 6, x 6 - x 5⟫ := by
    rw [← FF.hN, ← FF.hN, ← FF.hN, ← FF.hN, a1, a5, b1, b6]
    have : (FF.f 2 (x 6) - 0) * (0 - FF.f 6 (x 5)) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) (by linarith)
    intro h; nlinarith
  have hcr := Frame20.cross_ne_zero _ _ hne
  obtain ⟨q, hq, e1, e2⟩ := F.cross_coords (FF.N 2) (FF.N 6)
  rw [← FF.hN, ← FF.hN, a1, a5, dC] at e1
  rw [← FF.hN, ← FF.hN, b1] at e2
  have hqy : q.y = 0 := by
    have : q.y * (FF.f 2 (x 6) - 0) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h (by linarith)
  have hqx : F.S.km * q.x = (1 - F.S.sm) * q.z := by
    rw [hqy] at e2
    have h : (-FF.f 6 (x 5)) * (F.S.km * q.x - (1 - F.S.sm) * q.z) = 0 := by
      linear_combination F.S.km * e2 + (-q.z) * g4
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h (by linarith)
    · linarith
  refine ⟨q.z / F.S.km, ?_, ?_⟩
  · intro h0
    have hz : q.z = 0 := by
      rcases div_eq_zero_iff.1 h0 with h | h
      · exact h
      · exact absurd h hk.ne'
    have hx0 : q.x = 0 := by
      rw [hz] at hqx
      have : F.S.km * q.x = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hk.ne'
      · exact h
    apply hcr
    rw [hq]
    simp only [Frame7.fvC, hqy, hz, hx0, zero_smul, add_zero]
  · rw [hq]
    have hx' : q.x = q.z / F.S.km * (1 - F.S.sm) := by field_simp; linarith
    have hz' : q.z = q.z / F.S.km * F.S.km := by field_simp
    simp only [Frame7.fvC]
    rw [← hx', ← hz', hqy]

end Frame20
end Minimality.CaseC20
end

section

/-!
# I_MA: the case D1 > 0 (leaf `LCG:01625[CvGv]`, either orientation)
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x) (FF : S0xFac 8 h20s_S x)

/-- Depths are linear in the view. -/
lemma dep_scale (l a b c : ℝ) (j : Fin 7) :
    F.dep ⟨l * a, l * b, l * c⟩ j = l * F.dep ⟨a, b, c⟩ j := by
  simp only [dep, GG_eq]; ring

/-- Robust unimodality of the frame depths gives it for the actual depths `⟪x_j, fvC q⟫`. -/
lemma robUni_of_dep {k : ℕ} (c : ZMod k → Fin 7) (q : C3)
    (h : RobUni (fun a => F.dep q (c a))) :
    RobUni (fun a => ⟪x (c a), F.toFrame7.fvC q⟫) := by
  have := robUni_add_const h ⟪x 5, F.toFrame7.fvC q⟫
  convert this using 1
  funext a
  exact F.inner_x_fvC q (c a)

/-- On the I_MA locus, `a12 < a11` (from the second equation and the lower roof). -/
lemma a12_lt_a11 (hL : (F.S.km*F.S.tm) * (F.a11 - F.a12) +
    (-F.S.hm*F.S.sm + F.S.hm + F.S.km*F.S.tm - F.S.km) * F.a12 = 0) : F.a12 < F.a11 := by
  have h1 : (F.S.km*F.S.tm) * (F.a11 - F.a12) =
      F.a12 * (F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm)) := by linear_combination hL
  have h2 : 0 < F.a12 * (F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm)) :=
    mul_pos F.A12_pos (by linarith [F.S.roof_m'])
  have h3 : 0 < (F.S.km*F.S.tm) * (F.a11 - F.a12) := by rw [h1]; exact h2
  have h4 : 0 < F.S.km * F.S.tm := mul_pos F.S.km_pos F.S.tm_pos
  have := pos_of_mul_pos_right h3 h4.le
  linarith

/-- The depth order at the line view `qL = (1-sm, 0, km)`: `z5 < z2 < z6 < z0 < z1`. -/
lemma lcg_depth_order
    (hO : (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0)
    (hL : (F.S.km*F.S.tm) * (F.a11 - F.a12) +
      (-F.S.hm*F.S.sm + F.S.hm + F.S.km*F.S.tm - F.S.km) * F.a12 = 0) :
    F.dep ⟨1 - F.S.sm, 0, F.S.km⟩ 5 < F.dep ⟨1 - F.S.sm, 0, F.S.km⟩ 2 ∧
    F.dep ⟨1 - F.S.sm, 0, F.S.km⟩ 2 < F.dep ⟨1 - F.S.sm, 0, F.S.km⟩ 6 ∧
    F.dep ⟨1 - F.S.sm, 0, F.S.km⟩ 6 < F.dep ⟨1 - F.S.sm, 0, F.S.km⟩ 0 ∧
    F.dep ⟨1 - F.S.sm, 0, F.S.km⟩ 0 < F.dep ⟨1 - F.S.sm, 0, F.S.km⟩ 1 := by
  have h11 := F.a12_lt_a11 hL
  have ha : 0 < F.a12 := F.A12_pos
  have hg := F.g_pos
  have s1 : 0 < 1 - F.S.sm := by linarith [F.S.sm_lt]
  have t1 : 0 < 1 - F.S.tp := by linarith [F.S.tp_lt]
  have sp1 : 0 < 1 - F.S.sp := by linarith [F.S.sp_lt]
  have := F.S.tp_pos; have := F.S.sp_pos; have := F.S.kp_pos; have := F.S.km_pos
  have := F.S.hp_pos
  simp only [dep_0, dep_1, dep_2, dep_5, dep_6]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have p1 := mul_pos ha (mul_pos F.S.sp_pos s1)
    have p2 := mul_pos hg (mul_pos F.S.kp_pos F.S.km_pos)
    nlinarith [p1, p2]
  · have key : F.S.hp * (F.a12 * (1 - F.S.sm) - F.a12 * (F.S.sp * (1 - F.S.sm)) +
        (-(F.gg * (F.S.kp * F.S.km)))) =
        F.a12 * (1 - F.S.sm) * (F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp)) := by
      linear_combination F.S.kp * hO
    have h5 : 0 < F.a12 * (1 - F.S.sm) * (F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp)) :=
      mul_pos (mul_pos ha s1) (by linarith [F.S.roof_p'])
    have := pos_of_mul_pos_right (key ▸ h5) F.S.hp_pos.le
    linarith
  · have key : F.a11 * (F.S.tp * (1 - F.S.sm)) + F.gg * (F.S.hp * F.S.km) - F.a12 * (1 - F.S.sm) =
        (1 - F.S.sm) * F.S.tp * (F.a11 - F.a12) := by
      linear_combination (-1 : ℝ) * hO
    have h5 : 0 < (1 - F.S.sm) * F.S.tp * (F.a11 - F.a12) :=
      mul_pos (mul_pos s1 F.S.tp_pos) (by linarith)
    nlinarith [key, h5]
  · have key : F.a11 * (1 - F.S.sm) - (F.a11 * (F.S.tp * (1 - F.S.sm)) + F.gg * (F.S.hp * F.S.km)) =
        (1 - F.S.sm) * (1 - F.S.tp) * (F.a11 - F.a12) := by
      linear_combination hO
    have h5 : 0 < (1 - F.S.sm) * (1 - F.S.tp) * (F.a11 - F.a12) :=
      mul_pos (mul_pos s1 t1) (by linarith)
    nlinarith [key, h5]

end Frame20
end Minimality.CaseC20
end

section

/-!
# I_MA: assembling the branch D1 > 0
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x) (FF : S0xFac 8 h20s_S x)

/-- Facings along the scaled line view are the scaled facings. -/
lemma facet_val_scale (t : Fin 8) (l : ℝ) :
    ⟪FF.N t, F.toFrame7.fvC ⟨l * (1 - F.S.sm), 0, l * F.S.km⟩⟫ =
      l * ⟪FF.N t, F.toFrame7.fvC ⟨1 - F.S.sm, 0, F.S.km⟩⟫ := by
  rw [F.facet_val FF, F.facet_val FF]; dsimp only; ring

/-- **I_MA, `D1 > 0`**: leaf `LCG:01625[CvGv]`, in the orientation given by the frame. -/
theorem isRupert_IMA_pos (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hO : (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0)
    (hL : (F.S.km*F.S.tm) * (F.a11 - F.a12) +
      (-F.S.hm*F.S.sm + F.S.hm + F.S.km*F.S.tm - F.S.km) * F.a12 = 0)
    (hD : F.S.hp * (1 - F.S.sm) < F.S.tp * F.S.km) :
    IsRupert (Finset.univ.image x) := by
  set FF := h20s_fac hR with hFF
  obtain ⟨l, hl, hc⟩ := F.cross_CG FF
  obtain ⟨o1, o2, o3, o4⟩ := F.lcg_depth_order hO hL
  have sc := fun t => F.facet_val_scale FF t l
  have lA := F.lcg_A FF
  have lB := F.lcg_B FF hD
  have lD := F.lcg_D FF
  have lE := F.lcg_E FF
  have lF := F.lcg_F FF hD
  have lH := F.lcg_H FF
  have hU : ∀ (_ : 0 < l ∨ l < 0), True := fun _ => trivial
  have e0 : h20s_LCG.c (0 : ZMod 5) = 0 := rfl
  have e1 : h20s_LCG.c (1 : ZMod 5) = 1 := rfl
  have e2 : h20s_LCG.c (2 : ZMod 5) = 6 := rfl
  have e3 : h20s_LCG.c (3 : ZMod 5) = 2 := rfl
  have e4 : h20s_LCG.c (4 : ZMod 5) = 5 := rfl
  have dsc : ∀ j, F.dep ⟨l * (1 - F.S.sm), 0, l * F.S.km⟩ j = l * F.dep ⟨1 - F.S.sm, 0, F.S.km⟩ j :=
    fun j => by simpa using F.dep_scale l (1 - F.S.sm) 0 F.S.km j
  rcases lt_or_gt_of_ne hl with hneg | hpos
  · refine h20s_I_LCG' FF hx ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hc, sc]; exact mul_pos_of_neg_of_neg hneg lA
    · rw [hc, sc]; exact mul_neg_of_neg_of_pos hneg lB
    · rw [hc, sc]; exact mul_pos_of_neg_of_neg hneg lD
    · rw [hc, sc]; exact mul_neg_of_neg_of_pos hneg lE
    · rw [hc, sc]; exact mul_neg_of_neg_of_pos hneg lF
    · rw [hc, sc]; exact mul_pos_of_neg_of_neg hneg lH
    · rw [hc]
      refine F.robUni_of_dep _ _ (robUni5_b ?_ ?_ ?_ ?_)
      · show F.dep _ (h20s_LCG.c 3) < F.dep _ (h20s_LCG.c 4)
        rw [e3, e4, dsc, dsc]; nlinarith
      · show F.dep _ (h20s_LCG.c 2) < F.dep _ (h20s_LCG.c 3)
        rw [e2, e3, dsc, dsc]; nlinarith
      · show F.dep _ (h20s_LCG.c 0) < F.dep _ (h20s_LCG.c 2)
        rw [e0, e2, dsc, dsc]; nlinarith
      · show F.dep _ (h20s_LCG.c 1) < F.dep _ (h20s_LCG.c 0)
        rw [e1, e0, dsc, dsc]; nlinarith
  · refine h20s_I_LCG FF hx ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hc, sc]; exact mul_neg_of_pos_of_neg hpos lA
    · rw [hc, sc]; exact mul_pos hpos lB
    · rw [hc, sc]; exact mul_neg_of_pos_of_neg hpos lD
    · rw [hc, sc]; exact mul_pos hpos lE
    · rw [hc, sc]; exact mul_pos hpos lF
    · rw [hc, sc]; exact mul_neg_of_pos_of_neg hpos lH
    · rw [hc]
      refine F.robUni_of_dep _ _ (robUni5_a ?_ ?_ ?_ ?_)
      · show F.dep _ (h20s_LCG.c 4) < F.dep _ (h20s_LCG.c 3)
        rw [e4, e3, dsc, dsc]; nlinarith
      · show F.dep _ (h20s_LCG.c 3) < F.dep _ (h20s_LCG.c 2)
        rw [e3, e2, dsc, dsc]; nlinarith
      · show F.dep _ (h20s_LCG.c 2) < F.dep _ (h20s_LCG.c 0)
        rw [e2, e0, dsc, dsc]; nlinarith
      · show F.dep _ (h20s_LCG.c 0) < F.dep _ (h20s_LCG.c 1)
        rw [e0, e1, dsc, dsc]; nlinarith

end Frame20
end Minimality.CaseC20
end

section

/-!
# I_MA: the branch D1 < 0 (leaf `s05:0162[B^C^]`, view `x 5 - x 0`)
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- The segment view `x 5 - x 0` in frame coordinates is `fvC (-tp, 0, -hp)`. -/
lemma x5_sub_x0 : x 5 - x 0 = F.toFrame7.fvC ⟨-F.S.tp, 0, -F.S.hp⟩ := by
  have := F.toFrame7.x_sub 5 0
  rw [this]
  simp only [Frame7.fvC, C3.sub, toFrame7, pt]
  simp only [Matrix.cons_val_zero, Matrix.cons_val, sub_zero]
  module

/-- With `D1 < 0` the cell `s05` cannot have `d0` and `d6` (even `d0` alone) weakly below both
`d1` and `d2` (the depths `d_j = x_j^T G (tp, 0, hp)`): the combination
`(1-tp)(d2-d0) + tp(d1-d0)` is negative. -/
lemma s05_no_low_d0
    (hO : (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0)
    (hD : F.S.tp * F.S.km < F.S.hp * (1 - F.S.sm))
    (P : F.a11 * (F.S.tp * F.S.tp) + F.gg * (F.S.hp * F.S.hp) ≤ F.a11 * F.S.tp)
    (Q : F.a11 * (F.S.tp * F.S.tp) + F.gg * (F.S.hp * F.S.hp) ≤
      F.a12 * (F.S.sp * F.S.tp) + F.gg * (F.S.kp * F.S.hp)) : False := by
  have t1 : 0 < 1 - F.S.tp := by linarith [F.S.tp_lt]
  have s1 : 0 < 1 - F.S.sm := by linarith [F.S.sm_lt]
  have ha : 0 < F.a12 := F.A12_pos
  have key : F.S.km * ((1 - F.S.tp) * ((F.a12 * (F.S.sp * F.S.tp) + F.gg * (F.S.kp * F.S.hp)) -
        (F.a11 * (F.S.tp * F.S.tp) + F.gg * (F.S.hp * F.S.hp))) +
      F.S.tp * (F.a11 * F.S.tp - (F.a11 * (F.S.tp * F.S.tp) + F.gg * (F.S.hp * F.S.hp)))) =
      (1 - F.S.tp) * F.a12 * (F.S.sp * F.S.tp * F.S.km -
        (1 - F.S.sm) * (F.S.hp - F.S.kp * (1 - F.S.tp))) := by
    linear_combination (F.S.hp - (1 - F.S.tp) * F.S.kp) * hO
  have hb : F.S.sp * F.S.tp * F.S.km - (1 - F.S.sm) * (F.S.hp - F.S.kp * (1 - F.S.tp)) < 0 := by
    have h1 := mul_lt_mul_of_pos_left hD F.S.sp_pos
    have h2 := mul_pos s1 (show 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) by
      linarith [F.S.roof_p'])
    nlinarith [h1, h2]
  have h3 : (1 - F.S.tp) * F.a12 * (F.S.sp * F.S.tp * F.S.km -
        (1 - F.S.sm) * (F.S.hp - F.S.kp * (1 - F.S.tp))) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos t1 ha) hb
  have h4 : 0 ≤ F.S.km * ((1 - F.S.tp) * ((F.a12 * (F.S.sp * F.S.tp) + F.gg * (F.S.kp * F.S.hp)) -
        (F.a11 * (F.S.tp * F.S.tp) + F.gg * (F.S.hp * F.S.hp))) +
      F.S.tp * (F.a11 * F.S.tp - (F.a11 * (F.S.tp * F.S.tp) + F.gg * (F.S.hp * F.S.hp)))) :=
    mul_nonneg F.S.km_pos.le (add_nonneg (mul_nonneg t1.le (by linarith))
      (mul_nonneg F.S.tp_pos.le (by linarith)))
  linarith

/-- **I_MA, `D1 < 0`**: leaf `s05:0162[B^C^]`. -/
theorem isRupert_IMA_neg (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hO : (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0)
    (hL : (F.S.km*F.S.tm) * (F.a11 - F.a12) +
      (-F.S.hm*F.S.sm + F.S.hm + F.S.km*F.S.tm - F.S.km) * F.a12 = 0)
    (hD : F.S.tp * F.S.km < F.S.hp * (1 - F.S.sm)) :
    IsRupert (Finset.univ.image x) := by
  set FF := h20s_fac hR with hFF
  have h11 := F.a12_lt_a11 hL
  refine h20s_I_s05 FF hx (F.lit_A_seg FF hD) (F.lit_G_seg FF hD) ?_
  rw [F.x5_sub_x0]
  refine F.robUni_of_dep _ _ (robUni4 ?_ ?_)
  · rintro ⟨a1, a2, a3, a4⟩
    have e0 : h20s_s05.c (0 : ZMod 4) = 0 := rfl
    have e1 : h20s_s05.c (1 : ZMod 4) = 1 := rfl
    have e2 : h20s_s05.c (2 : ZMod 4) = 6 := rfl
    have e3 : h20s_s05.c (3 : ZMod 4) = 2 := rfl
    simp only [e0, e1, e2, e3, dep_0, dep_1, dep_2, dep_6] at a1 a2 a3 a4
    exact F.s05_no_low_d0 hO hD (by nlinarith) (by nlinarith)
  · rintro ⟨a1, a2, a3, a4⟩
    have e0 : h20s_s05.c (0 : ZMod 4) = 0 := rfl
    have e1 : h20s_s05.c (1 : ZMod 4) = 1 := rfl
    have e2 : h20s_s05.c (2 : ZMod 4) = 6 := rfl
    have e3 : h20s_s05.c (3 : ZMod 4) = 2 := rfl
    simp only [e0, e1, e2, e3, dep_0, dep_1, dep_2, dep_6] at a1 a2 a3 a4
    have := mul_pos F.S.tp_pos (sub_pos.2 h11)
    nlinarith

end Frame20
end Minimality.CaseC20
end

section

/-!
# I_MA: the metric item I_MA is Rupert, away from the special position `D1 = 0`
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- **Type 20, item I_MA** (away from `D1 = tp km - hp (1 - sm) = 0`): `D1 < 0` uses the segment
leaf `s05:0162[B^C^]`, `D1 > 0` the line leaf `LCG:01625[CvGv]`. -/
theorem isRupert_IMA (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hO : (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0)
    (hL : (F.S.km*F.S.tm) * (F.a11 - F.a12) +
      (-F.S.hm*F.S.sm + F.S.hm + F.S.km*F.S.tm - F.S.km) * F.a12 = 0)
    (hD : F.S.tp * F.S.km - F.S.hp * (1 - F.S.sm) ≠ 0) :
    IsRupert (Finset.univ.image x) := by
  rcases lt_or_gt_of_ne hD with h | h
  · exact F.isRupert_IMA_neg hx hR hO hL (by linarith)
  · exact F.isRupert_IMA_pos hx hR hO hL (by linarith)

end Frame20
end Minimality.CaseC20
end

section

/-!
# I_MA: the special position `D1 = 0`
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.H20S

/-- Facing pattern of the tilted segment leaf `s05:13526[BvCvG^]`: up `A D G H`, down `B C E F`. -/
def h20s_s05t_pat : Fin 8 → Bool := ![true, false, false, true, false, false, true, true]

/-- Its silhouette cycle `1,3,5,2,6`. -/
def h20s_s05t_c : ZMod 5 → Fin 7 := ![1, 3, 5, 2, 6]

/-- The cycle `1,3,5,2,6` is a silhouette of the pattern. -/
theorem h20s_s05t_cyc : S0xCycOK h20s_S h20s_s05t_c h20s_s05t_pat := by decide

/-- The cycle `1,3,5,2,6` has distinct vertices. -/
theorem h20s_s05t_inj : Function.Injective h20s_s05t_c := by decide

end Minimality.H20S

namespace Minimality.CaseC20
namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x) (FF : S0xFac 8 h20s_S x)

/-- At `D1 = 0` facet `A` still faces up along the segment `x5 - x0` (the strict lower roof suffices). -/
lemma lit_A_seg_le (hD : F.S.tp * F.S.km ≤ F.S.hp * (1 - F.S.sm)) :
    0 < FF.f 0 (x 5) - FF.f 0 (x 0) := by
  obtain ⟨c0, c3, -, -⟩ := F.facet_coords (FF.f 0) (FF.N 0) (FF.hN 0)
  have z1 : FF.f 0 (x 1) = 0 := FF.zero 0 1 (by decide)
  have z3 : FF.f 0 (x 3) = 0 := FF.zero 0 3 (by decide)
  have n5 : FF.f 0 (x 5) < 0 := FF.neg 0 5 (by decide)
  have h1 := mul_lt_mul_of_pos_left F.S.roof_m' F.S.tp_pos
  have h2 := mul_le_mul_of_nonneg_right hD (show 0 ≤ 1 - F.S.tm by linarith [F.S.tm_lt])
  have hm := F.S.hm_pos
  rw [z1] at c0 c3
  rw [z3] at c3
  have key : F.S.hm * (FF.f 0 (x 0) - FF.f 0 (x 5)) =
      -FF.f 0 (x 5) * (F.S.tp * F.S.hm - F.S.hp * (1 - F.S.tm)) := by
    linear_combination F.S.hm * c0 + F.S.hp * c3
  have hs : 0 < 1 - F.S.sm := by linarith [F.S.sm_lt]
  have hQ : F.S.tp * F.S.hm - F.S.hp * (1 - F.S.tm) < 0 := by
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg hs.le hc]
  have h5 : -FF.f 0 (x 5) * (F.S.tp * F.S.hm - F.S.hp * (1 - F.S.tm)) < 0 :=
    mul_neg_of_pos_of_neg (by linarith) hQ
  by_contra hc
  push Not at hc
  nlinarith [mul_nonneg hm.le (show 0 ≤ FF.f 0 (x 0) - FF.f 0 (x 5) by linarith)]

/-- At `D1 = 0`, facet `G` is edge-on at the segment view: its values at `x0` and `x5` agree. -/
lemma G_edge_on (hD : F.S.tp * F.S.km = F.S.hp * (1 - F.S.sm)) :
    FF.f 6 (x 5) - FF.f 6 (x 0) = 0 := by
  obtain ⟨c0, -, -, c4⟩ := F.facet_coords (FF.f 6) (FF.N 6) (FF.hN 6)
  have z1 : FF.f 6 (x 1) = 0 := FF.zero 6 1 (by decide)
  have z4 : FF.f 6 (x 4) = 0 := FF.zero 6 4 (by decide)
  have z6 : FF.f 6 (x 6) = 0 := FF.zero 6 6 (by decide)
  rw [z1] at c0
  rw [z4, z6] at c4
  have key : F.S.km * (FF.f 6 (x 0) - FF.f 6 (x 5)) =
      -FF.f 6 (x 5) * (F.S.tp * F.S.km - F.S.hp * (1 - F.S.sm)) := by
    linear_combination F.S.km * c0 + F.S.hp * c4
  rw [hD, sub_self, mul_zero] at key
  have := (mul_eq_zero.1 key).resolve_left F.S.km_pos.ne'
  linarith

/-- The tilt `v = (x1 - x5) + (x6 - x5)`: it points into `B`, `C` (negative) and out of `G` (positive). -/
lemma tilt_B : ⟪FF.N 1, F.toFrame7.fvC ⟨1, 1, 0⟩⟫ < 0 := by
  rw [F.facet_val FF]
  have a1 : FF.f 1 (x 1) < 0 := FF.neg 1 1 (by decide)
  have a6 : FF.f 1 (x 6) < 0 := FF.neg 1 6 (by decide)
  have a5 : FF.f 1 (x 5) = 0 := FF.zero 1 5 (by decide)
  simp only [one_mul, zero_mul, add_zero]; linarith

lemma tilt_C : ⟪FF.N 2, F.toFrame7.fvC ⟨1, 1, 0⟩⟫ < 0 := by
  rw [F.facet_val FF]
  have a1 : FF.f 2 (x 1) = 0 := FF.zero 2 1 (by decide)
  have a6 : FF.f 2 (x 6) < 0 := FF.neg 2 6 (by decide)
  have a5 : FF.f 2 (x 5) = 0 := FF.zero 2 5 (by decide)
  simp only [one_mul, zero_mul, add_zero]; linarith

lemma tilt_G : 0 < ⟪FF.N 6, F.toFrame7.fvC ⟨1, 1, 0⟩⟫ := by
  rw [F.facet_val FF]
  have a1 : FF.f 6 (x 1) = 0 := FF.zero 6 1 (by decide)
  have a6 : FF.f 6 (x 6) = 0 := FF.zero 6 6 (by decide)
  have a5 : FF.f 6 (x 5) < 0 := FF.neg 6 5 (by decide)
  simp only [one_mul, zero_mul, add_zero]; linarith

/-- The lex facings of all eight facets at `(x5 - x0, v)` follow the pattern `A D G H` up, `B C E F` down,
when `D1 = 0`. -/
lemma s05t_fac (hD : F.S.tp * F.S.km = F.S.hp * (1 - F.S.sm)) :
    S0xFacOK FF h20s_s05t_pat (x 5 - x 0) (F.toFrame7.fvC ⟨1, 1, 0⟩) := by
  intro t
  have hu : ∀ t, ⟪FF.N t, x 5 - x 0⟫ = FF.f t (x 5) - FF.f t (x 0) := fun t => FF.inner_sub t 5 0
  have ht : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 := by
    revert t; decide
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- A
    have := F.lit_A_seg_le FF hD.le
    refine ⟨fun _ => Or.inl (by rw [hu]; exact this), fun h => absurd h (by decide)⟩
  · -- B
    have e5 : FF.f 1 (x 5) = 0 := FF.zero 1 5 (by decide)
    have e0 : FF.f 1 (x 0) = 0 := FF.zero 1 0 (by decide)
    have h0 : ⟪FF.N 1, x 5 - x 0⟫ = 0 := by rw [hu, e5, e0]; ring
    refine ⟨fun h => absurd h (by decide), fun _ => Or.inr ⟨by rw [h0]; ring, ?_⟩⟩
    linarith [F.tilt_B FF]
  · -- C
    have e5 : FF.f 2 (x 5) = 0 := FF.zero 2 5 (by decide)
    have e0 : FF.f 2 (x 0) = 0 := FF.zero 2 0 (by decide)
    have h0 : ⟪FF.N 2, x 5 - x 0⟫ = 0 := by rw [hu, e5, e0]; ring
    refine ⟨fun h => absurd h (by decide), fun _ => Or.inr ⟨by rw [h0]; ring, ?_⟩⟩
    linarith [F.tilt_C FF]
  · -- D
    have e5 : FF.f 3 (x 5) = 0 := FF.zero 3 5 (by decide)
    have e0 : FF.f 3 (x 0) < 0 := FF.neg 3 0 (by decide)
    exact ⟨fun _ => Or.inl (by rw [hu, e5]; linarith), fun h => absurd h (by decide)⟩
  · -- E
    have e0 : FF.f 4 (x 0) = 0 := FF.zero 4 0 (by decide)
    have e5 : FF.f 4 (x 5) < 0 := FF.neg 4 5 (by decide)
    exact ⟨fun h => absurd h (by decide), fun _ => Or.inl (by rw [hu, e0]; linarith)⟩
  · -- F
    have e0 : FF.f 5 (x 0) = 0 := FF.zero 5 0 (by decide)
    have e5 : FF.f 5 (x 5) < 0 := FF.neg 5 5 (by decide)
    exact ⟨fun h => absurd h (by decide), fun _ => Or.inl (by rw [hu, e0]; linarith)⟩
  · -- G
    have h0 : ⟪FF.N 6, x 5 - x 0⟫ = 0 := by rw [hu]; exact F.G_edge_on FF hD
    exact ⟨fun _ => Or.inr ⟨h0, F.tilt_G FF⟩, fun h => absurd h (by decide)⟩
  · -- H
    have e5 : FF.f 7 (x 5) = 0 := FF.zero 7 5 (by decide)
    have e0 : FF.f 7 (x 0) < 0 := FF.neg 7 0 (by decide)
    exact ⟨fun _ => Or.inl (by rw [hu, e5]; linarith), fun h => absurd h (by decide)⟩

end Frame20
end Minimality.CaseC20
end

section

/-!
# I_MA: `D1 = 0` assembled, and `isRupert_IMA` for every shape on the I_MA locus
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- At `D1 = 0` the depths along `x5 - x0` of the cycle `1,3,5,2,6` are robustly unimodal: with
`z_j` the depth along `x0 - x5`, `z5 = 0 < z2 < z6 < z1` and `z3 < z1`. -/
lemma s05t_robUni
    (hO : (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0)
    (hL : (F.S.km*F.S.tm) * (F.a11 - F.a12) +
      (-F.S.hm*F.S.sm + F.S.hm + F.S.km*F.S.tm - F.S.km) * F.a12 = 0)
    (hD : F.S.tp * F.S.km = F.S.hp * (1 - F.S.sm)) :
    RobUni (fun a : ZMod 5 => ⟪x (h20s_s05t_c a), x 5 - x 0⟫) := by
  have h11 := F.a12_lt_a11 hL
  have ha : 0 < F.a12 := F.A12_pos
  have hg := F.g_pos
  have t1 : 0 < 1 - F.S.tp := by linarith [F.S.tp_lt]
  have := F.S.tp_pos; have := F.S.sp_pos; have := F.S.kp_pos; have := F.S.km_pos
  have := F.S.hp_pos; have := F.S.hm_pos; have := F.S.tm_pos; have := F.S.tm_lt
  have hkh : 0 < F.S.km * F.S.hp := mul_pos F.S.km_pos F.S.hp_pos
  -- z6 - z2 > 0
  have key : F.S.km * F.S.hp * (F.a12 * F.S.tp - (F.a12 * (F.S.sp * F.S.tp) + F.gg * (F.S.kp * F.S.hp))) =
      F.a12 * F.S.tp * F.S.km * (F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp)) := by
    linear_combination (F.S.kp * F.S.hp) * hO + (F.a12 * F.S.kp * (1 - F.S.tp)) * hD
  have h62 : 0 < F.a12 * F.S.tp - (F.a12 * (F.S.sp * F.S.tp) + F.gg * (F.S.kp * F.S.hp)) := by
    have h5 : 0 < F.a12 * F.S.tp * F.S.km * (F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp)) :=
      mul_pos (mul_pos (mul_pos ha F.S.tp_pos) F.S.km_pos) (by linarith [F.S.roof_p'])
    exact pos_of_mul_pos_right (key ▸ h5) hkh.le
  have h20 : 0 < F.a12 * (F.S.sp * F.S.tp) + F.gg * (F.S.kp * F.S.hp) := by positivity
  have h16 : 0 < F.a11 * F.S.tp - F.a12 * F.S.tp := by nlinarith
  have h31 : 0 < F.a11 * F.S.tp - (F.a11 * (F.S.tm * F.S.tp) - F.gg * (F.S.hm * F.S.hp)) := by
    have : 0 < F.a11 := by linarith
    nlinarith [mul_pos hg (mul_pos F.S.hm_pos F.S.hp_pos), mul_pos (mul_pos this F.S.tp_pos) (show 0 < 1 - F.S.tm by linarith)]
  have e0 : h20s_s05t_c (0 : ZMod 5) = 1 := rfl
  have e1 : h20s_s05t_c (1 : ZMod 5) = 3 := rfl
  have e2 : h20s_s05t_c (2 : ZMod 5) = 5 := rfl
  have e3 : h20s_s05t_c (3 : ZMod 5) = 2 := rfl
  have e4 : h20s_s05t_c (4 : ZMod 5) = 6 := rfl
  rw [F.x5_sub_x0]
  refine F.robUni_of_dep _ _ (robUni5_c ?_ ?_ ?_ ?_)
  · show F.dep _ (h20s_s05t_c 0) < F.dep _ (h20s_s05t_c 4)
    rw [e0, e4]; simp only [dep_1, dep_6]; nlinarith
  · show F.dep _ (h20s_s05t_c 4) < F.dep _ (h20s_s05t_c 3)
    rw [e4, e3]; simp only [dep_6, dep_2]; nlinarith
  · show F.dep _ (h20s_s05t_c 3) < F.dep _ (h20s_s05t_c 2)
    rw [e3, e2]; simp only [dep_2, dep_5]; nlinarith
  · show F.dep _ (h20s_s05t_c 0) < F.dep _ (h20s_s05t_c 1)
    rw [e0, e1]; simp only [dep_1, dep_3]; nlinarith

/-- **I_MA at the special position `D1 = 0`**: the tilted segment leaf `s05:13526[BvCvG^]`. -/
theorem isRupert_IMA_zero (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hO : (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0)
    (hL : (F.S.km*F.S.tm) * (F.a11 - F.a12) +
      (-F.S.hm*F.S.sm + F.S.hm + F.S.km*F.S.tm - F.S.km) * F.a12 = 0)
    (hD : F.S.tp * F.S.km = F.S.hp * (1 - F.S.sm)) :
    IsRupert (Finset.univ.image x) := by
  set FF := h20s_fac hR with hFF
  exact s0x_seg_rupert_tilt FF hx (i := 0) (j := 5) (c := h20s_s05t_c) (pat := h20s_s05t_pat)
    (by decide) (by norm_num) h20s_s05t_inj h20s_s05t_cyc (F.toFrame7.fvC ⟨1, 1, 0⟩)
    (F.s05t_fac FF hD) (F.s05t_robUni hO hL hD)

/-- **Type 20, item I_MA, all shapes on the locus** (no hypothesis on `D1`). -/
theorem isRupert_IMA_all (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hO : (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0)
    (hL : (F.S.km*F.S.tm) * (F.a11 - F.a12) +
      (-F.S.hm*F.S.sm + F.S.hm + F.S.km*F.S.tm - F.S.km) * F.a12 = 0) :
    IsRupert (Finset.univ.image x) := by
  by_cases hD : F.S.tp * F.S.km - F.S.hp * (1 - F.S.sm) = 0
  · exact F.isRupert_IMA_zero hx hR hO hL (by linarith)
  · exact F.isRupert_IMA hx hR hO hL hD

end Frame20
end Minimality.CaseC20
end

section
open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace
namespace Minimality.CaseC20
namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- **The `R`-image of I_MA**: the metric item with the same first equation and second equation
`hp sp (a22 - a12) + (hp sp - hp - kp tp + kp) a12 = 0` is Rupert, by `isRupert_IMA_all` for the frame
of `x ∘ R`. -/
theorem isRupert_IMA_R (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 19))
    (hO : (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0)
    (hL : (F.S.hp*F.S.sp) * (F.a22 - F.a12) +
      (F.S.hp*F.S.sp - F.S.hp - F.S.kp*F.S.tp + F.S.kp) * F.a12 = 0) :
    IsRupert (Finset.univ.image x) := by
  have h12 : F.rFrame.a12 = F.a12 := by
    show ⟪x (rperm 1) - x (rperm 5), x (rperm 6) - x (rperm 5)⟫ = _
    show ⟪x 6 - x 5, x 1 - x 5⟫ = _
    exact real_inner_comm _ _
  have hg : F.rFrame.gg = F.gg := by
    show ⟪-F.e, -F.e⟫ = ⟪F.e, F.e⟫
    simp
  have h11 : F.rFrame.a11 = F.a22 := rfl
  have h22 : F.rFrame.a22 = F.a11 := rfl
  refine rupert_of_r (F.rFrame.isRupert_IMA_all (hx.comp rperm_bijective.1) (realizesFaces_rperm hR)
    ?_ ?_)
  · simp only [rFrame_S, Shape20.swap, h12, hg]; linear_combination hO
  · simp only [rFrame_S, Shape20.swap, h12, h11]; linear_combination hL

end Frame20
end Minimality.CaseC20
end


namespace Minimality.CaseC20
open Minimality.CaseC09 Minimality.CaseC18

/-- The special positions left after I_MA: `CaseC20Special''` without its I_MA disjuncts (the metric
item with first equation `(sm tp - sm - tp + 1) a12 - hp km gg = 0` and second equation either
`km tm (a11 - a12) + ... = 0` or its `R`-image with `a22`; the duplicates among the disjuncts
are removed too).  These disjuncts are Rupert by `isRupert_IMA_all` and `isRupert_IMA_R`. -/
def CaseC20Rest (x : Fin 7 → ℝ³) : Prop :=
  ∃ F : Frame20 x,
    (F.a12 = F.a11 ∧ F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm = 0 ∧
      0 < (1 - F.S.tp)*(1 - F.S.tm)*F.a12 - F.gg*F.S.hp*F.S.hm ∧
      (1 - F.S.tp)*(1 - F.S.tm)*F.a12 - F.gg*F.S.hp*F.S.hm ≤
        (1 - F.S.tp)*(1 - F.S.sm)*F.a12 - F.gg*F.S.hp*F.S.km) ∨
    (F.a12 = F.a22 ∧ F.S.kp*F.S.sm - F.S.kp + F.S.km*F.S.sp = 0 ∧
      0 < (1 - F.S.sm)*(1 - F.S.sp)*F.a12 - F.gg*F.S.km*F.S.kp ∧
      (1 - F.S.sm)*(1 - F.S.sp)*F.a12 - F.gg*F.S.km*F.S.kp ≤
        (1 - F.S.sm)*(1 - F.S.tp)*F.a12 - F.gg*F.S.km*F.S.hp) ∨
    (-F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm = 0) ∨
    (-F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm = 0) ∨
    (F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm = 0) ∨
    (F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp = 0) ∨
    ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg = 0) ∨
    ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg = 0) ∨
    ((-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg = 0 ∧ (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * (F.a22 - F.a12) + (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * F.a12 + (-F.S.km*F.S.kp) * F.gg = 0) ∨
    ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg = 0) ∨
    ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg = 0) ∨
    (F.S.hm*F.S.sp - F.S.hm + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp - F.S.km*F.S.tm + F.S.km + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm = 0) ∨
    ((-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg = 0 ∧ (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * (F.a22 - F.a12) + (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * F.a12 + (-F.S.km*F.S.kp) * F.gg = 0) ∨
    (F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.sp - F.S.hp*F.S.tm + F.S.hp + F.S.kp*F.S.tm - F.S.kp = 0)

/-- `CaseC20Special''` reduces to Rupert or `CaseC20Rest`: the I_MA disjuncts are Rupert
(`isRupert_IMA_all`, `isRupert_IMA_R`), the others are kept. -/
theorem caseC20Special''_reduce {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (hR : RealizesFaces x (sevenTypeFaces 19)) (h : CaseC20Special'' x) :
    IsRupert (Finset.univ.image x) ∨ CaseC20Rest x := by
  obtain ⟨F, h⟩ := h
  by_cases hA : (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0 ∧
      (F.S.km*F.S.tm) * (F.a11 - F.a12) + (-F.S.hm*F.S.sm + F.S.hm + F.S.km*F.S.tm - F.S.km) * F.a12 = 0
  · exact Or.inl (F.isRupert_IMA_all hx hR hA.1 hA.2)
  by_cases hB : (F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0 ∧
      (F.S.hp*F.S.sp) * (F.a22 - F.a12) + (F.S.hp*F.S.sp - F.S.hp - F.S.kp*F.S.tp + F.S.kp) * F.a12 = 0
  · exact Or.inl (F.isRupert_IMA_R hx hR hB.1 hB.2)
  right
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    first
    | exact absurd h hA
    | exact absurd h hB
    | exact ⟨F, Or.inl h⟩
    | exact ⟨F, Or.inr (Or.inl h)⟩
    | exact ⟨F, Or.inr (Or.inr (Or.inl h))⟩
    | exact ⟨F, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩
    | exact ⟨F, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩
    | exact ⟨F, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))⟩
    | exact ⟨F, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))⟩
    | exact ⟨F, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))⟩
    | exact ⟨F, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))⟩
    | exact ⟨F, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))⟩
    | exact ⟨F, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))⟩
    | exact ⟨F, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))⟩
    | exact ⟨F, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))⟩
    | exact ⟨F, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h)))))))))))))⟩

end Minimality.CaseC20
