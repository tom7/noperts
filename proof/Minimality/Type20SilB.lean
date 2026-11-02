module

public import Minimality.Type20SilA

@[expose] public section


/-!
# H20S-B: the metric-item leaves with explicit facing literals

Each leaf: facet family `F` of type 20 (e.g. `h20s_fac hR`), injectivity, the strict facings of the
free facets (segment view `x j - x i`: `f_t(x j) - f_t(x i)` for the facets through neither endpoint;
line view `u = N_X × N_Y`: `⟪N_t, u⟫` for `t ≠ X, Y`) and `RobUni` of the depths along the cycle.
Line cells come in two orientations (`…'` = complemented pattern, same depths).
-/

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace H20S
open Minimality.H21

/-- Discharges the literal part of `S0xSeg.Cond` / `S0xLin.Cond` from named hypotheses. -/
macro "h20s_lits" : tactic => `(tactic| (intro t h0 h1; fin_cases t <;> first
  | exact absurd h0 (by decide)
  | exact absurd h1 (by decide)
  | exact ⟨fun _ => by assumption, fun h => absurd h (by decide)⟩
  | exact ⟨fun h => absurd h (by decide), fun _ => by assumption⟩))

variable {x : Fin 7 → ℝ³}

/-! ### I_MA -/

/-- I_MA, `LCG:01625[CvGv]`: up `B E F`, down `A D H`. -/
theorem h20s_I_LCG (F : S0xFac 8 h20s_S x) (hx : Function.Injective x)
    (hA : ⟪F.N 0, cross (F.N 2) (F.N 6)⟫ < 0) (hB : 0 < ⟪F.N 1, cross (F.N 2) (F.N 6)⟫)
    (hD : ⟪F.N 3, cross (F.N 2) (F.N 6)⟫ < 0) (hE : 0 < ⟪F.N 4, cross (F.N 2) (F.N 6)⟫)
    (hF : 0 < ⟪F.N 5, cross (F.N 2) (F.N 6)⟫) (hH : ⟪F.N 7, cross (F.N 2) (F.N 6)⟫ < 0)
    (hU : RobUni (fun a : ZMod 5 => ⟪x (h20s_LCG.c a), cross (F.N 2) (F.N 6)⟫)) :
    IsRupert (univ.image x) :=
  s0x_lin_rupert F hx h20s_LCG h20s_LCG_good ⟨by h20s_lits, hU⟩

/-- I_MA, `LCG` at the opposite orientation: up `A D H`, down `B E F`. -/
theorem h20s_I_LCG' (F : S0xFac 8 h20s_S x) (hx : Function.Injective x)
    (hA : 0 < ⟪F.N 0, cross (F.N 2) (F.N 6)⟫) (hB : ⟪F.N 1, cross (F.N 2) (F.N 6)⟫ < 0)
    (hD : 0 < ⟪F.N 3, cross (F.N 2) (F.N 6)⟫) (hE : ⟪F.N 4, cross (F.N 2) (F.N 6)⟫ < 0)
    (hF : ⟪F.N 5, cross (F.N 2) (F.N 6)⟫ < 0) (hH : 0 < ⟪F.N 7, cross (F.N 2) (F.N 6)⟫)
    (hU : RobUni (fun a : ZMod 5 => ⟪x (h20s_LCG.c a), cross (F.N 2) (F.N 6)⟫)) :
    IsRupert (univ.image x) :=
  s0x_lin_rupert F hx h20s_LCG' h20s_LCG'_good ⟨by h20s_lits, hU⟩

/-- I_MA, `s05:0162[B^C^]`: literals `A+ G+`. -/
theorem h20s_I_s05 (F : S0xFac 8 h20s_S x) (hx : Function.Injective x)
    (hA : 0 < F.f 0 (x 5) - F.f 0 (x 0)) (hG : 0 < F.f 6 (x 5) - F.f 6 (x 0))
    (hU : RobUni (fun a : ZMod 4 => ⟪x (h20s_s05.c a), x 5 - x 0⟫)) :
    IsRupert (univ.image x) :=
  s0x_seg_rupert F hx h20s_s05 h20s_s05_good ⟨by h20s_lits, hU⟩

/-! ### I_MC -/

/-- I_MC, `s01:0546[C^E^]`: literals `D+ H-`. -/
theorem h20s_I_s01 (F : S0xFac 8 h20s_S x) (hx : Function.Injective x)
    (hD : 0 < F.f 3 (x 1) - F.f 3 (x 0)) (hH : F.f 7 (x 1) - F.f 7 (x 0) < 0)
    (hU : RobUni (fun a : ZMod 4 => ⟪x (h20s_s01.c a), x 1 - x 0⟫)) :
    IsRupert (univ.image x) :=
  s0x_seg_rupert F hx h20s_s01 h20s_s01_good ⟨by h20s_lits, hU⟩

/-- I_MC, `s35:1346[C^D^]`: literals `E+ F+ G-`. -/
theorem h20s_I_s35 (F : S0xFac 8 h20s_S x) (hx : Function.Injective x)
    (hE : 0 < F.f 4 (x 5) - F.f 4 (x 3)) (hF : 0 < F.f 5 (x 5) - F.f 5 (x 3))
    (hG : F.f 6 (x 5) - F.f 6 (x 3) < 0)
    (hU : RobUni (fun a : ZMod 4 => ⟪x (h20s_s35.c a), x 5 - x 3⟫)) :
    IsRupert (univ.image x) :=
  s0x_seg_rupert F hx h20s_s35 h20s_s35_good ⟨by h20s_lits, hU⟩

/-- I_MC, `LCF:01346[C^F^]`: up `B D H`, down `A E G`. -/
theorem h20s_I_LCF (F : S0xFac 8 h20s_S x) (hx : Function.Injective x)
    (hA : ⟪F.N 0, cross (F.N 2) (F.N 5)⟫ < 0) (hB : 0 < ⟪F.N 1, cross (F.N 2) (F.N 5)⟫)
    (hD : 0 < ⟪F.N 3, cross (F.N 2) (F.N 5)⟫) (hE : ⟪F.N 4, cross (F.N 2) (F.N 5)⟫ < 0)
    (hG : ⟪F.N 6, cross (F.N 2) (F.N 5)⟫ < 0) (hH : 0 < ⟪F.N 7, cross (F.N 2) (F.N 5)⟫)
    (hU : RobUni (fun a : ZMod 5 => ⟪x (h20s_LCF.c a), cross (F.N 2) (F.N 5)⟫)) :
    IsRupert (univ.image x) :=
  s0x_lin_rupert F hx h20s_LCF h20s_LCF_good ⟨by h20s_lits, hU⟩

theorem h20s_I_LCF' (F : S0xFac 8 h20s_S x) (hx : Function.Injective x)
    (hA : 0 < ⟪F.N 0, cross (F.N 2) (F.N 5)⟫) (hB : ⟪F.N 1, cross (F.N 2) (F.N 5)⟫ < 0)
    (hD : ⟪F.N 3, cross (F.N 2) (F.N 5)⟫ < 0) (hE : 0 < ⟪F.N 4, cross (F.N 2) (F.N 5)⟫)
    (hG : 0 < ⟪F.N 6, cross (F.N 2) (F.N 5)⟫) (hH : ⟪F.N 7, cross (F.N 2) (F.N 5)⟫ < 0)
    (hU : RobUni (fun a : ZMod 5 => ⟪x (h20s_LCF.c a), cross (F.N 2) (F.N 5)⟫)) :
    IsRupert (univ.image x) :=
  s0x_lin_rupert F hx h20s_LCF' h20s_LCF'_good ⟨by h20s_lits, hU⟩

/-- I_MC, `LBD:2546[B^D^]`: up `A C E F G`, down `H` (the silhouette is the boundary of `H`). -/
theorem h20s_I_LBD (F : S0xFac 8 h20s_S x) (hx : Function.Injective x)
    (hA : 0 < ⟪F.N 0, cross (F.N 1) (F.N 3)⟫) (hC : 0 < ⟪F.N 2, cross (F.N 1) (F.N 3)⟫)
    (hE : 0 < ⟪F.N 4, cross (F.N 1) (F.N 3)⟫) (hF : 0 < ⟪F.N 5, cross (F.N 1) (F.N 3)⟫)
    (hG : 0 < ⟪F.N 6, cross (F.N 1) (F.N 3)⟫) (hH : ⟪F.N 7, cross (F.N 1) (F.N 3)⟫ < 0)
    (hU : RobUni (fun a : ZMod 4 => ⟪x (h20s_LBD.c a), cross (F.N 1) (F.N 3)⟫)) :
    IsRupert (univ.image x) :=
  s0x_lin_rupert F hx h20s_LBD h20s_LBD_good ⟨by h20s_lits, hU⟩

theorem h20s_I_LBD' (F : S0xFac 8 h20s_S x) (hx : Function.Injective x)
    (hA : ⟪F.N 0, cross (F.N 1) (F.N 3)⟫ < 0) (hC : ⟪F.N 2, cross (F.N 1) (F.N 3)⟫ < 0)
    (hE : ⟪F.N 4, cross (F.N 1) (F.N 3)⟫ < 0) (hF : ⟪F.N 5, cross (F.N 1) (F.N 3)⟫ < 0)
    (hG : ⟪F.N 6, cross (F.N 1) (F.N 3)⟫ < 0) (hH : 0 < ⟪F.N 7, cross (F.N 1) (F.N 3)⟫)
    (hU : RobUni (fun a : ZMod 4 => ⟪x (h20s_LBD.c a), cross (F.N 1) (F.N 3)⟫)) :
    IsRupert (univ.image x) :=
  s0x_lin_rupert F hx h20s_LBD' h20s_LBD'_good ⟨by h20s_lits, hU⟩

/-- I_MC, `LAF:01352[AvFv]`: up `B C`, down `D E G H`. -/
theorem h20s_I_LAF (F : S0xFac 8 h20s_S x) (hx : Function.Injective x)
    (hB : 0 < ⟪F.N 1, cross (F.N 0) (F.N 5)⟫) (hC : 0 < ⟪F.N 2, cross (F.N 0) (F.N 5)⟫)
    (hD : ⟪F.N 3, cross (F.N 0) (F.N 5)⟫ < 0) (hE : ⟪F.N 4, cross (F.N 0) (F.N 5)⟫ < 0)
    (hG : ⟪F.N 6, cross (F.N 0) (F.N 5)⟫ < 0) (hH : ⟪F.N 7, cross (F.N 0) (F.N 5)⟫ < 0)
    (hU : RobUni (fun a : ZMod 5 => ⟪x (h20s_LAF.c a), cross (F.N 0) (F.N 5)⟫)) :
    IsRupert (univ.image x) :=
  s0x_lin_rupert F hx h20s_LAF h20s_LAF_good ⟨by h20s_lits, hU⟩

theorem h20s_I_LAF' (F : S0xFac 8 h20s_S x) (hx : Function.Injective x)
    (hB : ⟪F.N 1, cross (F.N 0) (F.N 5)⟫ < 0) (hC : ⟪F.N 2, cross (F.N 0) (F.N 5)⟫ < 0)
    (hD : 0 < ⟪F.N 3, cross (F.N 0) (F.N 5)⟫) (hE : 0 < ⟪F.N 4, cross (F.N 0) (F.N 5)⟫)
    (hG : 0 < ⟪F.N 6, cross (F.N 0) (F.N 5)⟫) (hH : 0 < ⟪F.N 7, cross (F.N 0) (F.N 5)⟫)
    (hU : RobUni (fun a : ZMod 5 => ⟪x (h20s_LAF.c a), cross (F.N 0) (F.N 5)⟫)) :
    IsRupert (univ.image x) :=
  s0x_lin_rupert F hx h20s_LAF' h20s_LAF'_good ⟨by h20s_lits, hU⟩

end H20S
end Minimality
