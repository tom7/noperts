module

public import Mathlib
public import Minimality.DiagCross
public import Minimality.RimCell
public import Minimality.Slide
public import Minimality.UnimodalCert
public import Minimality.FaceChordFac
public import Minimality.Q45Signs
public import Minimality.Q45Orient
public import Minimality.CornerU
public import Minimality.Q45Leaf
public import Minimality.RimFromSigns

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped RealInnerProductSpace Topology
open Filter Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.T24.RimFromSigns

namespace Minimality.T24.Q45

/-- Rewrite lemma for rim 6452 (DiagCross kappa convention):
`κ(6, 4, 5, 2) = - det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6)`.
The RHS is `kJ` in Q45THEOREM24. -/
theorem kappa_rim6452 (x : Fin 7 → ℝ³) :
    det3 (quad (x 6) (x 4) (x 5) (x 2) 2 - quad (x 6) (x 4) (x 5) (x 2) 0)
         (quad (x 6) (x 4) (x 5) (x 2) 3 - quad (x 6) (x 4) (x 5) (x 2) 1)
         (quad (x 6) (x 4) (x 5) (x 2) 0 - quad (x 6) (x 4) (x 5) (x 2) 1) =
      - det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) := by
  change det3 (x 5 - x 6) (x 2 - x 4) (x 6 - x 4) = - det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6)
  simp only [det3_expand, PiLp.sub_apply]
  ring

/-- **Leaf K0 (kJ = 0, Planar Rim 6452)**:
When `kJ = -det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) = 0`, the DiagCross orientation
`κ(6, 4, 5, 2)` vanishes identically. By `diagCross_zero`, neither strict alternation
can occur at any view on `J0`. With distinct rim depths, the quad is strictly unimodal.
- View: interior view along open arc `J0`.
- Rim: 6 4 5 2 (ridges 4-6, 5-2, 2-6, edge-on chord 4-5).
- Chord: 4 -> 5. Middles: 0, 3. Farther: w ∈ {2, 6}.
- Hypotheses:
  * `ha4`, `ha5`: corner-frame coordinate conditions `a4 > 1` and `a5 > 1`.
  * `hs0`, `ht`, `hst`, `hdecomp`: Lemma M decomposition of vertex 3 on facet 3.
  * `hk0`: case condition `kJ = 0`, i.e. `det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) = 0`.
  * `hS2`: persistent tie exclusion (rim depths do not vanish identically on Pi).
  * `hS3`: farther vertex tie exclusion (`F.f 3 (x 2) ≠ F.f 3 (x 6)`).
  * `hS4`: chord 4-5 exclusion (foot of farther vertex off open segment (4, 5)). -/
theorem q45_K0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha4 : ⟪F.N 5, x 4 - x 0⟫ < 0)
    (ha5 : ⟪F.N 5, x 5 - x 0⟫ < 0)
    (s t : ℝ)
    (hs0 : 0 < s)
    (ht : 0 < t)
    (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hk0 : det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) = 0)
    (hS2 : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0)
    (hS3 : F.f 3 (x 2) ≠ F.f 3 (x 6))
    (hS4 : ⟪F.N 3, cross (x 5 - x 4) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4)⟫ ≠ 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 5 - x 4⟫ < 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 4 - x 5⟫ < 0) :
    FaceChordView F 3 := by
  sorry

/-- **Leaf K+ (Subcase s ≤ 1, E5 = e5)**:
When `ρ0 * kJ > 0` and weak 6-high fails strictly at base `e5 = x 5 - x 0`.
- Views: `u_ε = e5 + ε • e4` in `J0` for small `ε > 0`.
- Rim: 6 4 5 2, chord 4 -> 5, middles 0, 3, farther w ∈ {2, 6}.
- Lemma K rules out 2-high everywhere on `J0`.
- Open condition `h6lo` rules out 6-high near `e5`. -/
theorem q45_Kplus_s_le_one {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha4 : ⟪F.N 5, x 4 - x 0⟫ < 0)
    (ha5 : ⟪F.N 5, x 5 - x 0⟫ < 0)
    (s t : ℝ)
    (hs0 : 0 < s)
    (ht : 0 < t)
    (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hk : det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) < 0)
    (hs : s ≤ 1)
    (h6lo : min ⟪x 6, x 5 - x 0⟫ ⟪x 5, x 5 - x 0⟫ < max ⟪x 4, x 5 - x 0⟫ ⟪x 2, x 5 - x 0⟫)
    (hS2 : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0)
    (hS3 : F.f 3 (x 2) ≠ F.f 3 (x 6))
    (hS4 : ⟪F.N 3, cross (x 5 - x 4) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4)⟫ ≠ 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 5 - x 4⟫ < 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 4 - x 5⟫ < 0) :
    FaceChordView F 3 := by
  sorry

/-- **Leaf K+ (Subcase 1 < s, E5 = e34)**:
When `ρ0 * kJ > 0` and weak 6-high fails strictly at base `e34 = x 3 - x 4`.
- Views: `u_ε = (x 3 - x 4) + ε • (x 4 - x 0)` in `J0` for small `ε > 0`.
- Rim: 6 4 5 2, chord 4 -> 5, middles 0, 3, farther w ∈ {2, 6}.
- Lemma K rules out 2-high everywhere on `J0`.
- Open condition `h6lo` rules out 6-high near `e34`. -/
theorem q45_Kplus_s_gt_one {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha4 : ⟪F.N 5, x 4 - x 0⟫ < 0)
    (ha5 : ⟪F.N 5, x 5 - x 0⟫ < 0)
    (s t : ℝ)
    (hs0 : 0 < s)
    (ht : 0 < t)
    (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hk : det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) < 0)
    (hs : 1 < s)
    (h6lo : min ⟪x 6, x 3 - x 4⟫ ⟪x 5, x 3 - x 4⟫ < max ⟪x 4, x 3 - x 4⟫ ⟪x 2, x 3 - x 4⟫)
    (hS2 : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 3 - x 4⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0)
    (hS3 : F.f 3 (x 2) ≠ F.f 3 (x 6))
    (hS4 : ⟪F.N 3, cross (x 5 - x 4) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4)⟫ ≠ 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 5 - x 4⟫ < 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 4 - x 5⟫ < 0) :
    FaceChordView F 3 := by
  sorry

/-- **Leaf K+ (Unified Dispatcher Form)**:
Dispatches between `s ≤ 1` (`E5 = e5`) and `1 < s` (`E5 = e34`). -/
theorem q45_Kplus {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha4 : ⟪F.N 5, x 4 - x 0⟫ < 0)
    (ha5 : ⟪F.N 5, x 5 - x 0⟫ < 0)
    (s t : ℝ)
    (hs0 : 0 < s)
    (ht : 0 < t)
    (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hk : det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) < 0)
    (hE5 : (s ≤ 1 ∧ min ⟪x 6, x 5 - x 0⟫ ⟪x 5, x 5 - x 0⟫ < max ⟪x 4, x 5 - x 0⟫ ⟪x 2, x 5 - x 0⟫) ∨
           (1 < s ∧ min ⟪x 6, x 3 - x 4⟫ ⟪x 5, x 3 - x 4⟫ < max ⟪x 4, x 3 - x 4⟫ ⟪x 2, x 3 - x 4⟫))
    (hS2_e5 : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0)
    (hS2_e34 : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 3 - x 4⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0)
    (hS3 : F.f 3 (x 2) ≠ F.f 3 (x 6))
    (hS4 : ⟪F.N 3, cross (x 5 - x 4) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4)⟫ ≠ 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 5 - x 4⟫ < 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 4 - x 5⟫ < 0) :
    FaceChordView F 3 := by
  rcases hE5 with ⟨hs, h6lo⟩ | ⟨hs, h6lo⟩
  · exact q45_Kplus_s_le_one F ha4 ha5 s t hs0 ht hst hdecomp hk hs h6lo hS2_e5 hS3 hS4
  · exact q45_Kplus_s_gt_one F ha4 ha5 s t hs0 ht hst hdecomp hk hs h6lo hS2_e34 hS3 hS4

/-- **Leaf K- (Subcase t ≤ 1, E4 = e4)**:
When `0 < ρ0 * kJ` (i.e. `0 < det3(256-plane) * Ω`) and weak 2-high fails strictly at base `e4 = x 4 - x 0`.
- Views: `u_ε = e4 + ε • e5` in `J0` for small `ε > 0`.
- Rim: 6 4 5 2, chord 4 -> 5, middles 0, 3, farther w ∈ {2, 6}.
- Lemma K rules out 6-high everywhere on `J0`.
- Open condition `h2lo` rules out 2-high near `e4`. -/
theorem q45_Kminus_t_le_one {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha4 : ⟪F.N 5, x 4 - x 0⟫ < 0)
    (ha5 : ⟪F.N 5, x 5 - x 0⟫ < 0)
    (s t : ℝ)
    (hs0 : 0 < s)
    (ht : 0 < t)
    (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hk : 0 < det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1))
    (ht1 : t ≤ 1)
    (h2lo : min ⟪x 4, x 4 - x 0⟫ ⟪x 2, x 4 - x 0⟫ < max ⟪x 6, x 4 - x 0⟫ ⟪x 5, x 4 - x 0⟫)
    (hS2 : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0)
    (hS3 : F.f 3 (x 2) ≠ F.f 3 (x 6))
    (hS4 : ⟪F.N 3, cross (x 5 - x 4) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4)⟫ ≠ 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 5 - x 4⟫ < 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 4 - x 5⟫ < 0) :
    FaceChordView F 3 := by
  sorry

/-- **Leaf K- (Subcase 1 < t, E4 = e35)**:
When `0 < ρ0 * kJ` and weak 2-high fails strictly at base `e35 = x 3 - x 5`.
- Views: `u_ε = (x 3 - x 5) + ε • (x 5 - x 0)` in `J0` for small `ε > 0`.
- Rim: 6 4 5 2, chord 4 -> 5, middles 0, 3, farther w ∈ {2, 6}.
- Lemma K rules out 6-high everywhere on `J0`.
- Open condition `h2lo` rules out 2-high near `e35`. -/
theorem q45_Kminus_t_gt_one {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha4 : ⟪F.N 5, x 4 - x 0⟫ < 0)
    (ha5 : ⟪F.N 5, x 5 - x 0⟫ < 0)
    (s t : ℝ)
    (hs0 : 0 < s)
    (ht : 0 < t)
    (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hk : 0 < det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1))
    (ht1 : 1 < t)
    (h2lo : min ⟪x 4, x 3 - x 5⟫ ⟪x 2, x 3 - x 5⟫ < max ⟪x 6, x 3 - x 5⟫ ⟪x 5, x 3 - x 5⟫)
    (hS2 : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 3 - x 5⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0)
    (hS3 : F.f 3 (x 2) ≠ F.f 3 (x 6))
    (hS4 : ⟪F.N 3, cross (x 5 - x 4) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4)⟫ ≠ 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 5 - x 4⟫ < 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 4 - x 5⟫ < 0) :
    FaceChordView F 3 := by
  sorry

/-- **Leaf K- (Unified Dispatcher Form)**:
Dispatches between `t ≤ 1` (`E4 = e4`) and `1 < t` (`E4 = e35`). -/
theorem q45_Kminus {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha4 : ⟪F.N 5, x 4 - x 0⟫ < 0)
    (ha5 : ⟪F.N 5, x 5 - x 0⟫ < 0)
    (s t : ℝ)
    (hs0 : 0 < s)
    (ht : 0 < t)
    (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hk : 0 < det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1))
    (hE4 : (t ≤ 1 ∧ min ⟪x 4, x 4 - x 0⟫ ⟪x 2, x 4 - x 0⟫ < max ⟪x 6, x 4 - x 0⟫ ⟪x 5, x 4 - x 0⟫) ∨
           (1 < t ∧ min ⟪x 4, x 3 - x 5⟫ ⟪x 2, x 3 - x 5⟫ < max ⟪x 6, x 3 - x 5⟫ ⟪x 5, x 3 - x 5⟫))
    (hS2_e4 : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0)
    (hS2_e35 : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 3 - x 5⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0)
    (hS3 : F.f 3 (x 2) ≠ F.f 3 (x 6))
    (hS4 : ⟪F.N 3, cross (x 5 - x 4) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4)⟫ ≠ 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 5 - x 4⟫ < 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 4 - x 5⟫ < 0) :
    FaceChordView F 3 := by
  rcases hE4 with ⟨ht1, h2lo⟩ | ⟨ht1, h2lo⟩
  · exact q45_Kminus_t_le_one F ha4 ha5 s t hs0 ht hst hdecomp hk ht1 h2lo hS2_e4 hS3 hS4
  · exact q45_Kminus_t_gt_one F ha4 ha5 s t hs0 ht hst hdecomp hk ht1 h2lo hS2_e35 hS3 hS4

end Minimality.T24.Q45
