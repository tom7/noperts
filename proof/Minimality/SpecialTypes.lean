module

public import Minimality.SpecialValue
public import Minimality.ParallelEdge
public import Minimality.Type05
public import Minimality.Type13
public import Minimality.Type17
public import Minimality.Type19
public import Minimality.Type23
public import Minimality.Type27
public import Minimality.Type12
public import Minimality.Type22
public import Minimality.Type28

@[expose] public section

/-!
# Types 05, 10, 13, 17, 19, 23, 27 at the special value of Lemma T′

Each of these types is decided by a number `s` (the value of an off point in a view of
Lemma T, `Type*.lean`). At `s = 1` three faces are edge-on in one view, one corner of the
shadow triangle carries a vertical edge, and the earlier statements asked `EdgeFar` along
that edge (Lemma T′ over the edge), which excluded a tie of the two other corners, while
their general position at the coinciding vertex views (`TriGenFarP`) excluded the ties
with the ends of the edge. Here `isRupert_special_index` (`FEWER-FACES-PROOFS.md`
Theorems 23.18 and 24.13: a reading of Lemma T′ at some corner) settles every tie at
`s = 1` except the triple tie (`SpecTriple`: the two far corners and an end of the edge at
one depth), with no condition on parallel segments. So each theorem below asks the
general position of the earlier statement only off `s = 1`, and at `s = 1` only that the
triple tie does not occur. The earlier statements imply these.

| type | `s = 1` | edge `v w` | third face | far corners |
|---|---|---|---|---|
| 05 | `fG x5 / fG x0 + fA x5 / fA x4` | `01` | `246` | `2`, `4` |
| 10 | `fB x0 / fB x2 + fA x0 / fA x3` | `14` | `023` | `2`, `3` |
| 13 | `fB x3 / fB x1 + fA x3 / fA x2` | `45` | `123` | `1`, `2` |
| 17 | `fB x0 / fB x6 + fD x0 / fD x4` | `24` | `136` | `6`, `3` |
| 19 | `fB x4 / fB x0 + fA x4 / fA x6` | `35` | `046` | `0`, `6` |
| 23 | `fA x6 / fA x1 + fD x6 / fD x5` | `04` | `156` | `1`, `5` |
| 27 | `fG x2 / fG x5` | `25` | `046` | `0`, `6` |

Types 12, 22, 28 (the second half of the file) have no forced vertical edge: at `s = 1` the
three corners are single vertices, the earlier statements asked `TriGenFar` at the view
(excluding a tie of two far corners and any segment parallel to the view), and
`isRupert_special3_index` settles everything but the triple tie of the three corners
(`ViewTriple`), again with no condition on parallel segments.

| type | `s = 1` | apex, faces | far corners | third face |
|---|---|---|---|---|
| 12 | `fD x6 / fD x3 + fA x6 / fA x2` | `0`: `0135`, `024` | `3`, `2` | `236` |
| 22 | `fG x5 / fG x1 + fA x5 / fA x2` | `4`: `0134`, `246` | `1`, `2` | `125` |
| 28 | `fG x3 / fG x0 + fA x3 / fA x6` | `4`: `0245`, `146` | `0`, `6` | `036` |
-/

namespace Minimality

open Finset
open scoped RealInnerProductSpace

set_option maxHeartbeats 8000000 in
/-- **Type 05 with the special value settled.** As `isRupert_type05_facets`, with its
general position asked only off the special value `s = 1`, and at `s = 1` only no triple
tie of `x2`, `x4` and `x0` or `x1` along `01`. -/
theorem isRupert_type05_sv (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (hgen : NoThreeCollinear (univ.image x)) (fA fB fG fK fH : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 2, 3} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 2, 3} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({0, 1, 4, 5} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({0, 1, 4, 5} : Finset (Fin 7)) → fB (x i) < 0))
    (hG : ∀ i, (i ∈ ({2, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({2, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hK : ∀ i, (i ∈ ({4, 5, 6} : Finset (Fin 7)) → fK (x i) = 0) ∧
      (i ∉ ({4, 5, 6} : Finset (Fin 7)) → fK (x i) < 0))
    (hH : ∀ i, (i ∈ ({2, 3, 4} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({2, 3, 4} : Finset (Fin 7)) → fH (x i) < 0))
    (hT1 : fG (x 5) / fG (x 0) + fA (x 5) / fA (x 4) ≠ 1 →
      TriGenPar (univ.image x) (({0, 1, 2, 3} : Finset (Fin 7)).image x)
        (({2, 4, 6} : Finset (Fin 7)).image x) (x 2) ∨
      TriGenFarP (univ.image x) (({0, 1, 2, 3} : Finset (Fin 7)).image x)
        (({2, 4, 6} : Finset (Fin 7)).image x) (x 2))
    (hT2 : fG (x 5) / fG (x 0) + fA (x 5) / fA (x 4) ≠ 1 →
      TriGenPar (univ.image x) (({0, 1, 4, 5} : Finset (Fin 7)).image x)
        (({2, 4, 6} : Finset (Fin 7)).image x) (x 4) ∨
      TriGenFarP (univ.image x) (({0, 1, 4, 5} : Finset (Fin 7)).image x)
        (({2, 4, 6} : Finset (Fin 7)).image x) (x 4))
    (hS : fG (x 5) / fG (x 0) + fA (x 5) / fA (x 4) = 1 → ¬ SpecTriple (x 0) (x 1) (x 2) (x 4)) :
    IsRupert (univ.image x) := by
  by_cases hs : fG (x 5) / fG (x 0) + fA (x 5) / fA (x 4) = 1
  · exact isRupert_special_index x hx hgen {0, 1, 2, 3} {0, 1, 4, 5} {2, 4, 6} fA fB fG hA hB hG
      0 1 2 4 6 3 5 (by decide) (by decide)
      (type05_special_parallel x hx hgen fA fB fG hA hB hG hs).1 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (hS hs)
  · exact isRupert_type05_facets x hx hgen fA fB fG fK fH hA hB hG hK hH
      ⟨hT1 hs, fun h => absurd h hs⟩ (hT2 hs)

set_option maxHeartbeats 8000000 in
/-- **Type 10 with the special value settled.** As `isRupert_type10`, with its general
position asked only off `s = 1`, and at `s = 1` only no triple tie of `x2`, `x3` and `x1`
or `x4` along `14`. -/
theorem isRupert_type10_sv (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (hgen : NoThreeCollinear (univ.image x))
    (hsol : (interior (convexHull ℝ ((univ.image x : Finset ℝ³) : Set ℝ³))).Nonempty)
    (fA fB fC fD : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({1, 2, 4, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({1, 2, 4, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({1, 3, 4, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({1, 3, 4, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({2, 3, 5, 6} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({2, 3, 5, 6} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 2, 3} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 2, 3} : Finset (Fin 7)) → fD (x i) < 0))
    (hZ1 : fB (x 0) / fB (x 2) + fA (x 0) / fA (x 3) ≠ 1 →
      EdgeTieR (univ.image x) (({1, 2, 4, 5} : Finset (Fin 7)).image x)
        (({1, 3, 4, 6} : Finset (Fin 7)).image x) (x 1) (x 4) ∨
      EdgeFarP (univ.image x) (({1, 2, 4, 5} : Finset (Fin 7)).image x)
        (({1, 3, 4, 6} : Finset (Fin 7)).image x) (x 1) (x 4))
    (hT2 : fB (x 0) / fB (x 2) + fA (x 0) / fA (x 3) ≠ 1 →
      TriGenPar (univ.image x) (({0, 2, 3} : Finset (Fin 7)).image x)
        (({1, 2, 4, 5} : Finset (Fin 7)).image x) (x 2) ∨
      TriGenFarP (univ.image x) (({0, 2, 3} : Finset (Fin 7)).image x)
        (({1, 2, 4, 5} : Finset (Fin 7)).image x) (x 2))
    (hS : fB (x 0) / fB (x 2) + fA (x 0) / fA (x 3) = 1 → ¬ SpecTriple (x 1) (x 4) (x 2) (x 3)) :
    IsRupert (univ.image x) := by
  by_cases hs : fB (x 0) / fB (x 2) + fA (x 0) / fA (x 3) = 1
  · exact isRupert_special_index x hx hgen {1, 2, 4, 5} {1, 3, 4, 6} {0, 2, 3} fA fB fD hA hB hD
      1 4 2 3 0 5 6 (by decide) (by decide)
      (type10_special_parallel x hx hgen fA fB fD hA hB hD hs).1 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (hS hs)
  · exact isRupert_type10 x hx hgen hsol fA fB fC fD hA hB hC hD (hZ1 hs)
      ⟨hT2 hs, fun h => absurd h hs⟩

set_option maxHeartbeats 8000000 in
/-- **Type 13 with the special value settled.** As `isRupert_type13`, with its general
position asked only off `s = 1`, and at `s = 1` only no triple tie of `x1`, `x2` and `x4`
or `x5` along `45`. -/
theorem isRupert_type13_sv (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (hgen : NoThreeCollinear (univ.image x))
    (hsol : (interior (convexHull ℝ ((univ.image x : Finset ℝ³) : Set ℝ³))).Nonempty)
    (fA fB fD fG : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 4, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 4, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({2, 4, 5, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({2, 4, 5, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hD : ∀ i, (i ∈ ({1, 2, 3} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({1, 2, 3} : Finset (Fin 7)) → fD (x i) < 0))
    (hG : ∀ i, (i ∈ ({1, 2, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({1, 2, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hZ1 : fB (x 3) / fB (x 1) + fA (x 3) / fA (x 2) ≠ 1 →
      EdgeTieR (univ.image x) (({0, 1, 4, 5} : Finset (Fin 7)).image x)
        (({2, 4, 5, 6} : Finset (Fin 7)).image x) (x 4) (x 5) ∨
      EdgeFarP (univ.image x) (({0, 1, 4, 5} : Finset (Fin 7)).image x)
        (({2, 4, 5, 6} : Finset (Fin 7)).image x) (x 4) (x 5))
    (hT2 : fB (x 3) / fB (x 1) + fA (x 3) / fA (x 2) ≠ 1 →
      TriGenPar (univ.image x) (({0, 1, 4, 5} : Finset (Fin 7)).image x)
        (({1, 2, 3} : Finset (Fin 7)).image x) (x 1) ∨
      TriGenFarP (univ.image x) (({0, 1, 4, 5} : Finset (Fin 7)).image x)
        (({1, 2, 3} : Finset (Fin 7)).image x) (x 1))
    (hS : fB (x 3) / fB (x 1) + fA (x 3) / fA (x 2) = 1 → ¬ SpecTriple (x 4) (x 5) (x 1) (x 2)) :
    IsRupert (univ.image x) := by
  by_cases hs : fB (x 3) / fB (x 1) + fA (x 3) / fA (x 2) = 1
  · exact isRupert_special_index x hx hgen {0, 1, 4, 5} {2, 4, 5, 6} {1, 2, 3} fA fB fD hA hB hD
      4 5 1 2 3 0 6 (by decide) (by decide)
      (type13_special_parallel x hx hgen fA fB fD hA hB hD hs).1 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (hS hs)
  · exact isRupert_type13 x hx hgen hsol fA fB fD fG hA hB hD hG (hZ1 hs)
      ⟨hT2 hs, fun h => absurd h hs⟩

set_option maxHeartbeats 8000000 in
/-- **Type 17 with the special value settled.** As `isRupert_type17`, with its general
position asked only off `s = 1`, and at `s = 1` only no triple tie of `x6`, `x3` and `x2`
or `x4` along `24`. -/
theorem isRupert_type17_sv (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (hgen : NoThreeCollinear (univ.image x)) (fA fB fD fE : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 2, 4, 6} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 2, 4, 6} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({2, 3, 4, 5} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({2, 3, 4, 5} : Finset (Fin 7)) → fB (x i) < 0))
    (hD : ∀ i, (i ∈ ({1, 3, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({1, 3, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({0, 3, 4} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({0, 3, 4} : Finset (Fin 7)) → fE (x i) < 0))
    (hT1 : fB (x 0) / fB (x 6) + fD (x 0) / fD (x 4) ≠ 1 →
      TriGenPar (univ.image x) (({1, 3, 6} : Finset (Fin 7)).image x)
        (({2, 3, 4, 5} : Finset (Fin 7)).image x) (x 3) ∨
      TriGenFarP (univ.image x) (({1, 3, 6} : Finset (Fin 7)).image x)
        (({2, 3, 4, 5} : Finset (Fin 7)).image x) (x 3))
    (hT2 : fB (x 0) / fB (x 6) + fD (x 0) / fD (x 4) ≠ 1 →
      TriGenPar (univ.image x) (({0, 2, 4, 6} : Finset (Fin 7)).image x)
        (({1, 3, 6} : Finset (Fin 7)).image x) (x 6) ∨
      TriGenFarP (univ.image x) (({0, 2, 4, 6} : Finset (Fin 7)).image x)
        (({1, 3, 6} : Finset (Fin 7)).image x) (x 6))
    (hS : fB (x 0) / fB (x 6) + fD (x 0) / fD (x 4) = 1 → ¬ SpecTriple (x 2) (x 4) (x 6) (x 3)) :
    IsRupert (univ.image x) := by
  by_cases hs : fB (x 0) / fB (x 6) + fD (x 0) / fD (x 4) = 1
  · exact isRupert_special_index x hx hgen {0, 2, 4, 6} {2, 3, 4, 5} {1, 3, 6} fA fB fD hA hB hD
      2 4 6 3 1 0 5 (by decide) (by decide)
      (type17_special_parallel x hx hgen fA fB fD hA hB hD hs).1 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (hS hs)
  · exact isRupert_type17 x hx hgen fA fB fD fE hA hB hD hE ⟨hT1 hs, fun h => absurd h hs⟩ (hT2 hs)

set_option maxHeartbeats 8000000 in
/-- **Type 19 with the special value settled.** As `isRupert_type19`, with its general
position asked only off `s = 1`, and at `s = 1` only no triple tie of `x0`, `x6` and `x3`
or `x5` along `35`. -/
theorem isRupert_type19_sv (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (hgen : NoThreeCollinear (univ.image x))
    (hsol : (interior (convexHull ℝ ((univ.image x : Finset ℝ³) : Set ℝ³))).Nonempty)
    (fA fB fD fG : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 2, 3, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 2, 3, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({1, 3, 5, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({1, 3, 5, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hG : ∀ i, (i ∈ ({3, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({3, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hZ1 : fB (x 4) / fB (x 0) + fA (x 4) / fA (x 6) ≠ 1 →
      EdgeTieR (univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
        (({1, 3, 5, 6} : Finset (Fin 7)).image x) (x 3) (x 5) ∨
      EdgeFarP (univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
        (({1, 3, 5, 6} : Finset (Fin 7)).image x) (x 3) (x 5))
    (hT2 : fB (x 4) / fB (x 0) + fA (x 4) / fA (x 6) ≠ 1 →
      TriGenPar (univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
        (({0, 4, 6} : Finset (Fin 7)).image x) (x 0) ∨
      TriGenFarP (univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
        (({0, 4, 6} : Finset (Fin 7)).image x) (x 0))
    (hS : fB (x 4) / fB (x 0) + fA (x 4) / fA (x 6) = 1 → ¬ SpecTriple (x 3) (x 5) (x 0) (x 6)) :
    IsRupert (univ.image x) := by
  by_cases hs : fB (x 4) / fB (x 0) + fA (x 4) / fA (x 6) = 1
  · exact isRupert_special_index x hx hgen {0, 2, 3, 5} {1, 3, 5, 6} {0, 4, 6} fA fB fD hA hB hD
      3 5 0 6 4 2 1 (by decide) (by decide)
      (type19_special_parallel x hx hgen fA fB fD hA hB hD hs).1 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (hS hs)
  · exact isRupert_type19 x hx hgen hsol fA fB fD fG hA hB hD hG (hZ1 hs)
      ⟨hT2 hs, fun h => absurd h hs⟩

set_option maxHeartbeats 8000000 in
/-- **Type 23 with the special value settled.** As `isRupert_type23`, with its general
position asked only off `s = 1`, and at `s = 1` only no triple tie of `x1`, `x5` and `x0`
or `x4` along `04`. -/
theorem isRupert_type23_sv (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (hgen : NoThreeCollinear (univ.image x)) (fA fD fE fH fK : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 3, 4, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 3, 4, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 1, 4} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 1, 4} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({1, 2, 5} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({1, 2, 5} : Finset (Fin 7)) → fE (x i) < 0))
    (hH : ∀ i, (i ∈ ({1, 5, 6} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({1, 5, 6} : Finset (Fin 7)) → fH (x i) < 0))
    (hK : ∀ i, (i ∈ ({4, 5, 6} : Finset (Fin 7)) → fK (x i) = 0) ∧
      (i ∉ ({4, 5, 6} : Finset (Fin 7)) → fK (x i) < 0))
    (hZ1 : fA (x 6) / fA (x 1) + fD (x 6) / fD (x 5) ≠ 1 →
      EdgePar (univ.image x) (x 0) (x 4) ∨
      EdgeFarP (univ.image x) (({0, 1, 4} : Finset (Fin 7)).image x)
        (({0, 3, 4, 5} : Finset (Fin 7)).image x) (x 0) (x 4))
    (hT1 : fA (x 6) / fA (x 1) + fD (x 6) / fD (x 5) ≠ 1 →
      TriGenPar (univ.image x) (({0, 1, 4} : Finset (Fin 7)).image x)
        (({1, 5, 6} : Finset (Fin 7)).image x) (x 1) ∨
      TriGenFarP (univ.image x) (({0, 1, 4} : Finset (Fin 7)).image x)
        (({1, 5, 6} : Finset (Fin 7)).image x) (x 1))
    (hT2 : fA (x 6) / fA (x 1) + fD (x 6) / fD (x 5) ≠ 1 →
      TriGenPar (univ.image x) (({0, 3, 4, 5} : Finset (Fin 7)).image x)
        (({1, 2, 5} : Finset (Fin 7)).image x) (x 5) ∨
      TriGenFarP (univ.image x) (({0, 3, 4, 5} : Finset (Fin 7)).image x)
        (({1, 2, 5} : Finset (Fin 7)).image x) (x 5))
    (hS : fA (x 6) / fA (x 1) + fD (x 6) / fD (x 5) = 1 → ¬ SpecTriple (x 0) (x 4) (x 1) (x 5)) :
    IsRupert (univ.image x) := by
  by_cases hs : fA (x 6) / fA (x 1) + fD (x 6) / fD (x 5) = 1
  · exact isRupert_special_index x hx hgen {0, 1, 4} {0, 3, 4, 5} {1, 5, 6} fD fA fH hD hA hH
      0 4 1 5 6 0 3 (by decide) (by decide)
      (type23_special_parallel x hx hgen fA fD fH hA hD hH hs).1 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (hS hs)
  · exact isRupert_type23 x hx hgen fA fD fE fH fK hA hD hE hH hK (hZ1 hs)
      ⟨hT1 hs, fun h => absurd h hs⟩ (hT2 hs)

set_option maxHeartbeats 8000000 in
/-- **Type 27 with the special value settled.** As `isRupert_type27`, with its general
position asked only off `fG x2 / fG x5 = 1`, and there only no triple tie of `x0`, `x6`
and `x2` or `x5` along `25`. -/
theorem isRupert_type27_sv (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (hgen : NoThreeCollinear (univ.image x)) (fB fD fE fG fH fI fJ : ℝ³ →ᵃ[ℝ] ℝ)
    (hB : ∀ i, (i ∈ ({2, 3, 5, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({2, 3, 5, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 2, 5} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 2, 5} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({0, 1, 6} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({0, 1, 6} : Finset (Fin 7)) → fE (x i) < 0))
    (hG : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hH : ∀ i, (i ∈ ({0, 4, 5} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({0, 4, 5} : Finset (Fin 7)) → fH (x i) < 0))
    (hI : ∀ i, (i ∈ ({0, 1, 2} : Finset (Fin 7)) → fI (x i) = 0) ∧
      (i ∉ ({0, 1, 2} : Finset (Fin 7)) → fI (x i) < 0))
    (hJ : ∀ i, (i ∈ ({4, 5, 6} : Finset (Fin 7)) → fJ (x i) = 0) ∧
      (i ∉ ({4, 5, 6} : Finset (Fin 7)) → fJ (x i) < 0))
    (hZ1 : fG (x 2) / fG (x 5) ≠ 1 →
      EdgePar (univ.image x) (x 2) (x 5) ∨
      EdgeFarP (univ.image x) (({0, 2, 5} : Finset (Fin 7)).image x)
        (({2, 3, 5, 6} : Finset (Fin 7)).image x) (x 2) (x 5))
    (hT1 : fG (x 2) / fG (x 5) ≠ 1 →
      TriGenPar (univ.image x) (({0, 1, 6} : Finset (Fin 7)).image x)
        (({2, 3, 5, 6} : Finset (Fin 7)).image x) (x 6) ∨
      TriGenFarP (univ.image x) (({0, 1, 6} : Finset (Fin 7)).image x)
        (({2, 3, 5, 6} : Finset (Fin 7)).image x) (x 6))
    (hT2 : fG (x 2) / fG (x 5) ≠ 1 →
      TriGenPar (univ.image x) (({0, 2, 5} : Finset (Fin 7)).image x)
        (({0, 4, 6} : Finset (Fin 7)).image x) (x 0) ∨
      TriGenFarP (univ.image x) (({0, 2, 5} : Finset (Fin 7)).image x)
        (({0, 4, 6} : Finset (Fin 7)).image x) (x 0))
    (hS : fG (x 2) / fG (x 5) = 1 → ¬ SpecTriple (x 2) (x 5) (x 0) (x 6)) :
    IsRupert (univ.image x) := by
  by_cases hs : fG (x 2) / fG (x 5) = 1
  · exact isRupert_special_index x hx hgen {0, 2, 5} {2, 3, 5, 6} {0, 4, 6} fD fB fG hD hB hG
      2 5 0 6 4 2 3 (by decide) (by decide)
      (type27_special_parallel x hx hgen fD fG hD hG hs).1 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (hS hs)
  · exact isRupert_type27 x hx hgen fB fD fE fG fH fI fJ hB hD hE hG hH hI hJ (hZ1 hs) (hT1 hs)
      ⟨hT2 hs, fun h => absurd h hs⟩

set_option maxHeartbeats 8000000 in
/-- **Type 12 with the special value settled.** As `isRupert_type12`, with its general
position asked only off `s = 1`, and at `s = 1` only no triple tie of `x0`, `x3`, `x2` in
the view along the line of the planes of `0135` and `024`. -/
theorem isRupert_type12_sv (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (hgen : NoThreeCollinear (univ.image x)) (fA fB fD fG fJ : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 3, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 3, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({0, 3, 4, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({0, 3, 4, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 2, 4} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 2, 4} : Finset (Fin 7)) → fD (x i) < 0))
    (hG : ∀ i, (i ∈ ({2, 3, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({2, 3, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hJ : ∀ i, (i ∈ ({2, 4, 6} : Finset (Fin 7)) → fJ (x i) = 0) ∧
      (i ∉ ({2, 4, 6} : Finset (Fin 7)) → fJ (x i) < 0))
    (hT1 : fD (x 6) / fD (x 3) + fA (x 6) / fA (x 2) ≠ 1 →
      TriGenPar (univ.image x) (({0, 1, 3, 5} : Finset (Fin 7)).image x)
        (({0, 2, 4} : Finset (Fin 7)).image x) (x 0) ∨
      TriGenFarP (univ.image x) (({0, 1, 3, 5} : Finset (Fin 7)).image x)
        (({0, 2, 4} : Finset (Fin 7)).image x) (x 0))
    (hT2 : fD (x 6) / fD (x 3) + fA (x 6) / fA (x 2) ≠ 1 →
      TriGenPar (univ.image x) (({0, 2, 4} : Finset (Fin 7)).image x)
        (({2, 3, 6} : Finset (Fin 7)).image x) (x 2) ∨
      TriGenFarP (univ.image x) (({0, 2, 4} : Finset (Fin 7)).image x)
        (({2, 3, 6} : Finset (Fin 7)).image x) (x 2))
    (hS : fD (x 6) / fD (x 3) + fA (x 6) / fA (x 2) = 1 → ¬ ViewTriple fA fD (x 0) (x 3) (x 2)) :
    IsRupert (univ.image x) := by
  by_cases hs : fD (x 6) / fD (x 3) + fA (x 6) / fA (x 2) = 1
  · exact isRupert_special3_index x hx hgen {0, 1, 3, 5} {0, 2, 4} {2, 3, 6} fA fD fG hA hD hG
      0 3 2 6 4 (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide))
      hs (hS hs)
  · exact isRupert_type12 x hx hgen fA fB fD fG fJ hA hB hD hG hJ
      ⟨hT1 hs, fun h => absurd h hs⟩ (hT2 hs)

set_option maxHeartbeats 8000000 in
/-- **Type 22 with the special value settled.** As `isRupert_type22`, with its general
position asked only off `s = 1`, and at `s = 1` only no triple tie of `x4`, `x1`, `x2` in
the view along the line of the planes of `0134` and `246`. -/
theorem isRupert_type22_sv (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (hgen : NoThreeCollinear (univ.image x)) (fA fD fG fN fI : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 3, 4} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 3, 4} : Finset (Fin 7)) → fA (x i) < 0))
    (hD : ∀ i, (i ∈ ({1, 2, 5} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({1, 2, 5} : Finset (Fin 7)) → fD (x i) < 0))
    (hG : ∀ i, (i ∈ ({2, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({2, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hN : ∀ i, (i ∈ ({1, 4, 6} : Finset (Fin 7)) → fN (x i) = 0) ∧
      (i ∉ ({1, 4, 6} : Finset (Fin 7)) → fN (x i) < 0))
    (hI : ∀ i, (i ∈ ({2, 5, 6} : Finset (Fin 7)) → fI (x i) = 0) ∧
      (i ∉ ({2, 5, 6} : Finset (Fin 7)) → fI (x i) < 0))
    (hT1 : fG (x 5) / fG (x 1) + fA (x 5) / fA (x 2) ≠ 1 →
      TriGenPar (univ.image x) (({1, 2, 5} : Finset (Fin 7)).image x)
        (({2, 4, 6} : Finset (Fin 7)).image x) (x 2) ∨
      TriGenFarP (univ.image x) (({1, 2, 5} : Finset (Fin 7)).image x)
        (({2, 4, 6} : Finset (Fin 7)).image x) (x 2))
    (hT2 : fG (x 5) / fG (x 1) + fA (x 5) / fA (x 2) ≠ 1 →
      TriGenPar (univ.image x) (({0, 1, 3, 4} : Finset (Fin 7)).image x)
        (({2, 4, 6} : Finset (Fin 7)).image x) (x 4) ∨
      TriGenFarP (univ.image x) (({0, 1, 3, 4} : Finset (Fin 7)).image x)
        (({2, 4, 6} : Finset (Fin 7)).image x) (x 4))
    (hS : fG (x 5) / fG (x 1) + fA (x 5) / fA (x 2) = 1 → ¬ ViewTriple fA fG (x 4) (x 1) (x 2)) :
    IsRupert (univ.image x) := by
  by_cases hs : fG (x 5) / fG (x 1) + fA (x 5) / fA (x 2) = 1
  · exact isRupert_special3_index x hx hgen {0, 1, 3, 4} {2, 4, 6} {1, 2, 5} fA fG fD hA hG hD
      4 1 2 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide))
      hs (hS hs)
  · exact isRupert_type22 x hx hgen fA fD fG fN fI hA hD hG hN hI (hT1 hs)
      ⟨hT2 hs, fun h => absurd h hs⟩

set_option maxHeartbeats 8000000 in
/-- **Type 28 with the special value settled.** As `isRupert_type28`, with its general
position asked only off `s = 1`, and at `s = 1` only no triple tie of `x4`, `x0`, `x6` in
the view along the line of the planes of `0245` and `146`. -/
theorem isRupert_type28_sv (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (hgen : NoThreeCollinear (univ.image x)) (fA fD fG fH fF fM : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 2, 4, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 2, 4, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 3, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 3, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hG : ∀ i, (i ∈ ({1, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({1, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hH : ∀ i, (i ∈ ({0, 2, 3} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({0, 2, 3} : Finset (Fin 7)) → fH (x i) < 0))
    (hF : ∀ i, (i ∈ ({0, 1, 5} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({0, 1, 5} : Finset (Fin 7)) → fF (x i) < 0))
    (hM : ∀ i, (i ∈ ({1, 4, 5} : Finset (Fin 7)) → fM (x i) = 0) ∧
      (i ∉ ({1, 4, 5} : Finset (Fin 7)) → fM (x i) < 0))
    (hT1 : fG (x 3) / fG (x 0) + fA (x 3) / fA (x 6) ≠ 1 →
      TriGenPar (univ.image x) (({0, 2, 4, 5} : Finset (Fin 7)).image x)
        (({1, 4, 6} : Finset (Fin 7)).image x) (x 4) ∨
      TriGenFarP (univ.image x) (({0, 2, 4, 5} : Finset (Fin 7)).image x)
        (({1, 4, 6} : Finset (Fin 7)).image x) (x 4))
    (hT2 : fG (x 3) / fG (x 0) + fA (x 3) / fA (x 6) ≠ 1 →
      TriGenPar (univ.image x) (({0, 2, 4, 5} : Finset (Fin 7)).image x)
        (({0, 3, 6} : Finset (Fin 7)).image x) (x 0) ∨
      TriGenFarP (univ.image x) (({0, 2, 4, 5} : Finset (Fin 7)).image x)
        (({0, 3, 6} : Finset (Fin 7)).image x) (x 0))
    (hS : fG (x 3) / fG (x 0) + fA (x 3) / fA (x 6) = 1 → ¬ ViewTriple fA fG (x 4) (x 0) (x 6)) :
    IsRupert (univ.image x) := by
  by_cases hs : fG (x 3) / fG (x 0) + fA (x 3) / fA (x 6) = 1
  · exact isRupert_special3_index x hx hgen {0, 2, 4, 5} {1, 4, 6} {0, 3, 6} fA fG fD hA hG hD
      4 0 6 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide))
      hs (hS hs)
  · exact isRupert_type28 x hx hgen fA fD fG fH fF fM hA hD hG hH hF hM
      ⟨hT1 hs, fun h => absurd h hs⟩ (hT2 hs)

end Minimality

end
