module

public import Minimality.Quad05Leaf
public import Minimality.FaceChordFac
public import Minimality.RimFromSigns
public import Minimality.Type24SAT.K24.Par2546

@[expose] public section

open scoped RealInnerProductSpace Topology
open Finset Filter
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.Quad05

namespace Minimality.T24.X5

/-- The perturbed view direction for Lemma X5 on facet `0345` (facet 3).
With chord edge `4 -> 0` and middle `5`, `u_X5 x η = (x 0 - x 5) + η • (x 4 - x 5)`. -/
def u_X5 (x : Fin 7 → ℝ³) (η : ℝ) : ℝ³ :=
  (x 0 - x 5) + η • (x 4 - x 5)

/-- Algebraic decomposition of vertex 3 as a chord middle over edge `0 -> 4`
along the perturbed view `u_X5 x η`. -/
theorem x3_middle_X5 (x : Fin 7 → ℝ³) (s t η : ℝ) (hη1 : 1 + η ≠ 0)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) :
    x 3 = x 0 + (s + t * η / (1 + η)) • (x 4 - x 0) + (-t / (1 + η)) • u_X5 x η := by
  sorry

/-- **Lemma X5 (Q45X24.md / Q45PROOF24.md): Corner Leaf at `e5 - ε e4`.**
For a Type 24 OB1 solid (`F : S0xFac 9 s0x_S24 x`), when `σ < 1` (where `x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)`
is the quad decomposition of Lemma M with `s < 1`), `g45 = ⟪x 4 - x 0, x 5 - x 0⟫ > 0`, and the special positions
S1-S4 hold, the solid is Rupert (`IsRupert (univ.image x)`). -/
theorem lemma_X5 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (s t : ℝ) (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hs0 : 0 < s) (hs : s < 1) (ht : 0 < t) (hst : 1 < s + t)
    (hg45 : 0 < ⟪x 4 - x 0, x 5 - x 0⟫)
    -- S1: Depth non-coincidence (vertex 2 not tied with 0, 4, 6 along x 0 - x 5)
    (hS1 : ⟪x 2 - x 0, x 0 - x 5⟫ ≠ 0 ∧ ⟪x 2 - x 4, x 0 - x 5⟫ ≠ 0 ∧ ⟪x 2 - x 6, x 0 - x 5⟫ ≠ 0)
    -- S2: Weak 6-high depth ordering at e5 (6 is shallower than 4 along x 0 - x 5)
    (hS2 : ⟪x 6 - x 4, x 0 - x 5⟫ < 0)
    -- S3: Farthest vertex condition (vertex 2 is strictly farther from facet 3 plane than vertex 6)
    (hS3 : 0 < det3 (x 0 - x 5) (x 4 - x 5) (x 2 - x 6) * det3 (x 0 - x 5) (x 4 - x 5) (x 1 - x 5))
    -- S4: Foot condition (foot of vertex 2 is off chord [x 4, x 0])
    (hS4 : det3 (x 0 - x 5) (x 4 - x 5) (cross (x 0 - x 4) (x 2 - x 4)) ≠ 0 ∨
      ⟪x 2 - x 4, x 0 - x 4⟫ < 0 ∨ ⟪x 2 - x 0, x 4 - x 0⟫ < 0)
    -- Convexity of rim 6-4-0-2 and vertex 1 strictly inside along u_X5 for small η > 0
    (hcyc_I : ∃ ρ : ℝ, ρ ≠ 0 ∧ ∀ᶠ η in 𝓝[>] (0 : ℝ),
      (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
        0 < ρ * det3 (quad (x 6) (x 4) (x 0) (x 2) (i + 1) - quad (x 6) (x 4) (x 0) (x 2) i)
          (quad (x 6) (x 4) (x 0) (x 2) j - quad (x 6) (x 4) (x 0) (x 2) i) (u_X5 x η)) ∧
      (∀ i : ZMod 4,
        0 < ρ * det3 (quad (x 6) (x 4) (x 0) (x 2) (i + 1) - quad (x 6) (x 4) (x 0) (x 2) i)
          (x 1 - quad (x 6) (x 4) (x 0) (x 2) i) (u_X5 x η))) :
    IsRupert (univ.image x) := by
  sorry

end Minimality.T24.X5
