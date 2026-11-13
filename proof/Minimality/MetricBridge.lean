module

public import Minimality.ManyTies

@[expose] public section

/-!
# From an affine-invariant certificate cover to metric-freeness (`FEWER-FACES-PROOFS.md` §24.3)

Theorem 24.3 (`ManyTies.lean`) needs its two rims `X, X′` to be *metric-free*: at the depth
functionals `G u`, `G u′` of metrics `G` near `I` at which the labels of both rims have distinct
depths, `X` or `X′` is cyclically unimodal.  A type's certificate cover is stated for every
point set realizing the type; a linear image `M ∘ x` of a realization (`M` invertible) realizes
the same type, so it is certified, and its certificates at the views `c M u` have the depths
`⟪x i, G u⟫` with `G = Mᵀ M`.  This file proves, for an abstract finite family `Q` of labelled
certificates, that the cover gives metric-freeness along a curve of metrics, or else `x` is Rupert
(by the limit lemma `isRupert_of_tendsto_rimCert`).

* `WeakLeft`: the closed part of `RimCertAt.left` (it passes to limits).
* `metricFree_of_cover`: **the bridge**.  Hypotheses: the cover (`hApprox`: for small `ε` the
  linear image `M ε ∘ x` is a limit of shapes carrying one of the certificates `q`), the pair of
  certificate classes `P₁, P₂` of the two tests (rotations or reflections of the test rims at the
  same views), and the escape for all other certificates that survive in the limit
  (`hO`: no horizontal double normal at their view and distinct depths of their labels).
* `pair_contra`: the case of a certificate of a test: the limit rim is robustly unimodal.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### Small lemmas -/

theorem IsRobustUnimodal.rot {k : ℕ} {z : ZMod k → ℝ} (hz : IsRobustUnimodal z) (r : ZMod k) :
    IsRobustUnimodal (fun i => z (i + r)) where
  noPeaks B a b c d hab hbc hcd hdk h := by
    refine hz.noPeaks (B + r) a b c d hab hbc hcd hdk ?_
    simp only [show ∀ t : ℕ, B + (t : ZMod k) + r = B + r + (t : ZMod k) from fun t => by ring]
      at h
    exact h
  noTriple i j l hij hjl hil e1 e2 :=
    hz.noTriple (i + r) (j + r) (l + r) (fun h => hij (add_right_cancel h))
      (fun h => hjl (add_right_cancel h)) (fun h => hil (add_right_cancel h)) e1 e2
  noLevelRun B a b c d hab hbc hcd hdk e := by
    have := hz.noLevelRun (B + r) a b c d hab hbc hcd hdk (by
      simpa only [show ∀ t : ℕ, B + (t : ZMod k) + r = B + r + (t : ZMod k) from fun t => by ring]
        using e)
    simpa only [show ∀ t : ℕ, B + (t : ZMod k) + r = B + r + (t : ZMod k) from fun t => by ring]
      using this

/-! ### A generic symmetric operator for a family of tests -/

/-! ### The case of a test certificate -/

/-! ### The bridge -/

end Minimality

end
