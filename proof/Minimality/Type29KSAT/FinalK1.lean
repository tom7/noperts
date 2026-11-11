module

public import Minimality.Type29KSAT.LinkK1aL
public import Minimality.Type29KSAT.K1Corner

@[expose] public section

/-!
# Type 29, class K1 on the corner stratum `Z`: `NF29.isRupert_K1_Z`

On the stratum `Z` (vertex `6` trirectangular: its three edges `63, 64, 65` pairwise orthogonal), every normal form of
class K1 (`a2 < 0 < b0`, `V < 0`, or `a2 > 0 > b0`, `V > 0`) is Rupert.  No hypothesis of general position.  The proof
is the kernel-checked unsatisfiability of a trimmed core of 1,637 clauses of the tie view encoding, with the brackets,
the corner conditions as class literals and the Corner Slide and Level Corner Slide clauses as class clauses
(`rupert_of_coreK1aL`); K1b is the `σ`-image of K1a.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.H29.SAT

/-- **Class K1a on the corner stratum `Z` is closed**: `a2 < 0 < b0`, `V < 0`. -/
theorem Minimality.NF29.isRupert_K1a_Z {x : Fin 7 → EuclideanSpace ℝ (Fin 3)} (N : NF29 x)
    (ha2 : N.a2 < 0) (hb0 : 0 < N.b0) (hV : N.V < 0)
    (hZ : inner ℝ (x 3 - x 6) (x 4 - x 6) = 0 ∧ inner ℝ (x 3 - x 6) (x 5 - x 6) = 0 ∧
      inner ℝ (x 4 - x 6) (x 5 - x 6) = 0) :
    IsRupert (Finset.univ.image x) :=
  Minimality.H29K1.nf29_K1a_Z_of_core
    (fun F h0 h1 h2 h3 hz => Minimality.H29K.SAT.rupert_of_coreK1aL Minimality.H29K.SAT.coreUnsatK1aL F h0 h1 h2 h3 hz)
    N ha2 hb0 hV hZ

/-- **Class K1 on the corner stratum `Z` is closed** (K1b as the `σ`-image of K1a). -/
theorem Minimality.NF29.isRupert_K1_Z {x : Fin 7 → EuclideanSpace ℝ (Fin 3)} (N : NF29 x)
    (hK1 : (N.a2 < 0 ∧ 0 < N.b0 ∧ N.V < 0) ∨ (0 < N.a2 ∧ N.b0 < 0 ∧ 0 < N.V))
    (hZ : inner ℝ (x 3 - x 6) (x 4 - x 6) = 0 ∧ inner ℝ (x 3 - x 6) (x 5 - x 6) = 0 ∧
      inner ℝ (x 4 - x 6) (x 5 - x 6) = 0) :
    IsRupert (Finset.univ.image x) :=
  Minimality.H29K1.nf29_K1_Z_of_core
    (fun F h0 h1 h2 h3 hz => Minimality.H29K.SAT.rupert_of_coreK1aL Minimality.H29K.SAT.coreUnsatK1aL F h0 h1 h2 h3 hz)
    N hK1 hZ

#print axioms Minimality.NF29.isRupert_K1_Z
