module

public import Minimality.Type29TSAT.FinalV0
public import Minimality.Type29TSAT.NfB0

@[expose] public section

/-!
# Type 29, class boundary: `NF29.isRupert_boundary`

Every type 29 normal form with `a2 = 0`, `b0 = 0` or `V = 0` is Rupert (core B0 for `b0 = 0`, its image under `σ` for
`a2 = 0`, core V0 for `V = 0`).
-/

set_option autoImplicit false
open Minimality

/-- **Class `b0 = 0` is closed** (core B0). -/
theorem Minimality.NF29.isRupert_B0 {x : Fin 7 → EuclideanSpace ℝ (Fin 3)} (N : NF29 x) (hb : N.b0 = 0) :
    IsRupert (Finset.univ.image x) :=
  Minimality.H29T.SAT.nf29_B0_of_core
    (fun F h0 h1 => Minimality.H29T.SAT.B0_of_core F h0 h1) N hb

/-- **The class boundary is closed.**  Every type 29 normal form with `a2 = 0`, `b0 = 0` or `V = 0` is Rupert, with no
hypothesis of general position.  (`a2 = 0` is `b0 = 0` for `σ`-image normal form.) -/
theorem Minimality.NF29.isRupert_boundary {x : Fin 7 → EuclideanSpace ℝ (Fin 3)} (N : NF29 x)
    (h : N.a2 = 0 ∨ N.b0 = 0 ∨ N.V = 0) : IsRupert (Finset.univ.image x) := by
  rcases h with h | h | h
  · have := N.sigma.isRupert_B0 (by exact h)
    rwa [image_sigma29] at this
  · exact N.isRupert_B0 h
  · exact N.isRupert_V0 h

#print axioms Minimality.NF29.isRupert_boundary
