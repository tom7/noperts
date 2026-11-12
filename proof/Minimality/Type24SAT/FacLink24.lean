module

public import Minimality.Type24SAT.LinkPpmmm
public import Minimality.Type24SAT.LinkPpmpm
public import Minimality.Type24SAT.LinkMpmpm
public import Minimality.Type24SAT.LinkMpppm
public import Minimality.Type24SAT.LinkPpmmm30
public import Minimality.Type24SAT.Facets24

@[expose] public section

/-! # Type 24, layer L1: the five cores against the tree's facet structure

`coreFalseNAME_fac`: for `y : Fin 7 → ℝ³` with the nine facets `F : S0xFac 9 s0x_S24 y` and the chirality bracket
`[0126] < 0` (the orientation of the labelled reference shape; the mirror image is handled by reflecting), no configuration satisfies all
literals of the core NAME (in the `ℕ`-indexed form `ext y` of Sem24).  The plane-quad `QuadD`, `Convex24` and the F24c
sign are all derived (`quadD_of_fac`, `convex24_of_fac`, `hdet24`). -/

set_option autoImplicit false
open scoped RealInnerProductSpace

namespace Minimality.T24.SAT
open Minimality Minimality.H21

theorem coreFalsePpmmm_fac (y : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 y)
    (hchir : det3 (y 1 - y 0) (y 2 - y 0) (y 6 - y 0) < 0)
    (hcore : ∀ p ∈ corePpmmm, LitHolds (ext y) p.1 p.2) : False :=
  coreFalsePpmmm (ext y) (quadD_of_fac F) (convex24_of_fac F hchir) hcore

theorem coreFalsePpmpm_fac (y : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 y)
    (hchir : det3 (y 1 - y 0) (y 2 - y 0) (y 6 - y 0) < 0)
    (hcore : ∀ p ∈ corePpmpm, LitHolds (ext y) p.1 p.2) : False :=
  coreFalsePpmpm (ext y) (quadD_of_fac F) (convex24_of_fac F hchir) hcore

theorem coreFalseMpmpm_fac (y : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 y)
    (hchir : det3 (y 1 - y 0) (y 2 - y 0) (y 6 - y 0) < 0)
    (hcore : ∀ p ∈ coreMpmpm, LitHolds (ext y) p.1 p.2) : False :=
  coreFalseMpmpm (ext y) (quadD_of_fac F) (convex24_of_fac F hchir) hcore

theorem coreFalseMpppm_fac (y : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 y)
    (hchir : det3 (y 1 - y 0) (y 2 - y 0) (y 6 - y 0) < 0)
    (hcore : ∀ p ∈ coreMpppm, LitHolds (ext y) p.1 p.2) : False :=
  coreFalseMpppm (ext y) (quadD_of_fac F) (convex24_of_fac F hchir) hcore

theorem coreFalsePpmmm30_fac (y : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 y)
    (hchir : det3 (y 1 - y 0) (y 2 - y 0) (y 6 - y 0) < 0)
    (hcore : ∀ p ∈ corePpmmm30, LitHolds (ext y) p.1 p.2) : False :=
  coreFalsePpmmm30 (ext y) (quadD_of_fac F) (convex24_of_fac F hchir) hcore

#print axioms coreFalseMpppm_fac
#print axioms coreFalsePpmmm_fac
#print axioms convex24_of_fac
#print axioms hdet24
#print axioms quadD_of_fac

end Minimality.T24.SAT
