module

public import Minimality.Type29SAT.FinalK4a
public import Minimality.Type29SAT.FinalK3a

@[expose] public section

/-!
# Type 29: the four closed classes K4a, K3a, K4b, K3b

K4a and K3a are the kernel-checked cores.  K4b and K3b are their images under `σ = (0 2)(4 5)` (`NF29.sigma`,
`image_sigma29`): `σ` exchanges `a2` and `b0` and negates `V`.
-/

set_option autoImplicit false
open Minimality

/-- **Class K4b is closed** (the `σ`-image of K4a): `a2, b0 > 0`, `V > 0`; every such normal form is Rupert. -/
theorem Minimality.NF29.isRupert_K4b_closed {x : Fin 7 → EuclideanSpace ℝ (Fin 3)} (N : NF29 x) (ha2 : 0 < N.a2)
    (hb0 : 0 < N.b0) (hV : 0 < N.V) : IsRupert (Finset.univ.image x) := by
  have h := NF29.isRupert_K4a_closed N.sigma hb0 ha2 (by simp only [NF29.sigma, NF29.V] at hV ⊢; linarith)
  rwa [image_sigma29] at h

/-- **Class K3b is closed** (the `σ`-image of K3a): `a2 > 0 > b0`, `V < 0`; every such normal form is Rupert. -/
theorem Minimality.NF29.isRupert_K3b_closed {x : Fin 7 → EuclideanSpace ℝ (Fin 3)} (N : NF29 x) (ha2 : 0 < N.a2)
    (hb0 : N.b0 < 0) (hV : N.V < 0) : IsRupert (Finset.univ.image x) := by
  have h := NF29.isRupert_K3a_closed N.sigma hb0 ha2 (by simp only [NF29.sigma, NF29.V] at hV ⊢; linarith)
  rwa [image_sigma29] at h

