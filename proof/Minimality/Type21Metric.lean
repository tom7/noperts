module

public import Minimality.Type21Limit
public import Minimality.Type16Metric

@[expose] public section

/-!
# Type 21 with several ties: linear images and the metric bridge (`FEWER-FACES-PROOFS.md` §24.3)

The analogue of `Type16Metric.lean` for type 21.  The cover at a generic normal-form shape
(`cert21_of_generic`) needs the type's sign conditions (polynomial in the parameters, `genPoly21`),
the negativity of the facet functions, and ties only at the named views; a linear image `M ∘ y` of
a normal-form shape is a normal-form shape with the same parameters, its facet functions are those
of `y` rescaled by `det M`, and its ties are broken by a generic small perturbation of `M`.

* `view21_map`, `NoTies21`, `cert21_nfShape21`: the named views are equivariant; a normal-form
  shape without ties at the named views and with its facet functions negative is certified.
* `exists_certSeq21_map`: for every invertible `M`, `M ∘ x` is a pointwise limit of certified
  shapes (**the cover is affine-invariant**).
* `Q21`, `MultiView21`, `isRupert_type21_multiView`: Theorem 24.3 for type 21 from the bridge
  `metricFree_of_cover`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### Named views under linear maps -/

/-! ### Shapes without ties are certified -/

/-! ### The certificates of type 21 as a finite family -/

/-- A labelled certificate index at a used view: a named view of the cover (`UsedV21`), a sign, and
a labelled rim (`CertL21`). -/
abbrev Q21 : Type :=
  {q : ((Fin 7 × Fin 7) ⊕ Fin 8) × Bool × Rim16 // UsedV21 q.1}

/-- The named view of a certificate index. -/
def Q21.v (q : Q21) : (Fin 7 × Fin 7) ⊕ Fin 8 := q.1.1

/-- The sign of a certificate index. -/
def Q21.e (q : Q21) : Bool := q.1.2.1

/-- The number of corners of the rim of `q`. -/
def Q21.K (q : Q21) : ℕ := (Lab16 q.1.2.2).1

/-- The labels of the rim of `q`. -/
def Q21.lab (q : Q21) : ZMod q.K → Fin 7 := (Lab16 q.1.2.2).2

theorem Q21.K_three (q : Q21) : 3 ≤ q.K := by
  obtain ⟨⟨v, e, L | L | L⟩, hq⟩ := q <;> simp [Q21.K, Lab16]

instance (q : Q21) : NeZero q.K :=
  ⟨by have := q.K_three; omega⟩

/-! ### Two views with ties -/

end Minimality

end
