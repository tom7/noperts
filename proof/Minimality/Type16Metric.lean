module

public import Minimality.Type16Limit
public import Minimality.MetricBridge
public import Minimality.Type29HDN

@[expose] public section

/-!
# Type 16 with several ties: linear images and the metric bridge (`FEWER-FACES-PROOFS.md` §24.3)

The cover of type 16 (`NF16.cert_nf`) certifies every normal-form shape off the special positions
`genPoly16` and with at most one tie at each segment view and at the two vertex views used by the
route.  A linear image `M ∘ y` of a normal-form shape is a normal-form shape with the same
parameters and the frame `M o, M E_i`, so it is certified as soon as it has no ties at the named
views; and ties are broken by a generic small perturbation of `M`.

* `detMap`, `det3_map`, `planeLine_map`, `view16_map`: the named views are equivariant.
* `NoTies16`, `cert16_nfShape`: a normal-form shape with no ties at the named views is certified.
* `exists_perturb`: a small perturbation of an invertible `M` that breaks finitely many ties.
* `exists_certSeq16_map`: for every `M` with `det ≠ 0`, `M ∘ x` is a pointwise limit of certified
  shapes (**the cover is affine-invariant**).
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### Named views under linear maps -/

/-! ### Shapes without ties are certified -/

/-! ### Breaking ties by a small linear perturbation -/

/-! ### The certificates of type 16 as a finite family -/

/-- The labelled rims of the cover: three, four or five corners. -/
abbrev Rim16 : Type := (ZMod 3 → Fin 7) ⊕ (ZMod 4 → Fin 7) ⊕ (ZMod 5 → Fin 7)

/-- A labelled certificate index: a named view, a sign, and a labelled rim (`CertL16`). -/
abbrev Q16 : Type := ((Fin 7 × Fin 7) ⊕ Fin 6) × Bool × Rim16

/-- The corner count and labels of a rim. -/
def Lab16 : Rim16 → (k : ℕ) × (ZMod k → Fin 7)
  | .inl l => ⟨3, l⟩
  | .inr (.inl l) => ⟨4, l⟩
  | .inr (.inr l) => ⟨5, l⟩

/-- The number of corners of the rim of `q`. -/
def Q16.K (q : Q16) : ℕ := (Lab16 q.2.2).1

/-- The labels of the rim of `q`. -/
def Q16.lab (q : Q16) : ZMod q.K → Fin 7 := (Lab16 q.2.2).2

theorem Q16.K_three (q : Q16) : 3 ≤ q.K := by
  rcases q with ⟨v, e, L | L | L⟩ <;> simp [Q16.K, Lab16]

instance (q : Q16) : NeZero q.K :=
  ⟨by have := q.K_three; omega⟩

/-! ### Rotations and reflections of a rim -/

/-! ### Several views with ties -/

end Minimality

end
