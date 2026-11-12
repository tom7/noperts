module

public import Minimality.Type24SAT.K24.WallEG

@[expose] public section

/-!
# Type 24: Lemma WV on `C ∥ I`, acute at `02`

The relabelling `σ = (2 6)(4 5)` (facets `A ↔ B`, `C ↔ E`, `G ↔ I`) turns `isRupert_wallEG_acute` into
`Minimality.T24.isRupert_wallCI_acute`.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT

namespace Minimality.H24K.SAT

/-- The vertex relabelling `σ = (2 6)(4 5)` of type 24, exchanging `E ∥ G` with `C ∥ I`. -/
def wallSig : Fin 7 → Fin 7 := ![0, 1, 6, 3, 5, 4, 2]

/-- The facet permutation induced by `σ`: `A ↔ B`, `C ↔ E`, `G ↔ I`, `D F H` fixed. -/
def wallPi : Fin 9 → Fin 9 := ![1, 0, 4, 3, 2, 5, 8, 7, 6]

theorem wallSig_mem : ∀ (t : Fin 9) (i : Fin 7), i ∈ s0x_S24 t ↔ wallSig i ∈ s0x_S24 (wallPi t) := by decide

theorem wallSig_invol : ∀ i : Fin 7, wallSig (wallSig i) = i := by decide

/-- The facet data of `x` relabelled by `σ` are facet data of `x ∘ σ`. -/
def facSig {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : S0xFac 9 s0x_S24 (x ∘ wallSig) where
  f t := F.f (wallPi t)
  N t := F.N (wallPi t)
  hN t y z := F.hN (wallPi t) y z
  zero t i hi := F.zero (wallPi t) (wallSig i) ((wallSig_mem t i).1 hi)
  neg t i hi := F.neg (wallPi t) (wallSig i) (fun h => hi ((wallSig_mem t i).2 h))

/-- **Lemma WV on type 24, `C ∥ I`, acute at `02`**: the image of `isRupert_wallEG_acute` under `σ = (2 6)(4 5)`. -/
theorem _root_.Minimality.T24.isRupert_wallCI_acute {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hCI0 : ⟪F.N 2, x 3 - x 6⟫ = 0 ∧ ⟪F.N 2, x 4 - x 6⟫ = 0)
    (hA : ⟪F.N 0, F.N 2⟫ < 0)
    (hgen : ∀ t ∈ ({1, 4, 3, 5, 7, 6} : Finset (Fin 9)), ⟪F.N t, F.N 2⟫ ≠ 0) :
    IsRupert (Finset.univ.image x) := by
  have h := Minimality.T24.isRupert_wallEG_acute (facSig F) (x := x ∘ wallSig)
    ⟨by
      show ⟪F.N 2, x 6 - x 3⟫ = 0
      rw [← neg_sub, inner_neg_right, hCI0.1, neg_zero], by
      show ⟪F.N 2, x 6 - x 4⟫ = 0
      rw [← neg_sub, inner_neg_right, hCI0.2, neg_zero]⟩
    hA (fun t ht => hgen (wallPi t) (by revert t; decide))
  have e : Finset.univ.image (x ∘ wallSig) = Finset.univ.image x := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨wallSig i, by rw [wallSig_invol]⟩
  rwa [e] at h

end Minimality.H24K.SAT
