module

public import Mathlib
public import MinimalityExtra
public import Minimality.Type24SAT.K24.WallEG

/-!
# Lemma WV on type 24, `E ∥ G`, acute at `06`

Proof of `WallViewTypeEG` of `MinimalityExtra.lean`, from `Minimality.T24.isRupert_wallEG_acute`
(Minimality/Type24SAT/K24/WallEG.lean): the plane data `N`, `c` make an `S0xFac`.
-/

@[expose] public section

open scoped RealInnerProductSpace
namespace MinimalityExtra

theorem faces24_iff : ∀ (t : Fin 9) (i : Fin 7),
    i ∈ Minimality.T24.SAT.s0x_S24 t ↔ i ∈ type24Faces t := by decide

/-- Proof of `WallViewTypeEG`. -/
theorem wallViewTypeEG : WallViewTypeEG := by
  intro x N c hz hn h23 h25 hB hgen
  let F : Minimality.H21.S0xFac 9 Minimality.T24.SAT.s0x_S24 x :=
    { f := fun t y => ⟪N t, y⟫ - c t
      N := N
      hN := fun t y z => by rw [inner_sub_right]; ring
      zero := fun t i hi => by simp [hz t i ((faces24_iff t i).1 hi)]
      neg := fun t i hi => by
        have := hn t i (fun h => hi ((faces24_iff t i).2 h))
        simp; linarith }
  exact Minimality.T24.isRupert_wallEG_acute F ⟨h23, h25⟩ hB hgen

end MinimalityExtra
end
