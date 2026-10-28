module

public import Minimality.QuadRect09

@[expose] public section

/-! Scratch (sp02): `QuadTripleRect` at the quadrilaterals `0235`, `1246` (vertex `2`) of type 02 is Rupert:
Theorem 09.Q (PROOFS §39.5) uses only `Q1 ∩ Q2 = {v}`, `Q1 ∪ Q2 = V`, four points each and no three
collinear, so `prismShape_of_quadTripleRect` and `isRupert_prismShape` apply verbatim. -/

namespace Minimality

open scoped RealInnerProductSpace

theorem isRupert_of_quadTripleRect02 {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (hgen : NoThreeCollinear (Finset.univ.image x))
    (hQ : QuadTripleRect (Finset.univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
      (({1, 2, 4, 6} : Finset (Fin 7)).image x) (x 2)) :
    IsRupert (Finset.univ.image x) := by
  classical
  have h1V : ({0, 2, 3, 5} : Finset (Fin 7)).image x ⊆ Finset.univ.image x :=
    Finset.image_subset_image (Finset.subset_univ _)
  have h2V : ({1, 2, 4, 6} : Finset (Fin 7)).image x ⊆ Finset.univ.image x :=
    Finset.image_subset_image (Finset.subset_univ _)
  have hint : ({0, 2, 3, 5} : Finset (Fin 7)).image x ∩ ({1, 2, 4, 6} : Finset (Fin 7)).image x
      = {x 2} := by
    rw [← Finset.image_inter _ _ hx, show ({0, 2, 3, 5} : Finset (Fin 7)) ∩ {1, 2, 4, 6} = {2} by
      decide, Finset.image_singleton]
  have hc1 : (({0, 2, 3, 5} : Finset (Fin 7)).image x).card = 4 := by
    rw [Finset.card_image_of_injective _ hx]; decide
  have hc2 : (({1, 2, 4, 6} : Finset (Fin 7)).image x).card = 4 := by
    rw [Finset.card_image_of_injective _ hx]; decide
  have hU : ({0, 2, 3, 5} : Finset (Fin 7)).image x ∪ ({1, 2, 4, 6} : Finset (Fin 7)).image x
      = Finset.univ.image x := by
    rw [← Finset.image_union, show ({0, 2, 3, 5} : Finset (Fin 7)) ∪ {1, 2, 4, 6} = Finset.univ by
      decide]
  obtain ⟨A, B, e, l, α, β, z1, z2, he, hA, hB, hdet, hl, hα0, hα1, hβ0, hβ1, hz1, hz2, hV⟩ :=
    prismShape_of_quadTripleRect hgen h1V h2V hint hc1 hc2 hU hQ
  rw [hV]
  exact isRupert_prismShape _ A B e l α β z1 z2 he hA hB hdet hl hα0 hα1 hβ0 hβ1 hz1 hz2

end Minimality
