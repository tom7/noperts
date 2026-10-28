module

public import Minimality.Type02A
public import Minimality.Type02B
public import Minimality.Type02R
public import Minimality.Type02X
public import Minimality.Type02FNB
public import Minimality.Type02V12
public import Minimality.QuadRect02
public import Minimality.Cases

@[expose] public section

/-! # sp02 Lean, group I: assembly of type 02 from the sector theorems (proved from the sector theorems of Type02A, B, R, X, FNB, V12).

`Frame02.isRupert` : every case-(c) frame is Rupert; `type02_false` : the form for the skeleton, replacing the
type-02 case of the skeleton in `Minimality.lean` (closed):

```
    have hQ := quadPairPar02 hx hN rfl hR
    exact byGen1 (type02_edge34_byGen'' …) (fun _ => byGen1 (fourQuad …) (fun _ => byThm5Faces hx hN _ h3 (fun _ =>
      Minimality.CaseC18.type02_false hx hN hR hQ)))
```
(the earlier `byGen1` wrappers could also be dropped: `type02_false` needs none of their hypotheses). -/

namespace Minimality.CaseC18
open Finset Filter Minimality.CaseC09
open scoped RealInnerProductSpace Topology

theorem isRupert_of_comp_perm {x : Fin 7 → ℝ³} (π : Equiv.Perm (Fin 7))
    (h : IsRupert (Finset.univ.image (x ∘ π))) : IsRupert (Finset.univ.image x) := by
  rwa [isRupert_image_comp_perm] at h

namespace Frame02
variable {x : Fin 7 → ℝ³}

/-- Theorem 02.C (acute), assembled. -/
theorem isRupert_acute (F : Frame02 x) (h1 : gA12 x < gA11 x) (h2 : gA12 x < gA22 x) :
    IsRupert (Finset.univ.image x) := by
  rcases lt_trichotomy F.S.tp F.S.sp with hA | hA | hA <;>
    rcases lt_trichotomy F.S.tm F.S.sm with hB | hB | hB
  · exact F.acute_A0B5_pf h1 h2 hA hB
  · obtain ⟨G, g1, g2, g3, g4, e1, e2, e3⟩ := F.alpha_spec
    refine isRupert_of_comp_perm permAlpha (G.acute_V1B5_pf (by rw [e2, e1]; exact h1) (by rw [e2, e3]; exact h2)
      (by rw [g1, g3]; exact hB) (by rw [g2, g4]; exact hA))
  · obtain ⟨G, g1, g2, g3, g4, e1, e2, e3⟩ := F.alpha_spec
    exact isRupert_of_comp_perm permAlpha (G.acute_A1B5_pf (by rw [e2, e1]; exact h1)
      (by rw [e2, e3]; exact h2) (by rw [g1, g3]; exact hB) (by rw [g2, g4]; exact hA))
  · exact F.acute_V1B5_pf h1 h2 hA hB
  · exact F.acute_V12_pf h1 h2 hA hB
  · exact F.acute_V1B6_pf h1 h2 hA hB
  · exact F.acute_A1B5_pf h1 h2 hA hB
  · obtain ⟨G, g1, g2, g3, g4, e1, e2, e3⟩ := F.alpha_spec
    exact isRupert_of_comp_perm permAlpha (G.acute_V1B6_pf (by rw [e2, e1]; exact h1)
      (by rw [e2, e3]; exact h2) (by rw [g1, g3]; exact hB) (by rw [g2, g4]; exact hA))
  · exact F.acute_A1B6_pf h1 h2 hA hB

/-- Theorem 02.R (right angle at `x3`), assembled. -/
theorem isRupert_right (F : Frame02 x) (hr : gA12 x = gA11 x) :
    IsRupert (Finset.univ.image x) := by
  rcases lt_trichotomy F.S.tp F.S.sp with hA | hA | hA <;>
    rcases lt_trichotomy F.S.tm F.S.sm with hB | hB | hB
  · exact F.right_A0B5_pf hr hA hB
  · -- α of (`A` vertical, `B = 5`)
    obtain ⟨G, g1, g2, g3, g4, e1, e2, e3⟩ := F.alpha_spec
    have hr' : gA12 (x ∘ permAlpha) = gA11 (x ∘ permAlpha) := by rw [e2, e1]; exact hr
    by_cases hR : F1Rect x
    · exact isRupert_of_comp_perm permAlpha (G.right_X1_pf hr' (by rw [g1, g3]; exact hB)
        (by rw [g2, g4]; exact hA) ((F1Rect_alpha x).2 hR))
    · exact isRupert_of_comp_perm permAlpha (G.right_V1B5_pf hr' (by rw [g1, g3]; exact hB)
        (by rw [g2, g4]; exact hA) (fun h => hR ((F1Rect_alpha x).1 h)))
  · -- α of (1,5)
    obtain ⟨G, g1, g2, g3, g4, e1, e2, e3⟩ := F.alpha_spec
    exact isRupert_of_comp_perm permAlpha (G.right_A1B5_pf (by rw [e2, e1]; exact hr)
      (by rw [g1, g3]; exact hB) (by rw [g2, g4]; exact hA))
  · by_cases hR : F1Rect x
    · exact F.right_X1_pf hr hA hB hR
    · exact F.right_V1B5_pf hr hA hB hR
  · by_cases hR : F1Rect x
    · exact F.right_X12_pf hr hA hB hR
    · by_cases hX : X2Set x
      · rcases lt_or_eq_of_le hX.2.2 with hlt | heq
        · exact F.right_X2_obtuse_pf hr hA hB hX hlt
        · exact absurd (F.f1Rect_of_X2_pf hX heq) hR
      · exact F.right_V12_pf hr hA hB hX
  · exact F.right_V1B6_pf hr hA hB
  · exact F.right_A1B5_pf hr hA hB
  · -- α of (`A` vertical, `B = 6`)
    obtain ⟨G, g1, g2, g3, g4, e1, e2, e3⟩ := F.alpha_spec
    exact isRupert_of_comp_perm permAlpha (G.right_V1B6_pf (by rw [e2, e1]; exact hr)
      (by rw [g1, g3]; exact hB) (by rw [g2, g4]; exact hA))
  · exact F.right_A1B6_pf hr hA hB

/-- **Every case-(c) frame of type 02 is Rupert** (acute, right at `x3`, right at `x4` by β). -/
theorem isRupert (F : Frame02 x) : IsRupert (Finset.univ.image x) := by
  have h1 := F.A12_le_A11
  have h2 := F.A12_le_A22
  change gA12 x ≤ gA11 x at h1
  change gA12 x ≤ gA22 x at h2
  rcases lt_or_eq_of_le h1 with h1 | h1
  · rcases lt_or_eq_of_le h2 with h2 | h2
    · exact F.isRupert_acute h1 h2
    · obtain ⟨G, -, -, -, -, e1, e2, e3⟩ := F.beta_spec
      exact isRupert_of_comp_perm permBeta (G.isRupert_right (by rw [e3, e1]; exact h2))
  · exact F.isRupert_right h1

end Frame02

/-- The form for the skeleton: `hQ` is `quadPairPar02`'s conclusion (the acute case-(c) triple tie or
`QuadTripleRect`); no other general position is needed. -/
theorem type02_false {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (hN : IsNopert (Finset.univ.image x))
    (hR : RealizesFaces x (sevenTypeFaces 1))
    (hQ : (TriGenPar (Finset.univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
        (({1, 2, 4, 6} : Finset (Fin 7)).image x) (x 2) ∧
      ¬ TriGenTieO (Finset.univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
        (({1, 2, 4, 6} : Finset (Fin 7)).image x) (x 2)) ∨
      QuadTripleRect (Finset.univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
        (({1, 2, 4, 6} : Finset (Fin 7)).image x) (x 2)) : False := by
  rcases hQ with ⟨hP, hT⟩ | hRect
  · obtain ⟨F⟩ := frame02 hx (noThreeCollinear_seven x hN hx) hR hP hT
    exact hN.2 F.isRupert
  · exact hN.2 (Minimality.isRupert_of_quadTripleRect02 hx (noThreeCollinear_seven x hN hx) hRect)

end Minimality.CaseC18
