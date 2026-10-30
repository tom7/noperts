module

public import Minimality.Type08S.P2QDefs
public import Minimality.Type08S.P2QQ0c
public import Minimality.Type08S.P2QQ1b
public import Minimality.Type08S.P2QQ2b
public import Minimality.Type08S.P2QQ3c
public import Minimality.Type08S.P2QQ4b
public import Minimality.Type08S.P2QQ5
public import Minimality.Type08S.P2QQ6

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# Type 08, plan 2 (final integration I, package P5): `Resid08FinalI` and `type08_rupert_or_residI`

The planar items `PlanarTwo ∨ PlanarGen` of `Resid08FinalH` survive only as a conjunct of the codim-3 leftovers
`ResidP6` (`LeftTT`, `κ_a = 0 ∧ ParEnd`): weak Lemma 6 gives every type-08 shape a `Norm08w` labelling, and the pipeline
runs on `Norm08w` (modules `P2Q*`: density, MF by limit, R2T*, E3, the limit theorem on the T4 closure, P3).
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp


/-! ## Assembly (proved) -/

/-- **The planar pipeline in one labelling.** -/
theorem planar_rupert_or_resP {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨ ResP a a' b b' c c' d := by
  classical
  by_cases hTT : IsT a' b c d ∨ IsT' a b c' d
  · rcases isRupert_type08_limit_T4cl N hTT with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨hTT, Or.inl h⟩)
    · exact Or.inr (Or.inl ⟨hTT, Or.inr (Or.inl h)⟩)
    · exact Or.inr (Or.inl ⟨hTT, Or.inr (Or.inr h)⟩)
  obtain ⟨hT, hT'⟩ := not_or.mp hTT
  by_cases hQ : RegQ N.F
  · exact Or.inl (close_caseQ N.F N.hd hQ.1 hQ.2)
  rcases isRupert_type08_limit_hdnR'_w N hT hT' hQ with h | ⟨t, ht, hreg, hr⟩
  · exact Or.inl h
  · by_cases hpe : det3 (c - b) (b' - b) (c' - b) = 0 ∧ ParEnd a a' b b' c c' d
    · exact Or.inr (Or.inr hpe)
    · exact Or.inl (close_hdn_w N hT hT' ht hreg hr hpe)

theorem wrapP {p p' q q' r r' d : ℝ³} (N : Norm08w p p' q q' r r' d) {V : Finset ℝ³}
    (hset : insert d ({p, p', q, q', r, r'} : Finset ℝ³) = V) :
    IsRupert V ∨ ResidP p p' q q' r r' d := by
  rcases planar_rupert_or_resP N with h | h
  · exact Or.inl (hset ▸ h)
  · exact Or.inr ⟨N, h⟩

/-- Every type-08 shape is Rupert or in one of the six planar residuals (no planarity hypothesis needed). -/
theorem type08_rupert_or_residP6 {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c') (hd : IsCap F d)
    (G : GaleData a a' b b' c c') :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨ ResidP6 a a' b b' c c' d := by
  have e := type08_set_perm a a' b b' c c' d
  rcases exists_norm08w F hd G with hN | hN | hN | hN | hN | hN
  · obtain ⟨N⟩ := hN
    rcases wrapP N rfl with r | r
    · exact Or.inl r
    · exact Or.inr (Or.inl r)
  · obtain ⟨N⟩ := hN
    rcases wrapP N e.2.1 with r | r
    · exact Or.inl r
    · exact Or.inr (Or.inr (Or.inl r))
  · obtain ⟨N⟩ := hN
    rcases wrapP N e.2.2.1 with r | r
    · exact Or.inl r
    · exact Or.inr (Or.inr (Or.inr (Or.inl r)))
  · obtain ⟨N⟩ := hN
    rcases wrapP N e.2.2.2.1 with r | r
    · exact Or.inl r
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl r))))
  · obtain ⟨N⟩ := hN
    rcases wrapP N e.2.2.2.2.1 with r | r
    · exact Or.inl r
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl r)))))
  · obtain ⟨N⟩ := hN
    rcases wrapP N e.2.2.2.2.2 with r | r
    · exact Or.inl r
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr r)))))

/-- **Point form of the target** (copy of `type08_rupert_or_resid_ptsH`, planar branch through `ResidP6`). -/
theorem type08_rupert_or_resid_ptsI {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap F d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨ Resid08FinalI a a' b b' c c' d := by
  classical
  obtain ⟨G⟩ := F.nonempty_galeData
  by_cases hall : galeD G.l G.m a a' ≠ 0 ∧ galeD G.l G.m b b' ≠ 0 ∧ galeD G.l G.m c c' ≠ 0
  · obtain ⟨hκa, hκb, hκc⟩ := hall
    have h := F.isOctahedron
    obtain ⟨-, -, hA⟩ := pole_signs F (G.hl.galeD G.hm a) (galeD_self _ _ a) hκa
    obtain ⟨-, -, hB⟩ := pole_signs F.perm₁₂ (G.hl.galeD G.hm b).perm₁₂ (galeD_self _ _ b) hκb
    obtain ⟨-, -, hC⟩ := pole_signs F.perm₂₃.perm₁₂ (G.hl.galeD G.hm c).perm₂₃.perm₁₂
      (galeD_self _ _ c) hκc
    obtain ⟨σ, hσ, hcases⟩ := type08_lemma6 hκa hκb hκc hA hB hC
    obtain ⟨G', hG'⟩ : ∃ G' : GaleData a a' b b' c c',
        ∀ s t, galeD G'.l G'.m s t = σ * galeD G.l G.m s t := by
      rcases hσ with rfl | rfl
      · exact ⟨G, fun s t => (one_mul _).symm⟩
      · exact ⟨G.mirror, fun s t => by rw [G.galeD_mirror]; ring⟩
    have hne : ∀ s t, galeD G.l G.m s t ≠ 0 → galeD G'.l G'.m s t ≠ 0 := by
      intro s t hst; rw [hG']; rcases hσ with rfl | rfl <;> simpa using hst
    have hpos : ∀ s t, 0 < σ * galeD G.l G.m s t → 0 < galeD G'.l G'.m s t := by
      intro s t h; rwa [hG']
    have hneg : ∀ s t, σ * galeD G.l G.m s t < 0 → galeD G'.l G'.m s t < 0 := by
      intro s t h; rwa [hG']
    have e := type08_set_perm a a' b b' c c' d
    rcases hcases with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2, h3⟩
    · rcases wrapNH (V := insert d ({a, a', b, b', c, c'} : Finset ℝ³))
        ⟨F, hd, G', hpos _ _ h1, hpos _ _ h2, hne _ _ hκc, hneg _ _ h3⟩ rfl with r | r
      · exact Or.inl r
      · exact Or.inr (Or.inr (Or.inl r))
    · rcases wrapNH ⟨F.perm₁₂, hd.perm₁₂, G'.perm₁₂, hpos _ _ h1, hpos _ _ h2, hne _ _ hκc,
        hneg _ _ h3⟩ e.2.1 with r | r
      · exact Or.inl r
      · exact Or.inr (Or.inr (Or.inr (Or.inl r)))
    · rcases wrapNH ⟨F.perm₂₃, hd.perm₂₃, G'.perm₂₃, hpos _ _ h1, hpos _ _ h2, hne _ _ hκb,
        hneg _ _ h3⟩ e.2.2.1 with r | r
      · exact Or.inl r
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl r))))
    · rcases wrapNH ⟨F.perm₂₃.perm₁₂, hd.perm₂₃.perm₁₂, G'.perm₂₃.perm₁₂, hpos _ _ h1,
        hpos _ _ h2, hne _ _ hκb, hneg _ _ h3⟩ e.2.2.2.1 with r | r
      · exact Or.inl r
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl r)))))
    · rcases wrapNH ⟨F.perm₁₂.perm₂₃, hd.perm₁₂.perm₂₃, G'.perm₁₂.perm₂₃, hpos _ _ h1,
        hpos _ _ h2, hne _ _ hκa, hneg _ _ h3⟩ e.2.2.2.2.1 with r | r
      · exact Or.inl r
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl r))))))
    · rcases wrapNH ⟨F.perm₁₂.perm₂₃.perm₁₂, hd.perm₁₂.perm₂₃.perm₁₂, G'.perm₁₂.perm₂₃.perm₁₂,
        hpos _ _ h1, hpos _ _ h2, hne _ _ hκa, hneg _ _ h3⟩ e.2.2.2.2.2 with r | r
      · exact Or.inl r
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr r))))))
  · -- planar: the old route (`isRupert_type08_flat_sel`) or `PlanarTwo ∨ PlanarGen`; then the weak pipeline
    have hold : IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨
        (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) := by
      by_cases hflat : ¬ (det3 (c - b) (b' - b) (c' - b) = 0 ∧ det3 (c - a) (a' - a) (c' - a) = 0) ∧
        ¬ (det3 (c - b) (b' - b) (c' - b) = 0 ∧ det3 (b - a) (a' - a) (b' - a) = 0) ∧
        ¬ (det3 (c - a) (a' - a) (c' - a) = 0 ∧ det3 (b - a) (a' - a) (b' - a) = 0)
      swap
      · exact Or.inr (Or.inl hflat)
      by_cases hg : GenSelFlat G d
      · exact Or.inl (isRupert_type08_flat_sel F hd hflat G hg)
      · refine Or.inr (Or.inr ⟨F, hd, G, ?_, hg⟩)
        by_contra hn
        push Not at hn
        exact hall hn
    rcases hold with h | hpl
    · exact Or.inl h
    rcases type08_rupert_or_residP6 F hd G with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨hpl, h⟩)

/-- **Facet form** (the integration point; same hypotheses as `type08_rupert_or_residH`). -/
theorem type08_rupert_or_residI (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (fA fB fC fD fE fF fG : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 2, 3} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 2, 3} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({0, 2, 4, 5} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({0, 2, 4, 5} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({2, 3, 5, 6} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({2, 3, 5, 6} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 1, 4} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 1, 4} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({1, 3, 6} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({1, 3, 6} : Finset (Fin 7)) → fE (x i) < 0))
    (hF : ∀ i, (i ∈ ({1, 4, 6} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({1, 4, 6} : Finset (Fin 7)) → fF (x i) < 0))
    (hG : ∀ i, (i ∈ ({4, 5, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({4, 5, 6} : Finset (Fin 7)) → fG (x i) < 0)) :
    IsRupert (univ.image x) ∨ Resid08FinalI (x 0) (x 6) (x 3) (x 4) (x 5) (x 1) (x 2) := by
  classical
  obtain ⟨-, eV⟩ := image_seven x
  rw [eV]
  obtain ⟨F, hcap⟩ := exists_type08_cap x hx fA fB fC fD fE fF fG hA hB hC hD hE hF hG
  exact type08_rupert_or_resid_ptsI F hcap

/-- The new target implies the tree's (`Resid08FinalI ⊆ Resid08FinalH`). -/
theorem type08_rupert_or_residI_imp_H (x : Fin 7 → ℝ³) {V : Finset ℝ³}
    (h : IsRupert V ∨ Resid08FinalI (x 0) (x 6) (x 3) (x 4) (x 5) (x 1) (x 2)) :
    IsRupert V ∨ Resid08FinalH (x 0) (x 6) (x 3) (x 4) (x 5) (x 1) (x 2) :=
  h.imp id resid08FinalI_imp_H

end Type08Sp
end Minimality
