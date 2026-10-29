module

public import Minimality.Type08S.SCi

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true

set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- **The residual in the labelling of `N`.** -/
def ResN' {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) : Prop :=
  (TieN2 a a' b b' c c' ∧ ¬ N2Closable N) ∨
  (TieT4 b b' c c' d ∧ ¬ T4Closable N) ∨
  ¬ TieOK a a' b b' c c' d ∨
  (∃ t ∈ SC08, ¬ NoHDNAt (insert d ({a, a', b, b', c, c'} : Finset ℝ³))
    ((test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d)) ∧ ¬ SCcl a a' b b' c c' d t) ∨
  (IsT a' b c d ∧ CoT2 a a' b b' c c' d) ∨
  (IsT' a b c' d ∧ CoT'2 a a' b b' c c' d)

theorem norm08_rupert_or_resN' {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨ ResN' N := by
  classical
  by_cases h2 : TieN2 a a' b b' c c'
  · by_cases hc : N2Closable N
    · exact Or.inl (gt_far_N2'' N hc.1 hc.2.1 h2 hc.2.2.1 hc.2.2.2)
    · exact Or.inr (Or.inl ⟨h2, hc⟩)
  by_cases h4 : TieT4 b b' c c' d
  · by_cases hc : T4Closable N
    · exact Or.inl (gt_far_T4' N hc.1 hc.2.1 h4 hc.2.2.1 hc.2.2.2)
    · exact Or.inr (Or.inr (Or.inl ⟨h4, hc⟩))
  have hnt : ¬ Touch a a' b b' c c' d := by
    rintro (h | h)
    · exact h2 h
    · exact h4 h
  by_cases hties : TieOK a a' b b' c c' d
  swap
  · exact Or.inr (Or.inr (Or.inr (Or.inl hties)))
  obtain ⟨q, hq, ties, ht, hi, hcov⟩ := hties
  by_cases hT : IsT a' b c d ∧ CoT2 a a' b b' c c' d
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hT)))))
  by_cases hT' : IsT' a b c' d ∧ CoT'2 a a' b b' c c' d
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hT')))))
  rcases isRupert_type08_limit_hdn' N hq ties ht hi hcov hnt (fun h hc => hT ⟨h, hc⟩)
      (fun h hc => hT' ⟨h, hc⟩) with h | h
  · exact Or.inl h
  · obtain ⟨t, ht, -, hn, hs⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨t, ht, hn, hs⟩))))

/-- `ResN` for some `Norm08` structure in the labelling `(a, b, c)`. -/
def ResidN' (a a' b b' c c' d : ℝ³) : Prop := ∃ N : Norm08 a a' b b' c c' d, ResN' N

theorem wrapN' {p p' q q' r r' d : ℝ³} (N : Norm08 p p' q q' r r' d) {V : Finset ℝ³}
    (hset : insert d ({p, p', q, q', r, r'} : Finset ℝ³) = V) :
    IsRupert V ∨ ResidN' p p' q q' r r' d := by
  rcases norm08_rupert_or_resN' N with h | h
  · exact Or.inl (hset ▸ h)
  · exact Or.inr ⟨N, h⟩

/-- **`Resid08Final'`**, on the seven points `(a, a', b, b', c, c', d)`. -/
def Resid08Final' (a a' b b' c c' d : ℝ³) : Prop :=
  PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d ∨
  ResidN' a a' b b' c c' d ∨ ResidN' b b' a a' c c' d ∨ ResidN' a a' c c' b b' d ∨
  ResidN' c c' a a' b b' d ∨ ResidN' b b' c c' a a' d ∨ ResidN' c c' b b' a a' d

theorem type08_rupert_or_resid_pts' {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap F d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨ Resid08Final' a a' b b' c c' d := by
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
    · rcases wrapN' (V := insert d ({a, a', b, b', c, c'} : Finset ℝ³))
        ⟨F, hd, G', hpos _ _ h1, hpos _ _ h2, hne _ _ hκc, hneg _ _ h3⟩ rfl with r | r
      · exact Or.inl r
      · exact Or.inr (Or.inr (Or.inr (Or.inl r)))
    · rcases wrapN' ⟨F.perm₁₂, hd.perm₁₂, G'.perm₁₂, hpos _ _ h1, hpos _ _ h2, hne _ _ hκc,
        hneg _ _ h3⟩ e.2.1 with r | r
      · exact Or.inl r
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl r))))
    · rcases wrapN' ⟨F.perm₂₃, hd.perm₂₃, G'.perm₂₃, hpos _ _ h1, hpos _ _ h2, hne _ _ hκb,
        hneg _ _ h3⟩ e.2.2.1 with r | r
      · exact Or.inl r
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl r)))))
    · rcases wrapN' ⟨F.perm₂₃.perm₁₂, hd.perm₂₃.perm₁₂, G'.perm₂₃.perm₁₂, hpos _ _ h1,
        hpos _ _ h2, hne _ _ hκb, hneg _ _ h3⟩ e.2.2.2.1 with r | r
      · exact Or.inl r
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl r))))))
    · rcases wrapN' ⟨F.perm₁₂.perm₂₃, hd.perm₁₂.perm₂₃, G'.perm₁₂.perm₂₃, hpos _ _ h1,
        hpos _ _ h2, hne _ _ hκa, hneg _ _ h3⟩ e.2.2.2.2.1 with r | r
      · exact Or.inl r
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl r)))))))
    · rcases wrapN' ⟨F.perm₁₂.perm₂₃.perm₁₂, hd.perm₁₂.perm₂₃.perm₁₂, G'.perm₁₂.perm₂₃.perm₁₂,
        hpos _ _ h1, hpos _ _ h2, hne _ _ hκa, hneg _ _ h3⟩ e.2.2.2.2.2 with r | r
      · exact Or.inl r
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr r)))))))
  · by_cases hflat : ¬ (det3 (c - b) (b' - b) (c' - b) = 0 ∧ det3 (c - a) (a' - a) (c' - a) = 0) ∧
      ¬ (det3 (c - b) (b' - b) (c' - b) = 0 ∧ det3 (b - a) (a' - a) (b' - a) = 0) ∧
      ¬ (det3 (c - a) (a' - a) (c' - a) = 0 ∧ det3 (b - a) (a' - a) (b' - a) = 0)
    swap
    · exact Or.inr (Or.inl hflat)
    by_cases hg : GenSelFlat G d
    · exact Or.inl (isRupert_type08_flat_sel F hd hflat G hg)
    · refine Or.inr (Or.inr (Or.inl ⟨F, hd, G, ?_, hg⟩))
      by_contra hn
      push Not at hn
      exact hall hn

/-- **Facet form** (the integration point). -/
theorem type08_rupert_or_resid' (x : Fin 7 → ℝ³) (hx : Function.Injective x)
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
    IsRupert (univ.image x) ∨ Resid08Final' (x 0) (x 6) (x 3) (x 4) (x 5) (x 1) (x 2) := by
  classical
  obtain ⟨-, eV⟩ := image_seven x
  rw [eV]
  obtain ⟨F, hcap⟩ := exists_type08_cap x hx fA fB fC fD fE fF fG hA hB hC hD hE hF hG
  exact type08_rupert_or_resid_pts' F hcap



end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.type08_rupert_or_resid'
