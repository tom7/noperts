module

public import Minimality.Type08S.P2I9b
public import Minimality.Type08S.P2E3
public import Minimality.Type08S.P2FIN1
public import Minimality.Type08S.P2CE3

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true

set_option linter.unusedVariables false

/-!
# Type 08, plan 2 (final integration E): `Resid08FinalE` and `type08_rupert_or_residE`

In a Lemma-6 labelling (`Norm08`): at `T` (`P1`, package `close_T_sig4`, unproved) the case is residual;
at `T'` the proved pieces (`close_Tp_X`, `close_T'2'`, R3, R4h, level, dichotomy) are used and the residual
is `S4Tp` or the hypotheses of the two unproved pieces `Tp_poked`, `Tp_far`; otherwise the Q region
(`region_Q`), the refined limit theorem `isRupert_type08_limit_hdnR'` and the HDN closings
(`close_hdn_np`, `close_hdn_pers_full`) are all proved.  The planar items are as in `Resid08FinalC`.
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- Q region is Rupert outright. -/
theorem region_Q {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (h : RegQ N.F) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) :=
  close_caseQ N.F N.hd h.1 h.2

/-- P3 assembled (non-persistent and persistent HDN closings). -/
theorem close_hdn {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (hT : ¬ IsT a' b c d) (hT' : ¬ IsT' a b c' d) {t : Fin 3 × Bool × Bool} (ht : t ∈ SC08)
    (hreg : (t.1 = 0 ∧ RegN2 N.F) ∨ (t.1 = 1 ∧ RegT4 N.F)) (h : RobHDN a a' b b' c c' d t) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  classical
  obtain ⟨k', hk', σ, hrim, hrob, -⟩ := h
  by_cases hnp : NoPersistHDN (fun i => pts08 a a' b b' c c' d ((test08 t.1 t.2.1 t.2.2).lab (σ i)))
      ((test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d)) (eF a a' b b' c c' d t)
  · exact close_hdn_np N hT hT' ht hreg hrim hrob hnp
  · exact close_hdn_pers_full N hT hT' ht hreg hrim hrob hnp

/-- **The residual in the labelling of `N`**: the old `ResNC N` (so provably no larger than C) together with:
`IsT a' b c d`: the case at `T` (package P1
`close_T_sig4`, unproved); `S4Tp`, `TpPokedH`, `TpFarH`: the case at `T'` (Σ₄ leftover and the hypotheses
of the unproved pieces `Tp_poked`, `Tp_far`). -/
def ResNE {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) : Prop :=
  ResNC N ∧ (IsT a' b c d ∨ TpResE N)

theorem norm08_rupert_or_resNE {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨ ResNE N := by
  classical
  by_cases hT : IsT a' b c d
  · rcases norm08_rupert_or_resNC N with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, Or.inl hT⟩
  by_cases hT' : IsT' a b c' d
  · rcases close_T'_sig4E N hT' with h | h
    · exact Or.inl h
    · rcases norm08_rupert_or_resNC N with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨h', Or.inr h⟩
  by_cases hQ : RegQ N.F
  · exact Or.inl (region_Q N hQ)
  rcases isRupert_type08_limit_hdnR' N hT hT' hQ with h | ⟨t, ht, hreg, hr⟩
  · exact Or.inl h
  · exact Or.inl (close_hdn N hT hT' ht hreg hr)

/-- `ResNE` for some `Norm08` structure in the labelling `(a, b, c)`. -/
def ResidNE (a a' b b' c c' d : ℝ³) : Prop := ∃ N : Norm08 a a' b b' c c' d, ResNE N

theorem wrapNE {p p' q q' r r' d : ℝ³} (N : Norm08 p p' q q' r r' d) {V : Finset ℝ³}
    (hset : insert d ({p, p', q, q', r, r'} : Finset ℝ³) = V) :
    IsRupert V ∨ ResidNE p p' q q' r r' d := by
  rcases norm08_rupert_or_resNE N with h | h
  · exact Or.inl (hset ▸ h)
  · exact Or.inr ⟨N, h⟩

/-- **`Resid08FinalE`**, on the seven points `(a, a', b, b', c, c', d)`. -/
def Resid08FinalE (a a' b b' c c' d : ℝ³) : Prop :=
  PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d ∨
  ResidNE a a' b b' c c' d ∨ ResidNE b b' a a' c c' d ∨ ResidNE a a' c c' b b' d ∨
  ResidNE c c' a a' b b' d ∨ ResidNE b b' c c' a a' d ∨ ResidNE c c' b b' a a' d

theorem type08_rupert_or_resid_ptsE {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap F d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨ Resid08FinalE a a' b b' c c' d := by
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
    · rcases wrapNE (V := insert d ({a, a', b, b', c, c'} : Finset ℝ³))
        ⟨F, hd, G', hpos _ _ h1, hpos _ _ h2, hne _ _ hκc, hneg _ _ h3⟩ rfl with r | r
      · exact Or.inl r
      · exact Or.inr (Or.inr (Or.inr (Or.inl r)))
    · rcases wrapNE ⟨F.perm₁₂, hd.perm₁₂, G'.perm₁₂, hpos _ _ h1, hpos _ _ h2, hne _ _ hκc,
        hneg _ _ h3⟩ e.2.1 with r | r
      · exact Or.inl r
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl r))))
    · rcases wrapNE ⟨F.perm₂₃, hd.perm₂₃, G'.perm₂₃, hpos _ _ h1, hpos _ _ h2, hne _ _ hκb,
        hneg _ _ h3⟩ e.2.2.1 with r | r
      · exact Or.inl r
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl r)))))
    · rcases wrapNE ⟨F.perm₂₃.perm₁₂, hd.perm₂₃.perm₁₂, G'.perm₂₃.perm₁₂, hpos _ _ h1,
        hpos _ _ h2, hne _ _ hκb, hneg _ _ h3⟩ e.2.2.2.1 with r | r
      · exact Or.inl r
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl r))))))
    · rcases wrapNE ⟨F.perm₁₂.perm₂₃, hd.perm₁₂.perm₂₃, G'.perm₁₂.perm₂₃, hpos _ _ h1,
        hpos _ _ h2, hne _ _ hκa, hneg _ _ h3⟩ e.2.2.2.2.1 with r | r
      · exact Or.inl r
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl r)))))))
    · rcases wrapNE ⟨F.perm₁₂.perm₂₃.perm₁₂, hd.perm₁₂.perm₂₃.perm₁₂, G'.perm₁₂.perm₂₃.perm₁₂,
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
theorem type08_rupert_or_residE (x : Fin 7 → ℝ³) (hx : Function.Injective x)
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
    IsRupert (univ.image x) ∨ Resid08FinalE (x 0) (x 6) (x 3) (x 4) (x 5) (x 1) (x 2) := by
  classical
  obtain ⟨-, eV⟩ := image_seven x
  rw [eV]
  obtain ⟨F, hcap⟩ := exists_type08_cap x hx fA fB fC fD fE fF fG hA hB hC hD hE hF hG
  exact type08_rupert_or_resid_ptsE F hcap



theorem resNE_imp_resNC {a a' b b' c c' d : ℝ³} {N : Norm08 a a' b b' c c' d} (h : ResNE N) :
    ResNC N := h.1

theorem resid08FinalE_imp_C {a a' b b' c c' d : ℝ³} (h : Resid08FinalE a a' b b' c c' d) :
    Resid08FinalC a a' b b' c c' d := by
  have g : ∀ {p p' q q' r r' : ℝ³}, ResidNE p p' q q' r r' d → ResidNC p p' q q' r r' d :=
    fun ⟨N, hN⟩ => ⟨N, hN.1⟩
  rcases h with h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl (g h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (g h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (g h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (g h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (g h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (g h)))))))

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.type08_rupert_or_residE
#print axioms Minimality.Type08Sp.resid08FinalE_imp_C
