module

public import Minimality.Type08S.SCl

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true

set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp


theorem rupert_of_SCcl2 {a a' b b' c c' d : ℝ³} {t : Fin 3 × Bool × Bool}
    (h : SCcl2 a a' b b' c c' d t) : IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  rcases h with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
  · exact rupert_SCfN2' h
  · have := rupert_SCfT4' h
    convert this using 1
    ext y; simp only [mem_insert, mem_singleton]; tauto
  · have := rupert_SCfT4' h
    convert this using 1
    ext y; simp only [mem_insert, mem_singleton]; tauto

/-- **Refined limit theorem.**  Rupert, or a single-circle closing `t` with certified limit rim and
an HDN at its view that does not satisfy the explicit class-(c) predicate `ClassCt`. -/
theorem isRupert_type08_limit_hdnC {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    {q : ℕ} (hq : q ≤ 2) (ties : Fin q → Fin 3 × Fin 7 × Fin 7)
    (hties : ∀ t, ⟪pts08 a a' b b' c c' d (ties t).2.1 - pts08 a a' b b' c c' d (ties t).2.2,
      (grp08 (ties t).1).view (pts08 a a' b b' c c' d)⟫ = 0)
    (hind : TieIndep (fun t => pts08 a a' b b' c c' d (ties t).2.1 - pts08 a a' b b' c c' d (ties t).2.2)
      (fun t => (grp08 (ties t).1).view (pts08 a a' b b' c c' d)))
    (hcover : ∀ i, ∀ T ∈ (grp08 i).tests, ∀ u v : ZMod T.k,
      T.depth (pts08 a a' b b' c c' d) u = T.depth (pts08 a a' b b' c c' d) v →
      Relation.EqvGen (fun p p' => ∃ t, (ties t).1 = i ∧ (ties t).2 = (p, p')) (T.lab u) (T.lab v))
    (hnt : ¬ Touch a a' b b' c c' d)
    (hTco : IsT a' b c d → ¬ CoT2 a a' b b' c c' d)
    (hT'co : IsT' a b c' d → ¬ CoT'2 a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨
      ∃ t ∈ SC08,
        (∃ (k' : ℕ) (_ : NeZero k') (σ : ZMod k' → ZMod (test08 t.1 t.2.1 t.2.2).k),
          RimCertAt (pts08 a a' b b' c c' d) ((test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d))
            ((test08 t.1 t.2.1 t.2.2).lab ∘ σ)) ∧
        ¬ NoHDNAt (insert d ({a, a', b, b', c, c'} : Finset ℝ³))
          ((test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d)) ∧
        ¬ ClassCt a a' b b' c c' d t := by
  classical
  rcases isRupert_type08_limit_hdn_rim N hq ties hties hind hcover hnt hTco hT'co with h | ⟨t, ht, hr, hn⟩
  · exact Or.inl h
  · by_cases hs : ClassCt a a' b b' c c' d t
    · exact Or.inl (rupert_of_SCcl2 (SCcl2_of_ClassCt N hs))
    · exact Or.inr ⟨t, ht, hr, hn, hs⟩

/-- **The residual in the labelling of `N`.** -/
def ResNC {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) : Prop :=
  (TieN2 a a' b b' c c' ∧ ¬ N2Closable N) ∨
  (TieT4 b b' c c' d ∧ ¬ T4Closable N) ∨
  ¬ TieOK a a' b b' c c' d ∨
  (∃ t ∈ SC08, ¬ NoHDNAt (insert d ({a, a', b, b', c, c'} : Finset ℝ³))
    ((test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d)) ∧ ¬ ClassCt a a' b b' c c' d t) ∨
  (IsT a' b c d ∧ CoT2 a a' b b' c c' d) ∨
  (IsT' a b c' d ∧ CoT'2 a a' b b' c c' d)

theorem norm08_rupert_or_resNC {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨ ResNC N := by
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
  rcases isRupert_type08_limit_hdnC N hq ties ht hi hcov hnt (fun h hc => hT ⟨h, hc⟩)
      (fun h hc => hT' ⟨h, hc⟩) with h | h
  · exact Or.inl h
  · obtain ⟨t, ht, -, hn, hs⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨t, ht, hn, hs⟩))))

/-- `ResN` for some `Norm08` structure in the labelling `(a, b, c)`. -/
def ResidNC (a a' b b' c c' d : ℝ³) : Prop := ∃ N : Norm08 a a' b b' c c' d, ResNC N

theorem wrapNC {p p' q q' r r' d : ℝ³} (N : Norm08 p p' q q' r r' d) {V : Finset ℝ³}
    (hset : insert d ({p, p', q, q', r, r'} : Finset ℝ³) = V) :
    IsRupert V ∨ ResidNC p p' q q' r r' d := by
  rcases norm08_rupert_or_resNC N with h | h
  · exact Or.inl (hset ▸ h)
  · exact Or.inr ⟨N, h⟩

/-- **`Resid08FinalC`**, on the seven points `(a, a', b, b', c, c', d)`. -/
def Resid08FinalC (a a' b b' c c' d : ℝ³) : Prop :=
  PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d ∨
  ResidNC a a' b b' c c' d ∨ ResidNC b b' a a' c c' d ∨ ResidNC a a' c c' b b' d ∨
  ResidNC c c' a a' b b' d ∨ ResidNC b b' c c' a a' d ∨ ResidNC c c' b b' a a' d

theorem type08_rupert_or_resid_ptsC {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap F d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨ Resid08FinalC a a' b b' c c' d := by
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
    · rcases wrapNC (V := insert d ({a, a', b, b', c, c'} : Finset ℝ³))
        ⟨F, hd, G', hpos _ _ h1, hpos _ _ h2, hne _ _ hκc, hneg _ _ h3⟩ rfl with r | r
      · exact Or.inl r
      · exact Or.inr (Or.inr (Or.inr (Or.inl r)))
    · rcases wrapNC ⟨F.perm₁₂, hd.perm₁₂, G'.perm₁₂, hpos _ _ h1, hpos _ _ h2, hne _ _ hκc,
        hneg _ _ h3⟩ e.2.1 with r | r
      · exact Or.inl r
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl r))))
    · rcases wrapNC ⟨F.perm₂₃, hd.perm₂₃, G'.perm₂₃, hpos _ _ h1, hpos _ _ h2, hne _ _ hκb,
        hneg _ _ h3⟩ e.2.2.1 with r | r
      · exact Or.inl r
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl r)))))
    · rcases wrapNC ⟨F.perm₂₃.perm₁₂, hd.perm₂₃.perm₁₂, G'.perm₂₃.perm₁₂, hpos _ _ h1,
        hpos _ _ h2, hne _ _ hκb, hneg _ _ h3⟩ e.2.2.2.1 with r | r
      · exact Or.inl r
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl r))))))
    · rcases wrapNC ⟨F.perm₁₂.perm₂₃, hd.perm₁₂.perm₂₃, G'.perm₁₂.perm₂₃, hpos _ _ h1,
        hpos _ _ h2, hne _ _ hκa, hneg _ _ h3⟩ e.2.2.2.2.1 with r | r
      · exact Or.inl r
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl r)))))))
    · rcases wrapNC ⟨F.perm₁₂.perm₂₃.perm₁₂, hd.perm₁₂.perm₂₃.perm₁₂, G'.perm₁₂.perm₂₃.perm₁₂,
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
theorem type08_rupert_or_residC (x : Fin 7 → ℝ³) (hx : Function.Injective x)
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
    IsRupert (univ.image x) ∨ Resid08FinalC (x 0) (x 6) (x 3) (x 4) (x 5) (x 1) (x 2) := by
  classical
  obtain ⟨-, eV⟩ := image_seven x
  rw [eV]
  obtain ⟨F, hcap⟩ := exists_type08_cap x hx fA fB fC fD fE fF fG hA hB hC hD hE hF hG
  exact type08_rupert_or_resid_ptsC F hcap



end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.type08_rupert_or_residC
#print axioms Minimality.Type08Sp.isRupert_type08_limit_hdnC
#print axioms Minimality.Type08Sp.SCcl2_of_ClassCt
