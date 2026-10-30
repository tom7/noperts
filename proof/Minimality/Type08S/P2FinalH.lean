module

public import Minimality.Type08S.P2FinalG
public import Minimality.Type08S.P2TL2
public import Minimality.Type08S.P2TT2
public import Minimality.Type08S.P2TA1c
public import Minimality.Type08S.P2TA2d
public import Minimality.Type08S.P2TBt3

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true

set_option linter.unusedVariables false

/-!
# Type 08, plan 2 (final integration H): `Resid08FinalH` and `type08_rupert_or_residH`

As `Resid08FinalG`, with the case at `T` (P1, package pkP: `P2T*`) closed down to the codim-4 leftover
`S4T2 = S4T' ∨ S4TB`: the refined limit theorem at `T` (`isRupert_type08_limit_T`), touching
(`close_touchT`), `K_b` with non-persistent / persistent HDN (`close_hdn_np_KbT`, `close_hdn_pers_KbT`), and case B
(`close_caseB_T`: cells (−,−,−) and (+,−,−), 18.3 on `X_ba'`, the slide of `K_2`).
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- The full leftover at `T` (codim 4): `S4T'` (touching L1/L2, the persistent-`K_b` valve L5) or case B's `S4TB`. -/
def S4T2 (a a' b b' c c' d : ℝ³) : Prop := S4T' a a' b b' c c' d ∨ S4TB a a' b b' c c' d

theorem close_T_sig4 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hT : IsT a' b c d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨ S4T2 a a' b b' c c' d := by
  rcases isRupert_type08_limit_T N hT with h | h | ⟨hA, s, h⟩ | ⟨hB, s, h⟩
  · exact Or.inl h
  · exact (close_touchT N hT h).imp id Or.inl
  · obtain ⟨k', hk', σ, hrim, hrob, -⟩ := h
    by_cases hnp : NoPersistHDN (fun i => pts08 a a' b b' c c' d ((test08 1 s true).lab (σ i)))
        ((test08 1 s true).view (pts08 a a' b b' c c' d)) (eF a a' b b' c c' d (1, s, true))
    · exact Or.inl (close_hdn_np_KbT N hT hrim hrob hnp)
    · exact (close_hdn_pers_KbT N hT hrim hrob hnp).imp id Or.inl
  · exact (close_caseB_T N hT hB h).imp id Or.inr

theorem S4T2_isT {a a' b b' c c' d : ℝ³} (h : S4T2 a a' b b' c c' d) : IsT a' b c d := by
  rcases h with h | h
  · exact h.1
  · exact h.1

/-- **The residual in the labelling of `N`** (H). -/
def ResNH {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) : Prop :=
  ResNC' N ∧ (S4T2 a a' b b' c c' d ∨ S4TpG2 a a' b b' c c' d)

theorem norm08_rupert_or_resNH {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨ ResNH N := by
  rcases norm08_rupert_or_resNG N with h | ⟨h1, hT | h2⟩
  · exact Or.inl h
  · rcases close_T_sig4 N hT with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h1, Or.inl h⟩
  · exact Or.inr ⟨h1, Or.inr h2⟩

theorem resNH_imp_resNG {a a' b b' c c' d : ℝ³} {N : Norm08 a a' b b' c c' d} (h : ResNH N) :
    ResNG N :=
  ⟨h.1, h.2.imp S4T2_isT id⟩

def ResidNH (a a' b b' c c' d : ℝ³) : Prop := ∃ N : Norm08 a a' b b' c c' d, ResNH N

theorem wrapNH {p p' q q' r r' d : ℝ³} (N : Norm08 p p' q q' r r' d) {V : Finset ℝ³}
    (hset : insert d ({p, p', q, q', r, r'} : Finset ℝ³) = V) :
    IsRupert V ∨ ResidNH p p' q q' r r' d := by
  rcases norm08_rupert_or_resNH N with h | h
  · exact Or.inl (hset ▸ h)
  · exact Or.inr ⟨N, h⟩

/-- **`Resid08FinalH`**, on the seven points `(a, a', b, b', c, c', d)`. -/
def Resid08FinalH (a a' b b' c c' d : ℝ³) : Prop :=
  PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d ∨
  ResidNH a a' b b' c c' d ∨ ResidNH b b' a a' c c' d ∨ ResidNH a a' c c' b b' d ∨
  ResidNH c c' a a' b b' d ∨ ResidNH b b' c c' a a' d ∨ ResidNH c c' b b' a a' d

theorem resid08FinalH_imp_G {a a' b b' c c' d : ℝ³} (h : Resid08FinalH a a' b b' c c' d) :
    Resid08FinalG a a' b b' c c' d := by
  have g : ∀ {p p' q q' r r' : ℝ³}, ResidNH p p' q q' r r' d → ResidNG p p' q q' r r' d :=
    fun ⟨N, hN⟩ => ⟨N, resNH_imp_resNG hN⟩
  rcases h with h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl (g h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (g h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (g h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (g h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (g h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (g h)))))))

theorem type08_rupert_or_resid_ptsH {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap F d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨ Resid08FinalH a a' b b' c c' d := by
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
      · exact Or.inr (Or.inr (Or.inr (Or.inl r)))
    · rcases wrapNH ⟨F.perm₁₂, hd.perm₁₂, G'.perm₁₂, hpos _ _ h1, hpos _ _ h2, hne _ _ hκc,
        hneg _ _ h3⟩ e.2.1 with r | r
      · exact Or.inl r
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl r))))
    · rcases wrapNH ⟨F.perm₂₃, hd.perm₂₃, G'.perm₂₃, hpos _ _ h1, hpos _ _ h2, hne _ _ hκb,
        hneg _ _ h3⟩ e.2.2.1 with r | r
      · exact Or.inl r
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl r)))))
    · rcases wrapNH ⟨F.perm₂₃.perm₁₂, hd.perm₂₃.perm₁₂, G'.perm₂₃.perm₁₂, hpos _ _ h1,
        hpos _ _ h2, hne _ _ hκb, hneg _ _ h3⟩ e.2.2.2.1 with r | r
      · exact Or.inl r
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl r))))))
    · rcases wrapNH ⟨F.perm₁₂.perm₂₃, hd.perm₁₂.perm₂₃, G'.perm₁₂.perm₂₃, hpos _ _ h1,
        hpos _ _ h2, hne _ _ hκa, hneg _ _ h3⟩ e.2.2.2.2.1 with r | r
      · exact Or.inl r
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl r)))))))
    · rcases wrapNH ⟨F.perm₁₂.perm₂₃.perm₁₂, hd.perm₁₂.perm₂₃.perm₁₂, G'.perm₁₂.perm₂₃.perm₁₂,
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
theorem type08_rupert_or_residH (x : Fin 7 → ℝ³) (hx : Function.Injective x)
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
    IsRupert (univ.image x) ∨ Resid08FinalH (x 0) (x 6) (x 3) (x 4) (x 5) (x 1) (x 2) := by
  classical
  obtain ⟨-, eV⟩ := image_seven x
  rw [eV]
  obtain ⟨F, hcap⟩ := exists_type08_cap x hx fA fB fC fD fE fF fG hA hB hC hD hE hF hG
  exact type08_rupert_or_resid_ptsH F hcap




end Type08Sp
end Minimality
