module

public import Minimality.Type08S.P2RDefs
public import Minimality.Type08S.P2RR0
public import Minimality.Type08S.P2RR1
public import Minimality.Type08S.P2RR6
public import Minimality.Type08S.P2RR2e
public import Minimality.Type08S.P2RR3
public import Minimality.Type08S.P2RR4i
public import Minimality.Type08S.P2RR5

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# Type 08, plan 2 (final integration J, package pkR): `Resid08FinalJ` and `type08_rupert_or_residJ`

The codim >= 3 special positions of `Resid08FinalI` closed by lexicographic cells (Theorem 24.1, `isRupert_of_lexCell`):
L1 empty (R1), N2 weak far triple with AngBig (R2), the level face at T' (R3), alpha4 = 1 with C < 0 (R4, `lexCell_TpA1_i`),
the P3 tie at T' with D_c < 0 (R5, `lexCell_P3Tp_n`), the QacTop split (R6).  New named leftovers `TpA1ii`, `P3Tpii`.
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality

theorem isRupert_of_hasLexCell (V : Finset ℝ³) (h : HasLexCell V) : IsRupert V := by
  obtain ⟨u₀, hu₀, k, hk, x, v, hc⟩ := h
  exact isRupert_of_lexCell V u₀ v hu₀ x hc

namespace Type08Sp

/-! ## Assembly (proved) -/

theorem bd_ne {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) : b - d ≠ 0 :=
  sub_ne_zero.mpr (Ne.symm N.hd.ne.2.2.1)

theorem rupert_of_at {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (h : HasLexCellAt (V8 a a' b b' c c' d) (b - d)) : IsRupert (V8 a a' b b' c c' d) :=
  isRupert_of_hasLexCell _ ⟨b - d, bd_ne N, h⟩

/-- The level face at `T'`: `α4 < 1` (tree `Tp_level_sep`) and `α4 > 1` (R3) are Rupert; `α4 = 1` has `C = 0`, so it is
the leftover `TpA1ii` (which needs the HDN and `¬ CaseATp` conjuncts from the caller). -/
theorem levTp_rupert_or {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hT' : IsT' a b c' d)
    (hlev : LevelQac a b c d) (hX : ¬ NoHDNAt ({d, a, b', c} : Finset ℝ³) (b - d)) (hA : ¬ CaseATp a b b' c d) :
    IsRupert (V8 a a' b b' c c' d) ∨ TpA1ii a a' b b' c c' d := by
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hα4, hγ4, hαγ, hβ1, hβ6, hγ6, hγ61, hcv⟩ :=
    norm08_coordsTp' N hT'
  rcases lt_trichotomy α4 1 with hlt | heq | hgt
  · exact Or.inl (Tp_level_sep N hT' hlev hb' hlt)
  · right
    have e1 : ⟪a, b - d⟫ = ⟪d, b - d⟫ := by
      have := hlev.1; rw [inner_sub_left] at this; linarith
    have e2 : ⟪c, b - d⟫ = ⟪d, b - d⟫ := by
      have := hlev.2; rw [inner_sub_left] at this; linarith
    have e3 : ⟪b', b - d⟫ = ⟪d, b - d⟫ := by
      rw [hb', inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
        inner_sub_left, inner_sub_left, e1, e2]
      ring
    refine ⟨hT', ?_, ?_, ?_, hX, hA⟩
    · unfold QacTop; rw [e1, e2, e3]
    · unfold Al4One; rw [det_alpha hb', heq, sub_self, zero_mul]
    · rw [inner_sub_left, e2, sub_self]
  · exact Or.inl (rupert_of_at N (lexCell_levTp N hT' hlev ⟨α4, γ4, hb', hgt⟩))

/-- **At `T`.** -/
theorem s4T2_rupert_or_R {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (h : S4T2 a a' b b' c c' d) :
    IsRupert (V8 a a' b b' c c' d) ∨ S4TR a a' b b' c c' d := by
  have ws : IsT a' b c d → ¬ RobKb a a' b b' c c' d → N2WST a' b b' c c' d → AngBig a b b' c d →
      IsRupert (V8 a a' b b' c c' d) :=
    fun hT hB hw hang => rupert_of_at N (lexCell_N2WS N ⟨hT, hB, hw⟩ hang)
  rcases h with ⟨hT, ⟨h1, heq⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2⟩⟩ |
      ⟨hT, hB, ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4, h5⟩⟩
  · exact (touchT_eq_false N hT h1 heq).elim
  · rcases (h1.2.2).eq_or_lt with heq | hlt
    · exact (touchT_eq_false N hT h1 heq).elim
    · exact Or.inr ⟨hT, Or.inl ⟨h1, hlt, h2, h3⟩⟩
  · rcases caseB_Xba N hT h1 with hX | hw
    · exact absurd hX h3
    · exact Or.inl (ws hT h1 hw h2)
  · rcases caseB_Xba N hT h1 with hX | hw
    · have hXh : ¬ NoHDNAt ({b, c', b', a'} : Finset ℝ³) (b - d) := fun hn => h4 ⟨hX, hn⟩
      by_cases hRP : ⟪c', b - d⟫ = ⟪b', b - d⟫
      · exact Or.inr ⟨hT, Or.inr (Or.inr (Or.inl ⟨h1, hX, h2, hRP, hXh, h3⟩))⟩
      · exact Or.inl (cellXba2_rupert N hT h1 h2 hX hRP)
    · exact Or.inr ⟨hT, Or.inr (Or.inl ⟨h1, hw, h2, h3⟩)⟩
  · exact Or.inr ⟨hT, Or.inr (Or.inr (Or.inr ⟨h1, h2⟩))⟩
  · exact Or.inl (ws hT hB h1 h2)
  · exact Or.inr ⟨hT, Or.inr (Or.inl ⟨hB, h1, h2, h3⟩)⟩
  · exact Or.inr ⟨hT, Or.inr (Or.inr (Or.inl ⟨hB, h1, h2, h3, h4, h5⟩))⟩

/-- `Al4One` with `QacTop`: case (i) is Rupert, case (ii) is the leftover. -/
theorem tpA1_rupert_or {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hT' : IsT' a b c' d)
    (hq : QacTop a b b' c d) (h1 : Al4One a b b' c d) (hX : ¬ NoHDNAt ({d, a, b', c} : Finset ℝ³) (b - d))
    (hA : ¬ CaseATp a b b' c d) : IsRupert (V8 a a' b b' c c' d) ∨ TpA1ii a a' b b' c c' d := by
  by_cases hC : ⟪c - d, b - d⟫ < 0
  · exact Or.inl (rupert_of_at N (lexCell_TpA1_i N hT' hq h1 hC))
  · exact Or.inr ⟨hT', hq, h1, not_lt.mp hC, hX, hA⟩

/-- **At `T'`.** -/
theorem s4TpG2_rupert_or_R {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (h : S4TpG2 a a' b b' c c' d) :
    IsRupert (V8 a a' b b' c c' d) ∨ (S4TpR a a' b b' c c' d ∨ TpA1ii a a' b b' c c' d ∨
      P3Tpii a a' b b' c c' d) := by
  obtain ⟨hT', hq, ⟨hlev, -, α4, γ4, hb', hgt⟩ | ⟨hX, h2, hA⟩⟩ := h
  · exact Or.inl (rupert_of_at N (lexCell_levTp N hT' hlev ⟨α4, γ4, hb', hgt⟩))
  rcases tpQacTop_cases N hT' hq hA with hlev | h1 | h3 | ⟨htie, hnl, hlt, h1⟩
  · exact (levTp_rupert_or N hT' hlev hX hA).imp id (fun h => Or.inr (Or.inl h))
  · exact (tpA1_rupert_or N hT' hq h1 hX hA).imp id (fun h => Or.inr (Or.inl h))
  · by_cases h1 : Al4One a b b' c d
    · exact (tpA1_rupert_or N hT' hq h1 hX hA).imp id (fun h => Or.inr (Or.inl h))
    · by_cases hD : ⟪c - d, b - d⟫ < 0
      · exact Or.inl (rupert_of_at N (lexCell_P3Tp_n N h3 h1 hD))
      · rcases h2 with h2 | h2
        · exact Or.inr (Or.inr (Or.inr ⟨h3, h1, not_lt.mp hD, hX, h2, hA⟩))
        · exact absurd h2 h1
  · rcases h2 with h2 | h2
    · exact Or.inr (Or.inl ⟨hT', hq, htie, hnl, hlt, hX, h2, hA⟩)
    · exact absurd h2 h1

theorem resNH_rupert_or_J {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (h : ResNH N)
    (hL : ¬ HasLexCell (V8 a a' b b' c c' d)) : IsRupert (V8 a a' b b' c c' d) ∨ ResNJ N := by
  obtain ⟨h1, h2 | h2⟩ := h
  · rcases s4T2_rupert_or_R N h2 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h1, Or.inl h, hL⟩
  · rcases s4TpG2_rupert_or_R N h2 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h1, Or.inr h, hL⟩

theorem residNH_rupert_or_J {p p' q q' r r' d : ℝ³} {V : Finset ℝ³} (hset : V8 p p' q q' r r' d = V)
    (h : ResidNH p p' q q' r r' d) (hL : ¬ HasLexCell V) : IsRupert V ∨ ResidNJ p p' q q' r r' d := by
  obtain ⟨N, hN⟩ := h
  subst hset
  rcases resNH_rupert_or_J N hN hL with h | h
  · exact Or.inl h
  · exact Or.inr ⟨N, h⟩

/-- **`I → Rupert ∨ J`.** -/
theorem resid08FinalI_rupert_or_J {a a' b b' c c' d : ℝ³} (h : Resid08FinalI a a' b b' c c' d) :
    IsRupert (V8 a a' b b' c c' d) ∨ Resid08FinalJ a a' b b' c c' d := by
  by_cases hL : HasLexCell (V8 a a' b b' c c' d)
  · exact Or.inl (isRupert_of_hasLexCell _ hL)
  have e := type08_set_perm a a' b b' c c' d
  rcases h with ⟨hp, hr⟩ | h | h | h | h | h | h
  · exact Or.inr (Or.inl ⟨hp, hr, hL⟩)
  · exact (residNH_rupert_or_J rfl h hL).imp id (fun r => Or.inr (Or.inl r))
  · exact (residNH_rupert_or_J e.2.1 h hL).imp id (fun r => Or.inr (Or.inr (Or.inl r)))
  · exact (residNH_rupert_or_J e.2.2.1 h hL).imp id (fun r => Or.inr (Or.inr (Or.inr (Or.inl r))))
  · exact (residNH_rupert_or_J e.2.2.2.1 h hL).imp id
      (fun r => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl r)))))
  · exact (residNH_rupert_or_J e.2.2.2.2.1 h hL).imp id
      (fun r => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl r))))))
  · exact (residNH_rupert_or_J e.2.2.2.2.2 h hL).imp id
      (fun r => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr r))))))

/-- **Point form of the target.** -/
theorem type08_rupert_or_resid_ptsJ {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap F d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨ Resid08FinalJ a a' b b' c c' d := by
  rcases type08_rupert_or_resid_ptsI F hd with h | h
  · exact Or.inl h
  · exact resid08FinalI_rupert_or_J h

/-- **Facet form** (the integration point; same hypotheses as `type08_rupert_or_residI`). -/
theorem type08_rupert_or_residJ (x : Fin 7 → ℝ³) (hx : Function.Injective x)
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
    IsRupert (univ.image x) ∨ Resid08FinalJ (x 0) (x 6) (x 3) (x 4) (x 5) (x 1) (x 2) := by
  classical
  obtain ⟨-, eV⟩ := image_seven x
  rw [eV]
  obtain ⟨F, hcap⟩ := exists_type08_cap x hx fA fB fC fD fE fF fG hA hB hC hD hE hF hG
  exact type08_rupert_or_resid_ptsJ F hcap

/-- The new target implies the tree's (`Resid08FinalJ ⊆ Resid08FinalI`). -/
theorem type08_rupert_or_residJ_imp_I (x : Fin 7 → ℝ³) {V : Finset ℝ³}
    (h : IsRupert V ∨ Resid08FinalJ (x 0) (x 6) (x 3) (x 4) (x 5) (x 1) (x 2)) :
    IsRupert V ∨ Resid08FinalI (x 0) (x 6) (x 3) (x 4) (x 5) (x 1) (x 2) :=
  h.imp id resid08FinalJ_imp_I

end Type08Sp
end Minimality
