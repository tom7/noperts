module

public import Minimality.Type08S.P2S6
public import Minimality.Type08S.P2FinalF

@[expose] public section

set_option relaxedAutoImplicit true
set_option autoImplicit true
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {a a' b b' c c' d : ℝ³}

/-- Level face: the separation is automatic, so T′S applies (needs only `α4 < 1`). -/
theorem Tp_level_sep (N : Norm08 a a' b b' c c' d) (hT' : IsT' a b c' d) (hlev : LevelQac a b c d)
    {α4 γ4 : ℝ} (hrep : b' = d + α4 • (a - d) + γ4 • (c - d)) (hα : α4 < 1) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨β1, β6, γ6, hne, hc', ha', hα4, hγ4, hαγ, hβ1, hβ6, hγ6, hγ61⟩ := Tp_frame N hT' hrep
  have hdb : d ≠ b := N.hd.ne.2.2.1
  have hn : 0 < ⟪b - d, b - d⟫ := real_inner_self_pos.mpr (sub_ne_zero.mpr (Ne.symm hdb))
  obtain ⟨l1, l2⟩ := hlev
  have e1 : ⟪a - d, b - d⟫ = ⟪a, b - d⟫ - ⟪d, b - d⟫ := inner_sub_left _ _ _
  have e2 : ⟪c - d, b - d⟫ = ⟪c, b - d⟫ - ⟪d, b - d⟫ := inner_sub_left _ _ _
  have e3 : ⟪b - d, b - d⟫ = ⟪b, b - d⟫ - ⟪d, b - d⟫ := inner_sub_left _ _ _
  have e4 : ⟪b' - d, b - d⟫ = ⟪b', b - d⟫ - ⟪d, b - d⟫ := inner_sub_left _ _ _
  have e5 : ⟪c' - d, b - d⟫ = ⟪c', b - d⟫ - ⟪d, b - d⟫ := inner_sub_left _ _ _
  have e6 : ⟪b' - d, b - d⟫ = α4 * ⟪a - d, b - d⟫ + γ4 * ⟪c - d, b - d⟫ := by
    have : b' - d = α4 • (a - d) + γ4 • (c - d) := by rw [hrep]; module
    rw [this, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have e7 : ⟪c' - d, b - d⟫ = ⟪a - d, b - d⟫ + β1 * ⟪b - d, b - d⟫ := by
    have : c' - d = (a - d) + β1 • (b - d) := by rw [hc']; module
    rw [this, inner_add_left, real_inner_smul_left]
  refine Tp_sep N hT' hrep hα ?_
  simp only [max_lt_iff, lt_min_iff]
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith [mul_pos hβ1 hn]

/-- `S4Tp` with the `R4ppEnd` disjunct removed and the level item restricted to `α4 > 1`. -/
def S4TpG (a a' b b' c c' d : ℝ³) : Prop :=
  IsT' a b c' d ∧ QacTop a b b' c d ∧
    ((LevelQac a b c d ∧ ¬ NoHDNAt ({b, c', b', c} : Finset ℝ³) (b - d) ∧
        ∃ α4 γ4 : ℝ, b' = d + α4 • (a - d) + γ4 • (c - d) ∧ 1 < α4) ∨
     (¬ NoHDNAt ({d, a, b', c} : Finset ℝ³) (b - d) ∧
       (TpHDN2 a b b' c c' d ∨ det3 (b' - a) (c - d) (b - d) = 0)))

theorem S4TpG_imp (h : S4TpG a a' b b' c c' d) : S4Tp a a' b b' c c' d := by
  obtain ⟨h1, h2, h3 | ⟨h3, h4 | h4⟩⟩ := h
  · exact ⟨h1, h2, Or.inl ⟨h3.1, h3.2.1⟩⟩
  · exact ⟨h1, h2, Or.inr ⟨h3, Or.inl h4⟩⟩
  · exact ⟨h1, h2, Or.inr ⟨h3, Or.inr (Or.inl h4)⟩⟩

/-- The `QacTop` core: no `R4ppEnd`, no `TpPokedH`, no `TpFarH`. -/
theorem close_Tp_hdn_caseG (N : Norm08 a a' b b' c c' d) (hT' : IsT' a b c' d)
    (hq : QacTop a b b' c d)
    (hX : ¬ NoHDNAt ({d, a, b', c} : Finset ℝ³) (b - d))
    (hS : ¬ (TpHDN2 a b b' c c' d ∨ det3 (b' - a) (c - d) (b - d) = 0)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  push Not at hS
  obtain ⟨hS1, hS2⟩ := hS
  obtain ⟨h2c, hbc⟩ := Tp_other_noHDN N hX hS1
  by_cases h2r : IsRobustUnimodal (fun i : ZMod 4 => ⟪quad d c' b' c i, b - d⟫)
  · exact close_Tp_R3_hdn N hT' h2r h2c
  rcases Tp_dichotomy N with h | h | h
  · exact absurd h h2r
  · obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hα4, hγ4, hαγ, hβ1, hβ6, hγ6, hγ61, hcv⟩ :=
      norm08_coordsTp' N hT'
    have hrep : b' = d + α4 • (a - d) + γ4 • (c - d) := hb'
    have hα1 : α4 - 1 ≠ 0 := by
      intro h0; apply hS2
      rw [det_alpha hrep, h0, zero_mul]
    rcases lt_trichotomy α4 1 with hlt | heq | hgt
    · exact Tp_poked' N hT' hrep hlt hq h h2r
    · exact absurd (by rw [heq]; ring) hα1
    · exact close_Tp_R4h_hdn N hT' hrep hgt h hbc
  · exact Tp_far N hT' h

theorem close_T'_sig4G (N : Norm08 a a' b b' c c' d) (hT' : IsT' a b c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨ S4TpG a a' b b' c c' d := by
  by_cases hq : QacTop a b b' c d
  · by_cases hlev : LevelQac a b c d
    · obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hα4, hγ4, hαγ, hβ1, hβ6, hγ6, hγ61, hcv⟩ :=
        norm08_coordsTp' N hT'
      have hrep : b' = d + α4 • (a - d) + γ4 • (c - d) := hb'
      have hX := level_not_noHDN N hT' hlev
      rcases lt_trichotomy α4 1 with hlt | heq | hgt
      · exact Or.inl (Tp_level_sep N hT' hlev hrep hlt)
      · refine Or.inr ⟨hT', hq, Or.inr ⟨hX, Or.inr ?_⟩⟩
        rw [det_alpha hrep, heq]; ring
      · by_cases hR1 : NoHDNAt ({b, c', b', c} : Finset ℝ³) (b - d)
        · exact Or.inl (Tp_level_hid N hT' hlev hrep hgt hR1)
        · exact Or.inr ⟨hT', hq, Or.inl ⟨hlev, hR1, α4, γ4, hrep, hgt⟩⟩
    · by_cases hX : NoHDNAt ({d, a, b', c} : Finset ℝ³) (b - d)
      · refine Or.inl (close_T'2' N hT' ?_)
        unfold CoT'2
        push Not
        exact ⟨hX, fun h1 h2 => hlev ⟨h1, h2⟩⟩
      · by_cases hS : TpHDN2 a b b' c c' d ∨ det3 (b' - a) (c - d) (b - d) = 0
        · exact Or.inr ⟨hT', hq, Or.inr ⟨hX, hS⟩⟩
        · exact Or.inl (close_Tp_hdn_caseG N hT' hq hX hS)
  · exact Or.inl (close_Tp_X N hT' hq)

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.close_T'_sig4G
#print axioms Minimality.Type08Sp.S4TpG_imp
