module

public import Minimality.Type08S.P2I5b
public import Minimality.Type08S.P2I7b
public import Minimality.Type08S.P2TpX
public import Minimality.Type08S.P2J1
public import Minimality.Type08S.P2J2
public import Minimality.Type08S.P2J3
public import Minimality.Type08S.P2J4

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# I9: assembly of the case at `T'` (`close_T'_sig4E`) from the finished lemmas; the residual keeps the hypotheses of `Tp_poked`, `Tp_far`.

Finished (other files): `close_Tp_X` (¬QacTop, pkC), `close_T'2'` (tree; X_2a HDN-free, not level),
`close_Tp_R3_hdn` (I5b), `close_Tp_R4h_hdn` (I7b).
Also used: `Tp_other_noHDN`, `Tp_dichotomy`, `level_not_noHDN`, `Tp_level_hid` (J1-J4).
Unproved pieces `Tp_poked`, `Tp_far` appear only as their hypotheses (`TpPokedH`, `TpFarH`).
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- **Residual hypotheses of the (unproved) package `Tp_poked`** (29.13, `α4 < 1`: `a` pokes out): `X_bc'`
robust at `ℓ` and HDN-free.  The package would give Rupert, or `R4ppEnd` (R4″'s end boundary). -/
def TpPokedH {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) : Prop :=
  IsT' a b c' d ∧ ∃ α4 γ4 : ℝ, b' = d + α4 • (a - d) + γ4 • (c - d) ∧ α4 < 1 ∧
    IsRobustUnimodal (fun i : ZMod 4 => ⟪quad b c' b' c i, b - d⟫) ∧
    NoHDNAt ({b, c', b', c} : Finset ℝ³) (b - d)

/-- **Residual hypotheses of the (unproved) package `Tp_far`**: the weak far triple at `T'`
(touching; codimension 3 together with `T'` and `QacTop`). -/
def TpFarH {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) : Prop :=
  IsT' a b c' d ∧ WeakFarTp b b' c c' d

/-- The residual of the case at `T'`: `S4Tp` (Σ₄) or the hypotheses of the two unproved pieces. -/
def TpResE {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) : Prop :=
  S4Tp a a' b b' c c' d ∨ TpPokedH N ∨ TpFarH N

/-- `det3 (b' - a) (c - d) (b - d) = (α4 - 1) det3 (a - d) (c - d) (b - d)`. -/
theorem det_alpha {a b b' c d : ℝ³} {α4 γ4 : ℝ} (hb'rep : b' = d + α4 • (a - d) + γ4 • (c - d)) :
    det3 (b' - a) (c - d) (b - d) = (α4 - 1) * det3 (a - d) (c - d) (b - d) := by
  have : b' - a = (α4 - 1) • (a - d) + γ4 • (c - d) := by rw [hb'rep]; module
  rw [this]
  simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

/-- The `QacTop` core: HDN of `X_2a`, no second polygon HDN, `α4 ≠ 1`, no `R4ppEnd`. -/
theorem close_Tp_hdn_case {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hT' : IsT' a b c' d)
    (hX : ¬ NoHDNAt ({d, a, b', c} : Finset ℝ³) (b - d))
    (hS : ¬ (TpHDN2 a b b' c c' d ∨ det3 (b' - a) (c - d) (b - d) = 0 ∨ R4ppEnd a b c c' d)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨ TpResE N := by
  push Not at hS
  obtain ⟨hS1, hS2, hS3⟩ := hS
  obtain ⟨h2c, hbc⟩ := Tp_other_noHDN N hX hS1
  rcases Tp_dichotomy N with h | h | h
  · exact Or.inl (close_Tp_R3_hdn N hT' h h2c)
  · obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hα4, hγ4, hαγ, hβ1, hβ6, hγ6, hγ61, hcv⟩ :=
      norm08_coordsTp' N hT'
    have hrep : b' = d + α4 • (a - d) + γ4 • (c - d) := hb'
    have hne : det3 (a - d) (c - d) (b - d) ≠ 0 := by
      intro h0; apply hdet
      have e : det3 (a - d) (b - d) (c - d) = - det3 (a - d) (c - d) (b - d) := by
        simp only [det3_expand]; ring
      rw [e, h0, neg_zero]
    have hα1 : α4 - 1 ≠ 0 := by
      intro h0; apply hS2
      rw [det_alpha hrep, h0, zero_mul]
    rcases lt_trichotomy α4 1 with hlt | heq | hgt
    · exact Or.inr (Or.inr (Or.inl ⟨hT', α4, γ4, hrep, hlt, h, hbc⟩))
    · exact absurd (by rw [heq]; ring) hα1
    · exact Or.inl (close_Tp_R4h_hdn N hT' hrep hgt h hbc)
  · exact Or.inr (Or.inr (Or.inr ⟨hT', h⟩))

/-- **`close_T'_sig4`** (the `P2Pkg` statement), modulo the residual lemmas above. -/
theorem close_T'_sig4E {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hT' : IsT' a b c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨ TpResE N := by
  by_cases hq : QacTop a b b' c d
  · by_cases hlev : LevelQac a b c d
    · by_cases hR1 : NoHDNAt ({b, c', b', c} : Finset ℝ³) (b - d)
      · obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hα4, hγ4, hαγ, hβ1, hβ6, hγ6, hγ61, hcv⟩ :=
          norm08_coordsTp' N hT'
        have hrep : b' = d + α4 • (a - d) + γ4 • (c - d) := hb'
        have hX := level_not_noHDN N hT' hlev
        rcases lt_trichotomy α4 1 with hlt | heq | hgt
        · exact Or.inr (Or.inr (Or.inl ⟨hT', α4, γ4, hrep, hlt, level_robust_Xbc N hT' hlev, hR1⟩))
        · refine Or.inr (Or.inl ⟨hT', hq, Or.inr ⟨hX, Or.inr (Or.inl ?_)⟩⟩)
          rw [det_alpha hrep, heq]; ring
        · exact Or.inl (Tp_level_hid N hT' hlev hrep hgt hR1)
      · exact Or.inr (Or.inl ⟨hT', hq, Or.inl ⟨hlev, hR1⟩⟩)
    · by_cases hX : NoHDNAt ({d, a, b', c} : Finset ℝ³) (b - d)
      · refine Or.inl (close_T'2' N hT' ?_)
        unfold CoT'2
        push Not
        exact ⟨hX, fun h1 h2 => hlev ⟨h1, h2⟩⟩
      · by_cases hS : TpHDN2 a b b' c c' d ∨ det3 (b' - a) (c - d) (b - d) = 0 ∨ R4ppEnd a b c c' d
        · exact Or.inr (Or.inl ⟨hT', hq, Or.inr ⟨hX, hS⟩⟩)
        · exact close_Tp_hdn_case N hT' hX hS
  · exact Or.inl (close_Tp_X N hT' hq)

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.close_T'_sig4E
