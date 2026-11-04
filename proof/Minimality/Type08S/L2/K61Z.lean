module

public import Minimality.Type08S.L2.K61A
public import Minimality.Type08S.L2.k61_A
public import Minimality.Type08S.L2.k61_Ap
public import Minimality.Type08S.L2.k61_B
public import Minimality.Type08S.L2.k61_C
public import Minimality.Type08S.L2.k61_D
public import Minimality.Type08S.L2.k61_D0

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace
namespace Minimality.Type08Sp.C2

/-- The screen parameter of the K61 view `D:a'b' × P:abd`: `lam = -⟪b-d, a'-b'⟫ / ⟪a-d, a'-b'⟫`. -/
noncomputable def k61_lam (a a' b b' d : ℝ³) : ℝ := -⟪b - d, a' - b'⟫ / ⟪a - d, a' - b'⟫

/-- The depth direction `R = (b-d) + lam (a-d)` (so `⟪R, a'-b'⟫ = 0`). -/
noncomputable def k61_R (a a' b b' d : ℝ³) : ℝ³ := (b - d) + k61_lam a a' b b' d • (a - d)

theorem k61_tie {a a' b b' d : ℝ³} (hAv : ⟪a - d, a' - b'⟫ ≠ 0) :
    ⟪a' - b', k61_R a a' b b' d⟫ = 0 := by
  unfold k61_R k61_lam
  rw [inner_add_right, inner_smul_right, real_inner_comm (b - d) (a' - b'), real_inner_comm (a - d) (a' - b')]
  field_simp
  ring

/-- **Combining lemma** for the type 08 L2 tail, view `D:a'b' × P:abd`.  Besides the brief's hypotheses it takes
`hb6, hg6, hσ, hX4` (all in the K46LeftMN2 context) and the NUMERICS-ONLY facts `fAv .. fhole` (checked on
exact samples of the hypothesis locus, not proved; `fhole` is FALSE there: see HANDOFF.md). -/
theorem k61_l2_cells {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hα1 : 1 < α1) (hβ1 : 1 < β1) (hb6 : 1 < β6) (hg6 : 1 < γ6)
    (hσ : β1 < β6 + γ6) (hX4 : 0 ≤ ⟪c' - a, b' - c⟫)
    (hz1 : ⟪a - a', k28l2aU0 a b c d α1 β1⟫ = 0)
    (hz2 : ⟪a', k28l2aU0 a b c d α1 β1⟫ = ⟪c, k28l2aU0 a b c d α1 β1⟫)
    -- numerics-only facts
    (fAv : ⟪a - d, a' - b'⟫ < 0) (fL : 0 < ⟪b - d, a' - b'⟫)
    (fF1 : 0 < ⟪c' - a, k61_R a a' b b' d⟫) (fF2 : 0 < ⟪c' - b, k61_R a a' b b' d⟫)
    (fF3 : 0 < ⟪c' - b', k61_R a a' b b' d⟫)
    (fzA : 0 < ⟪a - d, k61_R a a' b b' d⟫) (fzB : 0 < ⟪b - d, k61_R a a' b b' d⟫)
    (fDP : ⟪a - b', k61_R a a' b b' d⟫ = 0 → 0 < ⟪b' - a, a - d⟫)
    (fQ1 : β1 * k61_lam a a' b b' d + 1 < α1 → 0 < ⟪b' - a', c - d⟫)
    (fQ2 : α1 ≤ (β1 - 1) * k61_lam a a' b b' d → 0 < ⟪a' - b', c - d⟫)
    (fAC0 : α1 = β1 * k61_lam a a' b b' d + 1 → 0 < ⟪a - b', k61_R a a' b b' d⟫)
    (fhole : ¬ (⟪a - b', k61_R a a' b b' d⟫ ≤ 0 ∧ ⟪a' - b, k61_R a a' b b' d⟫ = 0 ∧
      β1 * k61_lam a a' b b' d + 1 > α1 ∧ α1 > (β1 - 1) * k61_lam a a' b b' d)) :
    HasLexCell (V8 a a' b b' c c' d) := by
  have hlam : 0 < k61_lam a a' b b' d := by
    unfold k61_lam; exact div_pos_of_neg_of_neg (neg_neg_of_pos fL) fAv
  have htie := k61_tie (a := a) (a' := a') (b := b) (b' := b') (d := d) fAv.ne
  obtain ⟨lam, hlamd⟩ : ∃ l, l = k61_lam a a' b b' d := ⟨_, rfl⟩
  obtain ⟨R, hRd⟩ : ∃ R, R = k61_R a a' b b' d := ⟨_, rfl⟩
  rw [← hlamd] at hlam fQ1 fQ2 fAC0 fhole
  rw [← hRd] at htie fF1 fF2 fF3 fzA fzB fAC0 fhole fDP
  have hR1 : R = (1 : ℝ) • ((b - d) + lam • (a - d)) := by rw [hRd, one_smul, hlamd]; rfl
  have hS : ∀ (x y : ℝ³), ⟪x - y, R⟫ = ⟪x, R⟫ - ⟪y, R⟫ := fun x y => inner_sub_left x y R
  have hT : ⟪a', R⟫ - ⟪b', R⟫ = 0 := by rw [← hS]; exact htie
  simp only [hS] at fF1 fF2 fF3 fAC0 fhole fzA fzB fDP
  have hP : 0 < ⟪b', a - d⟫ - ⟪a', a - d⟫ := by
    have h1 : ⟪a' - b', a - d⟫ = ⟪a', a - d⟫ - ⟪b', a - d⟫ := inner_sub_left _ _ _
    have h2 : ⟪a - d, a' - b'⟫ = ⟪a' - b', a - d⟫ := real_inner_comm _ _
    linarith
  have hQ1 : β1 * lam + 1 < α1 → 0 < ⟪b', c - d⟫ - ⟪a', c - d⟫ := fun h => by
    have := fQ1 h; rwa [inner_sub_left] at this
  have hQ2 : α1 ≤ (β1 - 1) * lam → 0 < ⟪a', c - d⟫ - ⟪b', c - d⟫ := fun h => by
    have := fQ2 h; rwa [inner_sub_left] at this
  by_cases hB : β1 * lam + 1 < α1
  · exact k61_B hC hR1 hα1 hβ1 hb6 hlam hg6 hB (by nlinarith) fF2 fF3 hT (hQ1 hB)
  by_cases hCc : α1 ≤ (β1 - 1) * lam
  · exact k61_C hC hR1 hα1 hβ1 hb6 hlam hg6 hσ (by nlinarith) hCc fF1 fF3 hT (hQ2 hCc)
  push_neg at hB hCc
  by_cases hzab : 0 < ⟪a, R⟫ - ⟪b', R⟫
  · exact k61_A hC hR1 hα1 hβ1 hb6 hlam hg6 hB hCc fF1 fF2 hzab hT hP
  push_neg at hzab
  rcases hB.lt_or_eq with hlt | heq
  · rcases lt_trichotomy (⟪a', R⟫ - ⟪b, R⟫) 0 with hz | hz | hz
    · exact k61_Ap hC hR1 hα1 hβ1 hb6 hlam hg6 hlt hCc fF1 fF2 hT hP (by linarith)
    · exact absurd ⟨hzab, hz, hlt, hCc⟩ fhole
    · obtain ⟨R', hR'⟩ : ∃ R', R' = -R := ⟨_, rfl⟩
      have hR2 : R' = (-1 : ℝ) • ((b - d) + lam • (a - d)) := by rw [hR', hR1]; module
      have e : ∀ x : ℝ³, ⟪x, R'⟫ = -⟪x, R⟫ := fun x => by rw [hR', inner_neg_right]
      have dD1 : 0 < ⟪d, R'⟫ - ⟪a, R'⟫ := by simp only [e]; linarith
      have dD2 : 0 < ⟪d, R'⟫ - ⟪b, R'⟫ := by simp only [e]; linarith
      have dzba : 0 < ⟪b, R'⟫ - ⟪a', R'⟫ := by simp only [e]; linarith
      have h3 : ⟪b' - a, a - d⟫ = ⟪b', a - d⟫ - ⟪a, a - d⟫ := inner_sub_left _ _ _
      rcases hzab.lt_or_eq with hz2 | hz2
      · exact k61_D hC hR2 hα1 hβ1 hb6 hlam hg6 hlt hCc dD1 dD2 (by simp only [e]; linarith) dzba
      · have dDP : 0 < ⟪b', a - d⟫ - ⟪a, a - d⟫ := by have := fDP (by linarith); linarith
        exact k61_D0 hC hR2 hα1 hβ1 hb6 hlam hg6 hlt hCc dD1 dD2 (by simp only [e]; linarith)
          dDP dzba
  · have := fAC0 heq; linarith
end Minimality.Type08Sp.C2
