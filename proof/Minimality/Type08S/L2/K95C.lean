module

public import Minimality.Type08S.L2.K61Z
public import Minimality.Type08S.L2.k63_Dz
public import Minimality.Type08S.L2.k93_D0w
public import Minimality.Type08S.L2.k93_Pw
public import Minimality.Type08S.L2.k93_Tw

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace
namespace Minimality.Type08Sp.C2

/-- `k93_tie`: the tie ac = 0, zab = 0, in the frame R' = -R, by the sign of zba. -/
theorem k93_tie {a a' b b' c c' d R' : ℝ³} {α1 β1 β6 γ6 lam : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hR : R' = (-1 : ℝ) • ((b - d) + lam • (a - d)))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hb6 : 1 < β6) (hlam : 0 < lam) (hg6 : 1 < γ6)
    (hac : α1 = β1 * lam + 1) (hcb : (β1 - 1) * lam < α1)
    (dD1 : 0 < ⟪d, R'⟫ - ⟪a, R'⟫) (dD2 : 0 < ⟪d, R'⟫ - ⟪b, R'⟫)
    (dDP : 0 < ⟪b', a - d⟫ - ⟪a, a - d⟫)
    (dzab : ⟪a, R'⟫ - ⟪b', R'⟫ = 0) (dza : ⟪a, R'⟫ - ⟪a', R'⟫ = 0)
    (dC1 : 0 < ⟪b', R'⟫ - ⟪c', R'⟫) (dQ : 0 < ⟪b', c - d⟫ - ⟪a', c - d⟫)
    (dQ2 : 0 < ⟪a', c - d⟫ - ⟪b, c - d⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  rcases lt_trichotomy (⟪b, R'⟫ - ⟪a', R'⟫) 0 with h | h | h
  · exact k93_Pw hC hR hα1 hβ1 hb6 hlam hg6 hac hcb dzab dza (by linarith) dC1 dQ
  · exact k93_Tw hC hR hα1 hβ1 hb6 hlam hg6 hac hcb dzab dza (by linarith) dC1 dQ dQ2
  · exact k93_D0w hC hR hα1 hβ1 hb6 hlam hg6 hac.le hcb dD1 dD2 dzab dDP h

/-- **Combining lemma** for the type 08 L2 tail, view `D:a'b' × P:abd`.  Besides the brief's hypotheses it takes
`hb6, hg6, hσ, hX4` (all in the K46LeftMN2 context) and the NUMERICS-ONLY facts `fAv .. fhole` (checked on
exact samples of the hypothesis locus, not proved; the old `fhole` is replaced by `fcorner`, which may be FALSE: the corner zab = zba = 0 has no cell, see K63ZBA/HANDOFF.md). -/
theorem k95_comb {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
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
    (fAC0 : α1 = β1 * k61_lam a a' b b' d + 1 → 0 ≤ ⟪a - b', k61_R a a' b b' d⟫)
    (fN1 : 0 < ⟪b - a', a - d⟫)
    (fQT : α1 = β1 * k61_lam a a' b b' d + 1 → 0 < ⟪b' - a', c - d⟫)
    (fQ2T : α1 = β1 * k61_lam a a' b b' d + 1 → ⟪a - b', k61_R a a' b b' d⟫ = 0 → 0 < ⟪a' - b, c - d⟫) :
    HasLexCell (V8 a a' b b' c c' d) ∨ (⟪a - b', k61_R a a' b b' d⟫ = 0 ∧ ⟪a' - b, k61_R a a' b b' d⟫ = 0 ∧
      0 < 1 - α1 + β1 * k61_lam a a' b b' d ∧ 0 < α1 - (β1 - 1) * k61_lam a a' b b' d) := by
  have hlam : 0 < k61_lam a a' b b' d := by
    unfold k61_lam; exact div_pos_of_neg_of_neg (neg_neg_of_pos fL) fAv
  have htie := k61_tie (a := a) (a' := a') (b := b) (b' := b') (d := d) fAv.ne
  obtain ⟨lam, hlamd⟩ : ∃ l, l = k61_lam a a' b b' d := ⟨_, rfl⟩
  obtain ⟨R, hRd⟩ : ∃ R, R = k61_R a a' b b' d := ⟨_, rfl⟩
  rw [← hlamd] at hlam fQ1 fQ2 fAC0 fQT fQ2T ⊢
  rw [← hRd] at htie fF1 fF2 fF3 fzA fzB fAC0 fDP fQ2T ⊢
  have hR1 : R = (1 : ℝ) • ((b - d) + lam • (a - d)) := by rw [hRd, one_smul, hlamd]; rfl
  have hS : ∀ (x y : ℝ³), ⟪x - y, R⟫ = ⟪x, R⟫ - ⟪y, R⟫ := fun x y => inner_sub_left x y R
  have hT : ⟪a', R⟫ - ⟪b', R⟫ = 0 := by rw [← hS]; exact htie
  simp only [hS] at fF1 fF2 fF3 fAC0 fzA fzB fDP
  have hP : 0 < ⟪b', a - d⟫ - ⟪a', a - d⟫ := by
    have h1 : ⟪a' - b', a - d⟫ = ⟪a', a - d⟫ - ⟪b', a - d⟫ := inner_sub_left _ _ _
    have h2 : ⟪a - d, a' - b'⟫ = ⟪a' - b', a - d⟫ := real_inner_comm _ _
    linarith
  have hQ1 : β1 * lam + 1 < α1 → 0 < ⟪b', c - d⟫ - ⟪a', c - d⟫ := fun h => by
    have := fQ1 h; rwa [inner_sub_left] at this
  have hQ2 : α1 ≤ (β1 - 1) * lam → 0 < ⟪a', c - d⟫ - ⟪b', c - d⟫ := fun h => by
    have := fQ2 h; rwa [inner_sub_left] at this
  by_cases hB : β1 * lam + 1 < α1
  · left; exact k61_B hC hR1 hα1 hβ1 hb6 hlam hg6 hB (by nlinarith) fF2 fF3 hT (hQ1 hB)
  by_cases hCc : α1 ≤ (β1 - 1) * lam
  · left; exact k61_C hC hR1 hα1 hβ1 hb6 hlam hg6 hσ (by nlinarith) hCc fF1 fF3 hT (hQ2 hCc)
  push_neg at hB hCc
  by_cases hzab : 0 < ⟪a, R⟫ - ⟪b', R⟫
  · left; exact k61_A hC hR1 hα1 hβ1 hb6 hlam hg6 hB hCc fF1 fF2 hzab hT hP
  push_neg at hzab
  rcases hB.lt_or_eq with hlt | heq
  · rcases lt_trichotomy (⟪a', R⟫ - ⟪b, R⟫) 0 with hz | hz | hz
    · left; exact k61_Ap hC hR1 hα1 hβ1 hb6 hlam hg6 hlt hCc fF1 fF2 hT hP (by linarith)
    · rcases hzab.lt_or_eq with hz1' | hz1'
      · obtain ⟨R', hR'⟩ : ∃ R', R' = -R := ⟨_, rfl⟩
        have hR2 : R' = (-1 : ℝ) • ((b - d) + lam • (a - d)) := by rw [hR', hR1]; module
        have e : ∀ x : ℝ³, ⟪x, R'⟫ = -⟪x, R⟫ := fun x => by rw [hR', inner_neg_right]
        have dD1 : 0 < ⟪d, R'⟫ - ⟪a, R'⟫ := by simp only [e]; linarith
        have dD2 : 0 < ⟪d, R'⟫ - ⟪b, R'⟫ := by simp only [e]; linarith
        have dN1 : 0 < ⟪b, a - d⟫ - ⟪a', a - d⟫ := by
          have := fN1
          rwa [inner_sub_left] at this
        left; exact k63_Dz hC hR2 hα1 hβ1 hb6 hlam hg6 hlt hCc dD1 dD2 (by simp only [e]; linarith)
          (by simp only [e]; linarith) dN1
      · right; rw [hS, hS]; refine ⟨by linarith, by linarith, by linarith, by linarith⟩
    · obtain ⟨R', hR'⟩ : ∃ R', R' = -R := ⟨_, rfl⟩
      have hR2 : R' = (-1 : ℝ) • ((b - d) + lam • (a - d)) := by rw [hR', hR1]; module
      have e : ∀ x : ℝ³, ⟪x, R'⟫ = -⟪x, R⟫ := fun x => by rw [hR', inner_neg_right]
      have dD1 : 0 < ⟪d, R'⟫ - ⟪a, R'⟫ := by simp only [e]; linarith
      have dD2 : 0 < ⟪d, R'⟫ - ⟪b, R'⟫ := by simp only [e]; linarith
      have dzba : 0 < ⟪b, R'⟫ - ⟪a', R'⟫ := by simp only [e]; linarith
      have h3 : ⟪b' - a, a - d⟫ = ⟪b', a - d⟫ - ⟪a, a - d⟫ := inner_sub_left _ _ _
      rcases hzab.lt_or_eq with hz2 | hz2
      · left; exact k61_D hC hR2 hα1 hβ1 hb6 hlam hg6 hlt hCc dD1 dD2 (by simp only [e]; linarith) dzba
      · have dDP : 0 < ⟪b', a - d⟫ - ⟪a, a - d⟫ := by have := fDP (by linarith); linarith
        left; exact k61_D0 hC hR2 hα1 hβ1 hb6 hlam hg6 hlt hCc dD1 dD2 (by simp only [e]; linarith)
          dDP dzba
  · have h0 := fAC0 heq
    have hzab0 : ⟪a - b', R⟫ = 0 := by rw [hS]; linarith
    obtain ⟨R', hR'⟩ : ∃ R', R' = -R := ⟨_, rfl⟩
    have hR2 : R' = (-1 : ℝ) • ((b - d) + lam • (a - d)) := by rw [hR', hR1]; module
    have e : ∀ x : ℝ³, ⟪x, R'⟫ = -⟪x, R⟫ := fun x => by rw [hR', inner_neg_right]
    have dD1 : 0 < ⟪d, R'⟫ - ⟪a, R'⟫ := by simp only [e]; linarith
    have dD2 : 0 < ⟪d, R'⟫ - ⟪b, R'⟫ := by simp only [e]; linarith
    have dDP : 0 < ⟪b', a - d⟫ - ⟪a, a - d⟫ := by
      have := fDP (by linarith)
      have h3 : ⟪b' - a, a - d⟫ = ⟪b', a - d⟫ - ⟪a, a - d⟫ := inner_sub_left _ _ _
      linarith
    have dQ : 0 < ⟪b', c - d⟫ - ⟪a', c - d⟫ := by
      have := fQT heq; rwa [inner_sub_left] at this
    have dQ2 : 0 < ⟪a', c - d⟫ - ⟪b, c - d⟫ := by
      have := fQ2T heq hzab0; rwa [inner_sub_left] at this
    left
    exact k93_tie hC hR2 hα1 hβ1 hb6 hlam hg6 heq hCc dD1 dD2 dDP (by simp only [e]; linarith)
      (by simp only [e]; linarith) (by simp only [e]; linarith) dQ dQ2
end Minimality.Type08Sp.C2
