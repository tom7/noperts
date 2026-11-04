module

public import Minimality.Type08S.C2K46ZA
public import Minimality.Type08S.L2.K83B
public import Minimality.Type08S.L2.K91Z
public import Minimality.Type08S.L2.K95F
public import Minimality.Type08S.L2.K94WL

/-!
# K47 / Z: the L2 tail corners; type 08's special positions are closed

`K46LeftMN2` reduces by `k83_reduce` to hz1 ∧ hz2 ∧ (gWb = 0 ∨ U0 = 0). The U0 = 0 branch is `k91_c1` (lex cells), the
gWb = 0 branch is `k95_gwb` (lex cells). Both leave the corner zab = zba = 0, a planar "waist" a a′ b b′: for α1 ≠ β1 it
is closed by k-jets (`k94_corner`, `isRupert_of_cayleyPolyJet`), and on the wall α1 = β1 by two lex cells and a motion
cell (`k94_wall`). The tie ⟪c − a′, a − b′⟫ = 0 is `k28_h1tie`. Design: specpos/C2/K56VTX … K95GLUE.
-/
@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
open C2

theorem k47_av {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hα : 1 < α1) (hβ : 1 < β1) (hσ : β1 < β6 + γ6) :
    ⟪a - d, a' - b'⟫ < 0 := by
  obtain ⟨hPR, hpp, hqq, hrr⟩ := k32e_facts hC hM
  obtain ⟨hdet, hc', hb', ha', -⟩ := hC
  have ip := k32e_ip (a - d) (b - d) (c - d) hPR
  obtain ⟨hr1, hr2⟩ := hrel
  have hpqn : ⟪a - d, b - d⟫ < 0 := k61_pq_neg hβ hα hqq hrr hr1 hr2
  have hAv0 : ⟪a - d, a' - b'⟫ = -α1 * ⟪a - d, a - d⟫ + (β6 + γ6 - β1) * ⟪a - d, b - d⟫ := by
    have e : a' - b' = (-α1) • (a - d) + β6 • (b - d) + (γ6 - β1) • (c - d) := by
      rw [ha', hb']; module
    have e1 : a - d = (1:ℝ) • (a - d) + (0:ℝ) • (b - d) + (0:ℝ) • (c - d) := by module
    rw [e]; nth_rewrite 1 [e1]; rw [ip]; simp only [k32e_G]; ring
  have h1 : 0 < α1 * ⟪a - d, a - d⟫ := mul_pos (by linarith) hpp
  have h2 : (β6 + γ6 - β1) * ⟪a - d, b - d⟫ < 0 := mul_neg_of_pos_of_neg (by linarith) hpqn
  rw [hAv0]; linarith

/-- The corner zab = zba = 0. -/
theorem k47_corner {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (hno : ¬ HasLexCell (V8 a a' b b' c c' d))
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hα : 1 < α1) (hβ : 1 < β1) (hβ6 : 1 < β6) (hγ6 : 1 < γ6)
    (hσ : β1 < β6 + γ6) (hX3 : ⟪a - c', a - b'⟫ ≤ 0) (hX4 : 0 ≤ ⟪c' - a, b' - c⟫)
    (hH : 0 ≤ ⟪c' - a', b' - c⟫) (hk17 : (α1 - 1) * (β1 - 1) * (β6 + γ6 - 1) ≤ α1 + β1 - 1)
    (hac : 0 < ⟪a - c', d - a'⟫)
    (hz1 : ⟪a - a', k28l2aU0 a b c d α1 β1⟫ = 0)
    (hz2 : ⟪a', k28l2aU0 a b c d α1 β1⟫ = ⟪c, k28l2aU0 a b c d α1 β1⟫)
    (hgWb : β6 * (α1 - 1) = β1 * (γ6 - 1))
    (hzab : ⟪a - b', k61_R a a' b b' d⟫ = 0) (hzba : ⟪a' - b, k61_R a a' b b' d⟫ = 0)
    (hacL : 0 < 1 - α1 + β1 * k61_lam a a' b b' d)
    (hcbL : 0 < α1 - (β1 - 1) * k61_lam a a' b b' d) : False := by
  by_cases hw : α1 = β1
  · rcases k94_wall hC hM hrel hα hβ hX4 hz1 hz2 hgWb hzab hzba hw hk17 with h | h
    · exact hno h
    · exact hNR h
  · exact hNR (k94_corner hC hM hrel hα hβ hβ6 hγ6 hσ hX3 hX4 hH hac hz1 hz2 hgWb hzab hzba hw hacL hcbL)

/-- The whole L2 residual is empty. -/
theorem k47_final {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (hno : ¬ HasLexCell (V8 a a' b b' c c' d))
    (h : K46LeftMN2 W) : False := by
  by_cases ht : ⟪c - a', a - b'⟫ = 0
  · obtain ⟨hs, α1, β1, β6, γ6, hC, hreg, hH1, hL2, hK⟩ := h
    exact hno (k28_h1tie W hs hC hH1 ht)
  obtain ⟨α1, β1, β6, γ6, hC, hM, hrel, hα, hβ, hβ6, hγ6, hσ, hX3, hX4, hH, hk17, hac, hz1, hz2, hor⟩ :=
    k83_reduce W ht h
  by_cases hU0 : k28l2aU0 a b c d α1 β1 = 0
  · -- U0 = 0
    have hgW : 0 ≤ β6 * (α1 - 1) - β1 * (γ6 - 1) := by
      obtain ⟨hdet, hc', hb', ha', -⟩ := hC
      have := k6m_gWb W hdet hc' hb' ha'
      nlinarith
    have hAv := k47_av hC hM hrel hα hβ hσ
    have hlam : k61_lam a a' b b' d * ⟪a - d, a' - b'⟫ = -⟪b - d, a' - b'⟫ := by
      unfold k61_lam; field_simp [hAv.ne]
    obtain ⟨-, -, hacU, -, -, -, -, -, hzabU, -, hA0, -⟩ :=
      k86_facts hC hM hrel hα hβ hβ6 hγ6 hσ hU0 hlam
    have hν : (β1 * (-⟪a - a', c - d⟫) / ⟪a - a', a - d⟫) * ⟪a - a', a - d⟫ =
        β1 * (-⟪a - a', c - d⟫) := by field_simp [hA0.ne']
    rcases k91_c1 hC hM hrel hU0 hα hβ hβ6 hγ6 hσ hgW hlam hν hH with h1 | ⟨hg, hzba, hcb⟩
    · exact hno h1
    · have hzab : ⟪a - b', k61_R a a' b b' d⟫ = 0 := by
        have e : a - b' = -(b' - a) := by abel
        rw [e, inner_neg_left]; unfold k61_R; rw [hzabU]; simp
      exact k47_corner hNR hno hC hM hrel hα hβ hβ6 hγ6 hσ hX3 hX4 hH hk17 hac hz1 hz2 (by linarith)
        hzab (by unfold k61_R; exact hzba) (by linarith) hcb
  · have hg := hor.resolve_right hU0
    rcases k95_gwb hC hM hrel hα hβ hβ6 hγ6 hσ hX3 hX4 hH hz1 hz2 hg hU0 with h1 | ⟨hzab, hzba, hacL, hcbL⟩
    · exact hno h1
    · exact k47_corner hNR hno hC hM hrel hα hβ hβ6 hγ6 hσ hX3 hX4 hH hk17 hac hz1 hz2 hg hzab hzba hacL hcbL

theorem k47_residP_false {p p' q q' r r' d : ℝ³}
    (hNR : ¬ IsRupert (V8 p p' q q' r r' d)) (hno : ¬ HasLexCell (V8 p p' q q' r r' d))
    (h : K46ResidP p p' q q' r r' d) : False := by
  obtain ⟨W, -, hs⟩ := h
  exact k47_final W hNR hno hs

/-- **Type 08's special-position residual is empty.** -/
theorem resid08FinalK46_false {a a' b b' c c' d : ℝ³}
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : Resid08FinalK46 a a' b b' c c' d) : False := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  rcases h6 with h | h | h | h | h | h
  · exact k47_residP_false hNR hno h
  · exact k47_residP_false (fun hR => hNR (by rw [V8, ← e.2.1]; exact hR))
      (fun hc => hno (by rw [V8, ← e.2.1]; exact hc)) h
  · exact k47_residP_false (fun hR => hNR (by rw [V8, ← e.2.2.1]; exact hR))
      (fun hc => hno (by rw [V8, ← e.2.2.1]; exact hc)) h
  · exact k47_residP_false (fun hR => hNR (by rw [V8, ← e.2.2.2.1]; exact hR))
      (fun hc => hno (by rw [V8, ← e.2.2.2.1]; exact hc)) h
  · exact k47_residP_false (fun hR => hNR (by rw [V8, ← e.2.2.2.2.1]; exact hR))
      (fun hc => hno (by rw [V8, ← e.2.2.2.2.1]; exact hc)) h
  · exact k47_residP_false (fun hR => hNR (by rw [V8, ← e.2.2.2.2.2]; exact hR))
      (fun hc => hno (by rw [V8, ← e.2.2.2.2.2]; exact hc)) h

end Type08Sp
end Minimality
