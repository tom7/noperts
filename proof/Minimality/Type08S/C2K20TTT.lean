module

public import Minimality.Type08S.C2K20TGA
public import Minimality.Type08S.C2K6TCZ

@[expose] public section


set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- Leftover of the tie slice `K6t3LeftTT0` after the K20 cover: the ties of the split literals
`γ4 = 1`, `β1 = 1`, `Q_a = ⟪b'-a, a-d⟫ = 0`, `⟪a-d, c-d⟫ = 0`. -/
def K20Left (a a' b b' c c' d : ℝ³) : Prop :=
  det3 (a - d) (b - d) (b' - c) = 0 ∨ det3 (a - d) (c' - b) (c - d) = 0 ∨ ⟪b' - a, a - d⟫ = 0 ∨ ⟪a - d, c - d⟫ = 0

set_option maxHeartbeats 12800000 in
/-- **K20 / TT.**  The tie slice `K6t3LeftTT0` (`q = b - d ⟂ (a-d, c-d)`) is closed by five cells, up to the ties
`K20Left`.  Cells (frame coordinates over `d`, `E = α4 - α4β1 - 1 + γ4 ≥ 0` the Gale constraint):
* `γ4 > 1`, `β1 < 1 ∨ β6 < 1`: `E` `(b,c',a,b',a')` at `d - b` (no Gram condition);
* `γ4 > 1`, `β1, β6 ≥ 1`, `Q_a > 0`: `(b',a',b,d,a)` at `d - b`;
* `γ4 > 1`, `β1 > 1`, `β6 ≥ 1`, `Q_a < 0`: `(a,b',a',c')` at `c' - b`;
* `γ4 < 1` (forces `β1 < 1`), `⟪a-d,c-d⟫ ≠ 0`: the facet `(d,b,a',c)` at `a - d`. -/
theorem k20_TT {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT : IsT a' b c d) (hT' : IsT' a b c' d)
    (h : K6t3LeftTT0 a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K20Left a a' b b' c c' d := by
  obtain ⟨hL1, hL2⟩ := h
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hΔ, hβ1, hα4p, hγ4, hαγ, hβ6, hγ6, hβγ, hfar', hc', hb', ha', hmem7, hVall⟩ :=
    k5d_setup W hT'
  have hg6 : γ6 = 1 := isT_gamma6 hdet ha' hT
  subst hg6
  have hE := k20t_E_nonneg W hdet hc' hb' ha' hβ1 hαγ
  have hF0 := k6t3_facet_a'bc' W hc' hb' ha' hβ1 hγ6 hβγ
  have hF : α4 * (1 - β1) + γ4 * (1 - β6) < 1 := by nlinarith
  have hpq : ⟪a - d, b - d⟫ = 0 := by
    have : ⟪a - d, d - b⟫ = -⟪a - d, b - d⟫ := by
      rw [show d - b = -(b - d) by abel, inner_neg_right]
    linarith
  have hrq : ⟪c - d, b - d⟫ = 0 := by
    have : ⟪c - d, d - b⟫ = -⟪c - d, b - d⟫ := by
      rw [show d - b = -(b - d) by abel, inner_neg_right]
    linarith
  have hR0 : d - b ≠ 0 := k5d_R_ne hΔ
  -- the generic coordinates
  have hfp : ∀ (u v w : ℝ³) (x y z : ℝ), fpoint u v w d (x, y, z) = d + x • u + y • v + z • w := fun u v w x y z =>
    k17gc_fp u v w d x y z
  rcases lt_trichotomy γ4 1 with hG | hG | hG
  · ----------------------------------------------------------------- γ4 < 1 : facet cell
    have hb11 : β1 < 1 := by nlinarith
    by_cases hpr : ⟪a - d, c - d⟫ = 0
    · exact Or.inr (Or.inr (Or.inr (Or.inr hpr)))
    · left
      have hΔ3 : det3 (b - d) (c - d) (a - d) ≠ 0 := by
        have e : det3 (b - d) (c - d) (a - d) = det3 (a - d) (b - d) (c - d) := by
          simp only [det3_expand, PiLp.sub_apply]; ring
        rw [e]; exact hdet
      have Ea : fpoint (b - d) (c - d) (a - d) d (0, 0, 1) = a := by rw [hfp]; module
      have Ed : fpoint (b - d) (c - d) (a - d) d (0, 0, 0) = d := by rw [hfp]; module
      have Eb : fpoint (b - d) (c - d) (a - d) d (1, 0, 0) = b := by rw [hfp]; module
      have Ec : fpoint (b - d) (c - d) (a - d) d (0, 1, 0) = c := by rw [hfp]; module
      have Ea' : fpoint (b - d) (c - d) (a - d) d (β6, 1, 0) = a' := by rw [hfp, ha']; module
      have Eb' : fpoint (b - d) (c - d) (a - d) d (0, γ4, α4) = b' := by rw [hfp, hb']; module
      have Ec' : fpoint (b - d) (c - d) (a - d) d (β1, 0, 1) = c' := by rw [hfp, hc']; module
      refine ⟨a - d, ?_, ?_⟩
      · intro h0; apply hΔ3; rw [h0]; simp [det3_expand]
      · refine k20tH_cell (V8 a a' b b' c c' d) (b - d) (c - d) (a - d) d hΔ3 hα4p hγ4 hG hβ1 hb11 hβ6
          (by rw [real_inner_comm]; exact hpq) (by rw [real_inner_comm]; exact hpr) ?_ ?_
        · intro i
          rcases z4_cases' i with rfl | rfl | rfl | rfl
          · simp only [k20tH_0, Ed]; simp [V8]
          · simp only [k20tH_1, Eb]; simp [V8]
          · simp only [k20tH_2, Ea']; simp [V8]
          · simp only [k20tH_3, Ec]; simp [V8]
        · intro y hy
          rw [Ed, Eb, Ea', Ec, Ea, Ec', Eb']
          simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
          tauto
  · ----------------------------------------------------------------- γ4 = 1 : tie
    right; left
    rw [k6t2_det_gamma4 hb', hG]; ring
  · ----------------------------------------------------------------- γ4 > 1
    by_cases hlow : β1 < 1 ∨ β6 < 1
    · -- cell E (no Gram condition)
      left
      refine ⟨d - b, hR0, ?_⟩
      refine k20tE_cell (V8 a a' b b' c c' d) (a - d) (c - d) (d - b) d hΔ hα4p hG hαγ hβ1 hβ6 hlow hL1 hL2 ?_ ?_
      · intro i
        apply hmem7
        rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
          simp [k20tE_0, k20tE_1, k20tE_2, k20tE_3, k20tE_4, k5dL]
      · intro y hy
        have := hVall y hy
        tauto
    · push Not at hlow
      obtain ⟨hb1, hb6⟩ := hlow
      have hQe : ⟪b' - a, a - d⟫ = (α4 - 1) * ⟪a - d, a - d⟫ + γ4 * ⟪c - d, a - d⟫ := by
        have : b' - a = (α4 - 1) • (a - d) + γ4 • (c - d) := by rw [hb']; module
        rw [this, inner_add_left, real_inner_smul_left, real_inner_smul_left]
      rcases lt_trichotomy ((α4 - 1) * ⟪a - d, a - d⟫ + γ4 * ⟪c - d, a - d⟫) 0 with hQ | hQ | hQ
      · -- Q_a < 0
        rcases hb1.lt_or_eq with hb1' | hb1'
        · -- cell Z at `c' - b`
          left
          have hc'b : c' - b = (a - d) + (β1 - 1) • (b - d) := by rw [hc']; module
          have hΔz : det3 (c - d) (b - d) (c' - b) ≠ 0 := by
            have e : det3 (c - d) (b - d) (c' - b) = - det3 (a - d) (b - d) (c - d) := by
              rw [hc']
              simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
            rw [e]; exact neg_ne_zero.2 hdet
          have Ea : fpoint (c - d) (b - d) (c' - b) d (0, 1 - β1, 1) = a := by rw [hfp, hc']; module
          have Eb' : fpoint (c - d) (b - d) (c' - b) d (γ4, -α4 * (β1 - 1), α4) = b' := by
            rw [hfp, hb', hc']; module
          have Ea' : fpoint (c - d) (b - d) (c' - b) d (1, β6, 0) = a' := by rw [hfp, ha']; module
          have Ec' : fpoint (c - d) (b - d) (c' - b) d (0, 1, 1) = c' := by rw [hfp]; module
          have Ed : fpoint (c - d) (b - d) (c' - b) d (0, 0, 0) = d := by rw [hfp]; module
          have Eb : fpoint (c - d) (b - d) (c' - b) d (0, 1, 0) = b := by rw [hfp]; module
          have Ec : fpoint (c - d) (b - d) (c' - b) d (1, 0, 0) = c := by rw [hfp]; module
          have hq0 : b - d ≠ 0 := by intro h0; apply hdet; rw [h0]; simp [det3_expand]
          have hqq : 0 < ⟪b - d, b - d⟫ := real_inner_self_pos.2 hq0
          have hpq' : ⟪b - d, a - d⟫ = 0 := by rw [real_inner_comm]; exact hpq
          have hrq' : ⟪c - d, b - d⟫ = 0 := hrq
          have g1 : ⟪b - d, c' - b⟫ = (β1 - 1) * ⟪b - d, b - d⟫ := by
            rw [hc'b, inner_add_right, real_inner_smul_right, hpq']; ring
          have g2 : ⟪c - d, c' - b⟫ = ⟪c - d, a - d⟫ := by
            rw [hc'b, inner_add_right, real_inner_smul_right, hrq']; ring
          have g3 : ⟪c' - b, c' - b⟫ = ⟪a - d, a - d⟫ + (β1 - 1) ^ 2 * ⟪b - d, b - d⟫ := by
            rw [hc'b, inner_add_left, inner_add_right, inner_add_right, real_inner_smul_left, real_inner_smul_left,
              real_inner_smul_right, real_inner_smul_right, hpq', hpq]
            ring
          refine ⟨c' - b, k17gc_r0 hΔz, ?_⟩
          refine k20tZ_cell (V8 a a' b b' c c' d) (c - d) (b - d) (c' - b) d hΔz hα4p hG hαγ hb1' hβ6 hF
            (by rw [g1]; exact mul_pos (by linarith) hqq) ?_ ?_ ?_
          · rw [g1, g2, g3]; nlinarith
          · intro i
            rcases z4_cases' i with rfl | rfl | rfl | rfl
            · simp only [k20tZ_0, Ea]; simp [V8]
            · simp only [k20tZ_1, Eb']; simp [V8]
            · simp only [k20tZ_2, Ea']; simp [V8]
            · simp only [k20tZ_3, Ec']; simp [V8]
          · intro y hy
            rw [Ea, Eb', Ea', Ec', Ed, Eb, Ec]
            simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
            tauto
        · -- β1 = 1 : tie
          right; right; left
          rw [det_beta1 hc', ← hb1']; ring
      · -- Q_a = 0 : tie
        right; right; right; left
        rw [hQe]; exact hQ
      · -- Q_a > 0 : cell A3b at `d - b`
        left
        refine ⟨d - b, hR0, ?_⟩
        refine k20tG_cell (V8 a a' b b' c c' d) (a - d) (c - d) (d - b) d hΔ hα4p hG hαγ hβ1 hβ6 hL1 hL2
          (by have h' := hQ; rw [real_inner_comm (a - d) (c - d)] at h'; exact h') ?_ ?_
        · exact fun i => hmem7 _ (k5dX5_mem α4 γ4 β1 β6 1 i)
        · intro y hy
          have := hVall y hy
          tauto

end C2
end Type08Sp
end Minimality
