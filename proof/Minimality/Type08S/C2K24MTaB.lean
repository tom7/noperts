module

public import Minimality.Type08S.C2K24MTaA

@[expose] public section


set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

set_option maxHeartbeats 12800000 in
/-- Type 08 M-stratum double tie `K14mTie`, side 1, on `L = ⟪b - c, b - a'⟫ ≤ 0`: one cell at the view `b - a'`
(silhouette `(a', c, b', c')`).  Extra hypothesis `hrel` (the `K16Rel` Gram relation, gives `⟪a-d,b-d⟫ < 0`). -/
theorem k24mt_le {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ} (W : Norm08w a a' b b' c c' d)
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1)
    (h : 1 < α1 ∧ 1 < β1 ∧ 1 < β6 ∧ γ6 < 1 ∧ ⟪c - a', a - b'⟫ = 0 ∧ ⟪c' - a', a - b'⟫ = 0)
    (hL : ⟪b - c, b - a'⟫ ≤ 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hα1, hβ1, hβ6, hγ61, ht1, ht2⟩ := h
  obtain ⟨k1, k2, k3, k4⟩ := k24mta_keys hC hM hrel hα1 hβ1 hβ6 hγ61 ht1
  have hC' := hC
  obtain ⟨hdet, hc', hb', ha', -, -, -, -, hγ6, -⟩ := hC'
  obtain ⟨q, hq⟩ : ∃ q : ℝ³, q = γ6⁻¹ • (b - d) := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ³, r = (1 - β6) • q - (c - d) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℝ³, P = a - d := ⟨_, rfl⟩
  have hb2 : b = d + γ6 • q := by
    rw [hq, smul_smul, mul_inv_cancel₀ hγ6.ne', one_smul]; abel
  have hc2 : c = d + (1 - β6) • q - r := by rw [hr]; module
  have ha2 : a = d + P := by rw [hP]; abel
  have hbd : b - d = γ6 • q := by rw [hb2]; abel
  have hcd : c - d = (1 - β6) • q - r := by rw [hc2]; abel
  have had : a - d = P := hP.symm
  have ha'2 : a' = d + (-γ6) • r + γ6 • q := by rw [ha', hbd, hcd]; module
  have hb'2 : b' = d + α1 • P + (β1 * (1 - β6)) • q + (-β1) • r := by rw [hb', hcd, had]; module
  have hc'2 : c' = d + α1 • P + (β1 * γ6) • q := by rw [hc', hbd, had]; module
  have hγr : b - a' = γ6 • r := by rw [hb2, ha'2]; module
  have hΔ : det3 P q r ≠ 0 := by
    have e : det3 P q r = -γ6⁻¹ * det3 (a - d) (b - d) (c - d) := by
      rw [hr, hq, hP]
      simp only [det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e]
    exact mul_ne_zero (neg_ne_zero.2 (inv_ne_zero hγ6.ne')) hdet
  have hr0 : r ≠ 0 := k17f_r0 hΔ
  have Ea : fpoint P q r d (1, 0, 0) = a := by rw [k17f_fp, ha2]; module
  have Ed : fpoint P q r d (0, 0, 0) = d := by rw [k17f_fp]; module
  have Eb : fpoint P q r d (0, γ6, 0) = b := by rw [k17f_fp, hb2]; module
  have Ec : fpoint P q r d (0, 1 - β6, -1) = c := by rw [k17f_fp, hc2]; module
  have Ea' : fpoint P q r d (0, γ6, -γ6) = a' := by rw [k17f_fp, ha'2]; module
  have Eb' : fpoint P q r d (α1, β1 * (1 - β6), -β1) = b' := by rw [k17f_fp, hb'2]; try module
  have Ec' : fpoint P q r d (α1, β1 * γ6, 0) = c' := by rw [k17f_fp, hc'2]; module
  -- metric facts
  have hF1 : ⟪a', r⟫ < ⟪c, r⟫ := by
    have e : ⟪c - a', b - a'⟫ = γ6 * ⟪c - a', r⟫ := by rw [hγr, inner_smul_right]
    have : 0 < ⟪c - a', r⟫ := by
      by_contra hn; push Not at hn; nlinarith [mul_nonneg hγ6.le (neg_nonneg.2 hn)]
    rw [inner_sub_left] at this; linarith
  have hF2 : 0 ≤ ⟪b', r⟫ - ⟪c', r⟫ := by
    have e : γ6 * (⟪b', r⟫ - ⟪c', r⟫) = ⟪b' - c', b - a'⟫ := by
      rw [hγr, inner_smul_right, inner_sub_left]
    have : 0 ≤ ⟪b' - c', b - a'⟫ := by rw [k4]; nlinarith
    by_contra hn; push Not at hn
    nlinarith [mul_pos hγ6 (neg_pos.2 hn)]
  have hbc : b' - c' = β1 • (c - b) := by rw [hb', hc']; module
  have hcbq : ⟪c - b, q⟫ < 0 := by
    have : ⟪c - b, q⟫ = γ6⁻¹ * ⟪c - b, b - d⟫ := by rw [hq, inner_smul_right]
    rw [this]; exact mul_neg_of_pos_of_neg (inv_pos.2 hγ6) k2
  have hcbP : ⟪c - b, P⟫ = 0 := by rw [hP]; exact k3
  refine ⟨r, hr0, ?_⟩
  refine k18_cone_cell (V8 a a' b b' c c' d) P q r d hΔ (k := 4) (by norm_num) (k24mtaY α1 β1 β6 γ6)
    (k24mtaY_inj hα1 (by linarith) hβ6 hγ6) ?_ [(-1, 0), (0, -1), (-(γ6 * (β1 - 1)), α1)] (by simp) ?_ ?_ ?_
    (ρ1 := -1) (ρ2 := 0) (δ1 := 0) (δ2 := -1) ?_
  · intro i
    rcases k19_z4_cases i with rfl | rfl | rfl | rfl
    · rw [k24mtaY_0, Ea']; simp [V8]
    · rw [k24mtaY_1, Ec]; simp [V8]
    · rw [k24mtaY_2, Eb']; simp [V8]
    · rw [k24mtaY_3, Ec']; simp [V8]
  · intro v1 v2 hC D hD
    have h1 := hC (-1, 0) (by simp)
    have h2 := hC (0, -1) (by simp)
    have h3 := hC (-(γ6 * (β1 - 1)), α1) (by simp)
    simp only at h1 h2 h3
    exact (k24mta_tsc hD hα1 hβ1 hβ6 hγ6 hγ61 (by linarith) (by linarith) (by linarith)).1
  · intro y hy hyx
    have hV : y = fpoint P q r d (0, γ6, -γ6) ∨ y = fpoint P q r d (0, 1 - β6, -1) ∨
        y = fpoint P q r d (α1, β1 * (1 - β6), -β1) ∨ y = fpoint P q r d (α1, β1 * γ6, 0) ∨
        y = fpoint P q r d (1, 0, 0) ∨ y = fpoint P q r d (0, 0, 0) ∨ y = fpoint P q r d (0, γ6, 0) := by
      rw [Ea', Ec, Eb', Ec', Ea, Ed, Eb]
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    have hT : ∀ v1 v2 : ℝ, k18Cone [(-1, 0), (0, -1), (-(γ6 * (β1 - 1)), α1)] v1 v2 → ∀ D : ℝ, 0 < D →
        ∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (1, 0, 0), (0, γ6, 0)], ∀ i : ZMod 4,
          TSc D (k24mtaY α1 β1 β6 γ6 (i + 1) - k24mtaY α1 β1 β6 γ6 i) (t - k24mtaY α1 β1 β6 γ6 i) (v1, v2, 0) := by
      intro v1 v2 hC D hD
      have h1 := hC (-1, 0) (by simp)
      have h2 := hC (0, -1) (by simp)
      have h3 := hC (-(γ6 * (β1 - 1)), α1) (by simp)
      simp only at h1 h2 h3
      exact (k24mta_tsc hD hα1 hβ1 hβ6 hγ6 hγ61 (by linarith) (by linarith) (by linarith)).2
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by rw [k24mtaY_0])).elim
    · exact (hyx 1 (by rw [k24mtaY_1])).elim
    · exact (hyx 2 (by rw [k24mtaY_2])).elim
    · exact (hyx 3 (by rw [k24mtaY_3])).elim
    · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
    · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
    · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
  · intro v1 v2 hC hw
    obtain ⟨p0, p1, p2, p3, m0, m1, m2, m3⟩ := k19_z4
    have h2 := hC (0, -1) (by simp)
    simp only at h2
    have hv2 : v2 < 0 := by linarith
    have hF2' : LexLt (⟪c', r⟫, ⟪c', fcomb P q r v1 v2 0⟫) (⟪b', r⟫, ⟪b', fcomb P q r v1 v2 0⟫) := by
      rcases hF2.lt_or_eq with h | h
      · left; simp only; linarith
      · right
        refine ⟨by simp only; linarith, ?_⟩
        simp only
        have e : ⟪b' - c', fcomb P q r v1 v2 0⟫ = β1 * (v1 * 0 + v2 * ⟪c - b, q⟫) := by
          rw [hbc, inner_smul_left]
          simp only [fcomb, zero_smul, add_zero, inner_add_right, inner_smul_right, hcbP]
          simp
        rw [inner_sub_left] at e
        nlinarith [mul_pos (by linarith : (0:ℝ) < β1) (mul_pos_of_neg_of_neg hv2 hcbq)]
    have hd : (⟪c, r⟫, ⟪c, fcomb P q r v1 v2 0⟫) ≠ (⟪b', r⟫, ⟪b', fcomb P q r v1 v2 0⟫) := by
      intro e
      have := hw 1 2 (by rw [k24mtaY_1, k24mtaY_2, Ec, Eb']; exact congrArg Prod.fst e)
        (by rw [k24mtaY_1, k24mtaY_2, Ec, Eb']; exact congrArg Prod.snd e)
      revert this; decide
    rcases lexLt_total hd with h | h
    · refine k19_lexUni_nb _ _ hw 2 ?_ ?_ ?_
      · rw [m2]; simp only [k24mtaY_1, k24mtaY_2, Ec, Eb']; exact h
      · rw [p2]; simp only [k24mtaY_3, k24mtaY_2, Ec', Eb']; exact hF2'
      · intro i hi
        rcases k19_z4_cases i with rfl | rfl | rfl | rfl
        · right; rw [p0]; left; simp only [k24mtaY_0, k24mtaY_1, Ea', Ec]; exact hF1
        · right; rw [p1]; simp only [k24mtaY_1, k24mtaY_2, Ec, Eb']; exact h
        · exact absurd rfl hi
        · left; rw [m3]; simp only [k24mtaY_3, k24mtaY_2, Ec', Eb']; exact hF2'
    · refine k19_lexUni_nb _ _ hw 1 ?_ ?_ ?_
      · rw [m1]; left; simp only [k24mtaY_0, k24mtaY_1, Ea', Ec]; exact hF1
      · rw [p1]; simp only [k24mtaY_2, k24mtaY_1, Eb', Ec]; exact h
      · intro i hi
        rcases k19_z4_cases i with rfl | rfl | rfl | rfl
        · right; rw [p0]; left; simp only [k24mtaY_0, k24mtaY_1, Ea', Ec]; exact hF1
        · exact absurd rfl hi
        · left; rw [m2]; simp only [k24mtaY_2, k24mtaY_1, Eb', Ec]; exact h
        · left; rw [m3]; simp only [k24mtaY_3, k24mtaY_2, Ec', Eb']; exact hF2'
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · left; norm_num
    · right; refine ⟨by norm_num, by norm_num⟩
    · left; simp only; nlinarith

end C2
end Type08Sp
end Minimality
