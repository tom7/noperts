module

public import Minimality.Type08S.C2K24MTbA
public import Minimality.Type08S.C2K19C
public import Minimality.Type08S.C2K14D

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
/-- Type 08 M-stratum double tie `K14mTie`, side 1, literal `L = ⟪b-c, b-a'⟫ > 0`: the view `a - b'` cone cell with
silhouette cycle `(d, a, c', a', c)`.  No `Rel` hypothesis is needed. -/
theorem k24mt_gt {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ} (W : Norm08w a a' b b' c c' d)
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (h : 1 < α1 ∧ 1 < β1 ∧ 1 < β6 ∧ γ6 < 1 ∧ ⟪c - a', a - b'⟫ = 0 ∧ ⟪c' - a', a - b'⟫ = 0)
    (hL : 0 < ⟪b - c, b - a'⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hdet, hc', hb', ha', hα1p, hβ1p, h1, hβ6p, hγ6p, h3⟩ := hC
  obtain ⟨hM1, hM2, hM3⟩ := hM
  obtain ⟨hα1, hβ1, hβ6, hγ6, T1, T2⟩ := h
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ α1 = 1 + β1 * s :=
    ⟨(α1 - 1) / β1, div_pos (by linarith) (by linarith), by field_simp; ring⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ³, R = (-s) • (a - d) - (c - d) := ⟨_, rfl⟩
  have hΔ : det3 (a - d) (b - d) R ≠ 0 := by
    intro h0; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = - det3 (a - d) (b - d) R := by
      rw [hR]; simp only [det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e, h0]; simp
  have hR0 : R ≠ 0 := k17f_r0 hΔ
  have hcd : c - d = (-s) • (a - d) - R := by rw [hR]; module
  have hab' : a - b' = β1 • R := by rw [hb', hR]; module
  have hcb : c' - b = (1 + β1 * s) • (a - d) + (β1 - 1) • (b - d) := by rw [hc']; module
  have hsPQ : s • (a - d) + (b - d) = (b - c) - R := by rw [hR]; module
  have Ea : fpoint (a - d) (b - d) R d (1, 0, 0) = a := by rw [k17f_fp]; module
  have Ed : fpoint (a - d) (b - d) R d (0, 0, 0) = d := by rw [k17f_fp]; module
  have Eb : fpoint (a - d) (b - d) R d (0, 1, 0) = b := by rw [k17f_fp]; module
  have Ec : fpoint (a - d) (b - d) R d (-s, 0, -1) = c := by rw [k17f_fp, hR]; module
  have Ec' : fpoint (a - d) (b - d) R d (1 + β1 * s, β1, 0) = c' := by rw [k17f_fp, hc']; module
  have Ea' : fpoint (a - d) (b - d) R d (-(γ6 * s), β6, -γ6) = a' := by rw [k17f_fp, ha', hR]; module
  have Eb' : fpoint (a - d) (b - d) R d (1, 0, -β1) = b' := by rw [k17f_fp, hb', hR]; module
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint (a - d) (b - d) R d t, R⟫ =
      ⟪d, R⟫ + t.1 * ⟪a - d, R⟫ + t.2.1 * ⟪b - d, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  -- depth facts
  have hnr : ⟪R, R⟫ = -s * ⟪a - d, R⟫ - ⟪c - d, R⟫ := by
    have : ⟪c - d, R⟫ = -s * ⟪a - d, R⟫ - ⟪R, R⟫ := by
      rw [hcd]; simp only [inner_sub_left, inner_smul_left, conj_trivial]
    linarith
  have hPb : ⟪a - d, b - c⟫ = 0 := hM1
  have hQb : 0 < ⟪b - d, b - c⟫ := by
    have e : c' - d = (1 + β1 * s) • (a - d) + β1 • (b - d) := by rw [hc']; module
    rw [e] at hM2
    simp only [inner_add_left, inner_smul_left, conj_trivial, hPb] at hM2
    have : 0 < β1 * ⟪b - d, b - c⟫ := by linarith
    exact (pos_iff_pos_of_mul_pos this).1 (by linarith)
  have hCb : ⟪c - d, b - c⟫ < 0 := by
    have e : b' - d = (1 + β1 * s) • (a - d) + β1 • (c - d) := by rw [hb']; module
    rw [e] at hM3
    simp only [inner_add_left, inner_smul_left, conj_trivial, hPb] at hM3
    nlinarith
  have hYZ : -s * ⟪a - d, R⟫ - ⟪R, R⟫ < ⟪b - d, R⟫ := by
    have e1 : ⟪b - c, R⟫ = ⟪b - d, R⟫ - ⟪c - d, R⟫ := by
      rw [← inner_sub_left]; congr 1; abel
    have e2 : ⟪b - c, R⟫ = -s * ⟪b - c, a - d⟫ - ⟪b - c, c - d⟫ := by
      conv_lhs => rw [hR]
      simp only [inner_sub_right, inner_smul_right]
    have e3 : ⟪b - c, a - d⟫ = 0 := by rw [real_inner_comm]; exact hPb
    have e4 : ⟪b - c, c - d⟫ = ⟪c - d, b - c⟫ := real_inner_comm _ _
    rw [e3, mul_zero] at e2
    linarith
  have hT1 : (1 - γ6) * (-s * ⟪a - d, R⟫ - ⟪R, R⟫) - β6 * ⟪b - d, R⟫ = 0 := by
    have e : c - a' = (1 - γ6) • (c - d) - β6 • (b - d) := by rw [ha']; module
    rw [e, hab', inner_sub_left] at T1
    simp only [inner_smul_left, inner_smul_right, conj_trivial] at T1
    have hz' : ⟪c - d, R⟫ = -s * ⟪a - d, R⟫ - ⟪R, R⟫ := by linarith
    rw [hz'] at T1
    have : β1 * ((1 - γ6) * (-s * ⟪a - d, R⟫ - ⟪R, R⟫) - β6 * ⟪b - d, R⟫) = 0 := by linarith
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 (by linarith)
    · exact h0
  have hT2R : ⟪c' - a', R⟫ = 0 := by
    rw [hab'] at T2
    simp only [inner_smul_right] at T2
    rcases mul_eq_zero.1 T2 with h0 | h0
    · exact absurd h0 (by linarith)
    · exact h0
  have hT2 : (1 + β1 * s) * ⟪a - d, R⟫ + (β1 - β6) * ⟪b - d, R⟫ - γ6 * (-s * ⟪a - d, R⟫ - ⟪R, R⟫) = 0 := by
    have e : c' - a' = (1 + β1 * s) • (a - d) + (β1 - β6) • (b - d) - γ6 • (c - d) := by rw [hc', ha']; module
    rw [e, inner_sub_left, inner_add_left] at hT2R
    simp only [inner_smul_left, conj_trivial] at hT2R
    have hz' : ⟪c - d, R⟫ = -s * ⟪a - d, R⟫ - ⟪R, R⟫ := by linarith
    rw [hz'] at hT2R
    linarith
  obtain ⟨F1, F2, F3⟩ := k24mtb_depth hs hβ1 hβ6 hγ6p hγ6 hYZ hT1 hT2
  -- the tie functional value at the ray
  have hm : 0 < ⟪c' - a', a - d⟫ * s + ⟪c' - a', b - d⟫ := by
    have e1 : ⟪c' - a', a - d⟫ * s + ⟪c' - a', b - d⟫ = ⟪c' - a', (b - c) - R⟫ := by
      rw [← hsPQ]; simp only [inner_add_right, inner_smul_right]; ring
    have e2 : ⟪c' - a', b - c⟫ = ⟪c' - b, b - c⟫ + ⟪b - c, b - a'⟫ := by
      rw [real_inner_comm (b - a') (b - c), ← inner_add_left]; congr 1; abel
    have e3 : ⟪c' - b, b - c⟫ = (β1 - 1) * ⟪b - d, b - c⟫ := by
      rw [hcb]; simp only [inner_add_left, inner_smul_left, conj_trivial, hPb]; ring
    rw [e1, inner_sub_right, hT2R, e2, e3]
    have : 0 < (β1 - 1) * ⟪b - d, b - c⟫ := mul_pos (by linarith) hQb
    linarith
  refine ⟨R, hR0, ?_⟩
  refine k18_cone_cell (V8 a a' b b' c c' d) (a - d) (b - d) R d hΔ (k := 5) (by norm_num)
    (k24mtbY β1 s β6 γ6) (k24mtbY_inj hβ1 hs hγ6p hβ6)
    ?_ [(0, 1), (-1, s), (⟪c' - a', a - d⟫, ⟪c' - a', b - d⟫)] (by simp) ?_ ?_ ?_
    (ρ1 := s) (ρ2 := 1) (δ1 := 0) (δ2 := 1) ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · rw [k24mtbY_0, Ed]; simp [V8]
    · rw [k24mtbY_1, Ea]; simp [V8]
    · rw [k24mtbY_2, Ec']; simp [V8]
    · rw [k24mtbY_3, Ea']; simp [V8]
    · rw [k24mtbY_4, Ec]; simp [V8]
  · intro v1 v2 hC D hD
    have h1 := hC (0, 1) (by simp)
    have h2 := hC (-1, s) (by simp)
    simp only at h1 h2
    exact (k24mtb_tsc hD hβ1 hs hγ6p hγ6 hβ6 (by linarith) (by linarith)).1
  · intro y hy hyx
    have hV : y = fpoint (a - d) (b - d) R d (0, 0, 0) ∨ y = fpoint (a - d) (b - d) R d (1, 0, 0) ∨
        y = fpoint (a - d) (b - d) R d (1 + β1 * s, β1, 0) ∨
        y = fpoint (a - d) (b - d) R d (-(γ6 * s), β6, -γ6) ∨ y = fpoint (a - d) (b - d) R d (-s, 0, -1) ∨
        y = fpoint (a - d) (b - d) R d (0, 1, 0) ∨ y = fpoint (a - d) (b - d) R d (1, 0, -β1) := by
      rw [Ed, Ea, Ec', Ea', Ec, Eb, Eb']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    have hT : ∀ v1 v2 : ℝ, k18Cone [(0, 1), (-1, s), (⟪c' - a', a - d⟫, ⟪c' - a', b - d⟫)] v1 v2 →
        ∀ D : ℝ, 0 < D → ∀ t ∈ [((0 : ℝ), (1 : ℝ), (0 : ℝ)), (1, 0, -β1)], ∀ i : ZMod 5,
          TSc D (k24mtbY β1 s β6 γ6 (i + 1) - k24mtbY β1 s β6 γ6 i) (t - k24mtbY β1 s β6 γ6 i) (v1, v2, 0) := by
      intro v1 v2 hC D hD
      have h1 := hC (0, 1) (by simp)
      have h2 := hC (-1, s) (by simp)
      simp only at h1 h2
      exact (k24mtb_tsc hD hβ1 hs hγ6p hγ6 hβ6 (by linarith) (by linarith)).2
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by rw [k24mtbY_0])).elim
    · exact (hyx 1 (by rw [k24mtbY_1])).elim
    · exact (hyx 2 (by rw [k24mtbY_2])).elim
    · exact (hyx 3 (by rw [k24mtbY_3])).elim
    · exact (hyx 4 (by rw [k24mtbY_4])).elim
    · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
    · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
  · intro v1 v2 hC hw
    obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
    have hw3 := hC (⟪c' - a', a - d⟫, ⟪c' - a', b - d⟫) (by simp)
    simp only at hw3
    have hLex : (0 : ZMod 5) + 1 + 1 = 2 := by decide
    have hne : (0 : ZMod 5) + 1 ≠ 0 := by decide
    refine k19_lexUni_nb2 _ _ hw 0 hne ?_ ?_ ?_
    · rw [e0]; left; simp only [k24mtbY_4, k24mtbY_0, hz]; nlinarith
    · rw [hLex, f0]; left; simp only [k24mtbY_2, k24mtbY_1, hz]; nlinarith
    · intro i hi0 hi1
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · exact absurd rfl hi0
      · exact absurd (by decide) hi1
      · left; rw [e2]; left; simp only [k24mtbY_2, k24mtbY_1, hz]; nlinarith
      · left; rw [e3]; right
        refine ⟨?_, ?_⟩
        · simp only [k24mtbY_3, k24mtbY_2, hz]; nlinarith
        · rw [k24mtbY_3, k24mtbY_2, Ea', Ec']
          have : ⟪c', fcomb (a - d) (b - d) R v1 v2 0⟫ - ⟪a', fcomb (a - d) (b - d) R v1 v2 0⟫ =
              v1 * ⟪c' - a', a - d⟫ + v2 * ⟪c' - a', b - d⟫ := by
            rw [← inner_sub_left]; simp only [fcomb, inner_add_right, inner_smul_right, inner_zero_right]
            ring
          nlinarith
      · right; rw [f4]; left; simp only [k24mtbY_4, k24mtbY_0, hz]; nlinarith
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · left; norm_num
    · right; exact ⟨by ring, by nlinarith⟩
    · left; simp only; linarith

end C2
end Type08Sp
end Minimality
