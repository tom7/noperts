module

public import Minimality.Type08S.C2K24H1B0A
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

set_option maxHeartbeats 3200000 in
/-- `⟪a-d,b-d⟫ < 0` from `Rel`. -/
theorem k24h1b0_m {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hα1 : 1 < α1) (hβ1 : 1 < β1) :
    ⟪a - d, b - d⟫ < 0 ∧ ⟪a - d, c - d⟫ = ⟪a - d, b - d⟫ := by
  obtain ⟨hdet, hc', hb', ha', -, -, -, -, hγ6, -⟩ := hC
  obtain ⟨hm0, hm1, hm2⟩ := hM
  obtain ⟨hr1, hr2⟩ := hrel
  set P := a - d with hP
  set Q := b - d with hQ
  set R := c - d with hR
  have e4 : b - c = Q - R := by rw [hQ, hR]; module
  have e5 : c' - d = α1 • P + β1 • Q := by rw [hc']; module
  have e6 : b' - d = α1 • P + β1 • R := by rw [hb']; module
  rw [e4] at hm0
  rw [e4, e5] at hm1
  rw [e6, e4] at hm2
  have hRP : ⟪R, P⟫ = ⟪P, R⟫ := real_inner_comm _ _
  have hRQ : ⟪R, Q⟫ = ⟪Q, R⟫ := real_inner_comm _ _
  have hPQ : ⟪Q, P⟫ = ⟪P, Q⟫ := real_inner_comm _ _
  have hcs := k24h1b0_cs hdet
  simp only [inner_smul_right, inner_sub_right, inner_add_right, inner_smul_left,
    inner_sub_left, inner_add_left, conj_trivial, hRP, hRQ, hPQ] at hm0 hm1 hm2
  have hr1' : α1 * ⟪P, Q⟫ * (⟪Q, Q⟫ + ⟪R, R⟫ - 2 * ⟪Q, R⟫) =
      -(β1 - 1) * (⟪Q, Q⟫ * ⟪R, R⟫ - ⟪Q, R⟫ ^ 2) := hr1
  have hPR : ⟪P, R⟫ = ⟪P, Q⟫ := by linarith
  rw [hPR] at hm1 hm2
  have hqq : ⟪Q, R⟫ < ⟪Q, Q⟫ := by nlinarith
  have hrr : ⟪Q, R⟫ < ⟪R, R⟫ := by nlinarith
  have hD : 0 < ⟪Q, Q⟫ * ⟪R, R⟫ - ⟪Q, R⟫ ^ 2 := by linarith
  have hW : 0 < ⟪Q, Q⟫ + ⟪R, R⟫ - 2 * ⟪Q, R⟫ := by linarith
  refine ⟨?_, hPR⟩
  by_contra hn; push_neg at hn
  have := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ α1) hn) hW.le
  nlinarith [mul_pos (sub_pos.2 hβ1) hD]

set_option maxHeartbeats 12800000 in
/-- Type 08 M-stratum H1 tie, side `N2 = ⟪a-b', a'-c'⟫ > 0`: cell B, view `a - b'`, silhouette `(b', c', a', c)`. -/
theorem k24h1_B0 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hH1 : K6mH1Left a a' b b' c c' d α1 β1 β6 γ6)
    (ht : ⟪c - a', a - b'⟫ = 0) (hN : ⟪a - b', a' - c'⟫ = 0)
    (hW : 0 < ⟪a' - c', c - b⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  have hTT := k24h1b0_T hC hM hrel hH1.1 ht
  obtain ⟨⟨hα1, hβ1, -, hβ6, hγ61⟩, -, -⟩ := hH1
  obtain ⟨hmneg, hmeq⟩ := k24h1b0_m hC hM hrel hα1 hβ1
  obtain ⟨hdet, hc', hb', ha', hα1p, hβ1p, h1, hβ6p, hγ6p, h3⟩ := hC
  obtain ⟨hM1, hM2, hM3⟩ := hM
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
  -- metric facts
  have hCb : ⟪c - d, b - c⟫ < 0 := by
    have e : b' - d = (1 + β1 * s) • (a - d) + β1 • (c - d) := by rw [hb']; module
    rw [e] at hM3
    simp only [inner_add_left, inner_smul_left, conj_trivial, hM1] at hM3
    nlinarith
  have hbcR : 0 < ⟪b - c, R⟫ := by
    have : ⟪b - c, R⟫ = -s * ⟪b - c, a - d⟫ - ⟪b - c, c - d⟫ := by
      rw [hR]; simp only [inner_sub_right, inner_smul_right]
    have e3 : ⟪b - c, a - d⟫ = 0 := by rw [real_inner_comm]; exact hM1
    have e4 : ⟪b - c, c - d⟫ = ⟪c - d, b - c⟫ := real_inner_comm _ _
    rw [this, e3, e4]; linarith
  have hF1 : 0 < ⟪c' - b', R⟫ := by
    have : c' - b' = β1 • (b - c) := by rw [hc', hb']; module
    rw [this, inner_smul_left]; simpa using mul_pos (by linarith : (0:ℝ) < β1) hbcR
  have hF2 : ⟪a' - c', R⟫ = 0 := by
    rw [hab'] at hN
    simp only [inner_smul_left, conj_trivial] at hN
    rw [real_inner_comm] at hN
    rcases mul_eq_zero.1 hN with h0 | h0
    · exact absurd h0 (by linarith)
    · exact h0
  have hF3 : ⟪c - a', R⟫ = 0 := by
    rw [hab'] at ht
    simp only [inner_smul_right] at ht
    rcases mul_eq_zero.1 ht with h0 | h0
    · exact absurd h0 (by linarith)
    · exact h0
  have hT1 : 0 < ⟪c - a', a - d⟫ := by
    have e : c - a' = (1 - γ6) • (c - d) - β6 • (b - d) := by rw [ha']; module
    rw [e]
    rw [inner_sub_left, inner_smul_left, inner_smul_left, real_inner_comm (a - d) (c - d),
      real_inner_comm (a - d) (b - d), hmeq]
    simp only [conj_trivial]
    nlinarith
  refine ⟨R, hR0, ?_⟩
  refine k18_cone_cell (V8 a a' b b' c c' d) (a - d) (b - d) R d hΔ (k := 4) (by norm_num)
    (k24h1b0Y β1 s β6 γ6) (k24h1b0Y_inj hβ1 hs hγ6p hβ6)
    ?_ [(0, -1), (1, -s), (⟪c - a', a - d⟫, ⟪c - a', b - d⟫), (⟪a' - c', a - d⟫, ⟪a' - c', b - d⟫)] (by simp) ?_ ?_ ?_
    (ρ1 := -s) (ρ2 := -1) (δ1 := s) (δ2 := 0) ?_
  · intro i
    rcases k19_z4_cases i with rfl | rfl | rfl | rfl
    · rw [k24h1b0Y_0, Eb']; simp [V8]
    · rw [k24h1b0Y_1, Ec']; simp [V8]
    · rw [k24h1b0Y_2, Ea']; simp [V8]
    · rw [k24h1b0Y_3, Ec]; simp [V8]
  · intro v1 v2 hC D hD
    have h1 := hC (0, -1) (by simp)
    have h2 := hC (1, -s) (by simp)
    simp only at h1 h2
    exact (k24h1b0_tsc hD hβ1 hs hγ6p hβ6 (by linarith) (by linarith)).1
  · intro y hy hyx
    have hV : y = fpoint (a - d) (b - d) R d (1, 0, -β1) ∨ y = fpoint (a - d) (b - d) R d (1 + β1 * s, β1, 0) ∨
        y = fpoint (a - d) (b - d) R d (-(γ6 * s), β6, -γ6) ∨ y = fpoint (a - d) (b - d) R d (-s, 0, -1) ∨
        y = fpoint (a - d) (b - d) R d (0, 0, 0) ∨ y = fpoint (a - d) (b - d) R d (1, 0, 0) ∨
        y = fpoint (a - d) (b - d) R d (0, 1, 0) := by
      rw [Eb', Ec', Ea', Ec, Ed, Ea, Eb]
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    have hT : ∀ v1 v2 : ℝ, k18Cone [(0, -1), (1, -s), (⟪c - a', a - d⟫, ⟪c - a', b - d⟫), (⟪a' - c', a - d⟫, ⟪a' - c', b - d⟫)] v1 v2 →
        ∀ D : ℝ, 0 < D → ∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (1, 0, 0), (0, 1, 0)], ∀ i : ZMod 4,
          TSc D (k24h1b0Y β1 s β6 γ6 (i + 1) - k24h1b0Y β1 s β6 γ6 i) (t - k24h1b0Y β1 s β6 γ6 i) (v1, v2, 0) := by
      intro v1 v2 hC D hD
      have h1 := hC (0, -1) (by simp)
      have h2 := hC (1, -s) (by simp)
      simp only at h1 h2
      exact (k24h1b0_tsc hD hβ1 hs hγ6p hβ6 (by linarith) (by linarith)).2
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by rw [k24h1b0Y_0])).elim
    · exact (hyx 1 (by rw [k24h1b0Y_1])).elim
    · exact (hyx 2 (by rw [k24h1b0Y_2])).elim
    · exact (hyx 3 (by rw [k24h1b0Y_3])).elim
    · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
    · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
    · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
  · intro v1 v2 hC hw
    obtain ⟨p0, p1, p2, p3, m0, m1, m2, m3⟩ := k19_z4
    have hw3 := hC (⟪c - a', a - d⟫, ⟪c - a', b - d⟫) (by simp)
    simp only at hw3
    have zb : ⟪b', R⟫ < ⟪c', R⟫ := by rw [inner_sub_left] at hF1; linarith
    have zc : ⟪c', R⟫ = ⟪a', R⟫ := by rw [inner_sub_left] at hF2; linarith
    have hw4 := hC (⟪a' - c', a - d⟫, ⟪a' - c', b - d⟫) (by simp)
    simp only at hw4
    have wac : ⟪c', fcomb (a - d) (b - d) R v1 v2 0⟫ < ⟪a', fcomb (a - d) (b - d) R v1 v2 0⟫ := by
      have : ⟪a', fcomb (a - d) (b - d) R v1 v2 0⟫ - ⟪c', fcomb (a - d) (b - d) R v1 v2 0⟫ =
          v1 * ⟪a' - c', a - d⟫ + v2 * ⟪a' - c', b - d⟫ := by
        rw [← inner_sub_left]; simp only [fcomb, inner_add_right, inner_smul_right, inner_zero_right]
        ring
      nlinarith
    have za : ⟪a', R⟫ = ⟪c, R⟫ := by rw [inner_sub_left] at hF3; linarith
    have wca : ⟪a', fcomb (a - d) (b - d) R v1 v2 0⟫ < ⟪c, fcomb (a - d) (b - d) R v1 v2 0⟫ := by
      have : ⟪c, fcomb (a - d) (b - d) R v1 v2 0⟫ - ⟪a', fcomb (a - d) (b - d) R v1 v2 0⟫ =
          v1 * ⟪c - a', a - d⟫ + v2 * ⟪c - a', b - d⟫ := by
        rw [← inner_sub_left]; simp only [fcomb, inner_add_right, inner_smul_right, inner_zero_right]
        ring
      nlinarith
    refine k19_lexUni_nb _ _ hw 3 ?_ ?_ ?_
    · rw [show (3 : ZMod 4) - 1 = 2 by decide]
      right; refine ⟨?_, ?_⟩
      · simp only [k24h1b0Y_2, k24h1b0Y_3, Ea', Ec]; exact za
      · simp only [k24h1b0Y_2, k24h1b0Y_3, Ea', Ec]; exact wca
    · rw [show (3 : ZMod 4) + 1 = 0 by decide]
      left; simp only [k24h1b0Y_0, k24h1b0Y_3, Eb', Ec]
      have : ⟪b', R⟫ < ⟪c, R⟫ := by linarith
      exact this
    · intro i hi
      rcases k19_z4_cases i with rfl | rfl | rfl | rfl
      · right; rw [p0]; left; simp only [k24h1b0Y_0, k24h1b0Y_1, Eb', Ec']; exact zb
      · right; rw [p1]; right; simp only [k24h1b0Y_1, k24h1b0Y_2, Ec', Ea']; exact ⟨zc, wac⟩
      · right; rw [p2]; right; simp only [k24h1b0Y_2, k24h1b0Y_3, Ea', Ec]; exact ⟨za, wca⟩
      · exact absurd rfl hi
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · left; norm_num
    · right; refine ⟨?_, ?_⟩ <;> simp only <;> linarith
    · left; simp only
      have e : c - b = (-s) • (a - d) - (b - d) - R := by rw [hR]; module
      rw [e] at hTT
      rw [inner_sub_right, inner_sub_right, inner_smul_right, hF3] at hTT
      linarith
    · left; simp only
      have e : c - b = (-s) • (a - d) - (b - d) - R := by rw [hR]; module
      rw [e] at hW
      rw [inner_sub_right, inner_sub_right, inner_smul_right, hF2] at hW
      linarith

end C2
end Type08Sp
end Minimality
