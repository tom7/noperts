module

public import Minimality.Type08S.C2K22T1A

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
/-- Pc corner C2, tie T1 (`β1 = 1`): cell X3 pentagon at `a - d`. -/
theorem k22t1_cell {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K6t3LeftPc a a' b b' c c' d)
    (hC2 : 0 < ⟪a - d, a - c'⟫ ∧ ⟪c - d, c - a'⟫ = 0 ∧ ⟪b' - c, d - b⟫ = 0)
    (hβ : c' = d + (1 : ℝ) • (a - d) + (1 : ℝ) • (b - d)) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hPc, hca, -⟩ := h
  obtain ⟨β1, γ4, γ6, hdet, hc', hb', ha', hβ1, hγ4p, hγ6, hγ61, -⟩ := k17gc_pc_frame W hPc
  obtain ⟨hlit, hc2, hb2⟩ := hC2
  set P := b - d with hP
  set Q := c - d with hQ
  set R := a - d with hR
  have hΔ : det3 P Q R ≠ 0 := by
    intro h; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = det3 P Q R := by simp only [hP, hQ, hR, det3_expand]; ring
    rw [e, h]
  have hP0 : P ≠ 0 := by intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  have hβ1e : β1 = 1 := by
    have h1 : (β1 - 1) • P = 0 := by
      have := hc'.symm.trans hβ
      rw [hP]
      have h2 := add_left_cancel this
      rw [sub_smul, h2, one_smul]; simp
    rcases smul_eq_zero.1 h1 with h | h
    · linarith
    · exact absurd h hP0
  subst hβ1e
  have Ea : fpoint P Q R d (0, 0, 1) = a := by rw [k17f_fp, hR]; module
  have Ed : fpoint P Q R d (0, 0, 0) = d := by rw [k17f_fp]; module
  have Eb : fpoint P Q R d (1, 0, 0) = b := by rw [k17f_fp, hP]; module
  have Ec : fpoint P Q R d (0, 1, 0) = c := by rw [k17f_fp, hQ]; module
  have Ea' : fpoint P Q R d (1, γ6, 0) = a' := by rw [k17f_fp, ha']; module
  have Eb' : fpoint P Q R d (0, γ4, 1) = b' := by rw [k17f_fp, hb']; module
  have Ec' : fpoint P Q R d (1, 0, 1) = c' := by rw [k17f_fp, hc']; module
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hR0 : R ≠ 0 := k17f_r0 hΔ
  have hRR : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
  have hQ0 : Q ≠ 0 := by intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  have hQQ : 0 < ⟪Q, Q⟫ := real_inner_self_pos.2 hQ0
  -- Gram facts
  have eac : a - c' = (-(1:ℝ)) • P := by rw [hc', hP]; module
  have eca : c - a' = (1 - γ6) • Q - P := by rw [ha', hQ, hP]; module
  have ebc : b' - c = R + (γ4 - 1) • Q := by rw [hb', hQ, hR]; module
  have edb : d - b = -P := by rw [hP]; module
  have ecd : c - d = Q := hQ.symm
  have ead : a - d = R := hR.symm
  rw [eac] at hlit
  rw [eca] at hc2
  rw [ebc, edb] at hb2
  rw [eca] at hca
  have hRP : ⟪R, P⟫ = ⟪P, R⟫ := real_inner_comm _ _
  have hRQ : ⟪R, Q⟫ = ⟪Q, R⟫ := real_inner_comm _ _
  have hPQ : ⟪Q, P⟫ = ⟪P, Q⟫ := real_inner_comm _ _
  simp only [inner_smul_right, inner_sub_right, inner_add_right, inner_neg_right, inner_smul_left,
    inner_sub_left, inner_add_left, inner_neg_left, conj_trivial, hRP, hRQ, hPQ] at hlit hc2 hb2 hca
  have hx : ⟪P, R⟫ < 0 := by nlinarith
  have hy : ⟪Q, R⟫ < 0 := by nlinarith
  have hz0 : 0 < ⟪P, Q⟫ := by nlinarith
  have hγ4 : 1 < γ4 := by
    by_contra hn
    push Not at hn
    nlinarith
  refine ⟨R, hR0, ?_⟩
  refine k18_cone_cell (V8 a a' b b' c c' d) P Q R d hΔ (k := 5) (by norm_num) (k22t1Y γ4 γ6)
    (k22t1Y_inj hγ6 hγ4) ?_ [(1, 0), (0, 1)] (by simp) ?_ ?_ ?_
    (ρ1 := 1) (ρ2 := 1) (δ1 := 0) (δ2 := 0) ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · rw [k22t1Y_0, Ea]; simp [V8]
    · rw [k22t1Y_1, Ec']; simp [V8]
    · rw [k22t1Y_2, Eb]; simp [V8]
    · rw [k22t1Y_3, Ea']; simp [V8]
    · rw [k22t1Y_4, Eb']; simp [V8]
  · intro v1 v2 hC D hD
    have h1 := hC (1, 0) (by simp)
    have h2 := hC (0, 1) (by simp)
    simp only at h1 h2
    exact (k22t1_tsc hD hγ4 hγ6 hγ61 (by linarith) (by linarith)).1
  · intro y hy hyx
    have hV : y = fpoint P Q R d (0, 0, 1) ∨ y = fpoint P Q R d (1, 0, 1) ∨ y = fpoint P Q R d (1, 0, 0) ∨
        y = fpoint P Q R d (1, γ6, 0) ∨ y = fpoint P Q R d (0, γ4, 1) ∨ y = fpoint P Q R d (0, 0, 0) ∨
        y = fpoint P Q R d (0, 1, 0) := by
      rw [Ea, Ed, Eb, Ea', Ec, Eb', Ec']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    have hT : ∀ v1 v2 : ℝ, k18Cone [(1, 0), (0, 1)] v1 v2 → ∀ D : ℝ, 0 < D →
        ∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 1, 0)], ∀ i : ZMod 5,
          TSc D (k22t1Y γ4 γ6 (i + 1) - k22t1Y γ4 γ6 i) (t - k22t1Y γ4 γ6 i) (v1, v2, 0) := by
      intro v1 v2 hC D hD
      have h1 := hC (1, 0) (by simp)
      have h2 := hC (0, 1) (by simp)
      simp only at h1 h2
      exact (k22t1_tsc hD hγ4 hγ6 hγ61 (by linarith) (by linarith)).2
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by rw [k22t1Y_0])).elim
    · exact (hyx 1 (by rw [k22t1Y_1])).elim
    · exact (hyx 2 (by rw [k22t1Y_2])).elim
    · exact (hyx 3 (by rw [k22t1Y_3])).elim
    · exact (hyx 4 (by rw [k22t1Y_4])).elim
    · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
    · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
  · intro v1 v2 hC hw
    obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
    refine k19_lexUni_nb _ _ hw 0 ?_ ?_ ?_
    · rw [e0]; left; simp only [k22t1Y_4, k22t1Y_0, hz]; nlinarith
    · rw [f0]; left; simp only [k22t1Y_0, k22t1Y_1, hz]; nlinarith
    · intro i hi
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · exact absurd rfl hi
      · left; rw [e1]; left; simp only [k22t1Y_0, k22t1Y_1, hz]; nlinarith
      · left; rw [e2]; left; simp only [k22t1Y_1, k22t1Y_2, hz]; nlinarith
      · left; rw [e3]; left; simp only [k22t1Y_2, k22t1Y_3, hz]; nlinarith
      · right; rw [f4]; left; simp only [k22t1Y_4, k22t1Y_0, hz]; nlinarith
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> (left; norm_num)

end C2
end Type08Sp
end Minimality
