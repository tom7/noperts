module

public import Minimality.Type08S.C2K28L2a1

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem k28l2a_step_lt {p q r d : ℝ³} {L : List (ℝ × ℝ)} {s t : ℝ × ℝ × ℝ}
    (h : ⟪fpoint p q r d s, r⟫ < ⟪fpoint p q r d t, r⟫) : K25Step p q r d L s t :=
  ⟨h.le, fun e => absurd e h.ne⟩

set_option maxHeartbeats 12800000 in
/-- Core of leaf A: frame `(a-d, b-d, R)`, `R = (c-d) + ρ (a-d)`, pentagon `(b',a,c',a',c)`. -/
theorem k28l2a_core {a a' b b' c c' d R : ℝ³} {α1 β1 β6 γ6 ρ mp mq : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 1 < β6) (hγ6 : 1 < γ6) (hσ : β1 < β6 + γ6)
    (hρ : 0 < ρ) (hx1 : α1 - 1 < β1 * ρ) (hx2 : (β1 - 1) * ρ < α1)
    (hR : R = (c - d) + ρ • (a - d))
    (hmp : mp < 0) (hm1 : ⟪a - c', a - d⟫ = mp) (hm2 : ⟪a - c', b - d⟫ = mq)
    (hle : ⟪c', R⟫ ≤ ⟪a, R⟫) (hz1 : ⟪a, R⟫ < ⟪b', R⟫) (hz2 : ⟪c, R⟫ < ⟪b', R⟫)
    (hz3 : ⟪a', R⟫ < ⟪c', R⟫ ∨ ⟪a', R⟫ < ⟪c, R⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨P, hP⟩ : ∃ P : ℝ³, P = a - d := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ³, Q = b - d := ⟨_, rfl⟩
  have hΔ : det3 P Q R ≠ 0 := by
    have e : det3 P Q R = det3 (a - d) (b - d) (c - d) := by
      rw [hR, hP, hQ]
      simp only [det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e]; exact hdet
  have Ea : fpoint P Q R d (1, 0, 0) = a := by rw [k17f_fp, hP]; module
  have Ed : fpoint P Q R d (0, 0, 0) = d := by rw [k17f_fp]; module
  have Eb : fpoint P Q R d (0, 1, 0) = b := by rw [k17f_fp, hQ]; module
  have Ec : fpoint P Q R d (-ρ, 0, 1) = c := by rw [k17f_fp, hR, hP]; module
  have Ea' : fpoint P Q R d (-(γ6 * ρ), β6, γ6) = a' := by rw [ha', k17f_fp, hR, hP, hQ]; module
  have Eb' : fpoint P Q R d (α1 - β1 * ρ, 0, β1) = b' := by rw [hb', k17f_fp, hR, hP]; module
  have Ec' : fpoint P Q R d (α1, β1, 0) = c' := by rw [hc', k17f_fp, hP, hQ]; module
  have hmp' : ⟪a - c', P⟫ = mp := by rw [hP]; exact hm1
  have hmq' : ⟪a - c', Q⟫ = mq := by rw [hQ]; exact hm2
  refine ⟨R, k17f_r0 hΔ, ?_⟩
  refine k25_tie_cell (V8 a a' b b' c c' d) P Q R d hΔ (k := 5) (by norm_num) (k28l2aY α1 β1 β6 γ6 ρ)
    (k28l2aY_inj hα1 hβ1 hβ6 hγ6 hρ hx1 hx2) ?_ [(0, 1), (mp, mq)] (by simp) ?_ ?_
    0 ?_ ?_ ?_ (ρ1 := mq - 1) (ρ2 := -mp) (δ1 := 0) (δ2 := 0) ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · rw [k28l2aY_0, Eb']; simp [V8]
    · rw [k28l2aY_1, Ea]; simp [V8]
    · rw [k28l2aY_2, Ec']; simp [V8]
    · rw [k28l2aY_3, Ea']; simp [V8]
    · rw [k28l2aY_4, Ec]; simp [V8]
  · intro v1 v2 hC D hD
    have h1 := hC (0, 1) (by simp)
    simp only at h1
    exact (k28l2a_tsc (v1 := v1) hD hα1 hβ1 hβ6 hγ6 hσ hρ hx1 hx2 (by linarith)).1
  · intro y hy hyx
    have hV : y = fpoint P Q R d (α1 - β1 * ρ, 0, β1) ∨ y = fpoint P Q R d (1, 0, 0) ∨
        y = fpoint P Q R d (α1, β1, 0) ∨ y = fpoint P Q R d (-(γ6 * ρ), β6, γ6) ∨
        y = fpoint P Q R d (-ρ, 0, 1) ∨ y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (0, 1, 0) := by
      rw [Eb', Ea, Ec', Ea', Ec, Ed, Eb]
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    have hT : ∀ v1 v2 : ℝ, k18Cone [(0, 1), (mp, mq)] v1 v2 → ∀ D : ℝ, 0 < D →
        ∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 1, 0)], ∀ i : ZMod 5,
          TSc D (k28l2aY α1 β1 β6 γ6 ρ (i + 1) - k28l2aY α1 β1 β6 γ6 ρ i)
            (t - k28l2aY α1 β1 β6 γ6 ρ i) (v1, v2, 0) := by
      intro v1 v2 hC D hD
      have h1 := hC (0, 1) (by simp)
      simp only at h1
      exact (k28l2a_tsc (v1 := v1) hD hα1 hβ1 hβ6 hγ6 hσ hρ hx1 hx2 (by linarith)).2
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by rw [k28l2aY_0])).elim
    · exact (hyx 1 (by rw [k28l2aY_1])).elim
    · exact (hyx 2 (by rw [k28l2aY_2])).elim
    · exact (hyx 3 (by rw [k28l2aY_3])).elim
    · exact (hyx 4 (by rw [k28l2aY_4])).elim
    · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
    · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
  · obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
    rw [e0, k28l2aY_4, k28l2aY_0]; apply k28l2a_step_lt; rw [Ec, Eb']; exact hz2
  · obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
    rw [f0, k28l2aY_1, k28l2aY_0]; apply k28l2a_step_lt; rw [Ea, Eb']; exact hz1
  · obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
    intro i hi
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hi
    · left; rw [e1, k28l2aY_1, k28l2aY_0]; apply k28l2a_step_lt; rw [Ea, Eb']; exact hz1
    · left; rw [e2, k28l2aY_2, k28l2aY_1]
      refine ⟨by rw [Ec', Ea]; exact hle, fun _ v1 v2 hC => ?_⟩
      have h2 := hC (mp, mq) (by simp)
      simp only at h2
      rw [Ec', Ea, hmp', hmq']; exact h2
    · rcases hz3 with h | h
      · left; rw [e3, k28l2aY_3, k28l2aY_2]; apply k28l2a_step_lt; rw [Ea', Ec']; exact h
      · right; rw [f3, k28l2aY_3, k28l2aY_4]; apply k28l2a_step_lt; rw [Ea', Ec]; exact h
    · right; rw [f4, k28l2aY_4, k28l2aY_0]; apply k28l2a_step_lt; rw [Ec, Eb']; exact hz2
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · left; simp only; linarith
    · left; simp only; nlinarith

end C2
end Type08Sp
end Minimality
