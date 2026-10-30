module

public import Minimality.Type08S.P2S3
public import Minimality.CaseC18Vertex
public import Minimality.RobustUnimodal

@[expose] public section

set_option relaxedAutoImplicit true
set_option autoImplicit true
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality

theorem quad_robust_facts {z0 z1 z2 z3 : ℝ} (h : IsRobustUnimodal (quad z0 z1 z2 z3)) :
    ¬ (z1 = z2 ∧ z2 = z3) ∧ ¬ (z0 = z2 ∧ z2 = z3) ∧ (z2 = z3 → ¬ (z1 > z2 ∧ z0 < z2)) := by
  have q0 : quad z0 z1 z2 z3 0 = z0 := rfl
  have q1 : quad z0 z1 z2 z3 1 = z1 := rfl
  have q2 : quad z0 z1 z2 z3 2 = z2 := rfl
  have q3 : quad z0 z1 z2 z3 3 = z3 := rfl
  refine ⟨fun ⟨e1, e2⟩ => ?_, fun ⟨e1, e2⟩ => ?_, fun e ⟨h1, h2⟩ => ?_⟩
  · exact h.noTriple 1 2 3 (by decide) (by decide) (by decide) (by rw [q1, q2, e1]) (by rw [q2, q3, e2])
  · exact h.noTriple 0 2 3 (by decide) (by decide) (by decide) (by rw [q0, q2, e1]) (by rw [q2, q3, e2])
  · have := (h.noLevelRun 1 0 1 2 3 (by omega) (by omega) (by omega) (by omega)
      (by
        have a1 : (1 : ZMod 4) + ((1 : ℕ) : ZMod 4) = 2 := by decide
        have a2 : (1 : ZMod 4) + ((2 : ℕ) : ZMod 4) = 3 := by decide
        rw [a1, a2, q2, q3]; exact e)).2
    apply this
    have a0 : (1 : ZMod 4) + ((0 : ℕ) : ZMod 4) = 1 := by decide
    have a1 : (1 : ZMod 4) + ((1 : ℕ) : ZMod 4) = 2 := by decide
    have a2 : (1 : ZMod 4) + ((2 : ℕ) : ZMod 4) = 3 := by decide
    have a3 : (1 : ZMod 4) + ((3 : ℕ) : ZMod 4) = 0 := by decide
    rw [a0, a1, a2, a3, q0, q1, q2, q3]
    exact ⟨h1, by rw [← e]; exact h2⟩

/-- The depth lemma (draft §3), in absolute depths `Z*`. -/
theorem Tp_depth_sep {Zd Za Zb Zbp Zc Zcp α4 γ4 β1 : ℝ}
    (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hαγ : 1 < α4 + γ4) (hβ1 : 0 < β1) (hb : Zd < Zb)
    (hbp : Zbp - Zd = α4 * (Za - Zd) + γ4 * (Zc - Zd))
    (hcp : Zcp - Zd = (Za - Zd) + β1 * (Zb - Zd))
    (hq : max Zd Zc = max Za Zbp)
    (hrob : IsRobustUnimodal (quad Zb Zcp Zbp Zc))
    (h2 : ¬ IsRobustUnimodal (quad Zd Zcp Zbp Zc)) :
    max (max Zd Za) (max Zbp Zc) < min Zb Zcp := by
  obtain ⟨hT, hT0, hR3⟩ := quad_robust_facts hrob
  obtain ⟨a, ha⟩ : ∃ a, a = Za - Zd := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = Zc - Zd := ⟨_, rfl⟩
  have hbp' : Zbp - Zd = α4 * a + γ4 * c := by rw [hbp, ha, hc]
  have hcp' : Zcp - Zd = a + β1 * (Zb - Zd) := by rw [hcp, ha]
  have hb0 : 0 < Zb - Zd := by linarith
  have hbb : β1 * (Zb - Zd) > 0 := mul_pos hβ1 hb0
  have hsepw : Zd ≤ Zcp ∧ Zbp ≤ Zcp ∧ Zd ≤ Zc ∧ Zbp ≤ Zc := by
    by_contra hcon
    apply h2
    by_cases hA : Zd < Zcp ∨ Zd < Zc ∨ Zbp < Zcp ∨ Zbp < Zc
    · by_cases hB : Zcp < Zd ∨ Zc < Zd ∨ Zcp < Zbp ∨ Zc < Zbp
      · exact CaseC18.robust_quad_of_nws hA hB
      · exfalso
        push Not at hB
        obtain ⟨b1, b2, b3, b4⟩ := hB
        exact hcon ⟨b1, b3, b2, b4⟩
    · exfalso
      push Not at hA
      obtain ⟨b1, b2, b3, b4⟩ := hA
      have hcc : c ≤ 0 := by linarith
      have hcpa : a + β1 * (Zb - Zd) ≤ 0 := by linarith
      have had : a < 0 := by linarith
      have hbp1 : α4 * a + γ4 * c ≥ c := by linarith
      have hbp2 : α4 * a + γ4 * c ≥ a + β1 * (Zb - Zd) := by linarith
      rcases lt_or_ge a c with hac | hac
      · nlinarith [mul_pos hα4 (sub_pos.2 hac), mul_nonneg (sub_pos.2 hαγ).le (neg_nonneg.2 hcc)]
      · nlinarith [mul_neg_of_pos_of_neg (sub_pos.2 hαγ) had, mul_nonneg hγ4.le (sub_nonneg.2 hac)]
  obtain ⟨s1, s2, s3, s4⟩ := hsepw
  have hc0 : 0 ≤ c := by linarith
  have hq' : Zc = max Za Zbp := by rw [max_eq_right s3] at hq; exact hq
  have hZ : Zbp = Zc := by
    rcases max_choice Za Zbp with h | h
    · rw [h] at hq'
      have hca : a = c := by rw [ha, hc, hq']
      have : Zbp - Zd = (α4 + γ4) * c := by rw [hbp', hca]; ring
      nlinarith [mul_nonneg (sub_pos.2 hαγ).le hc0]
    · rw [h] at hq'; exact hq'.symm
  have hcpgt : Zbp < Zcp := by
    rcases lt_or_eq_of_le s2 with h | h
    · exact h
    · exact absurd ⟨h.symm, hZ⟩ hT
  have hbgt : Zbp < Zb := by
    rcases lt_or_ge Zbp Zb with h | h
    · exact h
    · rcases lt_or_eq_of_le h with h' | h'
      · exact absurd ⟨hcpgt, h'⟩ (hR3 hZ)
      · exact absurd ⟨h', hZ⟩ hT0
  have haZ : Za ≤ Zc := by rw [hq']; exact le_max_left _ _
  simp only [max_lt_iff, lt_min_iff]
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

end Minimality
