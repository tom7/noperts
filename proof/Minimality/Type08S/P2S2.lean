module

public import Minimality.Type08S.P2S1

@[expose] public section

set_option relaxedAutoImplicit true
set_option autoImplicit true
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality

theorem Tp_sep_Nex (A B C : ℝ³) {α4 γ4 : ℝ} (hα : α4 < 1) (hH : 0 < det3 A C B) :
    ∃ s : ℝ, 0 < s ∧ (⟪B, B⟫ * ⟪A, (α4 - 1) • A + (s + γ4) • C⟫ -
        ⟪A, B⟫ * ⟪B, (α4 - 1) • A + (s + γ4) • C⟫) ≠ 0 := by
  have hcr : cross A B ≠ 0 := by
    intro h0
    have : det3 A C B = 0 := by
      have e : det3 A C B = - ⟪cross A B, C⟫ := by simp only [det3]; ex
      rw [e, h0]; simp
    linarith
  have hG : 0 < ⟪B, B⟫ * ⟪A, A⟫ - ⟪A, B⟫ * ⟪A, B⟫ := by
    have e : ⟪B, B⟫ * ⟪A, A⟫ - ⟪A, B⟫ * ⟪A, B⟫ = ⟪cross A B, cross A B⟫ := by ex
    rw [e]; exact real_inner_self_pos.2 hcr
  by_contra hcon
  push Not at hcon
  have h1 := hcon 1 one_pos
  have h2 := hcon 2 two_pos
  have e1 : ⟪B, B⟫ * ⟪A, (α4 - 1) • A + (1 + γ4) • C⟫ - ⟪A, B⟫ * ⟪B, (α4 - 1) • A + (1 + γ4) • C⟫
      = (α4 - 1) * (⟪B, B⟫ * ⟪A, A⟫ - ⟪A, B⟫ * ⟪A, B⟫) +
        (1 + γ4) * (⟪B, B⟫ * ⟪A, C⟫ - ⟪A, B⟫ * ⟪B, C⟫) := by ex
  have e2 : ⟪B, B⟫ * ⟪A, (α4 - 1) • A + (2 + γ4) • C⟫ - ⟪A, B⟫ * ⟪B, (α4 - 1) • A + (2 + γ4) • C⟫
      = (α4 - 1) * (⟪B, B⟫ * ⟪A, A⟫ - ⟪A, B⟫ * ⟪A, B⟫) +
        (2 + γ4) * (⟪B, B⟫ * ⟪A, C⟫ - ⟪A, B⟫ * ⟪B, C⟫) := by ex
  rw [e1] at h1; rw [e2] at h2
  have hM : (⟪B, B⟫ * ⟪A, C⟫ - ⟪A, B⟫ * ⟪B, C⟫) = 0 := by linarith
  have : (α4 - 1) * (⟪B, B⟫ * ⟪A, A⟫ - ⟪A, B⟫ * ⟪A, B⟫) = 0 := by rw [hM] at h1; linarith
  have : (α4 - 1) * (⟪B, B⟫ * ⟪A, A⟫ - ⟪A, B⟫ * ⟪A, B⟫) < 0 := mul_neg_of_neg_of_pos (by linarith) hG
  linarith

theorem Tp_sep_core (d A B C : ℝ³) {α4 β1 γ4 β6 γ6 : ℝ}
    (hH : 0 < det3 A C B)
    (hα4 : 0 < α4) (hα : α4 < 1) (hγ4 : 0 < γ4) (hαγ : 1 < α4 + γ4) (hβ1 : 0 < β1)
    (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hsep : max (max 0 ⟪A, B⟫) (max (α4 * ⟪A, B⟫ + γ4 * ⟪C, B⟫) ⟪C, B⟫)
              < min ⟪B, B⟫ (⟪A, B⟫ + β1 * ⟪B, B⟫)) :
    IsRupert (insert d ({d + A, d + β6 • B + γ6 • C, d + B, d + α4 • A + γ4 • C, d + C,
      d + A + β1 • B} : Finset ℝ³)) := by
  obtain ⟨ζ, h1, h2⟩ := exists_between hsep
  simp only [max_lt_iff, lt_min_iff] at h1 h2
  obtain ⟨⟨hz0, hDa⟩, hDb', hDc⟩ := h1
  obtain ⟨hDb, hDc'⟩ := h2
  obtain ⟨s, hs, hNs⟩ := Tp_sep_Nex A B C (γ4 := γ4) hα hH
  set N : ℝ := ⟪B, B⟫ * ⟪A, (α4 - 1) • A + (s + γ4) • C⟫ -
        ⟪A, B⟫ * ⟪B, (α4 - 1) • A + (s + γ4) • C⟫ with hNdef
  have hN : 0 < N * N := mul_self_pos.2 hNs
  obtain ⟨w, hw⟩ : ∃ w : ℝ³, w = (α4 - 1) • A + (s + γ4) • C := ⟨_, rfl⟩
  have key := Tp_sep_rows d A B C w (κ := N) hw hH hα4 hα hγ4 hαγ hβ1 hβ6 hγ6 hγ61 hs hN hz0 hDa hDb'
    hDc hDb hDc'
  have hv0 : ∀ x : ℝ³, cross (cross B w) x + (-(cross (cross B w) d) - ζ • w) =
      (⟪x - d, B⟫ - ζ) • w - ⟪w, x - d⟫ • B := by
    intro x
    ext i; fin_cases i <;> simp [cross, PiLp.inner_apply, Fin.sum_univ_three] <;> ring
  have hv1 : ∀ x : ℝ³, cross (N • B) x + (-(cross (N • B) (d + (1/2 : ℝ) • A))) =
      N • cross B (x - d - (1/2 : ℝ) • A) := by
    intro x
    ext i; fin_cases i <;> simp [cross] <;> ring
  have hu : B ≠ 0 := by
    intro h0; rw [h0] at hH; simp [det3, cross] at hH
  refine isRupert_of_motionCert2 _ B w (cross B w) (N • B) (-(cross (cross B w) d) - ζ • w)
    (-(cross (N • B) (d + (1/2 : ℝ) • A))) hu ?_
  obtain ⟨⟨c1, c2, c3⟩, ⟨d1, d2, d3⟩, ⟨b1, b2, b3⟩, ⟨e1, e2, e3⟩, ⟨a1, a2, a3⟩,
    ⟨p1, p2, p3⟩, ⟨h1, h2, h3, h4⟩⟩ := key
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  unfold MotionCert2
  simp only [hv0, hv1]
  rcases hx with hx | hx | hx | hx | hx | hx | hx <;> rw [hx]
  · -- d
    exact Or.inl ⟨d + C, by simp, d + B, by simp, d1, d2, d3⟩
  · -- a
    exact Or.inl ⟨d + A + β1 • B, by simp, d + α4 • A + γ4 • C, by simp, a1, a2, a3⟩
  · -- a'
    exact Or.inr ⟨d + C, by simp, d, by simp, d + A, by simp, h1, h2, h3, h4⟩
  · -- b
    exact Or.inl ⟨d, by simp, d + A + β1 • B, by simp, b1, b2, b3⟩
  · -- b'
    exact Or.inl ⟨d + A, by simp, d + C, by simp, p1, p2, p3⟩
  · -- c
    exact Or.inl ⟨d + α4 • A + γ4 • C, by simp, d, by simp, c1, c2, c3⟩
  · -- c'
    exact Or.inl ⟨d + B, by simp, d + A, by simp, e1, e2, e3⟩

end Minimality
