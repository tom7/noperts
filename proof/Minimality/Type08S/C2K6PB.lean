module

public import Minimality.Type08S.C2K6PA

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

set_option maxHeartbeats 1600000 in
theorem k6p_qce2z_hasLexCell {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0) (h : ParEndK2 b b' c c' d)
    (hfar1 : W.F.abc'.f c < W.F.abc'.f a') (hfar2 : W.F.a'bc.f c' < W.F.a'bc.f a)
    (hζ : ⟪b - c, a - d⟫ = 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨α1, α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hα1, hβ1, h1, hα4, hγ4, h2, hβ6, hγ6, h3,
    hfa, hfb, hγ, hβ, s', hs0, hs1, e1, e2⟩ := p0_k2_extract W hκ h
  have hγ61 : γ6 < 1 := hfa hfar1
  have hα11 : 1 < α1 := hfb hfar2
  subst hγ hβ
  have hBne := k6p_B_ne h hc' hb' e2
  have hs : 1 < β6 + γ6 := h3
  set p := b - d with hp
  set q := c - d with hq
  set r := a - d with hr
  set m := α1 - α4 + s' * α4 with hm
  have hr0 : r ≠ 0 := by intro h0; rw [h0] at hdet; simp [det3_expand] at hdet
  have hA : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  have hζ' : ⟪b - c, a - d⟫ = -(m * ⟪r, r⟫) := by
    have : b - c = p - q := by rw [hp, hq]; abel
    rw [this, inner_sub_left, real_inner_comm r p, real_inner_comm r q]
    linarith
  have hm0 : m = 0 := by
    have : m * ⟪r, r⟫ = 0 := by rw [hζ'] at hζ; linarith
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hA.ne'
  have hcyc : ∀ x y z : ℝ³, det3 x y z = det3 z x y := by
    intro x y z; simp only [det3_expand]; ring
  have hΔ : det3 p q r ≠ 0 := by rw [hcyc]; exact hdet
  have hΔ' : det3 q p r ≠ 0 := by
    have : det3 q p r = - det3 p q r := by simp only [det3_expand]; ring
    rw [this]; exact neg_ne_zero.2 hΔ
  have hfp : ∀ (u v : ℝ³) (x y z : ℝ), fpoint u v r d (x, y, z) = d + x • u + y • v + z • r := by
    intro u v x y z; simp only [fpoint, fcomb]; module
  have hrdef : r = a - d := rfl
  have eA : a = d + r := by rw [hrdef]; abel
  have eB : b = d + p := by rw [hp]; abel
  have eC : c = d + q := by rw [hq]; abel
  have eC' : c' = d + α1 • r + p := by rw [hc', hr, hp]; module
  have eB' : b' = d + α4 • r + q := by rw [hb', hr, hq]; module
  have eA' : a' = d + β6 • p + γ6 • q := by rw [ha', hp, hq]
  have ez : ∀ x y z : ℝ, d + x • p + y • q + z • r = fpoint p q r d (x, y, z) := fun x y z => (hfp p q x y z).symm
  have hpr : ⟪p, r⟫ = ⟪r, p⟫ := real_inner_comm r p
  have hqr : ⟪q, r⟫ = ⟪r, q⟫ := real_inner_comm r q
  have hmα1 : 1 < m + α4 := by rw [hm]; nlinarith [mul_nonneg hs0 hα4.le]
  have P1a : fpoint p q r d (0, 0, 1) = a := by rw [hfp]; simp only [hr]; module
  have P1d : fpoint p q r d (0, 0, 0) = d := by rw [hfp]; module
  have P1b : fpoint p q r d (1, 0, 0) = b := by rw [hfp]; simp only [hp]; module
  have P1a' : fpoint p q r d (β6, γ6, 0) = a' := by rw [hfp, ha']; simp only [hp, hq]; module
  have P1b' : fpoint p q r d (0, 1, α4) = b' := by rw [hfp, hb']; simp only [hr, hq]; module
  have P1c : fpoint p q r d (0, 1, 0) = c := by rw [hfp]; simp only [hq]; module
  have P1c' : fpoint p q r d (1, 0, α1) = c' := by rw [hfp, hc']; simp only [hr, hp]; module
  have P2a : fpoint q p r d (0, 0, 1) = a := by rw [hfp]; simp only [hr]; module
  have P2d : fpoint q p r d (0, 0, 0) = d := by rw [hfp]; module
  have P2c : fpoint q p r d (1, 0, 0) = c := by rw [hfp]; simp only [hq]; module
  have P2a' : fpoint q p r d (γ6, β6, 0) = a' := by rw [hfp, ha']; simp only [hp, hq]; module
  have P2c' : fpoint q p r d (0, 1, α1) = c' := by rw [hfp, hc']; simp only [hr, hp]; module
  have P2b : fpoint q p r d (0, 1, 0) = b := by rw [hfp]; simp only [hp]; module
  have P2b' : fpoint q p r d (1, 0, α4) = b' := by rw [hfp, hb']; simp only [hr, hq]; module
  refine ⟨r, hr0, ?_⟩
  have hα14 : α1 ≤ α4 := by nlinarith [mul_nonneg hs0 hα4.le]
  have hα4' : 1 < α4 := by linarith
  have hBne' : ⟪p, r⟫ ≠ 0 := by rw [hpr]; exact hBne
  refine k6p_core_hasLexCellAt (V8 a a' b b' c c' d) p q r d hΔ (α1 := α1) (α4 := α4) (β6 := β6)
    (γ6 := γ6) (m := m) hα1 hα4 hβ6 hγ6 hs hm0.ge (Or.inr hBne') (by linarith) ?_ ?_ ?_ ?_
  · rw [hm0]; nlinarith [mul_pos (sub_pos.2 hα4') (by linarith : 0 < β6 + γ6)]
  · linarith
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [kCyc, pc5_0, P1a]; simp [V8]
    · simp only [kCyc, pc5_1, P1d]; simp [V8]
    · simp only [kCyc, pc5_2, P1b]; simp [V8]
    · simp only [kCyc, pc5_3, P1a']; simp [V8]
    · simp only [kCyc, pc5_4, P1b']; simp [V8]
  · intro y hy
    rw [P1a, P1d, P1b, P1a', P1b', P1c, P1c']
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto

end C2
end Type08Sp
end Minimality
