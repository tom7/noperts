module

public import Minimality.Type21Sl2B

@[expose] public section

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace H21
variable {n k : ℕ} [NeZero k] {x : Fin n → ℝ³} {c : ZMod k → Fin n} {u₀ v : ℝ³}

theorem h21b_sign_agree (hk : 3 ≤ k) (hx : Function.Injective x) (hc : Function.Injective c)
    (D : h21b_SilDataL k x c u₀ v) (μ : ZMod k → ℝ) (hμ0 : ∀ i, μ i ≠ 0)
    (hd : ∀ i, x (c (i + 1)) - x (c i) = μ i • cross (D.A i) (D.B i)) :
    (∀ i, 0 < μ i) ∨ (∀ i, μ i < 0) := by
  obtain ⟨h1, h2⟩ := zmod_ne hk
  have step : ∀ i, 0 < μ i ↔ 0 < μ (i + 1) := by
    intro i
    have n1 : c (i + 1 + 1) ≠ c i := fun h => h2 (by
      have := hc h; linear_combination this)
    have n2 : c (i + 1 + 1) ≠ c (i + 1) := fun h => h1 (by
      have := hc h; linear_combination this)
    have n3 : c i ≠ c (i + 1) := fun h => h1 (by simpa using (hc h))
    have n4 : c i ≠ c (i + 1 + 1) := fun h => h2 (by
      have := hc h; linear_combination -this)
    have Q1 := h21b_Q_pos D i (c (i + 1 + 1)) n1 n2
    have Q2 := h21b_Q_pos D (i + 1) (c i) n3 n4
    have key : ∀ w, μ i * (D.fA i (x (c (i + 1 + 1))) * ⟪D.B i, w⟫ - D.fB i (x (c (i + 1 + 1))) * ⟪D.A i, w⟫)
        = μ (i + 1) * (D.fA (i + 1) (x (c i)) * ⟪D.B (i + 1), w⟫ - D.fB (i + 1) (x (c i)) * ⟪D.A (i + 1), w⟫) := by
      intro w
      have e1 := h21b_det_eq D i (μ i) (hd i) (c (i + 1 + 1)) w
      have e2 := h21b_det_eq D (i + 1) (μ (i + 1)) (hd (i + 1)) (c i) w
      have rot := det3_rot3 (x (c (i + 1))) (x (c (i + 1 + 1))) (x (c i)) w
      rw [e2] at rot; rw [e1] at rot
      exact rot.symm
    constructor
    · intro h
      exact h21b_lp_sign Q1 Q2 (key u₀) (key v) h (hμ0 _)
    · intro h
      exact h21b_lp_sign Q2 Q1 (key u₀).symm (key v).symm h (hμ0 _)
  have all : ∀ N : ℕ, (0 < μ (N : ZMod k) ↔ 0 < μ 0) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih => rw [Nat.cast_succ, ← step, ih]
  by_cases h0 : 0 < μ 0
  · left; intro i
    rw [← ZMod.natCast_zmod_val i, all]; exact h0
  · right; intro i
    have : ¬ 0 < μ i := by rw [← ZMod.natCast_zmod_val i, all]; exact h0
    exact lt_of_le_of_ne (not_lt.1 this) (hμ0 i)

theorem h21b_core_pos (hc : Function.Injective c) (hk : 3 ≤ k) (D : h21b_SilDataL k x c u₀ v)
    (μ : ZMod k → ℝ) (hμ : ∀ i, 0 < μ i)
    (hd : ∀ i, x (c (i + 1)) - x (c i) = μ i • cross (D.A i) (D.B i))
    (hL : LexUni (fun i => ⟪x (c i), u₀⟫) (fun i => ⟪x (c i), v⟫)) :
    HasLexCellAt (univ.image x) u₀ := by
  have P : ∀ i m, m ≠ c i → m ≠ c (i + 1) →
      TiltSign (x (c (i + 1)) - x (c i)) (x m - x (c i)) u₀ v := by
    intro i m h0 h1
    have Q := h21b_Q_pos D i m h0 h1
    unfold TiltSign
    rw [h21b_det_eq D i (μ i) (hd i) m u₀, h21b_det_eq D i (μ i) (hd i) m v]
    unfold h21b_LP at Q
    rcases Q with Q | ⟨Q, Q'⟩
    · exact Or.inl (mul_pos (hμ i) Q)
    · right; rw [Q]; exact ⟨by ring, mul_pos (hμ i) Q'⟩
  refine ⟨k, inferInstance, fun i => x (c i), v, hk, fun i => mem_image_of_mem _ (mem_univ _),
    ?_, ?_, hL⟩
  · intro i j hji hj1
    exact P i (c j) (fun h => hji (hc h)) (fun h => hj1 (hc h))
  · intro y hy hne i
    obtain ⟨m, -, rfl⟩ := mem_image.1 hy
    exact P i m (fun h => hne i (by rw [h])) (fun h => hne (i + 1) (by rw [h]))

end H21
end Minimality
