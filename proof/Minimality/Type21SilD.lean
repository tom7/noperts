module

public import Minimality.Type21SilC

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace H21

variable {n k : ℕ} [NeZero k] {x : Fin n → ℝ³} {c : ZMod k → Fin n} {u₀ : ℝ³}

/-- A tilt separating the cycle points by their depth along `v`. -/
theorem exists_tilt (hx : Function.Injective x) (hc : Function.Injective c) :
    ∃ v : ℝ³, ∀ i j : ZMod k, i ≠ j → ⟪x (c i), v⟫ ≠ ⟪x (c j), v⟫ := by
  let ι := {p : ZMod k × ZMod k // p.1 ≠ p.2}
  obtain ⟨v, -, hv⟩ := exists_avoid_kernels (E := ℝ³) (ι := ι)
    (fun p => (innerSL ℝ (x (c p.1.1) - x (c p.1.2))).toLinearMap)
    (by
      intro p h
      have hne : x (c p.1.1) - x (c p.1.2) ≠ 0 := sub_ne_zero.2 fun e => p.2 (hc (hx e))
      have := LinearMap.congr_fun h (x (c p.1.1) - x (c p.1.2))
      exact hne (inner_self_eq_zero.1 this))
    isOpen_univ ⟨0, trivial⟩
  refine ⟨v, fun i j hij e => hv ⟨(i, j), hij⟩ ?_⟩
  simp [inner_sub_left, e]

theorem core_pos (hc : Function.Injective c) (hk : 3 ≤ k) (D : SilData k x c u₀) (μ : ZMod k → ℝ)
    (hμ : ∀ i, 0 < μ i)
    (hd : ∀ i, x (c (i + 1)) - x (c i) = μ i • cross (D.A i) (D.B i)) (v : ℝ³)
    (hL : LexUni (fun i => ⟪x (c i), u₀⟫) (fun i => ⟪x (c i), v⟫)) :
    HasLexCellAt (univ.image x) u₀ := by
  have P : ∀ i m, m ≠ c i → m ≠ c (i + 1) →
      0 < det3 (x (c (i + 1)) - x (c i)) (x m - x (c i)) u₀ := by
    intro i m h0 h1
    rw [det_eq D i (μ i) (hd i) m]
    exact mul_pos (hμ i) (Q_pos D i m h0 h1)
  refine ⟨k, inferInstance, fun i => x (c i), v, hk, fun i => mem_image_of_mem _ (mem_univ _),
    ?_, ?_, hL⟩
  · intro i j hji hj1
    exact Or.inl (P i (c j) (fun h => hji (hc h)) (fun h => hj1 (hc h)))
  · intro y hy hne i
    obtain ⟨m, -, rfl⟩ := mem_image.1 hy
    exact Or.inl (P i m (fun h => hne i (by rw [h])) (fun h => hne (i + 1) (by rw [h])))

theorem sign_agree (hk : 3 ≤ k) (hx : Function.Injective x) (hc : Function.Injective c)
    (D : SilData k x c u₀) (μ : ZMod k → ℝ) (hμ0 : ∀ i, μ i ≠ 0)
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
    have e1 := det_eq D i (μ i) (hd i) (c (i + 1 + 1))
    have e2 := det_eq D (i + 1) (μ (i + 1)) (hd (i + 1)) (c i)
    have rot := det3_rot3 (x (c (i + 1))) (x (c (i + 1 + 1))) (x (c i)) u₀
    have Q1 := Q_pos D i (c (i + 1 + 1)) n1 n2
    have Q2 := Q_pos D (i + 1) (c i) n3 n4
    rw [e2] at rot; rw [e1] at rot
    constructor
    · intro h; by_contra hb; push Not at hb
      nlinarith [mul_pos h Q1, mul_le_mul_of_nonneg_right hb Q2.le]
    · intro h; by_contra hb; push Not at hb
      nlinarith [mul_pos h Q2, mul_le_mul_of_nonneg_right hb Q1.le]
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

end H21
end Minimality
