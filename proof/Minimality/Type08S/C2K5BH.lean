module

public import Minimality.Type08S.C2K5BG

@[expose] public section


/-!
# K5b / H: coefficient uniqueness and `cond1 = (α1-1)(β6+γ6)+β1 > 0` from the Gale data (`hU`, via `exists_nf08w`).
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem k5b_coeff3 {p q r : ℝ³} (hΔ : det3 p q r ≠ 0) {x y z x' y' z' : ℝ}
    (h : x • p + y • q + z • r = x' • p + y' • q + z' • r) : x = x' ∧ y = y' ∧ z = z' := by
  have k1 : ∀ x y z : ℝ, det3 (x • p + y • q + z • r) q r = x * det3 p q r := by
    intro x y z; simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have k2 : ∀ x y z : ℝ, det3 p (x • p + y • q + z • r) r = y * det3 p q r := by
    intro x y z; simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have k3 : ∀ x y z : ℝ, det3 p q (x • p + y • q + z • r) = z * det3 p q r := by
    intro x y z; simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (fun v => det3 v q r) h
    simp only [k1] at this; exact mul_right_cancel₀ hΔ this
  · have := congrArg (fun v => det3 p v r) h
    simp only [k2] at this; exact mul_right_cancel₀ hΔ this
  · have := congrArg (fun v => det3 p q v) h
    simp only [k3] at this; exact mul_right_cancel₀ hΔ this

theorem k5b_cond1 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d)) (hβ1 : 0 < β1) :
    0 < (α1 - 1) * (β6 + γ6) + β1 := by
  obtain ⟨o, E₁, E₂, E₃, θ, hE, hθ, hpts, μ, hμ, -, -, -⟩ := exists_nf08w W
  have h0 := congrFun hpts 0
  have h1 := congrFun hpts 1
  have h2 := congrFun hpts 2
  have h3 := congrFun hpts 3
  have h4 := congrFun hpts 4
  have h5 := congrFun hpts 5
  have h6 := congrFun hpts 6
  simp only [pts08, nfShape08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h0 h1 h2 h3 h4 h5 h6
  have ea : a - d = E₁ := by rw [h0, h6]; abel
  have eb : b - d = E₂ := by rw [h2, h6]; abel
  have ec : c - d = E₃ := by rw [h4, h6]; abel
  have e5 : c' = d + θ 0 • (a - d) + θ 1 • (b - d) := by rw [ea, eb, h5, h6]
  have e3 : b' = d + θ 2 • (a - d) + θ 3 • (c - d) := by rw [ea, ec, h3, h6]
  have e1 : a' = d + θ 4 • (b - d) + θ 5 • (c - d) := by rw [eb, ec, h1, h6]
  have u5 := k5b_coeff3 hdet (x := α1) (y := β1) (z := 0) (x' := θ 0) (y' := θ 1) (z' := 0)
    (by have := hc'.symm.trans e5; simpa [add_assoc] using this)
  have u3 := k5b_coeff3 hdet (x := α1) (y := 0) (z := β1) (x' := θ 2) (y' := 0) (z' := θ 3)
    (by have := hb'.symm.trans e3; simpa [add_assoc] using this)
  have u1 := k5b_coeff3 hdet (x := 0) (y := β6) (z := γ6) (x' := 0) (y' := θ 4) (z' := θ 5)
    (by have := ha'.symm.trans e1; simpa [add_assoc] using this)
  have hU := gWU_neg_w0 θ hθ.1
  unfold gWU at hU
  rw [← u5.1, ← u5.2.1, ← u3.1, ← u3.2.2, ← u1.2.1, ← u1.2.2] at hU
  by_contra hc
  push Not at hc
  nlinarith [mul_nonneg hβ1.le (neg_nonneg.2 hc)]

end C2
end Type08Sp
end Minimality
