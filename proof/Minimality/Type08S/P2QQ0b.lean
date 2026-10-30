module

public import Minimality.Type08S.P2QQ0w
public import Minimality.Type08S.P2QDefs

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkQ / Q0b: the normal form on the closure (`Norm08w`): `exists_nf08w`, `Norm08w.hU_lt`, small helpers.
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

theorem Ineq08w.pos {θ : Fin 6 → ℝ} (h : Ineq08w θ) (k : Fin 24) (h9 : k ≠ 9) (h10 : k ≠ 10)
    (h11 : k ≠ 11) : 0 < ineq08 θ k := h.1 k h9 h10 h11

theorem exists_vanish08 (x1 y1 x2 y2 x3 y3 : ℝ) (h12 : x1 * y2 - y1 * x2 = 0)
    (h23 : x2 * y3 - y2 * x3 = 0) (h31 : x3 * y1 - y3 * x1 = 0) :
    ∃ α β : ℝ, (α ≠ 0 ∨ β ≠ 0) ∧ α * x1 + β * y1 = 0 ∧ α * x2 + β * y2 = 0 ∧ α * x3 + β * y3 = 0 := by
  by_cases h1 : x1 = 0 ∧ y1 = 0
  · obtain ⟨rfl, rfl⟩ := h1
    by_cases h2 : x2 = 0 ∧ y2 = 0
    · obtain ⟨rfl, rfl⟩ := h2
      by_cases h3 : x3 = 0 ∧ y3 = 0
      · exact ⟨1, 0, Or.inl one_ne_zero, by simp, by simp, by simp [h3.1]⟩
      · refine ⟨y3, -x3, ?_, by simp, by simp, by ring⟩
        by_contra hc; push_neg at hc; exact h3 ⟨by linarith [hc.2], hc.1⟩
    · refine ⟨y2, -x2, ?_, by simp, by ring, by linarith⟩
      by_contra hc; push_neg at hc; exact h2 ⟨by linarith [hc.2], hc.1⟩
  · refine ⟨y1, -x1, ?_, by ring, by linarith, by linarith⟩
    by_contra hc; push_neg at hc; exact h1 ⟨by linarith [hc.2], hc.1⟩

/-- `gale_nf08` with `μ ≠ 0` (independence of the Gale data). -/
theorem gale_nf08w {a a' b b' c c' d : ℝ³} (G : GaleData a a' b b' c c')
    {p q r s t u : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + p • (a - d) + q • (b - d)) (hb' : b' = d + r • (a - d) + s • (c - d))
    (ha' : a' = d + t • (b - d) + u • (c - d)) (hνc : 1 - p - q ≠ 0) :
    ∃ μ : ℝ, μ ≠ 0 ∧ galeD G.l G.m a a' = μ * gWa ![p, q, r, s, t, u] ∧
      galeD G.l G.m b b' = μ * gWb ![p, q, r, s, t, u] ∧
      galeD G.l G.m c c' = μ * gWc ![p, q, r, s, t, u] ∧
      galeD G.l G.m b c = μ * gWU ![p, q, r, s, t, u] := by
  obtain ⟨la, lb, lc, ls⟩ := dep_rel08 G.hl hdet hc' hb' ha'
  obtain ⟨ma, mb, mc, ms⟩ := dep_rel08 G.hm hdet hc' hb' ha'
  set A1 := G.l a' * G.m b' - G.m a' * G.l b' with hA1
  set B1 := G.l b' * G.m c' - G.m b' * G.l c' with hB1
  set C1 := G.l c' * G.m a' - G.m c' * G.l a' with hC1
  obtain ⟨μ, hμ⟩ : ∃ μ, μ * (1 - p - q) = A1 := ⟨A1 / (1 - p - q), div_mul_cancel₀ _ hνc⟩
  have hB : B1 * (1 - p - q) = (1 - t - u) * A1 := by
    rw [hB1, hA1]
    linear_combination (G.l b') * ms - (G.m b') * ls
  have hC : C1 * (1 - p - q) = (1 - r - s) * A1 := by
    rw [hC1, hA1]
    linear_combination (G.m a') * ls - (G.l a') * ms
  have hB' : B1 = μ * (1 - t - u) := mul_right_cancel₀ hνc (by linear_combination hB - (1 - t - u) * hμ)
  have hC' : C1 = μ * (1 - r - s) := mul_right_cancel₀ hνc (by linear_combination hC - (1 - r - s) * hμ)
  have hA' : A1 = μ * (1 - p - q) := hμ.symm
  have hμ0 : μ ≠ 0 := by
    intro h0
    have e1 : A1 = 0 := by rw [hA', h0]; ring
    have e2 : B1 = 0 := by rw [hB', h0]; ring
    have e3 : C1 = 0 := by rw [hC', h0]; ring
    obtain ⟨α, β, hab, v1, v2, v3⟩ := exists_vanish08 (G.l a') (G.m a') (G.l b') (G.m b') (G.l c') (G.m c')
      e1 e2 e3
    have w1 : α * G.l a + β * G.m a = 0 := by rw [la, ma]; linear_combination (-r) * v2 + (-p) * v3
    have w2 : α * G.l b + β * G.m b = 0 := by rw [lb, mb]; linear_combination (-t) * v1 + (-q) * v3
    have w3 : α * G.l c + β * G.m c = 0 := by rw [lc, mc]; linear_combination (-u) * v1 + (-s) * v2
    obtain ⟨h1, h2⟩ := G.indep α β w1 v1 w2 v2 w3 v3
    rcases hab with h | h <;> contradiction
  refine ⟨μ, hμ0, ?_, ?_, ?_, ?_⟩
  · have e : galeD G.l G.m a a' = r * A1 - p * C1 := by
      unfold galeD; rw [la, ma, hA1, hC1]; ring
    rw [e, hA', hC']; simp [gWa]; ring
  · have e : galeD G.l G.m b b' = -t * A1 + q * B1 := by
      unfold galeD; rw [lb, mb, hA1, hB1]; ring
    rw [e, hA', hB']; simp [gWb]; ring
  · have e : galeD G.l G.m c c' = u * C1 - s * B1 := by
      unfold galeD; rw [lc, mc, hC1, hB1]; ring
    rw [e, hC', hB']; simp [gWc]; ring
  · have e : galeD G.l G.m b c = t * s * A1 + q * u * C1 - q * s * B1 := by
      unfold galeD; rw [lb, mb, lc, mc, hA1, hB1, hC1]; ring
    rw [e, hA', hB', hC']; simp [gWU]; ring

end Type08Sp
end Minimality
