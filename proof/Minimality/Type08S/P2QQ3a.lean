module

public import Minimality.Type08S.P2QQ2b
public import Minimality.Type08S.G3p

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkQ / Q3a: W copies of `region_gamma6`, `region_alpha1` on `Norm08w` (reused by Q4).
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace W

theorem region_gamma6 {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d) {o E₁ E₂ E₃ : ℝ³}
    {θ : Fin 6 → ℝ} (hE : det3 E₁ E₂ E₃ ≠ 0) (hθ : Ineq08w θ)
    (hpts : pts08 a a' b b' c c' d = nfShape08 o E₁ E₂ E₃ θ) :
    N.F.abc'.f a' = θ 5 * N.F.abc'.f c := by
  have hnd := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have hp := facet_prop08 N.F.abc' c a'
  have d1 : det3 (b - a) (c' - a) (c - a) = det3 E₁ E₂ E₃ * fc08 θ 0 2 5 4 := by
    have := det3_nf08 o E₁ E₂ E₃ θ 0 2 5 4; rw [← hpts] at this; exact this
  have d2 : det3 (b - a) (c' - a) (a' - a) = det3 E₁ E₂ E₃ * fc08 θ 0 2 5 1 := by
    have := det3_nf08 o E₁ E₂ E₃ θ 0 2 5 1; rw [← hpts] at this; exact this
  rw [d1, d2] at hp
  have hA : fc08 θ 0 2 5 4 = 1 - θ 0 - θ 1 := by simp only [fc08, cdet, cp08]; simp; ring
  have hB : fc08 θ 0 2 5 1 = θ 5 * (1 - θ 0 - θ 1) := by simp only [fc08, cdet, cp08]; simp; ring
  have e1 : 0 < θ 0 + θ 1 - 1 := hθ.pos 6 (by decide) (by decide) (by decide)
  have hD : det3 E₁ E₂ E₃ * (1 - θ 0 - θ 1) ≠ 0 := mul_ne_zero hE (by linarith)
  rw [hA, hB] at hp
  apply mul_right_cancel₀ hD; linear_combination hp

theorem region_alpha1 {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d) {o E₁ E₂ E₃ : ℝ³}
    {θ : Fin 6 → ℝ} (hE : det3 E₁ E₂ E₃ ≠ 0) (hθ : Ineq08w θ)
    (hpts : pts08 a a' b b' c c' d = nfShape08 o E₁ E₂ E₃ θ) :
    N.F.a'bc.f c' = θ 0 * N.F.a'bc.f a := by
  have hp := facet_prop08 N.F.a'bc a c'
  have d1 : det3 (b - a') (c - a') (a - a') = det3 E₁ E₂ E₃ * fc08 θ 1 2 4 0 := by
    have := det3_nf08 o E₁ E₂ E₃ θ 1 2 4 0; rw [← hpts] at this; exact this
  have d2 : det3 (b - a') (c - a') (c' - a') = det3 E₁ E₂ E₃ * fc08 θ 1 2 4 5 := by
    have := det3_nf08 o E₁ E₂ E₃ θ 1 2 4 5; rw [← hpts] at this; exact this
  rw [d1, d2] at hp
  have hA : fc08 θ 1 2 4 0 = 1 - θ 4 - θ 5 := by simp only [fc08, cdet, cp08]; simp; ring
  have hB : fc08 θ 1 2 4 5 = θ 0 * (1 - θ 4 - θ 5) := by simp only [fc08, cdet, cp08]; simp; ring
  have e1 : 0 < θ 4 + θ 5 - 1 := hθ.pos 8 (by decide) (by decide) (by decide)
  have hD : det3 E₁ E₂ E₃ * (1 - θ 4 - θ 5) ≠ 0 := mul_ne_zero hE (by linarith)
  rw [hA, hB] at hp
  apply mul_right_cancel₀ hD; linear_combination hp

end W
end Type08Sp
end Minimality
