module

public import Minimality.Type08S.C2K6TCA

@[expose] public section

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

/-- **The missing constraint** (facet `a'bc'` seen from `b'`, at `T'`, i.e. `α1 = 1`):
`γ6 - γ6 α4 (1 - β1) - γ4 (1 - β6) > 0`; at `γ6 = 1`: `α4 (1 - β1) + γ4 (1 - β6) < 1`. -/
theorem k6t3_facet_a'bc' {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) {α4 β1 γ4 β6 γ6 : ℝ}
    (hc' : c' = d + (1 : ℝ) • (a - d) + β1 • (b - d)) (hb' : b' = d + α4 • (a - d) + γ4 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d)) (hβ1 : 0 < β1) (hγ6 : 0 < γ6) (hcv : 1 < β6 + γ6) :
    0 < γ6 - γ6 * α4 * (1 - β1) - γ4 * (1 - β6) := by
  obtain ⟨F, hd, G, hκa, hκb, hU⟩ := W
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have fa := F.a'bc'.neg a (by simp) haa' hab hac'
  have fb' := F.a'bc'.neg b' (by simp) (Ne.symm ha'b') (Ne.symm hbb') hb'c'
  have fc := F.a'bc'.neg c (by simp) (Ne.symm ha'c) (Ne.symm hbc) hcc'
  have z1 := F.a'bc'.hP
  have z2 := F.a'bc'.hQ
  have z3 := F.a'bc'.hR
  have hN := F.a'bc'.hN
  set f := F.a'bc'.f
  set N := F.a'bc'.N
  have ea := hN a d
  have eb := hN b d
  have ec := hN c d
  have ec' : f c' - f d = ⟪N, a - d⟫ + β1 * ⟪N, b - d⟫ := by
    rw [hN c' d, hc']
    have : d + (1 : ℝ) • (a - d) + β1 • (b - d) - d = (a - d) + β1 • (b - d) := by module
    rw [this, inner_add_right, real_inner_smul_right]
  have eb' : f b' - f d = α4 * ⟪N, a - d⟫ + γ4 * ⟪N, c - d⟫ := by
    rw [hN b' d, hb']
    have : d + α4 • (a - d) + γ4 • (c - d) - d = α4 • (a - d) + γ4 • (c - d) := by module
    rw [this, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have ea' : f a' - f d = β6 * ⟪N, b - d⟫ + γ6 * ⟪N, c - d⟫ := by
    rw [hN a' d, ha']
    have : d + β6 • (b - d) + γ6 • (c - d) - d = β6 • (b - d) + γ6 • (c - d) := by module
    rw [this, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  set X := f d
  set n1 := ⟪N, a - d⟫
  set n2 := ⟪N, b - d⟫
  set n3 := ⟪N, c - d⟫
  -- f b = 0: n2 = -X;  f c' = 0: n1 = (β1 - 1) X;  f a' = 0: γ6 n3 = (β6 - 1) X
  have hn2 : n2 = -X := by linarith
  have hn1 : n1 = (β1 - 1) * X := by rw [z3] at ec'; nlinarith
  have hn3 : γ6 * n3 = (β6 - 1) * X := by rw [z1] at ea'; nlinarith
  have hXneg : X < 0 := by nlinarith
  have hc3 : (γ6 + β6 - 1) * X < 0 := by nlinarith
  -- f b' < 0:  X + α4 n1 + γ4 n3 < 0, multiply by γ6 > 0
  have hb'neg : γ6 * (X + α4 * n1 + γ4 * n3) < 0 := mul_neg_of_pos_of_neg hγ6 (by linarith)
  have : γ6 * (X + α4 * n1 + γ4 * n3) = X * (γ6 - γ6 * α4 * (1 - β1) - γ4 * (1 - β6)) := by
    have : γ6 * (X + α4 * n1 + γ4 * n3) = γ6 * X + γ6 * α4 * n1 + γ4 * (γ6 * n3) := by ring
    rw [this, hn1, hn3]; ring
  rw [this] at hb'neg
  by_contra hcon
  push Not at hcon
  nlinarith

end C2
end Type08Sp
end Minimality
