module

public import Minimality.Type08S.C2K6TCD

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

/-- **Facet `a'b'c'` at `α1 = α4 = β6 = 1`** (the Pc slice): `β1 (1 - γ6) < γ4` (`c'` below `b'` on the screen of `c - a'`). -/
theorem k6t3_facet_a'b'c' {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) {β1 γ4 γ6 : ℝ}
    (hc' : c' = d + (1 : ℝ) • (a - d) + β1 • (b - d)) (hb' : b' = d + (1 : ℝ) • (a - d) + γ4 • (c - d))
    (ha' : a' = d + (1 : ℝ) • (b - d) + γ6 • (c - d)) (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hγ6 : 0 < γ6) :
    β1 * (1 - γ6) < γ4 := by
  obtain ⟨F, hd, G, hκa, hκb, hU⟩ := W
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have fa := F.a'b'c'.neg a (by simp) haa' hab' hac'
  have fb := F.a'b'c'.neg b (by simp) (Ne.symm ha'b) hbb' hbc'
  have fc := F.a'b'c'.neg c (by simp) (Ne.symm ha'c) (Ne.symm hb'c) hcc'
  have z1 := F.a'b'c'.hP
  have z2 := F.a'b'c'.hQ
  have z3 := F.a'b'c'.hR
  have hN := F.a'b'c'.hN
  set f := F.a'b'c'.f
  set N := F.a'b'c'.N
  have ea := hN a d
  have eb := hN b d
  have ec := hN c d
  have ec' : f c' - f d = ⟪N, a - d⟫ + β1 * ⟪N, b - d⟫ := by
    rw [hN c' d, hc']
    have : d + (1 : ℝ) • (a - d) + β1 • (b - d) - d = (a - d) + β1 • (b - d) := by module
    rw [this, inner_add_right, real_inner_smul_right]
  have eb' : f b' - f d = ⟪N, a - d⟫ + γ4 * ⟪N, c - d⟫ := by
    rw [hN b' d, hb']
    have : d + (1 : ℝ) • (a - d) + γ4 • (c - d) - d = (a - d) + γ4 • (c - d) := by module
    rw [this, inner_add_right, real_inner_smul_right]
  have ea' : f a' - f d = ⟪N, b - d⟫ + γ6 * ⟪N, c - d⟫ := by
    rw [hN a' d, ha']
    have : d + (1 : ℝ) • (b - d) + γ6 • (c - d) - d = (b - d) + γ6 • (c - d) := by module
    rw [this, inner_add_right, real_inner_smul_right]
  set X := f d
  set n1 := ⟪N, a - d⟫
  set n2 := ⟪N, b - d⟫
  set n3 := ⟪N, c - d⟫
  -- f a = X + n1 < 0, f b = X + n2 < 0, f c = X + n3 < 0
  have h1 : X + n1 < 0 := by linarith
  have h2 : X + n2 < 0 := by linarith
  have h3 : X + n3 < 0 := by linarith
  have e1 : X + n1 + β1 * n2 = 0 := by linarith
  have e2 : X + n1 + γ4 * n3 = 0 := by linarith
  have e3 : X + n2 + γ6 * n3 = 0 := by linarith
  have hn3 : 0 < n3 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg hγ4.le (neg_nonneg.2 hh)]
  -- β1 n2 = γ4 n3 ; n2 = -X - γ6 n3 > n3 - γ6 n3
  have hn2 : (1 - γ6) * n3 < n2 := by nlinarith
  have : β1 * ((1 - γ6) * n3) < γ4 * n3 := by nlinarith [mul_lt_mul_of_pos_left hn2 hβ1]
  nlinarith

end C2
end Type08Sp
end Minimality
