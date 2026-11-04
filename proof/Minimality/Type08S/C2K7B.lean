module

public import Minimality.Type08S.C2K6

@[expose] public section

/-!
# K7 / B: the facet `(a', b, c')` of the octahedron puts `b'` on its inner side: `α4 (1 - β1) < α1 β6`
-/
set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem k7_facet {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) {α1 α4 β1 β6 : ℝ}
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α4 • (a - d) + (1 : ℝ) • (c - d))
    (ha' : a' = d + β6 • (b - d) + (c - d)) (hα1 : 0 < α1) (hβ6 : 0 < β6) :
    α4 * (1 - β1) < α1 * β6 := by
  have hnd := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  set F := N.F.a'bc' with hF
  have hfa : F.f a < 0 := F.neg a (by simp) haa' hab hac'
  have hfc : F.f c < 0 := F.neg c (by simp) (Ne.symm ha'c) (Ne.symm hbc) hcc'
  have hfb' : F.f b' < 0 := F.neg b' (by simp) (Ne.symm ha'b') (Ne.symm hbb') hb'c'
  have h0b : F.f b = 0 := F.hQ
  have h0a' : F.f a' = 0 := F.hP
  have h0c' : F.f c' = 0 := F.hR
  have ea : F.f a - F.f d = ⟪F.N, a - d⟫ := F.hN a d
  have ec : F.f c - F.f d = ⟪F.N, c - d⟫ := F.hN c d
  have eb : F.f b - F.f d = ⟪F.N, b - d⟫ := F.hN b d
  have ea' : F.f a' - F.f d = β6 * ⟪F.N, b - d⟫ + ⟪F.N, c - d⟫ := by
    rw [F.hN a' d, show a' - d = β6 • (b - d) + (c - d) by rw [ha']; abel, inner_add_right, real_inner_smul_right]
  have ec' : F.f c' - F.f d = α1 * ⟪F.N, a - d⟫ + β1 * ⟪F.N, b - d⟫ := by
    rw [F.hN c' d, show c' - d = α1 • (a - d) + β1 • (b - d) by rw [hc']; abel, inner_add_right,
      real_inner_smul_right, real_inner_smul_right]
  have eb' : F.f b' - F.f d = α4 * ⟪F.N, a - d⟫ + ⟪F.N, c - d⟫ := by
    rw [F.hN b' d, show b' - d = α4 • (a - d) + (c - d) by rw [hb', one_smul]; abel, inner_add_right,
      real_inner_smul_right]
  set δ := F.f d
  set n1 := ⟪F.N, a - d⟫
  set n2 := ⟪F.N, b - d⟫
  set n3 := ⟪F.N, c - d⟫
  have hn2 : n2 = -δ := by linarith
  have hn3 : n3 = -δ - β6 * n2 := by linarith
  have hn1 : α1 * n1 = -δ - β1 * n2 := by linarith
  have hδ : δ < 0 := by
    rw [hn3, hn2] at ec
    nlinarith
  by_contra hcon
  push Not at hcon
  have : α1 * F.f b' = δ * (α1 * β6 - α4 * (1 - β1)) := by
    have : F.f b' = δ + α4 * n1 + n3 := by linarith
    rw [this]
    have h3 : α1 * (δ + α4 * n1 + n3) = α1 * δ + α4 * (α1 * n1) + α1 * n3 := by ring
    rw [h3, hn1, hn3, hn2]; ring
  nlinarith [mul_pos hα1 (neg_pos.2 hfb'), mul_nonneg (neg_nonneg.2 hδ.le) (sub_nonneg.2 hcon)]

end C2
end Type08Sp
end Minimality
