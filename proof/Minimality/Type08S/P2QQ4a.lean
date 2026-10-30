module

public import Minimality.Type08S.P2QQ4reg
public import Minimality.Type08S.P2TL2

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkQ / Q4a: `T4cl_of_TTp` (statement as in PQ0) and the converse tie lemma at `T'`.
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

private theorem det3_mid'' {p q u : ℝ³} (x y : ℝ) :
    det3 p (x • q + y • u) u = x * det3 p q u := by
  simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

/-- Converse of `IsCap.tieT'_geom` (as `tie_conv_T_L` for `T`). -/
theorem tie_conv_T'_L {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'} (hd : IsCap F d)
    (h : ∃ r : ℝ, c' - a = r • (b - d)) : F.a'bc.f c' = F.a'bc.f a := by
  obtain ⟨r, hr⟩ := h
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  have hFa := F.a'bc.neg a (by simp) hnd.1.1 hnd.1.2.1 hnd.1.2.2.2.1
  obtain ⟨-, -, -, hc'⟩ : 0 < F.a'bc.f c' / F.a'bc.f a ∧ 0 < F.ab'c.f c' / F.ab'c.f b ∧
      1 < F.a'bc.f c' / F.a'bc.f a + F.ab'c.f c' / F.ab'c.f b ∧
      c' = d + (F.a'bc.f c' / F.a'bc.f a) • (a - d) + (F.ab'c.f c' / F.ab'c.f b) • (b - d) :=
    hd.perm₂₃.Qac_coords'
  generalize F.ab'c.f c' / F.ab'c.f b = k at hc'
  generalize hq : F.a'bc.f c' / F.a'bc.f a = q at hc'
  have hv : (q - 1) • (a - d) + (k - r) • (b - d) = 0 := by
    have : c' - a = r • (b - d) := hr
    rw [hc'] at this
    rw [← sub_eq_zero] at this
    rw [← this]; module
  have h0 := det3_mid'' (p := c - d) (q := a - d) (u := b - d) (q - 1) (k - r)
  rw [hv] at h0
  have hz : det3 (c - d) 0 (b - d) = 0 := by simp [det3_expand]
  rw [hz] at h0
  have hq1 : q = 1 := by
    have := hd.det_Qac_ne
    have h1 : det3 (c - d) (a - d) (b - d) ≠ 0 := by
      intro h; apply this; simp only [det3_expand] at h ⊢; linarith
    rcases mul_eq_zero.mp h0.symm with h | h
    · linarith
    · exact absurd h h1
  rw [hq1, div_eq_one_iff_eq hFa.ne] at hq
  exact hq

/-- `T ∨ T'` lies on the closure of the T4 region (`gWb ≥ 0`: at `T`, `α1 ≥ 1`; at `T'`, `γ6 ≤ 1`). -/
theorem T4cl_of_TTp {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d)
    (hTT : IsT a' b c d ∨ IsT' a b c' d) : T4cl N.F := by
  obtain ⟨o, E₁, E₂, E₃, θ, hE, hθ, hpts, -⟩ := exists_nf08w N
  have hg := W4.region_gamma6 N hE hθ hpts
  have ha := W4.region_alpha1 N hE hθ hpts
  have hnd := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have hfc : N.F.abc'.f c < 0 := N.F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc'
  have hfa : N.F.a'bc.f a < 0 :=
    N.F.a'bc.neg a (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have gb := hθ.2.2
  have p1 := hθ.pos 1 (by decide) (by decide) (by decide)
  have p4 := hθ.pos 4 (by decide) (by decide) (by decide)
  simp only [ineq08, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] at p1 p4
  simp only [gWb] at gb
  unfold T4cl
  rcases hTT with hT | hT'
  · have e := tie_conv_T_L N.hd hT
    have h5 : θ 5 = 1 := by rw [hg] at e; nlinarith
    have h0 : 1 ≤ θ 0 := by
      rw [h5] at gb
      by_contra hlt; push Not at hlt; nlinarith
    exact ⟨e.ge, by rw [ha]; nlinarith⟩
  · have e := tie_conv_T'_L N.hd hT'
    have h0 : θ 0 = 1 := by rw [ha] at e; nlinarith
    have h5 : θ 5 ≤ 1 := by
      rw [h0] at gb
      by_contra hlt; push Not at hlt; nlinarith
    exact ⟨by rw [hg]; nlinarith, e.le⟩

end Type08Sp
end Minimality
