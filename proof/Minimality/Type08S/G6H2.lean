module

public import Minimality.Type08S.G6H1

@[expose] public section

set_option autoImplicit true

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- `Norm08` + `IsT` + `H2`: normal-form coordinates with `γ4 = 1`, `1 < α1`, `0 < α4`, `0 < β1 < 1`. -/
theorem norm08_coords2 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (hT : IsT a' b c d) (hH : H2 a b b' c d) :
    ∃ α1 α4 β1 β6 : ℝ, det3 (a - d) (b - d) (c - d) ≠ 0 ∧
      c' = d + α1 • (a - d) + β1 • (b - d) ∧ b' = d + α4 • (a - d) + (1 : ℝ) • (c - d) ∧
      a' = d + β6 • (b - d) + (c - d) ∧ 1 < α1 ∧ 0 < α4 ∧ 0 < β1 ∧ β1 < 1 ∧ 0 < β6 := by
  obtain ⟨F, hd, G, hκa, hκb, hκc, hU⟩ := N
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  obtain ⟨p1, p2, -, hc'⟩ : 0 < F.a'bc.f c' / F.a'bc.f a ∧ 0 < F.ab'c.f c' / F.ab'c.f b ∧
      1 < F.a'bc.f c' / F.a'bc.f a + F.ab'c.f c' / F.ab'c.f b ∧
      c' = d + (F.a'bc.f c' / F.a'bc.f a) • (a - d) + (F.ab'c.f c' / F.ab'c.f b) • (b - d) :=
    hd.perm₂₃.Qac_coords'
  obtain ⟨q1, q2, -, hb'⟩ := hd.Qac_coords'
  obtain ⟨hβ6, -, -, ha'⟩ : 0 < F.ab'c.f a' / F.ab'c.f b ∧ 0 < F.abc'.f a' / F.abc'.f c ∧
      1 < F.ab'c.f a' / F.ab'c.f b + F.abc'.f a' / F.abc'.f c ∧
      a' = d + (F.ab'c.f a' / F.ab'c.f b) • (b - d) + (F.abc'.f a' / F.abc'.f c) • (c - d) :=
    hd.perm₁₂.Qac_coords'
  have hFc := F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc'
  have hFa := F.a'bc.neg a (by simp) haa' hab hac
  obtain ⟨r, hr⟩ := hT
  have hTf : F.abc'.f a' = F.abc'.f c := by
    have h1 := F.abc'.hN a' c
    have h2 : F.abc'.f b - F.abc'.f d = ⟪F.abc'.N, b - d⟫ := F.abc'.hN b d
    have h3 : F.abc'.f c - F.abc'.f a' = ⟪F.abc'.N, c - a'⟫ := F.abc'.hN c a'
    rw [hr, real_inner_smul_right] at h3
    have h4 : F.abc'.f b = 0 := F.abc'.hQ
    rw [hd.abc', h4] at h2
    have h5 : F.abc'.f c - F.abc'.f a' = 0 := by rw [h3, ← h2]; ring
    linarith
  have hfar := type08_T_far F G hκb hκc hU hTf
  have hα : 1 < F.a'bc.f c' / F.a'bc.f a := by
    rw [lt_div_iff_of_neg hFa]; linarith
  have hr1 : F.abc'.f a' / F.abc'.f c = 1 := by rw [hTf, div_self hFc.ne]
  rw [hr1, one_smul] at ha'
  generalize F.a'bc.f c' / F.a'bc.f a = α1 at *
  generalize F.ab'c.f c' / F.ab'c.f b = β1 at *
  generalize F.a'bc.f b' / F.a'bc.f a = α4 at *
  generalize F.abc'.f b' / F.abc'.f c = γ4 at *
  generalize F.ab'c.f a' / F.ab'c.f b = β6 at *
  have hdet : det3 (a - d) (b - d) (c - d) ≠ 0 := by
    have := hd.det_Qac_ne
    intro h; apply this
    have e : det3 (a - d) (c - d) (b - d) = - det3 (a - d) (b - d) (c - d) := by
      simp only [det3_expand]; ring
    rw [e, h, neg_zero]
  have hγ : γ4 = 1 := by
    have e : det3 (c - b') (a - d) (b - d) = (1 - γ4) * det3 (a - d) (b - d) (c - d) := by
      rw [hb']; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        smul_eq_mul]; ring
    have := hH
    unfold H2 at this
    rw [e] at this
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hdet
  subst hγ
  obtain ⟨μ, h1, h2⟩ := gale_coords2 G hdet hc' hb' ha' hβ6.ne'
  have hμ : 0 < μ := by
    have : 0 < μ * β6 * (α1 - 1) := h2 ▸ hκb
    have h3 : 0 < β6 * (α1 - 1) := mul_pos hβ6 (by linarith)
    nlinarith
  have : 0 < μ * (α4 * (1 - β1)) := by
    have := h1 ▸ hκa
    linarith [this]
  have h4 : 0 < α4 * (1 - β1) := pos_of_mul_pos_right this hμ.le
  have h5 : 0 < 1 - β1 := pos_of_mul_pos_right h4 q1.le
  exact ⟨α1, α4, β1, β6, hdet, hc', hb', ha', hα, q1, p2, by linarith, hβ6⟩

end Type08Sp
end Minimality
