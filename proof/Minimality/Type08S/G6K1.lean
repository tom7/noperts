module

public import Minimality.Type08S.G6J5
public import Minimality.Type08S.G2_Affine

@[expose] public section

set_option autoImplicit true

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- `Norm08` + `IsT'` : normal-form coordinates with `α1 = 1`, `0 < γ6 < 1`, `1 < α4 + γ4`. -/
theorem norm08_coordsTp {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (hT' : IsT' a b c' d) :
    ∃ α4 β1 γ4 β6 γ6 : ℝ, det3 (a - d) (b - d) (c - d) ≠ 0 ∧
      c' = d + (1 : ℝ) • (a - d) + β1 • (b - d) ∧ b' = d + α4 • (a - d) + γ4 • (c - d) ∧
      a' = d + β6 • (b - d) + γ6 • (c - d) ∧ 0 < α4 ∧ 0 < γ4 ∧ 1 < α4 + γ4 ∧ 0 < β1 ∧
      0 < β6 ∧ 0 < γ6 ∧ γ6 < 1 := by
  have hTT := norm08_tieTT' N
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
  obtain ⟨q1, q2, q3, hb'⟩ := hd.Qac_coords'
  obtain ⟨hβ6, hγ6, -, ha'⟩ : 0 < F.ab'c.f a' / F.ab'c.f b ∧ 0 < F.abc'.f a' / F.abc'.f c ∧
      1 < F.ab'c.f a' / F.ab'c.f b + F.abc'.f a' / F.abc'.f c ∧
      a' = d + (F.ab'c.f a' / F.ab'c.f b) • (b - d) + (F.abc'.f a' / F.abc'.f c) • (c - d) :=
    hd.perm₁₂.Qac_coords'
  have hFc := F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc'
  have hFa := F.a'bc.neg a (by simp) haa' hab hac
  have hdet : det3 (a - d) (b - d) (c - d) ≠ 0 := by
    have := hd.det_Qac_ne
    intro h; apply this
    have e : det3 (a - d) (c - d) (b - d) = - det3 (a - d) (b - d) (c - d) := by
      simp only [det3_expand]; ring
    rw [e, h, neg_zero]
  -- the tie `T'` gives `α1 = 1`
  obtain ⟨r, hr⟩ := hT'
  have hα1 : F.a'bc.f c' / F.a'bc.f a = 1 := by
    generalize F.ab'c.f c' / F.ab'c.f b = k at hc'
    generalize hp : F.a'bc.f c' / F.a'bc.f a = p at hc'
    have hv : (p - 1) • (a - d) + (-(r - k)) • (b - d) = 0 := by
      have : c' - a = r • (b - d) := hr
      rw [hc'] at this
      rw [← sub_eq_zero] at this
      rw [← this]; module
    have h0 : det3 ((p - 1) • (a - d) + (-(r - k)) • (b - d)) (c - d) (b - d) =
        (p - 1) * det3 (a - d) (c - d) (b - d) := by
      simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [hv] at h0
    have hz : det3 0 (c - d) (b - d) = 0 := by simp [det3_expand]
    rw [hz] at h0
    have hdet' := hd.det_Qac_ne
    rcases mul_eq_zero.mp h0.symm with h | h
    · linarith
    · exact absurd h hdet'
  -- not `T`
  have hTne : F.abc'.f a' ≠ F.abc'.f c := by
    intro h
    exact hTT ⟨hd.tieT_geom h, ⟨r, hr⟩⟩
  have hfa : F.a'bc.f c' = F.a'bc.f a := by
    rw [div_eq_one_iff_eq hFa.ne] at hα1; exact hα1
  have hfc := type08_T'_far F G hκb hκc hU hfa hTne
  have hγ1 : F.abc'.f a' / F.abc'.f c < 1 := (div_lt_one_of_neg hFc).mpr hfc
  rw [hα1] at hc'
  exact ⟨_, _, _, _, _, hdet, hc', hb', ha', q1, q2, q3, p2, hβ6, hγ6, hγ1⟩

end Type08Sp
end Minimality
