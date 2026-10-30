module

public import Minimality.Type08S.P2TpBase

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# T'X: frame data of `T'` with the convexity `1 < β6 + γ6` of `Q_bc` (copy of `norm08_coordsTp`
and `hTp_setup`, tree files G6K1/G6K3, with the third output of `Qac_coords'` kept)
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- `Norm08` + `IsT'` : normal-form coordinates with `α1 = 1`, `0 < γ6 < 1`, `1 < α4 + γ4`. -/
theorem norm08_coordsTp' {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (hT' : IsT' a b c' d) :
    ∃ α4 β1 γ4 β6 γ6 : ℝ, det3 (a - d) (b - d) (c - d) ≠ 0 ∧
      c' = d + (1 : ℝ) • (a - d) + β1 • (b - d) ∧ b' = d + α4 • (a - d) + γ4 • (c - d) ∧
      a' = d + β6 • (b - d) + γ6 • (c - d) ∧ 0 < α4 ∧ 0 < γ4 ∧ 1 < α4 + γ4 ∧ 0 < β1 ∧
      0 < β6 ∧ 0 < γ6 ∧ γ6 < 1 ∧ 1 < β6 + γ6 := by
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
  obtain ⟨hβ6, hγ6, hcv6, ha'⟩ : 0 < F.ab'c.f a' / F.ab'c.f b ∧ 0 < F.abc'.f a' / F.abc'.f c ∧
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
  refine ⟨_, _, _, _, _, hdet, hc', hb', ha', q1, q2, q3, p2, hβ6, hγ6, hγ1, ?_⟩
  exact hcv6


/-- The frame data of `T'`. -/
theorem hTp_setup' {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (hT' : IsT' a b c' d) :
    ∃ (e1 e2 e3 o : ℝ³) (ν v1 C0 w1 ha w3 α4 β1 γ4 β6 γ6 : ℝ), Fr e1 e2 e3 ∧ 0 < ν ∧ v1 ≠ 0 ∧
      0 < ha ∧ 0 < α4 ∧ 0 < γ4 ∧ 1 < α4 + γ4 ∧ 0 < β1 ∧ 0 < β6 ∧ 0 < γ6 ∧ γ6 < 1 ∧ 1 < β6 + γ6 ∧
      b - d = ν • e3 ∧
      d = pt e1 e2 e3 o (-v1) 0 0 ∧ b = pt e1 e2 e3 o (-v1) 0 ν ∧ c = pt e1 e2 e3 o 0 0 C0 ∧
      a = pt e1 e2 e3 o (-v1 + w1) ha w3 ∧
      a' = pt e1 e2 e3 o (-v1 * (1 - γ6)) 0 (γ6 * C0 + β6 * ν) ∧
      b' = pt e1 e2 e3 o (-v1 * (1 - γ4) + α4 * w1) (α4 * ha) (α4 * w3 + γ4 * C0) ∧
      c' = pt e1 e2 e3 o (-v1 + w1) ha (w3 + β1 * ν) ∧
      ⟪a - d, b - d⟫ = ν * w3 ∧ ⟪c - d, b - d⟫ = ν * C0 := by
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hα4, hγ4, hαγ, hβ1, hβ6, hγ6, hγ61, hcv⟩ :=
    norm08_coordsTp' N hT'
  obtain ⟨e1, e2, e3, hF, hu1, hu2, hu3, hv2, hv1, hw2⟩ := frame_exists hdet
  have hu : b - d = ⟪b - d, e3⟫ • e3 := by
    have := hF.expand (b - d); rw [hu1, hu2] at this; simpa using this
  have hv : c - d = ⟪c - d, e1⟫ • e1 + ⟪c - d, e3⟫ • e3 := by
    have := hF.expand (c - d); rw [hv2] at this; simpa using this
  have hw := hF.expand (a - d)
  have hin : ∀ x : ℝ³, ⟪x, b - d⟫ = ⟪b - d, e3⟫ * ⟪x, e3⟫ := by
    intro x; conv_lhs => rw [hu]
    rw [real_inner_smul_right, real_inner_comm]
  generalize hν : ⟪b - d, e3⟫ = ν at *
  generalize hV1 : ⟪c - d, e1⟫ = v1 at *
  generalize hC0 : ⟪c - d, e3⟫ = C0 at *
  generalize hW1 : ⟪a - d, e1⟫ = w1 at *
  generalize hHA : ⟪a - d, e2⟫ = ha at *
  generalize hW3 : ⟪a - d, e3⟫ = w3 at *
  obtain ⟨o, ho⟩ : ∃ o : ℝ³, o = d + v1 • e1 := ⟨_, rfl⟩
  have hd_pt : d = pt e1 e2 e3 o (-v1) 0 0 := by simp only [pt, pc, ho]; module
  have hb_pt : b = pt e1 e2 e3 o (-v1) 0 ν := by
    have : b = d + ν • e3 := by rw [← hu]; abel
    rw [this]; simp only [pt, pc, ho]; module
  have hc_pt : c = pt e1 e2 e3 o 0 0 C0 := by
    have : c = d + (v1 • e1 + C0 • e3) := by rw [← hv]; abel
    rw [this]; simp only [pt, pc, ho]; module
  have ha_pt : a = pt e1 e2 e3 o (-v1 + w1) ha w3 := by
    have : a = d + (w1 • e1 + ha • e2 + w3 • e3) := by rw [← hw]; abel
    rw [this]; simp only [pt, pc, ho]; module
  have ha'_pt : a' = pt e1 e2 e3 o (-v1 * (1 - γ6)) 0 (γ6 * C0 + β6 * ν) := by
    rw [ha', hu, hv]; simp only [pt, pc, ho]; module
  have hb'_pt : b' = pt e1 e2 e3 o (-v1 * (1 - γ4) + α4 * w1) (α4 * ha) (α4 * w3 + γ4 * C0) := by
    rw [hb', hw, hv]; simp only [pt, pc, ho]; module
  have hc'_pt : c' = pt e1 e2 e3 o (-v1 + w1) ha (w3 + β1 * ν) := by
    rw [hc', hw, hu]; simp only [pt, pc, ho]; module
  refine ⟨e1, e2, e3, o, ν, v1, C0, w1, ha, w3, α4, β1, γ4, β6, γ6, hF, hu3, hv1, hw2, hα4, hγ4,
    hαγ, hβ1, hβ6, hγ6, hγ61, hcv, hu, hd_pt, hb_pt, hc_pt, ha_pt, ha'_pt, hb'_pt, hc'_pt, ?_, ?_⟩
  · rw [hin, hW3]
  · rw [hin, hC0]



end Type08Sp
end Minimality
