module

public import Minimality.Type08S.G6B6

@[expose] public section

set_option autoImplicit true

/-!
# G6' bridge, part 7: `close_T_H1`, the Theorem 08.T' branch (case A)

`Norm08` + `T` + class-(d) HDN of `R1` with interior feet on `H1`, with `R1` robust and
`R2'`, `X_ba'` not robust (`Sep`, in the depths `⟪·, b - d⟫`): the set is Rupert.
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

theorem pt_X {e1 e2 e3 : ℝ³} {o : ℝ³} {X X' Y z : ℝ} (h : X = X') :
    pt e1 e2 e3 o X Y z = pt e1 e2 e3 o X' Y z := by rw [h]

set_option maxHeartbeats 2000000 in
theorem closeT_H1_caseA {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (hT : IsT a' b c d) (hD : ClassD1 b b' c c' d)
    (hR1 : ¬ Sep ⟪b, b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫ ⟪c', b - d⟫)
    (hR2 : Sep ⟪d, b - d⟫ ⟪b', b - d⟫ ⟪c', b - d⟫ ⟪c, b - d⟫)
    (hX : Sep ⟪b, b - d⟫ ⟪b', b - d⟫ ⟪c', b - d⟫ ⟪a', b - d⟫) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨α, β1, γ4, β6, hdet, hc', hb', ha', hα, hβ1, hγ, hβ6⟩ := norm08_coords N hT hD.1
  obtain ⟨e1, e2, e3, hF, hu1, hu2, hu3, hv2, hv1, hw2⟩ := frame_exists hdet
  have hu : b - d = ⟪b - d, e3⟫ • e3 := by
    have := hF.expand (b - d); rw [hu1, hu2] at this; simpa using this
  have hv : c - d = ⟪c - d, e1⟫ • e1 + ⟪c - d, e3⟫ • e3 := by
    have := hF.expand (c - d); rw [hv2] at this; simpa using this
  have hw := hF.expand (a - d)
  obtain ⟨⟨s, t, hs0, hs1, ht0, ht1, hf1, hf2⟩⟩ : Nonempty (∃ s t : ℝ, 0 < s ∧ s < 1 ∧ 0 < t ∧ t < 1 ∧
    ⟪(c' + s • (b' - c')) - (c + t • (b - c)), b - d⟫ = 0 ∧
    ⟪(c' + s • (b' - c')) - (c + t • (b - c)), c - d⟫ = 0) := ⟨hD.2⟩
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
  have ha'_pt : a' = pt e1 e2 e3 o 0 0 (β6 * ν + C0) := by
    rw [ha', hu, hv]; simp only [pt, pc, ho]; module
  have hb'_pt : b' = pt e1 e2 e3 o (-v1 * (1 - γ4) + α * w1) (α * ha) (α * w3 + γ4 * C0) := by
    rw [hb', hw, hv]; simp only [pt, pc, ho]; module
  have hc'_pt : c' = pt e1 e2 e3 o (-v1 + α * w1) (α * ha) (α * w3 + β1 * ν) := by
    rw [hc', hw, hu]; simp only [pt, pc, ho]; module
  -- inner products with e1, e3
  have i1 := fun X Y z => inner_pt_1 hF o X Y z
  have i3 := fun X Y z => inner_pt_3 hF o X Y z
  -- feet
  have hfe3 : ⟪(c' + s • (b' - c')) - (c + t • (b - c)), e3⟫ = 0 := by
    rw [hu, real_inner_smul_right] at hf1
    exact (mul_eq_zero.mp hf1).resolve_left hu3.ne'
  have hfe1 : ⟪(c' + s • (b' - c')) - (c + t • (b - c)), e1⟫ = 0 := by
    rw [hv, inner_add_right, real_inner_smul_right, real_inner_smul_right, hfe3] at hf2
    have : v1 * ⟪(c' + s • (b' - c')) - (c + t • (b - c)), e1⟫ = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hv1
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left] at hfe1 hfe3
  rw [hc'_pt, hb'_pt, hc_pt, hb_pt, i1, i1, i1, i1] at hfe1
  rw [hc'_pt, hb'_pt, hc_pt, hb_pt, i3, i3, i3, i3] at hfe3
  -- depths
  have dep : ∀ p : ℝ³, ⟪p, b - d⟫ = ν * ⟪p, e3⟫ := fun p => by
    rw [hu, real_inner_smul_right]
  have ez : ∀ (p : ℝ³) (X Y z : ℝ), p = pt e1 e2 e3 o X Y z → ⟪p, b - d⟫ = ν * (z + ⟪o, e3⟫) := by
    intro p X Y z hp; rw [dep, hp, i3, add_comm]
  have zd := ez d _ _ _ hd_pt
  have zb := ez b _ _ _ hb_pt
  have zc := ez c _ _ _ hc_pt
  have za' := ez a' _ _ _ ha'_pt
  have zb' := ez b' _ _ _ hb'_pt
  have zc' := ez c' _ _ _ hc'_pt
  rw [zb, zb', zc, zc', sep_aff hu3] at hR1
  rw [zd, zb', zc', zc, sep_aff hu3] at hR2
  rw [zb, zb', zc', za', sep_aff hu3] at hX
  have eqXu : (-v1 + α * w1) + s * ((-v1 * (1 - γ4) + α * w1) - (-v1 + α * w1)) = t * (-v1) := by
    linarith
  have eqzu : (α * w3 + β1 * ν) + s * ((α * w3 + γ4 * C0) - (α * w3 + β1 * ν)) =
      (1 - t) * C0 + t * ν := by linarith
  rcases lt_or_gt_of_ne hv1 with hneg | hpos
  · rw [hd_pt, ha_pt, ha'_pt, hb_pt, hb'_pt, hc_pt, hc'_pt]
    exact param_core hF o (L := -v1) (X0 := -v1 * (1 - γ4) + α * w1) (X1 := -v1 + α * w1)
      (P := α * w3 + γ4 * C0) (R := α * w3 + β1 * ν) rfl rfl rfl rfl (by linarith) hu3 hw2 hα hβ1 hγ
      hβ6 hs0 hs1 ht0 ht1 eqXu eqzu hR1 hR2 hX
  · apply isRupert_of_reflect e1 hF.n11
    simp only [Finset.image_insert, Finset.image_singleton]
    have rd : d - (2 * ⟪d, e1⟫) • e1 = pt e1 e2 e3 (o - (2 * ⟪o, e1⟫) • e1) v1 0 0 := by
      rw [hd_pt, refl_pt hF]; exact pt_X (by ring)
    have ra : a - (2 * ⟪a, e1⟫) • e1 = pt e1 e2 e3 (o - (2 * ⟪o, e1⟫) • e1) (v1 + -w1) ha w3 := by
      rw [ha_pt, refl_pt hF]; exact pt_X (by ring)
    have ra' : a' - (2 * ⟪a', e1⟫) • e1 = pt e1 e2 e3 (o - (2 * ⟪o, e1⟫) • e1) 0 0 (β6 * ν + C0) := by
      rw [ha'_pt, refl_pt hF]; exact pt_X (by ring)
    have rb : b - (2 * ⟪b, e1⟫) • e1 = pt e1 e2 e3 (o - (2 * ⟪o, e1⟫) • e1) v1 0 ν := by
      rw [hb_pt, refl_pt hF]; exact pt_X (by ring)
    have rb' : b' - (2 * ⟪b', e1⟫) • e1 = pt e1 e2 e3 (o - (2 * ⟪o, e1⟫) • e1)
        (v1 * (1 - γ4) + α * (-w1)) (α * ha) (α * w3 + γ4 * C0) := by
      rw [hb'_pt, refl_pt hF]; exact pt_X (by ring)
    have rc : c - (2 * ⟪c, e1⟫) • e1 = pt e1 e2 e3 (o - (2 * ⟪o, e1⟫) • e1) 0 0 C0 := by
      rw [hc_pt, refl_pt hF]; exact pt_X (by ring)
    have rc' : c' - (2 * ⟪c', e1⟫) • e1 = pt e1 e2 e3 (o - (2 * ⟪o, e1⟫) • e1)
        (v1 + α * (-w1)) (α * ha) (α * w3 + β1 * ν) := by
      rw [hc'_pt, refl_pt hF]; exact pt_X (by ring)
    rw [rd, ra, ra', rb, rb', rc, rc']
    exact param_core hF (o - (2 * ⟪o, e1⟫) • e1) (L := v1) (w1 := -w1)
      (X0 := v1 * (1 - γ4) + α * (-w1)) (X1 := v1 + α * (-w1))
      (P := α * w3 + γ4 * C0) (R := α * w3 + β1 * ν) rfl rfl rfl rfl hpos hu3 hw2 hα hβ1 hγ
      hβ6 hs0 hs1 ht0 ht1 (by linarith) eqzu hR1 hR2 hX

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.closeT_H1_caseA
