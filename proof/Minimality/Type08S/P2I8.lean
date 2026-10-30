module

public import Minimality.Type08S.P2RS1

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# I8: `NoHDNRim` at `u` (a strictly convex rim) implies `NoPersistHDN` for every slide direction `e`
(the converse of `eventually_noHDNRim_slide`'s pair extraction at the view itself).
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

theorem noPersist_of_noHDNRim {k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : ZMod k → ℝ³) {u : ℝ³} (e : ℝ³)
    (hu : u ≠ 0)
    (hcyc : ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 → 0 < det3 (x (i + 1) - x i) (x j - x i) u)
    (hnd : NoHDNRim x u) : NoPersistHDN x u e := by
  intro i j Y hY Y' hY' hne hu0 he hall
  obtain ⟨R, hR, r, hr, hRu⟩ := exists_rotation_to_ez_pos u hu
  have hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))) := by
    refine ⟨hk, fun i j hi hj => ?_⟩
    simp only [proj_rot_sub]
    exact cross2_proj_rot_pos hR hr hRu (hcyc i j hi hj)
  have hdepth := depth_rot hR hr.ne' hRu
  apply hnd R hR r hr.ne' hRu hp
  have hhor : (R.toEuclideanLin (Y' - Y)) 2 = 0 := by
    rw [hdepth, hu0, mul_zero]
  have hhor' : (R.toEuclideanLin (Y - Y')) 2 = 0 := by rw [← neg_sub, map_neg, PiLp.neg_apply, hhor, neg_zero]
  have hseg : ∀ {a b w : ℝ³}, w ∈ segment ℝ a b → R.toEuclideanLin w ∈ segment ℝ (R.toEuclideanLin a) (R.toEuclideanLin b) := by
    intro a b w hw
    obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hw
    exact ⟨α, β, hα, hβ, hαβ, by simp [map_add, map_smul]⟩
  have hLinj : ∀ A B : ℝ³, R.toEuclideanLin A = R.toEuclideanLin B → A = B := by
    intro A B h
    have h1 : ⟪R.toEuclideanLin (A - B), R.toEuclideanLin (A - B)⟫ = 0 := by rw [map_sub, h, sub_self, inner_zero_left]
    rw [inner_toEuclideanLin_SO3 hR] at h1
    exact sub_eq_zero.mp (inner_self_eq_zero.mp h1)
  have hnc : ∀ (A B : ℝ³), (R.toEuclideanLin (A - B)) 2 = 0 → (∀ m, ⟪A - B, x m - A⟫ ≤ 0) →
      proj_xy (R.toEuclideanLin A) - proj_xy (R.toEuclideanLin B) ∈ normalConeAt
        (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))) (proj_xy (R.toEuclideanLin A)) := by
    intro A B hAB hext q hq
    have hconv : Convex ℝ {q : ℝ² | ⟪proj_xy (R.toEuclideanLin A) - proj_xy (R.toEuclideanLin B), q - proj_xy (R.toEuclideanLin A)⟫ ≤ 0} := by
      intro q1 h1 q2 h2 s t hs ht hst
      simp only [Set.mem_ofPred_eq] at h1 h2 ⊢
      have : ⟪proj_xy (R.toEuclideanLin A) - proj_xy (R.toEuclideanLin B), (s • q1 + t • q2) - proj_xy (R.toEuclideanLin A)⟫ =
          s * ⟪proj_xy (R.toEuclideanLin A) - proj_xy (R.toEuclideanLin B), q1 - proj_xy (R.toEuclideanLin A)⟫ +
          t * ⟪proj_xy (R.toEuclideanLin A) - proj_xy (R.toEuclideanLin B), q2 - proj_xy (R.toEuclideanLin A)⟫ := by
        have e : (s • q1 + t • q2) - proj_xy (R.toEuclideanLin A) = s • (q1 - proj_xy (R.toEuclideanLin A)) + t • (q2 - proj_xy (R.toEuclideanLin A)) := by
          have : proj_xy (R.toEuclideanLin A) = (s + t) • proj_xy (R.toEuclideanLin A) := by rw [hst, one_smul]
          conv_lhs => rw [this]
          module
        rw [e, inner_add_right, real_inner_smul_right, real_inner_smul_right]
      rw [this]; nlinarith
    have hsub : Set.range (fun i => proj_xy (R.toEuclideanLin (x i))) ⊆
        {q : ℝ² | ⟪proj_xy (R.toEuclideanLin A) - proj_xy (R.toEuclideanLin B), q - proj_xy (R.toEuclideanLin A)⟫ ≤ 0} := by
      rintro _ ⟨m, rfl⟩
      simp only [Set.mem_ofPred_eq]
      rw [← proj_xy_sub', ← proj_xy_sub', inner_proj_xy_of_horizontal (by rw [← map_sub]; exact hAB),
        ← map_sub, ← map_sub, inner_toEuclideanLin_SO3 hR]
      exact hext m
    exact convexHull_min hsub hconv hq
  refine ⟨R.toEuclideanLin Y, R.toEuclideanLin Y', ⟨i, ?_⟩, ⟨j, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [liftPt_proj_xy, liftPt_proj_xy]; exact hseg hY
  · rw [liftPt_proj_xy, liftPt_proj_xy]; exact hseg hY'
  · have := hhor; rw [map_sub, PiLp.sub_apply] at this; linarith
  · intro h
    apply hne
    apply hLinj
    have h2 : (R.toEuclideanLin Y) 2 = (R.toEuclideanLin Y') 2 := by have := hhor; rw [map_sub, PiLp.sub_apply] at this; linarith
    rw [← liftPt_proj_xy (R.toEuclideanLin Y), ← liftPt_proj_xy (R.toEuclideanLin Y'), h, h2]
  · exact hnc Y' Y hhor (fun m => (hall m).1)
  · exact hnc Y Y' hhor' (fun m => (hall m).2)

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.noPersist_of_noHDNRim
