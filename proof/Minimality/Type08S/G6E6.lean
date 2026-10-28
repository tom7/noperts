module

public import Minimality.Type08S.G6E5

@[expose] public section

set_option autoImplicit true

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- A quadrilateral rim at the view `ν e3` with two parallel sides (in the screen `e2`-direction
extremes) joined by a screen-perpendicular segment at equal depth is a horizontal double normal. -/
theorem hdn_contra (hF : Fr e1 e2 e3) {ν : ℝ} (hν : 0 < ν) (S : Finset ℝ³)
    (hno : NoHDNAt S (ν • e3)) (x : ZMod 4 → ℝ³) (hxS : ∀ i, x i ∈ S)
    (hccw : IsCcwPolygon fun i => (!₂[⟪x i, e1⟫, ⟪x i, e2⟫] : ℝ²))
    {P Q : ℝ³} {i j : ZMod 4} (hP : P ∈ segment ℝ (x i) (x (i + 1)))
    (hQ : Q ∈ segment ℝ (x j) (x (j + 1)))
    (h3 : ⟪P, e3⟫ = ⟪Q, e3⟫) (h1 : ⟪P, e1⟫ = ⟪Q, e1⟫) (h2 : ⟪Q, e2⟫ < ⟪P, e2⟫)
    (hb : ∀ i, ⟪Q, e2⟫ ≤ ⟪x i, e2⟫ ∧ ⟪x i, e2⟫ ≤ ⟪P, e2⟫) : False := by
  have hR := frameMat_mem hF
  have hRu : (orthoFrameMat e1 e2 e3).toEuclideanLin (ν • e3) = ν • ez := by
    have hn : ‖e3‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact hF.n33
    rw [orthoFrameMat_apply]
    ext i; fin_cases i <;>
      simp [Minimality.pt, ez, real_inner_smul_left, hF.n13, hF.n23, hn, real_inner_comm e1 e3,
        real_inner_comm e2 e3]
  have hpr : ∀ v, proj_xy ((orthoFrameMat e1 e2 e3).toEuclideanLin v) = (!₂[⟪v, e1⟫, ⟪v, e2⟫] : ℝ²) := fun v => (frameMat_apply v).1
  have hzz : ∀ v, ((orthoFrameMat e1 e2 e3).toEuclideanLin v) 2 = ⟪v, e3⟫ := fun v => (frameMat_apply v).2
  have hno' := hno _ hR ν hν.ne' hRu 4 x hxS (by simpa only [hpr] using hccw)
  apply hno'
  have key2 : ∀ u v : ℝ², ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 := by
    intro u v; simp [PiLp.inner_apply, Fin.sum_univ_two]; ring
  have hlift : ∀ v, liftPt (proj_xy ((orthoFrameMat e1 e2 e3).toEuclideanLin v)) (((orthoFrameMat e1 e2 e3).toEuclideanLin v) 2) = (orthoFrameMat e1 e2 e3).toEuclideanLin v := fun v => liftPt_proj_xy _
  refine ⟨(orthoFrameMat e1 e2 e3).toEuclideanLin P, (orthoFrameMat e1 e2 e3).toEuclideanLin Q, ⟨i, ?_⟩, ⟨j, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [hlift, hlift]
    obtain ⟨a, b, ha, hb', hab, rfl⟩ := hP
    exact ⟨a, b, ha, hb', hab, by simp [map_add, map_smul]⟩
  · rw [hlift, hlift]
    obtain ⟨a, b, ha, hb', hab, rfl⟩ := hQ
    exact ⟨a, b, ha, hb', hab, by simp [map_add, map_smul]⟩
  · rw [hzz, hzz, h3]
  · rw [hpr, hpr]
    intro h
    have := congrArg (fun w : ℝ² => w 1) h
    simp at this
    linarith
  · have hconv : Convex ℝ {q : ℝ² | ⟪Q, e2⟫ ≤ q 1 ∧ q 1 ≤ ⟪P, e2⟫} := by
      intro u hu v hv a b ha hb' hab
      simp only [Set.mem_ofPred_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at *
      have eQ : ⟪Q, e2⟫ = a * ⟪Q, e2⟫ + b * ⟪Q, e2⟫ := by rw [← add_mul, hab, one_mul]
      have eP : ⟪P, e2⟫ = a * ⟪P, e2⟫ + b * ⟪P, e2⟫ := by rw [← add_mul, hab, one_mul]
      constructor
      · nlinarith [mul_nonneg ha (sub_nonneg.2 hu.1), mul_nonneg hb' (sub_nonneg.2 hv.1)]
      · nlinarith [mul_nonneg ha (sub_nonneg.2 hu.2), mul_nonneg hb' (sub_nonneg.2 hv.2)]
    have hsub : convexHull ℝ (Set.range fun i => proj_xy ((orthoFrameMat e1 e2 e3).toEuclideanLin (x i))) ⊆
        {q : ℝ² | ⟪Q, e2⟫ ≤ q 1 ∧ q 1 ≤ ⟪P, e2⟫} := by
      refine convexHull_min ?_ hconv
      rintro _ ⟨i, rfl⟩
      show proj_xy ((orthoFrameMat e1 e2 e3).toEuclideanLin (x i)) ∈ _
      rw [hpr]; exact hb i
    intro q hq
    have := hsub hq
    rw [hpr, hpr, ← h1]
    rw [key2]
    simp only [PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [Set.mem_ofPred_eq] at this
    nlinarith [mul_nonneg (sub_nonneg.2 h2.le) (sub_nonneg.2 this.1)]
  · have hconv : Convex ℝ {q : ℝ² | ⟪Q, e2⟫ ≤ q 1 ∧ q 1 ≤ ⟪P, e2⟫} := by
      intro u hu v hv a b ha hb' hab
      simp only [Set.mem_ofPred_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at *
      have eQ : ⟪Q, e2⟫ = a * ⟪Q, e2⟫ + b * ⟪Q, e2⟫ := by rw [← add_mul, hab, one_mul]
      have eP : ⟪P, e2⟫ = a * ⟪P, e2⟫ + b * ⟪P, e2⟫ := by rw [← add_mul, hab, one_mul]
      constructor
      · nlinarith [mul_nonneg ha (sub_nonneg.2 hu.1), mul_nonneg hb' (sub_nonneg.2 hv.1)]
      · nlinarith [mul_nonneg ha (sub_nonneg.2 hu.2), mul_nonneg hb' (sub_nonneg.2 hv.2)]
    have hsub : convexHull ℝ (Set.range fun i => proj_xy ((orthoFrameMat e1 e2 e3).toEuclideanLin (x i))) ⊆
        {q : ℝ² | ⟪Q, e2⟫ ≤ q 1 ∧ q 1 ≤ ⟪P, e2⟫} := by
      refine convexHull_min ?_ hconv
      rintro _ ⟨i, rfl⟩
      show proj_xy ((orthoFrameMat e1 e2 e3).toEuclideanLin (x i)) ∈ _
      rw [hpr]; exact hb i
    intro q hq
    have := hsub hq
    rw [hpr, hpr, h1]
    rw [key2]
    simp only [PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [Set.mem_ofPred_eq] at this
    nlinarith [mul_nonneg (sub_nonneg.2 h2.le) (sub_nonneg.2 this.2)]

end Type08Sp
end Minimality
