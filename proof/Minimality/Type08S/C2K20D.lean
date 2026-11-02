module

public import Minimality.Type08S.C2K20C

@[expose] public section


/-!
# K20 / D: the 3D form (`k20_prism3`): any truncated right prism over a triangle plus a base point beyond an edge

`{d, d+B1, d+B2, d+βB1+γB2, d+z0 n, d+B1+z1 n, d+B2+z2 n}` with `n ⟂ B1, B2`, `det3 B1 B2 n ≠ 0`, `z0,z1,z2 > 0`,
`β + γ > 1` is Rupert (rotate `n` to `e_z`, translate `d` to `0`, `k20_triExt`).
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem k20_prism3 (d n B1 B2 : ℝ³) {β γ z0 z1 z2 : ℝ} (h1 : ⟪n, B1⟫ = 0) (h2 : ⟪n, B2⟫ = 0)
    (hD : det3 B1 B2 n ≠ 0) (hz0 : 0 < z0) (hz1 : 0 < z1) (hz2 : 0 < z2) (hβγ : 1 < β + γ) :
    IsRupert ({d, d + B1, d + B2, d + (β • B1 + γ • B2), d + z0 • n, d + B1 + z1 • n, d + B2 + z2 • n} :
      Finset ℝ³) := by
  classical
  have hn0 : n ≠ 0 := by rintro rfl; simp [det3] at hD
  obtain ⟨R, hR, lam, hlam, hRw⟩ := exists_rotation_to_ez_pos n hn0
  set L := R.toEuclideanLin
  have hz : ∀ u, ⟪n, u⟫ = 0 → (L u) 2 = 0 := by
    intro u hu
    have : lam * (L u) 2 = ⟪n, u⟫ := by
      rw [← inner_ez, ← real_inner_smul_right, ← hRw, inner_toEuclideanLin_SO3 hR,
        real_inner_comm]
    rw [hu] at this
    exact (mul_eq_zero.mp this).resolve_left hlam.ne'
  set b := proj_xy (L B1)
  set c := proj_xy (L B2)
  have hLB : L B1 = liftPt b 0 := by rw [← hz _ h1, liftPt_proj_xy]
  have hLC : L B2 = liftPt c 0 := by rw [← hz _ h2, liftPt_proj_xy]
  have hcr : lam * cross2 b c = det3 B1 B2 n := cross2_proj_rot hR hRw _ _
  set e : ℝ² := β • b + γ • c
  have hlift : ∀ (q : ℝ²) (z : ℝ), liftPt q 0 + (z * lam) • ez = liftPt q (z * lam) := by
    intro q z; ext i; fin_cases i <;> simp [liftPt, ez]
  apply isRupert_of_isRupert_image_rotation R hR
  apply isRupert_of_isRupert_image_add (-L d)
  have himg : ((({d, d + B1, d + B2, d + (β • B1 + γ • B2), d + z0 • n, d + B1 + z1 • n,
      d + B2 + z2 • n} : Finset ℝ³).image L).image fun x => -L d + x) =
      {liftPt 0 0, liftPt b 0, liftPt c 0, liftPt e 0, liftPt 0 (z0 * lam), liftPt b (z1 * lam),
        liftPt c (z2 * lam)} := by
    simp only [Finset.image_insert, Finset.image_singleton, map_add, map_smul, hRw, hLB, hLC]
    have e0 : -L d + L d = liftPt 0 0 := by ext i; fin_cases i <;> simp [liftPt]
    have eb : -L d + (L d + liftPt b 0) = liftPt b 0 := by abel
    have ec : -L d + (L d + liftPt c 0) = liftPt c 0 := by abel
    have ee : -L d + (L d + (β • liftPt b 0 + γ • liftPt c 0)) = liftPt e 0 := by
      rw [neg_add_cancel_left]; ext i; fin_cases i <;> simp [liftPt, e]
    have e4 : -L d + (L d + z0 • lam • ez) = liftPt 0 (z0 * lam) := by
      rw [neg_add_cancel_left, ← hlift, smul_smul]; ext i; fin_cases i <;> simp [liftPt]
    have e5 : -L d + (L d + liftPt b 0 + z1 • lam • ez) = liftPt b (z1 * lam) := by
      rw [add_assoc, neg_add_cancel_left, ← hlift, smul_smul]
    have e6 : -L d + (L d + liftPt c 0 + z2 • lam • ez) = liftPt c (z2 * lam) := by
      rw [add_assoc, neg_add_cancel_left, ← hlift, smul_smul]
    rw [e0, eb, ec, ee, e4, e5, e6]
  rw [himg]
  have hbc : cross2 b c ≠ 0 := by intro h0; apply hD; rw [← hcr, h0, mul_zero]
  have hEe : ∀ x y : ℝ², cross2 (β • x + γ • y - x) (y - (β • x + γ • y)) = (β + γ - 1) * cross2 x y := by
    intro x y; simp [cross2]; ring
  rcases lt_or_gt_of_ne hbc with hneg | hpos
  · have hE : 0 < cross2 (e - c) (b - e) := by
      have : cross2 (e - c) (b - e) = (β + γ - 1) * -cross2 b c := by simp [e, cross2]; ring
      rw [this]; nlinarith
    have := k20_triExt 0 c b e (mul_pos hz0 hlam) (mul_pos hz2 hlam) (mul_pos hz1 hlam)
      (by have : cross2 (c - 0) (b - 0) = -cross2 b c := by simp [cross2]; ring
          rw [this]; linarith) hE
    convert this using 1
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · have hE : 0 < cross2 (e - b) (c - e) := by rw [hEe]; nlinarith
    exact k20_triExt 0 b c e (mul_pos hz0 hlam) (mul_pos hz1 hlam) (mul_pos hz2 hlam)
      (by simpa using hpos) hE

end C2
end Type08Sp
end Minimality
