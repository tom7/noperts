module

public import Minimality.RightPrism
public import Minimality.Type10Prism

@[expose] public section

/-!
# Type 10: the capped right prism is Rupert

Type 10 with `RightPrism10` is a right triangular prism `123`-`456` with an apex `0` whose
projection along the lateral edges lies strictly inside the triangle `123`
(`FEWER-FACES-PROOFS.md` §31).  We prove it Rupert by the tilted-view certificates of
Theorem 8.1 (`Minimality/RightPrism.lean`), adding one hidden point (the apex) to the
prism: `isRupert_rightPrism_cap`.  Then `isRupert_type10_rightPrism` derives the hypotheses from
`RealizesFaces x (sevenTypeFaces 9)`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- A hidden point `y` over the triangle `q₁ q₂ q₃` of bottom points (at height `0`). -/
theorem cert_hidden_bottom (V : Finset ℝ³) (v : ℝ²) (ω τ : ℝ³) {q₁ q₂ q₃ : ℝ²} {y : ℝ³}
    (h1 : liftPt q₁ 0 ∈ V) (h2 : liftPt q₂ 0 ∈ V) (h3 : liftPt q₃ 0 ∈ V)
    (hE : 0 < cross2 (q₂ - q₁) (q₃ - q₁))
    (e1 : 0 < cross2 (q₂ - q₁) (proj_xy y - q₁))
    (e2 : 0 < cross2 (q₃ - q₂) (proj_xy y - q₂))
    (e3 : 0 < cross2 (q₁ - q₃) (proj_xy y - q₃)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), TiltCert V (ez + ε • liftPt v 0) ω τ y := by
  have T0 := tt v (q₂ - q₁) 0 (liftPt (q₃ - q₁) 0) (Or.inl (by rw [proj_xy_liftPt]; exact hE))
  have T1 := tt v (q₂ - q₁) 0 (y - liftPt q₁ 0)
    (Or.inl (by rw [proj_xy_sub', proj_xy_liftPt]; exact e1))
  have T2 := tt v (q₃ - q₂) 0 (y - liftPt q₂ 0)
    (Or.inl (by rw [proj_xy_sub', proj_xy_liftPt]; exact e2))
  have T3 := tt v (q₁ - q₃) 0 (y - liftPt q₃ 0)
    (Or.inl (by rw [proj_xy_sub', proj_xy_liftPt]; exact e3))
  filter_upwards [T0, T1, T2, T3] with ε t0 t1 t2 t3
  refine Or.inr ⟨_, h1, _, h2, _, h3, ?_, ?_, ?_, ?_⟩
  · rw [liftPt_sub_liftPt, liftPt_sub_liftPt, sub_self]; exact t0
  · rw [liftPt_sub_liftPt, sub_self]; exact t1
  · rw [liftPt_sub_liftPt, sub_self]; exact t2
  · rw [liftPt_sub_liftPt, sub_self]; exact t3

/-- **Theorem 8.1 with a hidden cap point**: a right prism over a strictly convex polygon,
together with one point `y` (at any height) projecting strictly inside a triangle of polygon
vertices, is Rupert. -/
theorem isRupert_rightPrism_cap {k : ℕ} [NeZero k] (p : ZMod k → ℝ²) (hp : IsCcwPolygon p) {h : ℝ}
    (hh : 0 < h) (y : ℝ³) (i₁ i₂ i₃ : ZMod k)
    (hy0 : 0 < cross2 (p i₂ - p i₁) (p i₃ - p i₁))
    (hy1 : 0 < cross2 (p i₂ - p i₁) (proj_xy y - p i₁))
    (hy2 : 0 < cross2 (p i₃ - p i₂) (proj_xy y - p i₂))
    (hy3 : 0 < cross2 (p i₁ - p i₃) (proj_xy y - p i₃)) :
    IsRupert (insert y (rightPrism p h)) := by
  classical
  refine isRupert_rightPrism_gen p hp hh _ (Finset.subset_insert _ _) fun v ω τ => ?_
  have hbot : ∀ i, liftPt (p i) 0 ∈ insert y (rightPrism p h) := fun i =>
    Finset.mem_insert_of_mem ((mem_rightPrism p h _).mpr (Or.inl ⟨i, rfl⟩))
  filter_upwards [cert_hidden_bottom (insert y (rightPrism p h)) v ω τ (hbot i₁) (hbot i₂)
    (hbot i₃) hy0 hy1 hy2 hy3] with ε hε z hz
  have : z = y := by
    rcases Finset.mem_insert.mp (Finset.mem_sdiff.mp hz).1 with rfl | hz'
    · rfl
    · exact absurd hz' (Finset.mem_sdiff.mp hz).2
  rw [this]; exact hε

theorem six_swap {α : Type*} [DecidableEq α] (a b c d e f : α) :
    ({a, b, c, d, e, f} : Finset α) = {a, c, b, d, f, e} := by
  ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

/-- Cramer's rule for `det3`, applied to a linear functional. -/
theorem det3_cramer_lin (g : ℝ³ →ₗ[ℝ] ℝ) (u v w z : ℝ³) :
    det3 u v w * g z = det3 z v w * g u + det3 u z w * g v + det3 u v z * g w := by
  have h : det3 u v w • z = det3 z v w • u + det3 u z w • v + det3 u v z • w := by
    ext i; fin_cases i <;>
      simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three] <;> ring
  have := congrArg g h
  simpa [map_add, map_smul, mul_comm] using this

/-- A capped right translation prism over a triangle: the cap `y` projects (along `w`)
strictly inside the triangle `ABC`, expressed by three signed determinants. -/
theorem isRupert_cap_translationPrism_right (A B C w y : ℝ³) (hw0 : w ≠ 0)
    (hB : ⟪w, B - A⟫ = 0) (hC : ⟪w, C - A⟫ = 0)
    (hD : det3 (B - A) (C - A) w ≠ 0)
    (h1 : 0 < det3 (B - A) (C - A) w * det3 (B - A) (y - A) w)
    (h2 : 0 < det3 (B - A) (C - A) w * det3 (y - A) (C - A) w)
    (h3 : 0 < det3 (B - A) (C - A) w * det3 ((C - A) - (B - A)) ((y - A) - (B - A)) w) :
    IsRupert (insert y {A, B, C, A + w, B + w, C + w}) := by
  classical
  obtain ⟨R, hR, lam, hlam, hRw⟩ := exists_rotation_to_ez_pos w hw0
  set L := R.toEuclideanLin
  have hz : ∀ u, ⟪w, u⟫ = 0 → (L u) 2 = 0 := by
    intro u hu
    have : lam * (L u) 2 = ⟪w, u⟫ := by
      rw [← inner_ez, ← real_inner_smul_right, ← hRw, inner_toEuclideanLin_SO3 hR,
        real_inner_comm]
    rw [hu] at this
    exact (mul_eq_zero.mp this).resolve_left hlam.ne'
  set b := proj_xy (L (B - A))
  set c := proj_xy (L (C - A))
  set q := proj_xy (L (y - A))
  have hLB : L (B - A) = liftPt b 0 := by rw [← hz _ hB, liftPt_proj_xy]
  have hLC : L (C - A) = liftPt c 0 := by rw [← hz _ hC, liftPt_proj_xy]
  have hlift : ∀ q : ℝ², liftPt q 0 + lam • ez = liftPt q lam := by
    intro q; ext i; fin_cases i <;> simp [liftPt, ez]
  have hcr : lam * cross2 b c = det3 (B - A) (C - A) w := cross2_proj_rot hR hRw _ _
  have hbq : lam * cross2 b q = det3 (B - A) (y - A) w := cross2_proj_rot hR hRw _ _
  have hqc : lam * cross2 q c = det3 (y - A) (C - A) w := cross2_proj_rot hR hRw _ _
  have hcbq : lam * cross2 (c - b) (q - b) =
      det3 ((C - A) - (B - A)) ((y - A) - (B - A)) w := by
    have := cross2_proj_rot hR hRw ((C - A) - (B - A)) ((y - A) - (B - A))
    rw [← this]
    have e1 : c - b = proj_xy (R.toEuclideanLin ((C - A) - (B - A))) := proj_rot_sub R _ _
    have e2 : q - b = proj_xy (R.toEuclideanLin ((y - A) - (B - A))) := proj_rot_sub R _ _
    rw [e1, e2]
  -- move the prism to standard position
  apply isRupert_of_isRupert_image_rotation R hR
  apply isRupert_of_isRupert_image_add (-L A)
  set y0 : ℝ³ := -L A + L y with hy0
  have hy0L : y0 = L (y - A) := by rw [hy0, map_sub]; abel
  have hy0p : proj_xy y0 = q := by rw [hy0L]
  have hy0l : y0 = liftPt q (y0 2) := by rw [← hy0p]; exact (liftPt_proj_xy y0).symm
  have himg : (((insert y {A, B, C, A + w, B + w, C + w} : Finset ℝ³).image L).image
      fun x => -L A + x) = insert y0 {liftPt 0 0, liftPt b 0, liftPt c 0, liftPt 0 lam,
        liftPt b lam, liftPt c lam} := by
    simp only [Finset.image_insert, Finset.image_singleton, map_add, hRw]
    have e1 : -L A + L A = liftPt 0 0 := by ext i; fin_cases i <;> simp [liftPt]
    have e2 : -L A + L B = liftPt b 0 := by rw [← hLB, map_sub]; abel
    have e3 : -L A + L C = liftPt c 0 := by rw [← hLC, map_sub]; abel
    have e4 : -L A + (L A + lam • ez) = liftPt 0 lam := by
      rw [← hlift, ← e1]; abel
    have e5 : -L A + (L B + lam • ez) = liftPt b lam := by
      rw [← hlift, ← e2]; abel
    have e6 : -L A + (L C + lam • ez) = liftPt c lam := by
      rw [← hlift, ← e3]; abel
    rw [e1, e2, e3, e4, e5, e6]
  rw [himg]
  have hbc : cross2 b c ≠ 0 := by
    intro h0; apply hD; rw [← hcr, h0, mul_zero]
  have hpl : ∀ x : ℝ, 0 < lam * lam * x → 0 < x := fun x hx => by
    by_contra hx'
    push Not at hx'
    have := mul_nonpos_of_nonneg_of_nonpos (mul_pos hlam hlam).le hx'
    linarith
  have s1 : 0 < cross2 b c * cross2 b q := by
    rw [← hcr, ← hbq] at h1; exact hpl _ (by linarith)
  have s2 : 0 < cross2 b c * cross2 q c := by
    rw [← hcr, ← hqc] at h2; exact hpl _ (by linarith)
  have s3 : 0 < cross2 b c * cross2 (c - b) (q - b) := by
    rw [← hcr, ← hcbq] at h3; exact hpl _ (by linarith)
  have k1 : cross2 (c - 0) (b - 0) = -cross2 b c := by simp [cross2]; ring
  have k2 : cross2 (c - 0) (q - 0) = -cross2 q c := by simp [cross2]; ring
  have k3 : cross2 (b - c) (q - c) = -cross2 (c - b) (q - b) := by simp [cross2]; ring
  have k4 : cross2 (0 - b) (q - b) = -cross2 b q := by simp [cross2]; ring
  have k5 : cross2 (b - 0) (c - 0) = cross2 b c := by simp
  have k6 : cross2 (b - 0) (q - 0) = cross2 b q := by simp
  have k7 : cross2 (0 - c) (q - c) = cross2 q c := by simp [cross2]; ring
  rcases lt_or_gt_of_ne hbc with hneg | hpos
  · have hp : IsCcwPolygon (tri 0 c b) := isCcwPolygon_tri (by rw [k1]; linarith)
    have := isRupert_rightPrism_cap (tri 0 c b) hp hlam y0 0 1 2
      (by show 0 < cross2 (c - 0) (b - 0); rw [k1]; linarith)
      (by rw [hy0p]; show 0 < cross2 (c - 0) (q - 0); rw [k2]; nlinarith)
      (by rw [hy0p]; show 0 < cross2 (b - c) (q - c); rw [k3]; nlinarith)
      (by rw [hy0p]; show 0 < cross2 (0 - b) (q - b); rw [k4]; nlinarith)
    rw [rightPrism_tri] at this
    rw [six_swap]; exact this
  · have hp : IsCcwPolygon (tri 0 b c) := isCcwPolygon_tri (by rw [k5]; exact hpos)
    have := isRupert_rightPrism_cap (tri 0 b c) hp hlam y0 0 1 2
      (by show 0 < cross2 (b - 0) (c - 0); rw [k5]; exact hpos)
      (by rw [hy0p]; show 0 < cross2 (b - 0) (q - 0); rw [k6]; nlinarith)
      (by rw [hy0p]; show 0 < cross2 (c - b) (q - b); nlinarith)
      (by rw [hy0p]; show 0 < cross2 (0 - c) (q - c); rw [k7]; nlinarith)
    rwa [rightPrism_tri] at this

theorem det3_cross_self (v w : ℝ³) :
    det3 (cross v w) v w = ⟪v, v⟫ * ⟪w, w⟫ - ⟪v, w⟫ ^ 2 := by
  simp only [det3, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial,
    cross_apply_zero, cross_apply_one, cross_apply_two]
  ring

theorem det3_sub_sub (u v z w : ℝ³) :
    det3 (v - u) (z - u) w = det3 u v w - det3 z v w - det3 u z w := by
  simp only [det3, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial,
    cross_apply_zero, cross_apply_one, cross_apply_two]
  simp only [PiLp.sub_apply]
  ring

theorem t10_sign1 {D E g₁ g₂ : ℝ} (hD : 0 < D * D) (h : D * g₂ = E * g₁) (hg₁ : g₁ < 0)
    (hg₂ : g₂ < 0) : 0 < D * E := by
  by_contra hneg
  push Not at hneg
  have e : (D * E) * g₁ = (D * D) * g₂ := by rw [mul_assoc, ← h]; ring
  have h1 : (D * D) * g₂ < 0 := mul_neg_of_pos_of_neg hD hg₂
  have h2 : 0 ≤ (D * E) * g₁ := mul_nonneg_of_nonpos_of_nonpos hneg hg₁.le
  linarith

theorem t10_sign2 {D T ρ g : ℝ} (hρ : 0 < ρ) (hD : 0 < D * D) (h : D * g = T * ρ)
    (hg : g < ρ) : 0 < D * (D - T) := by
  by_contra hneg
  push Not at hneg
  have e : ρ * (D * (D - T)) = (D * D) * (ρ - g) := by linear_combination D * h
  have h1 : 0 < (D * D) * (ρ - g) := mul_pos hD (by linarith)
  have h2 : ρ * (D * (D - T)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hρ.le hneg
  linarith

theorem affine_linear_sub (φ : ℝ³ →ᵃ[ℝ] ℝ) (a b : ℝ³) : φ.linear (a - b) = φ a - φ b := by
  simpa using φ.linearMap_vsub a b

/-- **The capped right prism of type 10 is Rupert.**  The apex `x 0` lies strictly on the
inner side of the three lateral facets `1245`, `1346`, `2356`, so it projects (along the
lateral edges) strictly inside the triangle `123`, and is hidden at the near-axis views of
Theorem 8.1. -/
theorem isRupert_type10_rightPrism (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (hP : RightPrism10 x) (hR : RealizesFaces x (sevenTypeFaces 9)) :
    IsRupert (Finset.univ.image x) := by
  classical
  obtain ⟨hP1, hP2, hP3, hP4⟩ := hP
  obtain ⟨fA, hfA⟩ := hR {1, 2, 4, 5} (by decide)
  obtain ⟨fB, hfB⟩ := hR {1, 3, 4, 6} (by decide)
  obtain ⟨fC, hfC⟩ := hR {2, 3, 5, 6} (by decide)
  set A := x 1
  set B := x 2
  set C := x 3
  set w := x 4 - x 1 with hw
  set y := x 0
  have h4 : x 4 = A + w := by rw [hw]; abel
  have h5 : x 5 = B + w := by rw [hP1]; abel
  have h6 : x 6 = C + w := by rw [hP2]; abel
  have hw5 : w = x 5 - x 2 := hP1
  have hw6 : w = x 6 - x 3 := hP2
  have hset : Finset.univ.image x = insert y {A, B, C, A + w, B + w, C + w} := by
    ext p
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h6)))))
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨4, h4⟩
      · exact ⟨5, h5⟩
      · exact ⟨6, h6⟩
  rw [hset]
  -- facet values
  have gA : ∀ a b, fA.linear (a - b) = fA a - fA b := affine_linear_sub fA
  have gB : ∀ a b, fB.linear (a - b) = fB a - fB b := affine_linear_sub fB
  have gC : ∀ a b, fC.linear (a - b) = fC a - fC b := affine_linear_sub fC
  set u := B - A with hu
  set v := C - A with hv
  set z := y - A with hz
  have a1 := (hfA 1).1 (by decide)
  have a2 := (hfA 2).1 (by decide)
  have a4 := (hfA 4).1 (by decide)
  have a3 := (hfA 3).2 (by decide)
  have a0 := (hfA 0).2 (by decide)
  have b1 := (hfB 1).1 (by decide)
  have b3 := (hfB 3).1 (by decide)
  have b4 := (hfB 4).1 (by decide)
  have b2 := (hfB 2).2 (by decide)
  have b0 := (hfB 0).2 (by decide)
  have c2 := (hfC 2).1 (by decide)
  have c3 := (hfC 3).1 (by decide)
  have c5 := (hfC 5).1 (by decide)
  have c1 := (hfC 1).2 (by decide)
  have c0 := (hfC 0).2 (by decide)
  have wA : fA.linear w = 0 := by rw [hw, gA]; simp only [a4, a1]; ring
  have uA : fA.linear u = 0 := by rw [hu, gA]; simp only [B, A, a2, a1]; ring
  have vA : fA.linear v < 0 := by rw [hv, gA]; simp only [C, A, a1]; linarith
  have zA : fA.linear z < 0 := by rw [hz, gA]; simp only [y, A, a1]; linarith
  have wB : fB.linear w = 0 := by rw [hw, gB]; simp only [b4, b1]; ring
  have vB : fB.linear v = 0 := by rw [hv, gB]; simp only [C, A, b3, b1]; ring
  have uB : fB.linear u < 0 := by rw [hu, gB]; simp only [B, A, b1]; linarith
  have zB : fB.linear z < 0 := by rw [hz, gB]; simp only [y, A, b1]; linarith
  have wC : fC.linear w = 0 := by rw [hw5, gC]; simp only [c5, c2]; ring
  have uC : fC.linear u = -fC A := by rw [hu, gC]; simp only [B, A, c2]; ring
  have vC : fC.linear v = -fC A := by rw [hv, gC]; simp only [C, A, c3]; ring
  have zC : fC.linear z = fC y - fC A := by rw [hz, gC]
  have hρ : 0 < -fC A := by simp only [A]; linarith
  have hy0 : fC y < 0 := c0
  -- nondegeneracy
  have hv0 : v ≠ 0 := by
    intro h0
    have : x 3 = x 1 := by rw [hv] at h0; exact sub_eq_zero.mp h0
    exact absurd (hx this) (by decide)
  have hw0 : w ≠ 0 := by
    intro h0
    have : x 4 = x 1 := by rw [hw] at h0; exact sub_eq_zero.mp h0
    exact absurd (hx this) (by decide)
  have hvw : ⟪v, w⟫ = 0 := hP4
  have huw : ⟪u, w⟫ = 0 := hP3
  have hD : det3 u v w ≠ 0 := by
    intro hD0
    have cr := det3_cramer_lin fB.linear u v w (cross v w)
    rw [hD0, wB, vB, zero_mul, mul_zero, mul_zero, add_zero, add_zero] at cr
    have hpos : 0 < det3 (cross v w) v w := by
      rw [det3_cross_self, hvw]
      have h1 : 0 < ⟪v, v⟫ := real_inner_self_pos.mpr hv0
      have h2 : 0 < ⟪w, w⟫ := real_inner_self_pos.mpr hw0
      nlinarith
    nlinarith
  have hD2 : 0 < det3 u v w * det3 u v w := mul_self_pos.mpr hD
  have e1 : 0 < det3 u v w * det3 u z w := by
    have cr := det3_cramer_lin fA.linear u v w z
    rw [wA, uA, mul_zero, mul_zero, zero_add, add_zero] at cr
    exact t10_sign1 hD2 cr vA zA
  have e2 : 0 < det3 u v w * det3 z v w := by
    have cr := det3_cramer_lin fB.linear u v w z
    rw [wB, vB, mul_zero, mul_zero, add_zero, add_zero] at cr
    exact t10_sign1 hD2 cr uB zB
  have e3 : 0 < det3 u v w * det3 (v - u) (z - u) w := by
    have cr := det3_cramer_lin fC.linear u v w z
    rw [wC, uC, vC, zC, mul_zero, add_zero] at cr
    rw [det3_sub_sub u v z w]
    have := t10_sign2 (T := det3 z v w + det3 u z w) hρ hD2
      (by rw [cr]; ring) (show fC y - fC A < -fC A by linarith)
    linarith
  exact isRupert_cap_translationPrism_right A B C w y hw0 (by rw [real_inner_comm]; exact huw)
    (by rw [real_inner_comm]; exact hvw) hD e1 e2 e3

end Minimality

end
