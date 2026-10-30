module

public import Minimality.Type08S.P2I5b
public import Minimality.Type08S.P2I7b
public import Minimality.Type08S.P2TpX

@[expose] public section

set_option relaxedAutoImplicit true

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

theorem normalCone_of_far (S : Set ℝ²) {u t : ℝ²} (hfar : ∀ m ∈ S, ‖m - u‖ ≤ ‖t - u‖) :
    t - u ∈ normalConeAt (convexHull ℝ S) t := by
  intro q hq
  have hsub : S ⊆ {q : ℝ² | ⟪t - u, q - t⟫ ≤ 0} := by
    intro m hm
    have h1 := hfar m hm
    have h2 : ‖m - u‖ ^ 2 ≤ ‖t - u‖ ^ 2 := by gcongr
    have e : m - u = (m - t) + (t - u) := by abel
    rw [e, norm_add_sq_real] at h2
    have : ⟪t - u, m - t⟫ ≤ 0 := by
      rw [real_inner_comm]; nlinarith [sq_nonneg ‖m - t‖]
    exact this
  have hconv : Convex ℝ {q : ℝ² | ⟪t - u, q - t⟫ ≤ 0} := by
    have : {q : ℝ² | ⟪t - u, q - t⟫ ≤ 0} = {q : ℝ² | ⟪t - u, q⟫ ≤ ⟪t - u, t⟫} := by
      ext q; simp only [Set.mem_setOf_eq, inner_sub_right]; constructor <;> intro h <;> linarith
    rw [this]
    exact convex_halfSpace_le (f := fun q : ℝ² => ⟪t - u, q⟫) ⟨fun x y => inner_add_right _ _ _,
      fun c x => inner_smul_right _ _ _⟩ _
  exact convexHull_min hsub hconv hq

/-- A level strictly convex quadrilateral has a horizontal double normal (its diameter). -/
theorem hdn_level_quad (p : ZMod 4 → ℝ²) (z : ZMod 4 → ℝ) (z0 : ℝ) (hz : ∀ x, z x = z0)
    (hp : IsCcwPolygon p) : HasHorizontalDoubleNormal p z := by
  classical
  have hinj : Function.Injective p := hp.injective
  obtain ⟨⟨i, j⟩, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (ZMod 4 × ZMod 4))
    (fun ij => ‖p ij.1 - p ij.2‖) ⟨(0, 0), Finset.mem_univ _⟩
  have hij : p i ≠ p j := by
    intro h
    have h01 : p 0 ≠ p 1 := fun h' => absurd (hinj h') (by decide)
    have := hmax (0, 1) (Finset.mem_univ _)
    simp only [h, sub_self, norm_zero] at this
    exact h01 (sub_eq_zero.mp (norm_le_zero_iff.mp this))
  refine ⟨liftPt (p i) (z i), liftPt (p j) (z j), ⟨i, ?_⟩, ⟨j, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact left_mem_segment _ _ _
  · exact left_mem_segment _ _ _
  · simp [liftPt, hz]
  · have e : ∀ q t, proj_xy (liftPt q t) = q := by
      intro q t; ext m; fin_cases m <;> simp [proj_xy, liftPt]
    rw [e, e]; exact hij
  · have e : ∀ q t, proj_xy (liftPt q t) = q := by
      intro q t; ext m; fin_cases m <;> simp [proj_xy, liftPt]
    rw [e, e]
    exact normalCone_of_far _ (u := p i) (fun m hm => by
      obtain ⟨m', rfl⟩ := hm
      have := hmax (m', i) (Finset.mem_univ _)
      rw [norm_sub_rev (p j) (p i)]
      simpa using this)
  · have e : ∀ q t, proj_xy (liftPt q t) = q := by
      intro q t; ext m; fin_cases m <;> simp [proj_xy, liftPt]
    rw [e, e]
    exact normalCone_of_far _ (u := p j) (fun m hm => by
      obtain ⟨m', rfl⟩ := hm
      have := hmax (m', j) (Finset.mem_univ _)
      simpa using this)

theorem det3_AC (A C B : ℝ³) (s1 t1 s2 t2 : ℝ) :
    det3 (s1 • A + t1 • C) (s2 • A + t2 • C) B = (s1 * t2 - s2 * t1) * det3 A C B := by
  simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

/-- At the level face of `Q_ac` the corner polygon `X_2a = (d, a, b', c)` has a horizontal double normal
at `ℓ = b - d` (it is a level strictly convex quadrilateral; its diameter). -/
theorem level_not_noHDN {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hT' : IsT' a b c' d)
    (hlev : LevelQac a b c d) : ¬ NoHDNAt ({d, a, b', c} : Finset ℝ³) (b - d) := by
  intro h
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hα4, hγ4, hαγ, hβ1, hβ6, hγ6, hγ61, hcv⟩ :=
    norm08_coordsTp' N hT'
  obtain ⟨hla, hlc⟩ := hlev
  have hne : det3 (a - d) (c - d) (b - d) ≠ 0 := by
    intro h0; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = - det3 (a - d) (c - d) (b - d) := by
      simp only [det3_expand]; ring
    rw [e, h0, neg_zero]
  have hℓ : b - d ≠ 0 := sub_ne_zero.mpr (N.hd.ne.2.2.1.symm)
  -- the four points in the frame `(a - d, c - d)`
  set s : ZMod 4 → ℝ := ![0, 1, α4, 0] with hs
  set t : ZMod 4 → ℝ := ![0, 0, γ4, 1] with ht
  set x : ZMod 4 → ℝ³ := quad d a b' c with hx
  have hxd : ∀ i, x i - d = s i • (a - d) + t i • (c - d) := by
    intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl
    · simp [hx, hs, ht, quad]
    · simp [hx, hs, ht, quad]
    · simp only [hx, hs, ht, quad, Matrix.cons_val]; rw [hb']; module
    · simp [hx, hs, ht, quad]
  have hcr : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      0 < (s (i + 1) - s i) * (t j - t i) - (s j - s i) * (t (i + 1) - t i) := by
    intro i j h1 h2
    have e2 : (1 : ZMod 4) + 1 = 2 := by decide
    have e3 : (2 : ZMod 4) + 1 = 3 := by decide
    have e0 : (3 : ZMod 4) + 1 = 0 := by decide
    have e0' : (0 : ZMod 4) + 1 = 1 := by decide
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl h1 | (exact absurd (by decide) h2) |
        (simp [hs, ht, e2, e3, e0, e0'] <;> nlinarith)
  have key : ∀ w : ℝ³, (w = b - d ∨ w = -(b - d)) → 0 < det3 (a - d) (c - d) w → False := by
    intro w hw hΔ
    have hw0 : w ≠ 0 := by rintro rfl; simp [det3_expand] at hΔ
    obtain ⟨R, hR, lam, hlam, hRw⟩ := exists_rotation_to_ez_pos w hw0
    have hRℓ : ∃ r : ℝ, r ≠ 0 ∧ R.toEuclideanLin (b - d) = r • ez := by
      rcases hw with rfl | rfl
      · exact ⟨lam, hlam.ne', hRw⟩
      · refine ⟨-lam, by linarith, ?_⟩
        rw [map_neg] at hRw
        rw [neg_smul, ← hRw, neg_neg]
    obtain ⟨r, hr, hRu⟩ := hRℓ
    have hdep : ∀ y, lam * (R.toEuclideanLin y) 2 = ⟪y, w⟫ := by
      intro y
      rw [← inner_ez, ← real_inner_smul_right, ← hRw, inner_toEuclideanLin_SO3 hR]
    have hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))) := by
      refine ⟨by norm_num, fun i j h1 h2 => ?_⟩
      simp only [proj_rot_sub]
      refine cross2_proj_rot_pos hR hlam hRw ?_
      have e1 : x (i + 1) - x i = (s (i + 1) - s i) • (a - d) + (t (i + 1) - t i) • (c - d) := by
        have := hxd (i + 1); have := hxd i
        rw [show x (i + 1) - x i = (x (i + 1) - d) - (x i - d) by abel, hxd, hxd]; module
      have e2 : x j - x i = (s j - s i) • (a - d) + (t j - t i) • (c - d) := by
        rw [show x j - x i = (x j - d) - (x i - d) by abel, hxd, hxd]; module
      rw [e1, e2, det3_AC]
      exact mul_pos (hcr i j h1 h2) hΔ
    have hw1 : ⟪a - d, w⟫ = 0 ∧ ⟪c - d, w⟫ = 0 := by
      rcases hw with rfl | rfl
      · exact ⟨hla, hlc⟩
      · rw [inner_neg_right, inner_neg_right, hla, hlc]; simp
    have hz : ∀ i, (R.toEuclideanLin (x i)) 2 = lam⁻¹ * ⟪d, w⟫ := by
      intro i
      have h1 : ⟪x i - d, w⟫ = 0 := by
        rw [hxd, inner_add_left, real_inner_smul_left, real_inner_smul_left, hw1.1, hw1.2]; ring
      rw [inner_sub_left] at h1
      field_simp
      rw [mul_comm, hdep]; linarith
    refine h R hR r hr hRu 4 x (fun i => ?_) hp ?_
    · rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp [hx, quad]
    · exact hdn_level_quad _ _ (lam⁻¹ * ⟪d, w⟫) hz hp
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · refine key (-(b - d)) (Or.inr rfl) ?_
    have : det3 (a - d) (c - d) (-(b - d)) = - det3 (a - d) (c - d) (b - d) := by
      simp only [det3_expand, PiLp.neg_apply]; ring
    rw [this]; linarith
  · exact key (b - d) (Or.inl rfl) hpos

end Type08Sp
end Minimality
#print axioms Minimality.Type08Sp.level_not_noHDN
