module

public import Mathlib
public import MinimalityExtra

/-!
# No passage with opposite inner and outer views

If the inner view is the opposite of the outer view, the inner shadow is a congruent copy of the
outer shadow (a reflection of it, composed with a translation), so it cannot lie in its interior:
a distance-preserving copy of a compact set `B` never fits in `interior B`, because a maximal
pair of points of `B` would map to interior points, which can be pushed further apart inside `B`.
-/

@[expose] public section

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace MinimalityExtra


/-- Two interior points of `B` cannot realise the maximal distance in `B`. -/
theorem no_maximal_pair_interior {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    {B : Set E} {a b : E} (ha : a ∈ interior B) (hb : b ∈ interior B)
    (hmax : ∀ x ∈ B, ∀ y ∈ B, dist x y ≤ dist a b) : False := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior b hb
  have hball' : Metric.ball b ε ⊆ B := hball.trans interior_subset
  have haB : a ∈ B := interior_subset ha
  obtain ⟨w, hw⟩ := exists_norm_eq E (zero_le_one' ℝ)
  by_cases hab : a = b
  · subst hab
    have hz : a + (ε/2) • w ∈ B := hball' (by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hw]
      simp [abs_of_pos hε]; linarith)
    have := hmax _ hz a haB
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hw, dist_self] at this
    simp [abs_of_pos hε] at this
    linarith
  · have hu : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hab))
    set u := b - a
    set t := ε / 2 / ‖u‖ with ht
    have htpos : 0 < t := by positivity
    have hz : b + t • u ∈ B := hball' (by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg htpos.le,
        ht]
      field_simp; linarith)
    have := hmax _ hz a haB
    have e : b + t • u - a = (1 + t) • u := by simp only [u]; module
    rw [dist_eq_norm, e, norm_smul, Real.norm_of_nonneg (by linarith), dist_eq_norm] at this
    have : (1 + t) * ‖u‖ ≤ ‖b - a‖ := by simpa [u, norm_sub_rev a b] using this
    nlinarith

/-- A compact set cannot be mapped distance-preservingly into its own interior. -/
theorem noIsometricCopyInInterior' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] {B : Set E} (hB : IsCompact B) (hne : B.Nonempty) (φ : E → E)
    (hφ : ∀ x ∈ B, ∀ y ∈ B, dist (φ x) (φ y) = dist x y) :
    ¬ φ '' B ⊆ interior B := by
  intro h
  obtain ⟨⟨p, q⟩, hpq, hmax⟩ := (hB.prod hB).exists_isMaxOn (hne.prod hne)
    (continuous_fst.dist continuous_snd).continuousOn
  refine no_maximal_pair_interior (a := φ p) (b := φ q) (h ⟨p, hpq.1, rfl⟩) (h ⟨q, hpq.2, rfl⟩) ?_
  intro x hx y hy
  rw [hφ p hpq.1 q hpq.2]
  exact hmax (show (x, y) ∈ B ×ˢ B from ⟨hx, hy⟩)


theorem rotNorm {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (p : ℝ³) : ‖R.toEuclideanLin p‖ = ‖p‖ := by
  have h1 : R.transpose * R = 1 := by
    have := (Matrix.mem_orthogonalGroup_iff' _ _ |>.mp
      (Matrix.mem_specialOrthogonalGroup_iff.mp hR).1)
    simpa [Matrix.star_eq_conjTranspose] using this
  have key : ∀ v : Fin 3 → ℝ, (R.mulVec v) ⬝ᵥ (R.mulVec v) = v ⬝ᵥ v := by
    intro v
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, h1,
      Matrix.one_mulVec]
  have : ‖R.toEuclideanLin p‖ ^ 2 = ‖p‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simpa [dotProduct, sq, Matrix.mulVec] using key p.ofLp
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp this

theorem normsq_proj_xy (v : ℝ³) : ‖proj_xy v‖ ^ 2 = ‖v‖ ^ 2 - (v 2) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp [proj_xy, Fin.sum_univ_succ, Fin.sum_univ_two]
  ring

theorem proj_xy_sub (v w : ℝ³) : proj_xy (v - w) = proj_xy v - proj_xy w := by
  ext i; fin_cases i <;> simp [proj_xy]

theorem dist_shadow_eq {Rin Rout : Matrix (Fin 3) (Fin 3) ℝ}
    (hin : Rin ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (hout : Rout ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (hopp : ∀ p : ℝ³, Rin.toEuclideanLin p 2 = - Rout.toEuclideanLin p 2) (p q : ℝ³) :
    dist (proj_xy (Rin.toEuclideanLin p)) (proj_xy (Rin.toEuclideanLin q)) =
      dist (proj_xy (Rout.toEuclideanLin p)) (proj_xy (Rout.toEuclideanLin q)) := by
  have key : ∀ R : Matrix (Fin 3) (Fin 3) ℝ, R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ →
      dist (proj_xy (R.toEuclideanLin p)) (proj_xy (R.toEuclideanLin q)) ^ 2 =
        ‖p - q‖ ^ 2 - (R.toEuclideanLin (p - q) 2) ^ 2 := by
    intro R hR
    rw [dist_eq_norm, ← proj_xy_sub, ← map_sub, normsq_proj_xy, rotNorm hR]
  have h1 := key Rin hin
  have h2 := key Rout hout
  rw [hopp (p - q)] at h1
  have : dist (proj_xy (Rin.toEuclideanLin p)) (proj_xy (Rin.toEuclideanLin q)) ^ 2 =
      dist (proj_xy (Rout.toEuclideanLin p)) (proj_xy (Rout.toEuclideanLin q)) ^ 2 := by
    rw [h1, h2]; ring
  exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp this

theorem noOppositeViewPassage' (vs : Finset ℝ³) (hvs : vs.Nonempty)
    (Rin : Matrix (Fin 3) (Fin 3) ℝ) (hin : Rin ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (off : EuclideanSpace ℝ (Fin 2))
    (Rout : Matrix (Fin 3) (Fin 3) ℝ) (hout : Rout ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (hopp : ∀ p : ℝ³, Rin.toEuclideanLin p 2 = - Rout.toEuclideanLin p 2) :
    ¬ ({ off + proj_xy (Rin.toEuclideanLin p) | p ∈ convexHull ℝ (vs : Set ℝ³) } ⊆
        interior { proj_xy (Rout.toEuclideanLin p) | p ∈ convexHull ℝ (vs : Set ℝ³) }) := by
  intro hsub
  obtain ⟨S, hSdef⟩ : ∃ S : Set ℝ³, S = convexHull ℝ (vs : Set ℝ³) := ⟨_, rfl⟩
  rw [← hSdef] at hsub
  have hS : IsCompact S := hSdef ▸ (Set.Finite.isCompact_convexHull (𝕜 := ℝ) vs.finite_toSet)
  have hSne : S.Nonempty := hSdef ▸ (convexHull_nonempty_iff).mpr (by simpa using hvs)
  have hcont : Continuous fun p : ℝ³ => proj_xy (Rout.toEuclideanLin p) := by
    unfold proj_xy
    fun_prop
  obtain ⟨⟨p, q⟩, hpq, hmax⟩ := (hS.prod hS).exists_isMaxOn (hSne.prod hSne)
    ((hcont.comp continuous_fst).dist (hcont.comp continuous_snd)).continuousOn
  have hp : off + proj_xy (Rin.toEuclideanLin p) ∈
      { off + proj_xy (Rin.toEuclideanLin p) | p ∈ S } := ⟨p, hpq.1, rfl⟩
  have hq : off + proj_xy (Rin.toEuclideanLin q) ∈
      { off + proj_xy (Rin.toEuclideanLin p) | p ∈ S } := ⟨q, hpq.2, rfl⟩
  have key := no_maximal_pair_interior (hsub hp) (hsub hq)
  apply key
  intro x hx y hy
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  rw [dist_add_left, dist_shadow_eq hin hout hopp]
  have hm := isMaxOn_iff.mp hmax (x', y') (Set.mk_mem_prod hx' hy')
  exact hm

theorem noIsometricCopyInInterior : NoIsometricCopyInInterior := by
  intro B hB hne φ hφ
  exact noIsometricCopyInInterior' hB hne φ hφ

theorem noOppositeViewPassage : NoOppositeViewPassage := by
  intro vs hvs Rin hin off Rout hout hopp
  exact noOppositeViewPassage' vs hvs Rin hin off Rout hout hopp

end MinimalityExtra
