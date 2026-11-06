module

public import Mathlib
public import MinimalityExtra
public import MinimalityExtra.Opposite

/-!
# Equal width in a screen direction: no passage

If the inner and outer shadows have the same extent in some unit direction `m` of the screen,
then the inner shadow (translated by any offset) is not in the interior of the outer shadow: the
extreme points of the inner shadow in direction `m` would lie in the interior of the outer one, so
the outer extent would be strictly larger. For a unit vector `n` of space whose images under both
rotations lie in the screen and agree up to sign (the "picture-symmetric" poses), the two extents
are both the width of the polytope in direction `n`; if instead both rotations send `n` to `±e₃`,
the two shadows are congruent. No mirror symmetry of the polytope is used anywhere.
-/

@[expose] public section

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace MinimalityExtra

/-- The extent of a continuous function over a compact set is its maximum minus its minimum. -/
theorem diam_image_eq {X : Type*} [TopologicalSpace X] {H : Set X} {g : X → ℝ}
    (hH : IsCompact H) (hg : Continuous g) {a b : X} (ha : a ∈ H) (hb : b ∈ H)
    (hmax : ∀ x ∈ H, g x ≤ g a) (hmin : ∀ x ∈ H, g b ≤ g x) :
    Metric.diam (g '' H) = g a - g b := by
  apply le_antisymm
  · apply Metric.diam_le_of_forall_dist_le (by linarith [hmax b hb, hmin b hb, hmin a ha])
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [hmax x hx, hmax y hy, hmin x hx, hmin y hy]
  · have hbd : Bornology.IsBounded (g '' H) := (hH.image hg).isBounded
    have := Metric.dist_le_diam_of_mem hbd (Set.mem_image_of_mem g ha) (Set.mem_image_of_mem g hb)
    rw [Real.dist_eq] at this
    exact le_trans (le_abs_self _) this

theorem noEqualWidthPassage' (vs : Finset ℝ³) (hvs : vs.Nonempty)
    (Ri : Matrix (Fin 3) (Fin 3) ℝ) (o : EuclideanSpace ℝ (Fin 2))
    (Ro : Matrix (Fin 3) (Fin 3) ℝ) (m : EuclideanSpace ℝ (Fin 2)) (hm : ‖m‖ = 1)
    (hw : Metric.diam { inner ℝ m (proj_xy (Ri.toEuclideanLin p)) | p ∈ convexHull ℝ (vs : Set ℝ³) } =
      Metric.diam { inner ℝ m (proj_xy (Ro.toEuclideanLin p)) | p ∈ convexHull ℝ (vs : Set ℝ³) }) :
    ¬ ({ o + proj_xy (Ri.toEuclideanLin p) | p ∈ convexHull ℝ (vs : Set ℝ³) } ⊆
        interior { proj_xy (Ro.toEuclideanLin p) | p ∈ convexHull ℝ (vs : Set ℝ³) }) := by
  intro hsub
  obtain ⟨H, hHdef⟩ : ∃ H : Set ℝ³, H = convexHull ℝ (vs : Set ℝ³) := ⟨_, rfl⟩
  rw [← hHdef] at hsub hw
  have hH : IsCompact H := hHdef ▸ (Set.Finite.isCompact_convexHull (𝕜 := ℝ) vs.finite_toSet)
  have hHne : H.Nonempty := hHdef ▸ (convexHull_nonempty_iff).mpr (by simpa using hvs)
  have hci : Continuous fun p : ℝ³ => proj_xy (Ri.toEuclideanLin p) := by
    unfold proj_xy; fun_prop
  have hco : Continuous fun p : ℝ³ => proj_xy (Ro.toEuclideanLin p) := by
    unfold proj_xy; fun_prop
  set gi : ℝ³ → ℝ := fun p => inner ℝ m (proj_xy (Ri.toEuclideanLin p)) with hgi
  set go : ℝ³ → ℝ := fun p => inner ℝ m (proj_xy (Ro.toEuclideanLin p)) with hgo
  have hgic : Continuous gi := continuous_const.inner hci
  have hgoc : Continuous go := continuous_const.inner hco
  obtain ⟨pM, hpM, hpM'⟩ := hH.exists_isMaxOn hHne hgic.continuousOn
  obtain ⟨pm, hpm, hpm'⟩ := hH.exists_isMinOn hHne hgic.continuousOn
  obtain ⟨qM, hqM, hqM'⟩ := hH.exists_isMaxOn hHne hgoc.continuousOn
  obtain ⟨qm, hqm, hqm'⟩ := hH.exists_isMinOn hHne hgoc.continuousOn
  have e1 := diam_image_eq hH hgic hpM hpm (fun x hx => isMaxOn_iff.mp hpM' x hx)
    (fun x hx => isMinOn_iff.mp hpm' x hx)
  have e2 := diam_image_eq hH hgoc hqM hqm (fun x hx => isMaxOn_iff.mp hqM' x hx)
    (fun x hx => isMinOn_iff.mp hqm' x hx)
  have s1 : { inner ℝ m (proj_xy (Ri.toEuclideanLin p)) | p ∈ H } = gi '' H := rfl
  have s2 : { inner ℝ m (proj_xy (Ro.toEuclideanLin p)) | p ∈ H } = go '' H := rfl
  rw [s1, s2, e1, e2] at hw
  have hmm : inner ℝ m m = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hm]; norm_num
  -- the extreme inner point pushed in direction ±m stays in the outer shadow
  have push : ∀ p ∈ H, ∃ ε > 0, ∀ s : ℝ, |s| ≤ ε →
      ∃ q ∈ H, go q = inner ℝ m o + gi p + s := by
    intro p hp
    have hy : o + proj_xy (Ri.toEuclideanLin p) ∈ interior { proj_xy (Ro.toEuclideanLin p) | p ∈ H } :=
      hsub ⟨p, hp, rfl⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior _ hy
    refine ⟨ε / 2, by positivity, fun s hs => ?_⟩
    have hmem : o + proj_xy (Ri.toEuclideanLin p) + s • m ∈
        { proj_xy (Ro.toEuclideanLin p) | p ∈ H } := interior_subset (hball (by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hm, Real.norm_eq_abs]
      linarith))
    obtain ⟨q, hq, hqe⟩ := hmem
    refine ⟨q, hq, ?_⟩
    show inner ℝ m (proj_xy (Ro.toEuclideanLin q)) = _
    rw [hqe, inner_add_right, inner_add_right, inner_smul_right, hmm]
    simp [hgi]
  obtain ⟨ε1, hε1, h1⟩ := push pM hpM
  obtain ⟨ε2, hε2, h2⟩ := push pm hpm
  obtain ⟨q1, hq1, hq1e⟩ := h1 ε1 (by rw [abs_of_pos hε1])
  obtain ⟨q2, hq2, hq2e⟩ := h2 (-ε2) (by rw [abs_neg, abs_of_pos hε2])
  have a1 := isMaxOn_iff.mp hqM' q1 hq1
  have a2 := isMinOn_iff.mp hqm' q2 hq2
  linarith

theorem noEqualWidthPassage : NoEqualWidthPassage := by
  intro vs hvs Ri _ o Ro _ m hm hw
  exact noEqualWidthPassage' vs hvs Ri o Ro m hm hw

/-! ### Rotations preserve the inner product; the picture-symmetric corollary -/

theorem rotInner {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (p q : ℝ³) : inner ℝ (R.toEuclideanLin p) (R.toEuclideanLin q) = inner ℝ p q := by
  have h := real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two p q
  have h' := real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two
    (R.toEuclideanLin p) (R.toEuclideanLin q)
  rw [← map_add, rotNorm hR, rotNorm hR, rotNorm hR] at h'
  rw [h', h]

theorem inner_proj_xy (a b : ℝ³) : inner ℝ (proj_xy a) (proj_xy b) = inner ℝ a b - a 2 * b 2 := by
  simp [proj_xy, PiLp.inner_apply, Fin.sum_univ_succ, Fin.sum_univ_two, Fin.sum_univ_three]
  ring

/-- If `‖R n‖ = 1` and the third coordinate of `R n` is `±1`, then the third coordinate of `R w`
is `±⟪n, w⟫`, so its square is `⟪n, w⟫²`. -/
theorem thirdSq {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (n : ℝ³) (hn : ‖n‖ = 1) (h3 : (R.toEuclideanLin n 2) ^ 2 = 1) (w : ℝ³) :
    (R.toEuclideanLin w 2) ^ 2 = (inner ℝ n w) ^ 2 := by
  have hn1 : inner ℝ (R.toEuclideanLin n) (R.toEuclideanLin n) = (1 : ℝ) := by
    rw [rotInner hR, real_inner_self_eq_norm_sq, hn]; norm_num
  have hxy : inner ℝ (proj_xy (R.toEuclideanLin n)) (proj_xy (R.toEuclideanLin n)) = (0 : ℝ) := by
    rw [inner_proj_xy, hn1]; nlinarith
  have hz : proj_xy (R.toEuclideanLin n) = 0 := by
    rw [real_inner_self_eq_norm_sq] at hxy
    have : ‖proj_xy (R.toEuclideanLin n)‖ = 0 := by nlinarith [norm_nonneg (proj_xy (R.toEuclideanLin n))]
    exact norm_eq_zero.mp this
  have h0 : (R.toEuclideanLin n) 0 = 0 := by
    have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) hz; simpa [proj_xy] using this
  have h1 : (R.toEuclideanLin n) 1 = 0 := by
    have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) hz; simpa [proj_xy] using this
  have key := rotInner hR n w
  have key2 : inner ℝ (R.toEuclideanLin n) (R.toEuclideanLin w) =
      (R.toEuclideanLin n 2) * (R.toEuclideanLin w 2) := by
    rw [PiLp.inner_apply, Fin.sum_univ_three]
    simp only [RCLike.inner_apply, conj_trivial, h0, h1]; ring
  have : (R.toEuclideanLin w 2) ^ 2 = ((R.toEuclideanLin n 2) * (R.toEuclideanLin w 2)) ^ 2 := by
    rw [mul_pow, h3, one_mul]
  rw [this]
  have key' : inner ℝ n w = (R.toEuclideanLin n 2) * (R.toEuclideanLin w 2) := by
    rw [← key, key2]
  rw [key']

theorem noSameThirdPassage' (vs : Finset ℝ³) (hvs : vs.Nonempty)
    (Ri : Matrix (Fin 3) (Fin 3) ℝ) (hi : Ri ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (o : EuclideanSpace ℝ (Fin 2))
    (Ro : Matrix (Fin 3) (Fin 3) ℝ) (ho : Ro ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (hsq : ∀ p : ℝ³, (Ri.toEuclideanLin p 2) ^ 2 = (Ro.toEuclideanLin p 2) ^ 2) :
    ¬ ({ o + proj_xy (Ri.toEuclideanLin p) | p ∈ convexHull ℝ (vs : Set ℝ³) } ⊆
        interior { proj_xy (Ro.toEuclideanLin p) | p ∈ convexHull ℝ (vs : Set ℝ³) }) := by
  intro hsub
  obtain ⟨S, hSdef⟩ : ∃ S : Set ℝ³, S = convexHull ℝ (vs : Set ℝ³) := ⟨_, rfl⟩
  rw [← hSdef] at hsub
  have hS : IsCompact S := hSdef ▸ (Set.Finite.isCompact_convexHull (𝕜 := ℝ) vs.finite_toSet)
  have hSne : S.Nonempty := hSdef ▸ (convexHull_nonempty_iff).mpr (by simpa using hvs)
  have hcont : Continuous fun p : ℝ³ => proj_xy (Ro.toEuclideanLin p) := by
    unfold proj_xy; fun_prop
  obtain ⟨⟨p, q⟩, hpq, hmax⟩ := (hS.prod hS).exists_isMaxOn (hSne.prod hSne)
    ((hcont.comp continuous_fst).dist (hcont.comp continuous_snd)).continuousOn
  have hp : o + proj_xy (Ri.toEuclideanLin p) ∈
      { o + proj_xy (Ri.toEuclideanLin p) | p ∈ S } := ⟨p, hpq.1, rfl⟩
  have hq : o + proj_xy (Ri.toEuclideanLin q) ∈
      { o + proj_xy (Ri.toEuclideanLin p) | p ∈ S } := ⟨q, hpq.2, rfl⟩
  apply no_maximal_pair_interior (hsub hp) (hsub hq)
  intro x hx y hy
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  rw [dist_add_left]
  have key : ∀ (R : Matrix (Fin 3) (Fin 3) ℝ), R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ →
      ∀ a b : ℝ³, dist (proj_xy (R.toEuclideanLin a)) (proj_xy (R.toEuclideanLin b)) ^ 2 =
        ‖a - b‖ ^ 2 - (R.toEuclideanLin (a - b) 2) ^ 2 := by
    intro R hR a b
    rw [dist_eq_norm, ← proj_xy_sub, ← map_sub, normsq_proj_xy, rotNorm hR]
  have heq : ∀ a b : ℝ³, dist (proj_xy (Ri.toEuclideanLin a)) (proj_xy (Ri.toEuclideanLin b)) =
      dist (proj_xy (Ro.toEuclideanLin a)) (proj_xy (Ro.toEuclideanLin b)) := by
    intro a b
    have : dist (proj_xy (Ri.toEuclideanLin a)) (proj_xy (Ri.toEuclideanLin b)) ^ 2 =
        dist (proj_xy (Ro.toEuclideanLin a)) (proj_xy (Ro.toEuclideanLin b)) ^ 2 := by
      rw [key Ri hi, key Ro ho, hsq (a - b)]
    exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp this
  rw [heq]
  exact isMaxOn_iff.mp hmax (x', y') (Set.mk_mem_prod hx' hy')

theorem pictureSymmetricPoseNoPassage : PictureSymmetricPoseNoPassage := by
  intro vs hvs Ri hi o Ro ho n hn hcase
  rcases hcase with ⟨h0o, h0i, hs⟩ | ⟨h1o, h1i⟩
  · -- case 1: equal widths in the direction `m = proj_xy (Ro n)`
    obtain ⟨m, hmdef⟩ : ∃ m, m = proj_xy (Ro.toEuclideanLin n) := ⟨_, rfl⟩
    rw [← hmdef] at hs
    have hm : ‖m‖ = 1 := by
      have h2 : ‖m‖ ^ 2 = 1 := by
        rw [hmdef, normsq_proj_xy, rotNorm ho, hn, h0o]; norm_num
      nlinarith [norm_nonneg m]
    have hout : ∀ p : ℝ³, inner ℝ m (proj_xy (Ro.toEuclideanLin p)) = inner ℝ n p := by
      intro p
      rw [hmdef, inner_proj_xy, rotInner ho, h0o]; ring
    have hin : ∃ c : ℝ, (c = 1 ∨ c = -1) ∧
        ∀ p : ℝ³, inner ℝ m (proj_xy (Ri.toEuclideanLin p)) = c * inner ℝ n p := by
      rcases hs with hs | hs
      · refine ⟨1, Or.inl rfl, fun p => ?_⟩
        rw [← hs, inner_proj_xy, rotInner hi, h0i]; ring
      · refine ⟨-1, Or.inr rfl, fun p => ?_⟩
        rw [show m = -proj_xy (Ri.toEuclideanLin n) by rw [hs, neg_neg], inner_neg_left,
          inner_proj_xy, rotInner hi, h0i]; ring
    obtain ⟨c, hc, hcp⟩ := hin
    apply noEqualWidthPassage' vs hvs Ri o Ro m hm _
    have e1 : { inner ℝ m (proj_xy (Ri.toEuclideanLin p)) | p ∈ convexHull ℝ (vs : Set ℝ³) } =
        (fun t : ℝ => c * t) '' { inner ℝ m (proj_xy (Ro.toEuclideanLin p)) | p ∈ convexHull ℝ (vs : Set ℝ³) } := by
      ext t; simp only [Set.mem_ofPred_eq, Set.mem_image, hcp, hout]
      constructor
      · rintro ⟨p, hp, rfl⟩; exact ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩; exact ⟨p, hp, rfl⟩
    rw [e1]
    rcases hc with rfl | rfl
    · simp
    · have : (fun t : ℝ => (-1 : ℝ) * t) = fun t => -t := by ext; ring
      rw [this]
      exact (IsometryEquiv.neg ℝ).isometry.diam_image _
  · -- case 2: both views along `n`
    apply noSameThirdPassage' vs hvs Ri hi o Ro ho
    intro p
    rw [thirdSq hi n hn h1i, thirdSq ho n hn h1o]

end MinimalityExtra
