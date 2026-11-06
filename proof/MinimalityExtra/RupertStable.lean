module

public import Mathlib
public import MinimalityExtra
public import MinimalityExtra.ShadowMap
public import Minimality

/-!
# Hausdorff stability of the Rupert property

`clearanceStable`: a passage of `W` with clearance `δ` carries over to `V` when the two hulls are
close, `ε₁ + ε₂ < δ`. `exists_clearance`: a Rupert passage has positive clearance. With
`isRupert_iff_of_card_le_six`, compactness gives `rupertNearFewPoints` and `closeVerticesRupert`.
-/

@[expose] public section

open MinimalityExtra




namespace RupertStab
open scoped RealInnerProductSpace

theorem rot_norm {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
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


theorem proj_norm (v : ℝ³) : ‖proj_xy v‖ ≤ ‖v‖ := by
  apply le_of_sq_le_sq _ (norm_nonneg _)
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_succ, proj_xy]
  nlinarith [sq_nonneg (v 2)]

theorem gL_dist {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hR : R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) (p q : ℝ³) :
    dist (gL R p) (gL R q) ≤ dist p q := by
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  calc ‖gL R (p - q)‖ ≤ ‖R.toEuclideanLin (p - q)‖ := proj_norm _
    _ = ‖p - q‖ := rot_norm hR _

/-- A convex set stays convex when thickened: if the points of `V` are within `ε` of the convex
set `K`, so are the points of its hull. -/
theorem hull_close {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {V K : Set E}
    (hK : Convex ℝ K) {ε : ℝ} (h : ∀ v ∈ V, ∃ q ∈ K, dist v q ≤ ε) :
    ∀ p ∈ convexHull ℝ V, ∃ q ∈ K, dist p q ≤ ε := by
  have hc : Convex ℝ {x : E | ∃ q ∈ K, dist x q ≤ ε} := by
    intro x hx y hy a b ha hb hab
    obtain ⟨qx, hqx, hx'⟩ := hx
    obtain ⟨qy, hqy, hy'⟩ := hy
    refine ⟨a • qx + b • qy, hK hqx hqy ha hb hab, ?_⟩
    have : a • x + b • y - (a • qx + b • qy) = a • (x - qx) + b • (y - qy) := by
      simp only [smul_sub]; abel
    rw [dist_eq_norm, this]
    calc ‖a • (x - qx) + b • (y - qy)‖ ≤ ‖a • (x - qx)‖ + ‖b • (y - qy)‖ := norm_add_le _ _
      _ = a * dist x qx + b * dist y qy := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb,
          dist_eq_norm, dist_eq_norm]
      _ ≤ a * ε + b * ε := by gcongr
      _ = ε := by rw [← add_mul, hab, one_mul]
  intro p hp
  exact convexHull_min (fun v hv => h v hv) hc hp

theorem inner_le_add {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n x y : E) :
    ⟪n, x⟫ ≤ ⟪n, y⟫ + ‖n‖ * dist x y := by
  have : ⟪n, x - y⟫ ≤ ‖n‖ * ‖x - y‖ := real_inner_le_norm _ _
  rw [inner_sub_right] at this
  rw [dist_eq_norm]; linarith

theorem clearanceStable {V W : Finset ℝ³} {δ ε₁ ε₂ : ℝ} (h : MinimalityExtra.HasClearance W δ)
    (h1 : ∀ v ∈ V, ∃ q ∈ convexHull ℝ (W : Set ℝ³), dist v q ≤ ε₁)
    (h2 : ∀ w ∈ W, ∃ q ∈ convexHull ℝ (V : Set ℝ³), dist w q ≤ ε₂)
    (hε : ε₁ + ε₂ < δ) : IsRupert V := by
  obtain ⟨Ri, hRi, off, Ro, hRo, hcl⟩ := h
  refine ⟨Ri, hRi, off, Ro, hRo, ?_⟩
  have hW1 := hull_close (convex_convexHull ℝ (W : Set ℝ³)) h1
  have hV2 := hull_close (convex_convexHull ℝ (V : Set ℝ³)) h2
  let B : Set (EuclideanSpace ℝ (Fin 2)) := gL Ro '' convexHull ℝ (V : Set ℝ³)
  have hBconv : Convex ℝ B := (convex_convexHull ℝ _).linear_image (gL Ro)
  have hBcomp : IsCompact B :=
    (V.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).image (LinearMap.continuous_of_finiteDimensional (gL Ro))
  dsimp only
  rintro y ⟨p, hp, rfl⟩
  obtain ⟨q, hq, hpq⟩ := hW1 p hp
  have hBne : B.Nonempty := ⟨gL Ro p, p, hp, rfl⟩
  set ρ := δ - ε₁ - ε₂ with hρ
  have hρpos : 0 < ρ := by linarith
  set c := off + proj_xy (Ri.toEuclideanLin p) with hc
  set c' := off + proj_xy (Ri.toEuclideanLin q) with hc'
  have hcc : dist c c' ≤ ε₁ := by
    have := gL_dist hRi p q
    rw [gL_apply, gL_apply] at this
    calc dist c c' = dist (proj_xy (Ri.toEuclideanLin p)) (proj_xy (Ri.toEuclideanLin q)) := by
          rw [hc, hc']; exact dist_add_left _ _ _
      _ ≤ dist p q := this
      _ ≤ ε₁ := hpq
  have hball : Metric.ball c ρ ⊆ B := by
    intro z hz
    by_contra hzB
    obtain ⟨z0, hz0B, hz0⟩ := exists_norm_eq_iInf_of_complete_convex hBne hBcomp.isComplete hBconv z
    have hproj := (norm_eq_iInf_iff_real_inner_le_zero hBconv hz0B).1 hz0
    set n := z - z0 with hn
    have hn0 : n ≠ 0 := fun h0 => hzB (by rw [hn, sub_eq_zero] at h0; rwa [h0])
    have hnpos : 0 < ‖n‖ := norm_pos_iff.2 hn0
    have hz0z : ⟪n, z0⟫ ≤ ⟪n, z⟫ := by
      have : ⟪n, z - z0⟫ = ‖n‖ ^ 2 := by rw [← hn]; exact real_inner_self_eq_norm_sq n
      rw [inner_sub_right] at this
      nlinarith [sq_nonneg ‖n‖]
    set a := c' + (δ / ‖n‖) • n with ha
    have hε2 : 0 ≤ ε₂ := le_trans dist_nonneg (hV2 q hq).choose_spec.2
    have hδ : 0 ≤ δ := by linarith [dist_nonneg (x := p) (y := q)]
    have hadist : dist a c' ≤ δ := by
      rw [dist_eq_norm, ha, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg
        (div_nonneg hδ hnpos.le), div_mul_cancel₀ _ hnpos.ne']
    obtain ⟨a0, ha0, hga0⟩ := hcl q hq (Metric.mem_closedBall.2 hadist)
    obtain ⟨b0, hb0, hab0⟩ := hV2 a0 ha0
    have hbB : gL Ro b0 ∈ B := ⟨b0, hb0, rfl⟩
    have hab : dist a (gL Ro b0) ≤ ε₂ := by
      have := gL_dist hRo a0 b0
      rw [gL_apply, gL_apply] at this
      rw [← hga0]; exact this.trans hab0
    have e1 := hproj _ hbB
    have e2 : ⟪n, gL Ro b0⟫ ≤ ⟪n, z0⟫ := by
      rw [inner_sub_right] at e1; linarith
    have e3 : ⟪n, a⟫ ≤ ⟪n, gL Ro b0⟫ + ‖n‖ * ε₂ := by
      have := inner_le_add n a (gL Ro b0)
      nlinarith
    have e4 : ⟪n, a⟫ = ⟪n, c'⟫ + δ * ‖n‖ := by
      rw [ha, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    have e5 : ⟪n, c⟫ ≤ ⟪n, c'⟫ + ‖n‖ * ε₁ := by
      have := inner_le_add n c c'
      nlinarith
    have e6 : ⟪n, z⟫ < ⟪n, c⟫ + ‖n‖ * ρ := by
      have := inner_le_add n z c
      have hd : dist z c < ρ := Metric.mem_ball.1 hz
      nlinarith
    nlinarith
  exact mem_interior.2 ⟨_, hball, Metric.isOpen_ball, Metric.mem_ball_self hρpos⟩

theorem exists_clearance {W : Finset ℝ³} (h : IsRupert W) : ∃ δ > 0, MinimalityExtra.HasClearance W δ := by
  obtain ⟨Ri, hRi, off, Ro, hRo, hsub⟩ := h
  let K : Set (EuclideanSpace ℝ (Fin 2)) :=
    (fun p => off + gL Ri p) '' convexHull ℝ (W : Set ℝ³)
  have hK : IsCompact K :=
    (W.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).image
      (continuous_const.add (LinearMap.continuous_of_finiteDimensional (gL Ri)))
  have hKsub : K ⊆ interior { proj_xy (Ro.toEuclideanLin p) | p ∈ convexHull ℝ (W : Set ℝ³) } := by
    rintro _ ⟨p, hp, rfl⟩
    exact hsub ⟨p, hp, rfl⟩
  obtain ⟨δ, hδ, hth⟩ := hK.exists_cthickening_subset_open isOpen_interior hKsub
  refine ⟨δ, hδ, Ri, hRi, off, Ro, hRo, fun p hp => ?_⟩
  intro x hx
  exact interior_subset (hth (Metric.closedBall_subset_cthickening (show off + proj_xy (Ri.toEuclideanLin p) ∈ K from ⟨p, hp, rfl⟩) δ hx))

end RupertStab

#print axioms RupertStab.clearanceStable
#print axioms RupertStab.exists_clearance




namespace RupertStab
open scoped RealInnerProductSpace
open MinimalityExtra

theorem cross_eq_zero_of_collinear {a b c : ℝ³} (h : Collinear ℝ ({a, b, c} : Set ℝ³)) :
    cross (b - a) (c - a) = 0 := by
  obtain ⟨p₀, v, hv⟩ := collinear_iff_exists_forall_eq_smul_vadd _ |>.1 h
  obtain ⟨ra, hra⟩ := hv a (by simp)
  obtain ⟨rb, hrb⟩ := hv b (by simp)
  obtain ⟨rc, hrc⟩ := hv c (by simp)
  have e1 : b - a = (rb - ra) • v := by
    rw [hrb, hra]; simp [sub_smul]
  have e2 : c - a = (rc - ra) • v := by
    rw [hrc, hra]; simp [sub_smul]
  rw [e1, e2]
  ext i; fin_cases i <;> simp [cross] <;> ring

theorem cross_eq_zero_left (b : ℝ³) : cross 0 b = 0 := by
  ext i; fin_cases i <;> simp [cross]
theorem cross_self (b : ℝ³) : cross b b = 0 := by
  ext i; fin_cases i <;> simp [cross] <;> ring

theorem continuous_cross : Continuous (fun p : ℝ³ × ℝ³ => cross p.1 p.2) := by
  simp only [cross]
  fun_prop

theorem exists_tuple (W : Finset ℝ³) (hW : W.card ≤ 6) (a b c : ℝ³) (ha : a ∈ W) (hb : b ∈ W)
    (hc : c ∈ W) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ t : Fin 6 → ℝ³, t 0 = a ∧ t 1 = b ∧ t 2 = c ∧ (∀ i, t i ∈ W) ∧ ∀ w ∈ W, ∃ i, t i = w := by
  set rest := ((W.erase a).erase b).erase c with hrest
  have hb' : b ∈ W.erase a := Finset.mem_erase.2 ⟨hab.symm, hb⟩
  have hc' : c ∈ (W.erase a).erase b := Finset.mem_erase.2 ⟨hbc.symm, Finset.mem_erase.2 ⟨hac.symm, hc⟩⟩
  have hcard : rest.card + 3 = W.card := by
    rw [hrest, Finset.card_erase_of_mem hc', Finset.card_erase_of_mem hb',
      Finset.card_erase_of_mem ha]
    have : 3 ≤ W.card := by
      have : ({a, b, c} : Finset ℝ³).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
          Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
      have h2 := Finset.card_le_card (show ({a, b, c} : Finset ℝ³) ⊆ W by
        intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption)
      omega
    omega
  set L : List ℝ³ := a :: b :: c :: rest.toList with hL
  have hLlen : L.length ≤ 6 := by
    simp [hL, Finset.length_toList]; omega
  have hmem : ∀ x ∈ L, x ∈ W := by
    intro x hx
    simp only [hL, List.mem_cons, Finset.mem_toList] at hx
    rcases hx with rfl | rfl | rfl | hx
    · exact ha
    · exact hb
    · exact hc
    · exact (Finset.mem_erase.1 (Finset.mem_erase.1 (Finset.mem_erase.1 hx).2).2).2
  refine ⟨fun i => L.getD i a, by simp [hL], by simp [hL], by simp [hL], ?_, ?_⟩
  · intro i
    show L.getD i a ∈ W
    by_cases hi : (i : ℕ) < L.length
    · rw [List.getD_eq_getElem _ _ hi]; exact hmem _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (not_lt.1 hi)]; exact ha
  · intro w hw
    have : w ∈ L := by
      by_cases hwa : w = a
      · simp [hL, hwa]
      by_cases hwb : w = b
      · simp [hL, hwb]
      by_cases hwc : w = c
      · simp [hL, hwc]
      simp only [hL, List.mem_cons, Finset.mem_toList]
      right; right; right
      exact Finset.mem_erase.2 ⟨hwc, Finset.mem_erase.2 ⟨hwb, Finset.mem_erase.2 ⟨hwa, hw⟩⟩⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 this
    exact ⟨⟨i, by omega⟩, by simp [List.getElem?_eq_getElem hi]⟩

end RupertStab





namespace RupertStab
open MinimalityExtra

theorem cross_eq_zero_right (b : ℝ³) : cross b 0 = 0 := by
  ext i; fin_cases i <;> simp [cross]

theorem rupertNearFewPoints : RupertNearFewPoints := by
  intro r hr
  by_contra hcon
  have key : ∀ n : ℕ, ∃ V W : Finset ℝ³, W.card ≤ 6 ∧ (∀ w ∈ W, ‖w‖ ≤ 1) ∧
      (∃ a ∈ W, ∃ b ∈ W, ∃ c ∈ W, r ≤ ‖cross (b - a) (c - a)‖) ∧
      (∀ v ∈ V, ∃ q ∈ convexHull ℝ (W : Set ℝ³), dist v q ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ w ∈ W, ∃ q ∈ convexHull ℝ (V : Set ℝ³), dist w q ≤ 1 / ((n : ℝ) + 1)) ∧
      ¬ IsRupert V := by
    intro n
    by_contra hn
    refine hcon ⟨1 / ((n : ℝ) + 1), by positivity, fun V W hc hb ht h1 h2 => ?_⟩
    by_contra hV
    exact hn ⟨V, W, hc, hb, ht, h1, h2, hV⟩
  choose V W hcard hunit htrip h1 h2 hnot using key
  choose a ha b hb c hc hr using htrip
  have hab : ∀ n, a n ≠ b n := fun n h => by
    have := hr n; rw [← h, sub_self, cross_eq_zero_left, norm_zero] at this; linarith
  have hac : ∀ n, a n ≠ c n := fun n h => by
    have := hr n; rw [← h, sub_self, cross_eq_zero_right, norm_zero] at this; linarith
  have hbc : ∀ n, b n ≠ c n := fun n h => by
    have := hr n; rw [← h, cross_self, norm_zero] at this; linarith
  choose t ht0 ht1 ht2 htW htcov using fun n =>
    exists_tuple (W n) (hcard n) (a n) (b n) (c n) (ha n) (hb n) (hc n) (hab n) (hac n) (hbc n)
  have hS : IsCompact (Set.pi Set.univ (fun _ : Fin 6 => Metric.closedBall (0 : ℝ³) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_closedBall _ _)
  have htS : ∀ n, t n ∈ Set.pi Set.univ (fun _ : Fin 6 => Metric.closedBall (0 : ℝ³) 1) :=
    fun n i _ => by simpa using hunit n _ (htW n i)
  obtain ⟨T, -, φ, hφ, hlim⟩ := hS.tendsto_subseq htS
  -- the limit is not collinear
  let f : (Fin 6 → ℝ³) → ℝ := fun s => ‖cross (s 1 - s 0) (s 2 - s 0)‖
  have hg : Continuous (fun s : Fin 6 → ℝ³ => (s 1 - s 0, s 2 - s 0)) := by fun_prop
  have hf : Continuous f := (continuous_cross.comp hg).norm
  have hfT : r ≤ f T :=
    ge_of_tendsto ((hf.tendsto T).comp hlim) (Filter.Eventually.of_forall fun n => by
      simp only [Function.comp, f, ht0, ht1, ht2]; exact hr _)
  let W' : Finset ℝ³ := Finset.univ.image T
  have hW'card : W'.card ≤ 6 := by
    calc W'.card ≤ (Finset.univ : Finset (Fin 6)).card := Finset.card_image_le
      _ = 6 := by simp
  have hnc : ¬ Collinear ℝ (W' : Set ℝ³) := by
    intro hcol
    have h3 : Collinear ℝ ({T 0, T 1, T 2} : Set ℝ³) := by
      refine hcol.subset ?_
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl <;> simp [W']
    have := cross_eq_zero_of_collinear h3
    simp only [f, this, norm_zero] at hfT
    linarith
  have hR : IsRupert W' := (isRupert_iff_of_card_le_six W' hW'card).2 (Or.inr hnc)
  obtain ⟨δ, hδ, hcl⟩ := exists_clearance hR
  have hev1 : ∀ᶠ n in Filter.atTop, dist (t (φ n)) T < δ / 4 :=
    (Metric.tendsto_nhds.1 hlim (δ / 4) (by positivity))
  have hev2 : ∀ᶠ n in Filter.atTop, 1 / ((φ n : ℝ) + 1) < δ / 4 :=
    (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop).eventually
      (gt_mem_nhds (by positivity))
  obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
  set m := φ n with hm
  have hdist : ∀ i, dist (t m i) (T i) < δ / 4 := fun i =>
    lt_of_le_of_lt (dist_le_pi_dist (t m) T i) hn1
  have hWc := hull_close (convex_convexHull ℝ (W' : Set ℝ³)) (V := (W m : Set ℝ³)) (ε := δ / 4)
    (fun w hw => by
      obtain ⟨i, rfl⟩ := htcov m w hw
      exact ⟨T i, subset_convexHull ℝ _ (by simp [W']), (hdist i).le⟩)
  have hVc := hull_close (convex_convexHull ℝ (V m : Set ℝ³)) (V := (W m : Set ℝ³))
    (ε := 1 / ((m : ℝ) + 1)) (h2 m)
  refine hnot m (clearanceStable (W := W') (ε₁ := 1 / ((m : ℝ) + 1) + δ / 4)
    (ε₂ := δ / 4 + 1 / ((m : ℝ) + 1)) hcl ?_ ?_ (by linarith))
  · intro v hv
    obtain ⟨q, hq, hvq⟩ := h1 m v hv
    obtain ⟨q', hq', hqq'⟩ := hWc q hq
    exact ⟨q', hq', (dist_triangle _ _ _).trans (add_le_add hvq hqq')⟩
  · intro w hw
    obtain ⟨i, rfl⟩ := Finset.mem_image.1 hw |>.imp fun i hi => hi.2
    obtain ⟨q, hq, hwq⟩ := hVc (t m i) (subset_convexHull ℝ _ (htW m i))
    refine ⟨q, hq, ?_⟩
    calc dist (T i) q ≤ dist (T i) (t m i) + dist (t m i) q := dist_triangle _ _ _
      _ ≤ δ / 4 + 1 / ((m : ℝ) + 1) := add_le_add (by rw [dist_comm]; exact (hdist i).le) hwq

end RupertStab

#print axioms RupertStab.rupertNearFewPoints





namespace RupertStab
open MinimalityExtra

theorem cross_norm_le (p q : ℝ³) : ‖cross p q‖ ≤ ‖p‖ * ‖q‖ := by
  apply le_of_sq_le_sq _ (by positivity)
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_succ, cross]
  nlinarith [sq_nonneg (p 0 * q 0 + p 1 * q 1 + p 2 * q 2)]

theorem cross_perturb (u u' v v' : ℝ³) (hu : ‖u‖ ≤ 2) (hv' : ‖v'‖ ≤ 2) :
    ‖cross u' v' - cross u v‖ ≤ ‖u' - u‖ * 2 + 2 * ‖v' - v‖ := by
  have : cross u' v' - cross u v = cross (u' - u) v' + cross u (v' - v) := by
    ext i; fin_cases i <;> simp [cross] <;> ring
  rw [this]
  calc _ ≤ ‖cross (u' - u) v'‖ + ‖cross u (v' - v)‖ := norm_add_le _ _
    _ ≤ ‖u' - u‖ * ‖v'‖ + ‖u‖ * ‖v' - v‖ :=
        add_le_add (cross_norm_le _ _) (cross_norm_le _ _)
    _ ≤ _ := by gcongr

theorem closeVerticesRupert : CloseVerticesRupert := by
  intro r hr
  obtain ⟨ε₀, hε₀, H⟩ := rupertNearFewPoints (r / 2) (by positivity)
  refine ⟨min ε₀ (r / 8), lt_min hε₀ (by positivity), ?_⟩
  intro V hcard hunit ⟨a, ha, b, hb, c, hc, habc⟩ ⟨x, hx, y, hy, hxy, hd⟩
  set ε := min ε₀ (r / 8) with hε
  have hε1 : ε ≤ ε₀ := min_le_left _ _
  have hε2 : ε ≤ r / 8 := min_le_right _ _
  set m : ℝ³ := midpoint ℝ x y with hm
  set W : Finset ℝ³ := insert m ((V.erase x).erase y) with hW
  have hy' : y ∈ V.erase x := Finset.mem_erase.2 ⟨hxy.symm, hy⟩
  have hmunit : ‖m‖ ≤ 1 := by
    have := (convex_closedBall (0 : ℝ³) 1).segment_subset (by simpa using hunit x hx)
      (by simpa using hunit y hy) (midpoint_mem_segment x y)
    simpa using this
  have hmV : m ∈ convexHull ℝ (V : Set ℝ³) :=
    (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ _ hx)
      (subset_convexHull ℝ _ hy) (midpoint_mem_segment x y)
  have hdx : dist x m ≤ ε / 2 := by
    rw [hm, dist_left_midpoint]; simp; linarith
  have hdy : dist y m ≤ ε / 2 := by
    rw [hm, dist_right_midpoint]; simp; linarith
  -- the contraction
  let π : ℝ³ → ℝ³ := fun p => if p = x ∨ p = y then m else p
  have hπ : ∀ p ∈ V, π p ∈ W ∧ dist p (π p) ≤ ε / 2 := by
    intro p hp
    by_cases h : p = x ∨ p = y
    · simp only [π, if_pos h, hW, Finset.mem_insert, true_or, true_and]
      rcases h with rfl | rfl
      · exact hdx
      · exact hdy
    · simp only [π, if_neg h, hW, Finset.mem_insert]
      push Not at h
      refine ⟨Or.inr (Finset.mem_erase.2 ⟨h.2, Finset.mem_erase.2 ⟨h.1, hp⟩⟩), ?_⟩
      simp; positivity
  have hWunit : ∀ w ∈ W, ‖w‖ ≤ 1 := by
    intro w hw
    rcases Finset.mem_insert.1 hw with rfl | hw
    · exact hmunit
    · exact hunit w (Finset.mem_erase.1 (Finset.mem_erase.1 hw).2).2
  have hWcard : W.card ≤ 6 := by
    have h1 : W.card ≤ ((V.erase x).erase y).card + 1 := Finset.card_insert_le m ((V.erase x).erase y)
    rw [Finset.card_erase_of_mem hy', Finset.card_erase_of_mem hx] at h1
    omega
  obtain ⟨ha1, ha2⟩ := hπ a ha
  obtain ⟨hb1, hb2⟩ := hπ b hb
  obtain ⟨hc1, hc2⟩ := hπ c hc
  refine H V W hWcard hWunit ⟨π a, ha1, π b, hb1, π c, hc1, ?_⟩ ?_ ?_
  · have hu : ‖b - a‖ ≤ 2 := by
      calc ‖b - a‖ ≤ ‖b‖ + ‖a‖ := norm_sub_le _ _
        _ ≤ 2 := by linarith [hunit a ha, hunit b hb]
    have hv' : ‖π c - π a‖ ≤ 2 := by
      calc ‖π c - π a‖ ≤ ‖π c‖ + ‖π a‖ := norm_sub_le _ _
        _ ≤ 2 := by linarith [hWunit _ hc1, hWunit _ ha1]
    have hdu : ‖(π b - π a) - (b - a)‖ ≤ ε := by
      have : (π b - π a) - (b - a) = (π b - b) - (π a - a) := by abel
      rw [this]
      calc _ ≤ ‖π b - b‖ + ‖π a - a‖ := norm_sub_le _ _
        _ ≤ ε / 2 + ε / 2 := by
          rw [← dist_eq_norm, ← dist_eq_norm, dist_comm, dist_comm (π a)]
          exact add_le_add hb2 ha2
        _ = ε := by ring
    have hdv : ‖(π c - π a) - (c - a)‖ ≤ ε := by
      have : (π c - π a) - (c - a) = (π c - c) - (π a - a) := by abel
      rw [this]
      calc _ ≤ ‖π c - c‖ + ‖π a - a‖ := norm_sub_le _ _
        _ ≤ ε / 2 + ε / 2 := by
          rw [← dist_eq_norm, ← dist_eq_norm, dist_comm, dist_comm (π a)]
          exact add_le_add hc2 ha2
        _ = ε := by ring
    have hp := cross_perturb (b - a) (π b - π a) (c - a) (π c - π a) hu hv'
    have := norm_sub_norm_le (cross (b - a) (c - a)) (cross (π b - π a) (π c - π a))
    rw [norm_sub_rev] at this
    nlinarith
  · intro v hv
    obtain ⟨h1, h2⟩ := hπ v hv
    exact ⟨π v, subset_convexHull ℝ _ h1, h2.trans (by linarith)⟩
  · intro w hw
    rcases Finset.mem_insert.1 hw with h | hw
    · exact ⟨w, h ▸ hmV, by simp; exact hε₀.le⟩
    · have hwV := (Finset.mem_erase.1 (Finset.mem_erase.1 hw).2).2
      exact ⟨w, subset_convexHull ℝ _ hwV, by simp; exact hε₀.le⟩

end RupertStab

#print axioms RupertStab.closeVerticesRupert

namespace MinimalityExtra

theorem clearanceStable' : ClearanceStable := fun _ _ _ _ _ h h1 h2 he => RupertStab.clearanceStable h h1 h2 he

theorem rupertHasClearance : RupertHasClearance := fun _ h => RupertStab.exists_clearance h

#print axioms clearanceStable'
#print axioms rupertHasClearance
#print axioms RupertStab.rupertNearFewPoints
#print axioms RupertStab.closeVerticesRupert

end MinimalityExtra
