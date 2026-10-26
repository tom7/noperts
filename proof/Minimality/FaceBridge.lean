module

public import Nopert
public import Minimality.SixVertices
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.Convex.Intrinsic

@[expose] public section

/-!
# A two-dimensional extreme face of a polytope is a facet

`exists_facet_of_isExtreme`: for finitely many points `V` of `ℝ³` in convex position with a
solid hull `K`, a convex extreme subset `B` of `K` whose affine span is a plane is a facet: the
points `F` of `V` on it are cut out by an affine functional (`IsFacet V F`), there are at least
3 of them and not all of `V`, and they are exactly the extreme points of `B`.

The proof: a point `c` in the intrinsic interior of `B` can be pushed a little away from any
point `m` of the plane `P = affineSpan B` while staying in `B`; so `c` lies in an open segment of
`K` ending at `m`, and extremality puts every `m ∈ K ∩ P` into `B` (`K ∩ P = B`). Hence `B` is
compact, the convex hull of its extreme points (Krein–Milman), which are the points of `V` on it;
and `V` lies on one side of `P` (a segment of `K` crossing `P` would cross it inside `B`).
-/

namespace Minimality

open Set
open scoped RealInnerProductSpace

/-- A point of `V` outside the hull of the other points is an extreme point of the hull
(Krein–Milman: the hull is the hull of its extreme points, all of which are in `V`). -/
theorem mem_extremePoints_convexHull_of_notMem {V : Finset ℝ³} {v : ℝ³} (hv : v ∈ V)
    (hvh : v ∉ convexHull ℝ ((V.erase v : Finset ℝ³) : Set ℝ³)) :
    v ∈ (convexHull ℝ (V : Set ℝ³)).extremePoints ℝ := by
  classical
  by_contra hne
  have hK := closure_convexHull_extremePoints (V.finite_toSet.isCompact_convexHull ℝ)
    (convex_convexHull ℝ (V : Set ℝ³))
  have hsubV : (convexHull ℝ (V : Set ℝ³)).extremePoints ℝ ⊆ (V : Set ℝ³) :=
    fun y hy => extremePoints_convexHull_subset hy
  have hsub : (convexHull ℝ (V : Set ℝ³)).extremePoints ℝ ⊆ ((V.erase v : Finset ℝ³) : Set ℝ³) := by
    intro y hy
    have hyv : y ≠ v := fun h => hne (h ▸ hy)
    simp only [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff]
    exact ⟨hsubV hy, hyv⟩
  rw [((V.finite_toSet.subset hsubV).isClosed_convexHull ℝ).closure_eq] at hK
  have hvK : v ∈ convexHull ℝ (V : Set ℝ³) := subset_convexHull ℝ _ (Finset.mem_coe.2 hv)
  rw [← hK] at hvK
  exact hvh (convexHull_mono hsub hvK)

/-- From a point `c` of the intrinsic interior of `B` one can move a little away from any point
`m` of the affine span of `B` and stay in `B`. -/
theorem exists_pos_add_smul_sub_mem {B : Set ℝ³} {c m : ℝ³} (hc : c ∈ intrinsicInterior ℝ B)
    (hm : m ∈ affineSpan ℝ B) : ∃ ε : ℝ, 0 < ε ∧ c + ε • (c - m) ∈ B := by
  obtain ⟨y, hy, rfl⟩ := mem_intrinsicInterior.1 hc
  have hmem : ∀ t : ℝ, (y : ℝ³) + t • ((y : ℝ³) - m) ∈ affineSpan ℝ B := by
    intro t
    have h := AffineMap.lineMap_mem (-t) y.2 hm
    rwa [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
      show (-t) • (m - (y : ℝ³)) + (y : ℝ³) = (y : ℝ³) + t • ((y : ℝ³) - m) by module] at h
  let φ : ℝ → affineSpan ℝ B := fun t => ⟨(y : ℝ³) + t • ((y : ℝ³) - m), hmem t⟩
  have hφ : Continuous φ := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  have hφ0 : φ 0 = y := Subtype.ext (by simp [φ])
  have hnhds : φ ⁻¹' interior ((↑) ⁻¹' B : Set (affineSpan ℝ B)) ∈ nhds (0 : ℝ) :=
    hφ.continuousAt.preimage_mem_nhds (by rw [hφ0]; exact isOpen_interior.mem_nhds hy)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hnhds
  refine ⟨δ / 2, by positivity, ?_⟩
  have hin : δ / 2 ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have h2 : φ (δ / 2) ∈ ((↑) ⁻¹' B : Set (affineSpan ℝ B)) := interior_subset (hball hin)
  exact h2

/-- An extreme subset `B` of `K` contains every point of `K` on its affine span, provided its
intrinsic interior is nonempty. -/
theorem mem_of_isExtreme_of_mem_affineSpan {K B : Set ℝ³} (hext : IsExtreme ℝ K B) {c : ℝ³}
    (hc : c ∈ intrinsicInterior ℝ B) {m : ℝ³} (hmK : m ∈ K) (hmP : m ∈ affineSpan ℝ B) :
    m ∈ B := by
  obtain ⟨ε, hε, hcε⟩ := exists_pos_add_smul_sub_mem hc hmP
  have hcB : c ∈ B := intrinsicInterior_subset hc
  have hseg : c ∈ openSegment ℝ (c + ε • (c - m)) m := by
    refine ⟨1 / (1 + ε), ε / (1 + ε), by positivity, by positivity, by field_simp, ?_⟩
    have h1 : (1 + ε) ≠ 0 := by positivity
    calc (1 / (1 + ε)) • (c + ε • (c - m)) + (ε / (1 + ε)) • m
        = (1 / (1 + ε)) • ((1 + ε) • c) := by module
      _ = c := by rw [smul_smul, one_div, inv_mul_cancel₀ h1, one_smul]
  exact hext.right_mem_of_mem_openSegment (hext.subset hcε) hmK hcB hseg

/-- **A two-dimensional extreme face is a facet.** For points `V` in convex position with a solid
hull, a convex extreme subset of the hull with a 2-dimensional affine span is cut out by an
affine functional; its extreme points are the points `F` of `V` on it, at least 3 and not all. -/
theorem exists_facet_of_isExtreme (V : Finset ℝ³)
    (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty)
    (hvert : ∀ v ∈ V, v ∉ convexHull ℝ ((V.erase v : Finset ℝ³) : Set ℝ³))
    (face : Set ℝ³) (hext : IsExtreme ℝ (convexHull ℝ (V : Set ℝ³)) face)
    (hdim : (affineSpan ℝ face).finDim = 2) (hconv : Convex ℝ face) :
    ∃ F : Finset ℝ³, F ⊂ V ∧ 3 ≤ F.card ∧ IsFacet V F ∧
      face.extremePoints ℝ = (F : Set ℝ³) := by
  classical
  set K := convexHull ℝ (V : Set ℝ³) with hKdef
  set P := affineSpan ℝ face with hPdef
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, AffineSubspace.finDim_bot] at hdim
    exact absurd hdim (by decide)
  have hfr : Module.finrank ℝ P.direction = 2 := by
    have := AffineSubspace.finDim_eq_finrank hPne
    rw [hdim] at this
    exact_mod_cast this.symm
  have hfne : face.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    exact hPne ((affineSpan_eq_bot ℝ).2 h)
  obtain ⟨c, hc⟩ := hfne.intrinsicInterior hconv
  have hcB : c ∈ face := intrinsicInterior_subset hc
  have hcP : c ∈ P := subset_affineSpan ℝ face hcB
  have key : ∀ m ∈ K, m ∈ P → m ∈ face :=
    fun m hmK hmP => mem_of_isExtreme_of_mem_affineSpan hext hc hmK hmP
  set F := V.filter (· ∈ face) with hFdef
  -- the extreme points of the face are its points in `V`
  have hextF : face.extremePoints ℝ = (F : Set ℝ³) := by
    rw [hext.extremePoints_eq]
    ext y
    simp only [hFdef, Finset.coe_filter, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hy, hyK⟩
      exact ⟨Finset.mem_coe.1 (extremePoints_convexHull_subset hyK), hy⟩
    · rintro ⟨hyV, hy⟩
      exact ⟨hy, mem_extremePoints_convexHull_of_notMem hyV (hvert y hyV)⟩
  -- the face is `K ∩ P`, compact, the convex hull of `F`
  have hfaceKP : face = K ∩ (P : Set ℝ³) :=
    Set.Subset.antisymm (fun y hy => ⟨hext.1 hy, subset_affineSpan ℝ face hy⟩)
      (fun y hy => key y hy.1 hy.2)
  have hcomp : IsCompact face := by
    rw [hfaceKP]
    exact (V.finite_toSet.isCompact_convexHull ℝ).inter_right P.closed_of_finiteDimensional
  have hconvF : convexHull ℝ (F : Set ℝ³) = face := by
    have := closure_convexHull_extremePoints hcomp hconv
    rwa [hextF, (F.finite_toSet.isClosed_convexHull ℝ).closure_eq] at this
  -- at least three points (the face spans a plane)
  have hF3 : 3 ≤ F.card := by
    by_contra hlt
    push Not at hlt
    have hFne : F.card ≠ 0 := by
      intro h0
      rw [Finset.card_eq_zero] at h0
      rw [h0, Finset.coe_empty, convexHull_empty] at hconvF
      exact hfne.ne_empty hconvF.symm
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hFne
    have hle := finrank_vectorSpan_image_finset_le ℝ (id : ℝ³ → ℝ³) F hn
    rw [Finset.image_id] at hle
    have hspan : P = affineSpan ℝ (F : Set ℝ³) := by
      rw [hPdef, ← hconvF, affineSpan_convexHull]
    rw [hspan, direction_affineSpan] at hfr
    omega
  -- not all points (the hull is solid)
  have hFV : F ⊂ V := by
    refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.filter_subset _ _, fun hFV => ?_⟩
    have hVP : (V : Set ℝ³) ⊆ P := by
      intro v hv
      have hvF : v ∈ F := by rw [hFV]; exact hv
      exact subset_affineSpan ℝ face (Finset.mem_filter.1 hvF).2
    have hcop : Coplanar ℝ (V : Set ℝ³) := by
      unfold Coplanar
      calc Module.rank ℝ (vectorSpan ℝ (V : Set ℝ³)) ≤ Module.rank ℝ P.direction := by
            apply Submodule.rank_mono
            rw [← direction_affineSpan]
            exact AffineSubspace.direction_le (affineSpan_le.2 hVP)
        _ = 2 := by rw [← Module.finrank_eq_rank, hfr]; norm_num
    exact ((not_coplanar_iff_interior_convexHull_nonempty _).2 hsol) hcop
  -- a normal of the plane
  have h1 : Module.finrank ℝ P.directionᗮ = 1 := by
    have := P.direction.finrank_add_finrank_orthogonal
    rw [hfr, finrank_euclideanSpace_fin] at this
    omega
  obtain ⟨n, hnP, hn0⟩ : ∃ n ∈ P.directionᗮ, n ≠ 0 := by
    refine Submodule.exists_mem_ne_zero_of_ne_bot fun h => ?_
    rw [h, finrank_bot] at h1
    exact absurd h1 (by norm_num)
  have hPg : ∀ y ∈ P, ⟪n, y - c⟫ = 0 := by
    intro y hy
    have hd : y - c ∈ P.direction := by
      rw [← vsub_eq_sub]; exact (AffineSubspace.vsub_right_mem_direction_iff_mem hcP y).2 hy
    rw [real_inner_comm]
    exact (Submodule.mem_orthogonal _ _).1 hnP _ hd
  have hgP : ∀ y, ⟪n, y - c⟫ = 0 → y ∈ P := by
    intro y hy
    have hspan : (ℝ ∙ n) = P.directionᗮ :=
      Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).2 hnP)
        (by rw [finrank_span_singleton hn0, h1])
    have hy' : y - c ∈ (ℝ ∙ n)ᗮ := (Submodule.mem_orthogonal_singleton_iff_inner_right).2 hy
    rw [hspan, Submodule.orthogonal_orthogonal] at hy'
    rw [← vsub_eq_sub] at hy'
    exact (AffineSubspace.vsub_right_mem_direction_iff_mem hcP y).1 hy'
  -- points of `V` off the face are off the plane, all on one side
  have hnot : ∀ v ∈ V, v ∉ face → ⟪n, v - c⟫ ≠ 0 :=
    fun v hv hvf h0 => hvf (key v (subset_convexHull ℝ _ (Finset.mem_coe.2 hv)) (hgP v h0))
  have hside : ∀ u ∈ V, ∀ w ∈ V, 0 < ⟪n, u - c⟫ → ⟪n, w - c⟫ < 0 → False := by
    intro u hu w hw hu0 hw0
    have hab : ⟪n, u - c⟫ - ⟪n, w - c⟫ ≠ 0 := by linarith
    set s := ⟪n, u - c⟫ / (⟪n, u - c⟫ - ⟪n, w - c⟫) with hsdef
    have hs0 : 0 < s := div_pos hu0 (by linarith)
    have hs1 : s < 1 := (div_lt_one (by linarith)).2 (by linarith)
    have huK : u ∈ K := subset_convexHull ℝ _ (Finset.mem_coe.2 hu)
    have hwK : w ∈ K := subset_convexHull ℝ _ (Finset.mem_coe.2 hw)
    have hmK : u + s • (w - u) ∈ K :=
      (convex_convexHull ℝ _).add_smul_sub_mem huK hwK ⟨hs0.le, hs1.le⟩
    have hm0 : ⟪n, u + s • (w - u) - c⟫ = 0 := by
      have he : ⟪n, u + s • (w - u) - c⟫ = ⟪n, u - c⟫ + s * (⟪n, w - c⟫ - ⟪n, u - c⟫) := by
        rw [show u + s • (w - u) - c = (u - c) + s • ((w - c) - (u - c)) by module,
          inner_add_right, real_inner_smul_right, inner_sub_right n (w - c) (u - c)]
      rw [he, hsdef]
      field_simp
      ring
    have hmB : u + s • (w - u) ∈ face := key _ hmK (hgP _ hm0)
    have hseg : u + s • (w - u) ∈ openSegment ℝ u w :=
      ⟨1 - s, s, by linarith, hs0, by ring, by module⟩
    have huB := hext.left_mem_of_mem_openSegment huK hwK hmB hseg
    exact absurd (hPg u (subset_affineSpan ℝ face huB)) (ne_of_gt hu0)
  obtain ⟨σ, hσ0, hσ⟩ : ∃ σ : ℝ, σ ≠ 0 ∧ ∀ v ∈ V, σ * ⟪n, v - c⟫ ≤ 0 := by
    by_cases hpos : ∃ u ∈ V, 0 < ⟪n, u - c⟫
    · obtain ⟨u, hu, hu0⟩ := hpos
      refine ⟨-1, by norm_num, fun v hv => ?_⟩
      have : 0 ≤ ⟪n, v - c⟫ := not_lt.1 fun hlt => hside u hu v hv hu0 hlt
      linarith
    · push Not at hpos
      exact ⟨1, one_ne_zero, fun v hv => by simpa using hpos v hv⟩
  -- the facet functional
  let f : ℝ³ →ᵃ[ℝ] ℝ :=
    { toFun := fun y => σ * ⟪n, y - c⟫
      linear := σ • innerₛₗ ℝ n
      map_vadd' := fun p v => by
        simp only [vadd_eq_add, LinearMap.smul_apply, innerₛₗ_apply_apply, smul_eq_mul]
        rw [add_sub_assoc, inner_add_right]
        ring }
  refine ⟨F, hFV, hF3, ⟨f, fun x hx => ?_, fun x hx hxF => ?_⟩, hextF⟩
  · have hxB : x ∈ face := (Finset.mem_filter.1 hx).2
    change σ * ⟪n, x - c⟫ = 0
    rw [hPg x (subset_affineSpan ℝ face hxB), mul_zero]
  · have hxB : x ∉ face := fun h => hxF (Finset.mem_filter.2 ⟨hx, h⟩)
    change σ * ⟪n, x - c⟫ < 0
    exact lt_of_le_of_ne (hσ x hx) (mul_ne_zero hσ0 (hnot x hx hxB))

end Minimality

end
