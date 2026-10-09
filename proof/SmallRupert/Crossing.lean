module

public import SmallRupert.Pyramid
public import SmallRupert.Planes

@[expose] public section

/-!
# Theorem 5 in an arbitrary frame; pyramids (Cor. 5.3) and Cor. 5.4

`isRupert_of_crossing` is the coplanar-silhouette theorem in the form used by
all corollaries: `W ⊆ V` lies on a plane `⟪N, x⟫ = c` and contains an
affinely independent triple, `u₀` is not parallel to the plane, and the line
through every other point of `V` in direction `u₀` meets the plane in a
combination of `W` with all weights positive (a point of `relint (conv W)`).
It is reduced to the waist lemma `isRupert_of_waist` by a rigid motion taking
the plane to `z = 0`.
-/

namespace SmallRupert

open scoped RealInnerProductSpace

/-- **Theorem 5, frame-free form.** -/
theorem isRupert_of_crossing (V W : Finset ℝ³) (hWV : W ⊆ V) (N : ℝ³) (c : ℝ)
    (hWN : ∀ w ∈ W, ⟪N, w⟫ = c) {a b d : ℝ³} (ha : a ∈ W) (hb : b ∈ W) (hd : d ∈ W)
    (hind : AffineIndependent ℝ ![a, b, d]) (u₀ : ℝ³) (hu₀ : ⟪N, u₀⟫ ≠ 0)
    (hcross : ∀ v ∈ V, v ∉ W → ∃ t : ℝ, ∃ μ : ℝ³ → ℝ, (∀ w ∈ W, 0 < μ w) ∧
      ∑ w ∈ W, μ w = 1 ∧ v + t • u₀ = ∑ w ∈ W, μ w • w) :
    IsRupert V := by
  classical
  have hN0 : N ≠ 0 := by rintro rfl; simp at hu₀
  obtain ⟨R, hR, n, hn, hRN⟩ := exists_rotation_to_ez N hN0
  set f := so3Isometry hR with hf
  have hfx : ∀ x, f x = R.toEuclideanLin x := fun x => rfl
  have hfN : f (n⁻¹ • N) = ez := by
    rw [map_smul, hfx, hRN, smul_smul, inv_mul_cancel₀ hn, one_smul]
  have hz : ∀ x : ℝ³, (f x) 2 = n⁻¹ * ⟪N, x⟫ := by
    intro x
    rw [← inner_ez, ← hfN, f.inner_map_map, real_inner_smul_right, real_inner_comm]
  set k : ℝ := -(n⁻¹ * c) with hk
  let G : ℝ³ →ᵃ[ℝ] ℝ³ := (AffineEquiv.constVAdd ℝ ℝ³ (k • ez)).toAffineMap.comp
    f.toLinearEquiv.toLinearMap.toAffineMap
  have hG : ∀ x, G x = k • ez + f x := fun x => by simp [G, vadd_eq_add]
  have hGinj : Function.Injective G := by
    intro x y h; rw [hG, hG] at h; exact f.injective (add_left_cancel h)
  have hez2 : ez 2 = 1 := by simp [ez]
  have hGz : ∀ w ∈ W, (G w) 2 = 0 := by
    intro w hw
    rw [hG, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hez2, hz, hWN w hw, hk]
    try ring
  -- reduce to the rigidly moved solid
  apply isRupert_of_isRupert_image_rotation R hR
  apply isRupert_of_isRupert_image_add (k • ez)
  have hVimg : (V.image R.toEuclideanLin).image (fun x => k • ez + x) = V.image G := by
    rw [Finset.image_image]; congr 1
  rw [hVimg]
  set P := W.image G
  set Q := (V.filter (· ∉ W)).image G
  have hPQ : V.image G = P ∪ Q := by
    rw [← Finset.image_union]
    congr 1
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hx; by_cases hxW : x ∈ W
      · exact Or.inl hxW
      · exact Or.inr ⟨hx, hxW⟩
    · rintro (hx | ⟨hx, _⟩)
      · exact hWV hx
      · exact hx
  rw [hPQ]
  have hP : ∀ p ∈ P, p 2 = 0 := by
    intro p hp
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hp
    exact hGz w hw
  -- the waist polygon is solid
  have hint : (interior (convexHull ℝ ((P.image proj_xy : Finset ℝ²) : Set ℝ²))).Nonempty := by
    have h1 : AffineIndependent ℝ (G ∘ ![a, b, d]) := hind.map' G hGinj
    have hcomp : (liftL.toAffineMap ∘ (proj_xy ∘ G ∘ ![a, b, d])) = G ∘ ![a, b, d] := by
      funext i
      fin_cases i <;>
        simp [liftL_proj_xy (hGz _ ha), liftL_proj_xy (hGz _ hb), liftL_proj_xy (hGz _ hd)]
    have h2 : AffineIndependent ℝ (proj_xy ∘ G ∘ ![a, b, d]) :=
      AffineIndependent.of_comp liftL.toAffineMap (by rw [hcomp]; exact h1)
    have hspan : affineSpan ℝ (Set.range (proj_xy ∘ G ∘ ![a, b, d])) = ⊤ :=
      (h2.affineSpan_eq_top_iff_card_eq_finrank_add_one).mpr (by simp)
    have := (interior_convexHull_nonempty_iff_affineSpan_eq_top).mpr hspan
    refine this.mono (interior_mono (convexHull_mono ?_))
    rintro _ ⟨i, rfl⟩
    simp only [Finset.coe_image, Function.comp_apply]
    refine ⟨G (![a, b, d] i), Finset.mem_coe.mpr (Finset.mem_image_of_mem G ?_), rfl⟩
    fin_cases i <;> simp [ha, hb, hd]
  have hu₀' : (f u₀) 2 ≠ 0 := by rw [hz]; exact mul_ne_zero (inv_ne_zero hn) hu₀
  refine isRupert_of_waist P Q hP hint (f u₀) hu₀' ?_
  intro q hq
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hvV, hvW⟩ := Finset.mem_filter.mp hv
  obtain ⟨t, μ, hμ, hμ1, hvt⟩ := hcross v hvV hvW
  have key : G v + t • f u₀ = ∑ w ∈ W, μ w • G w := by
    simp only [hG, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hμ1, one_smul]
    rw [add_assoc, ← map_smul, ← map_add, hvt, map_sum]
    simp only [map_smul]
  have hz0 : (G v) 2 + t * (f u₀) 2 = 0 := by
    have := congrArg (fun x : ℝ³ => x 2) key
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at this
    rw [this]
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
    exact Finset.sum_eq_zero fun w hw => by rw [hGz w hw, mul_zero]
  have ht : t = -((G v) 2 / (f u₀) 2) := by field_simp; linarith
  have hpt : G v - ((G v) 2 / (f u₀) 2) • f u₀ = ∑ w ∈ W, μ w • G w := by
    rw [← key, ht, neg_smul, sub_eq_add_neg]
  rw [hpt, show proj_xy (∑ w ∈ W, μ w • G w) = ∑ w ∈ W, μ w • (proj_xy ∘ G) w by
    rw [← projL_apply, map_sum]; simp [map_smul, projL_apply]]
  have := sum_smul_mem_interior_convexHull_image W (proj_xy ∘ G) μ hμ hμ1
    (by rwa [← Finset.image_image])
  rwa [← Finset.image_image] at this

/-- **Corollary 5.3 (pyramids).** If all points of `V` but one are coplanar
(and `conv V` is solid), `V` is Rupert. -/
theorem isRupert_of_pyramid (V : Finset ℝ³) (E : ℝ³)
    (hint : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty)
    (hplane : Coplanar ℝ ((V.erase E : Finset ℝ³) : Set ℝ³)) :
    IsRupert V := by
  classical
  set W := V.erase E with hW
  have hVnc := not_coplanar_of_interior_nonempty hint
  have hE : E ∈ V := by
    by_contra hE; rw [hW, Finset.erase_eq_of_notMem hE] at hplane; exact hVnc hplane
  have hVW : (V : Set ℝ³) = insert E (W : Set ℝ³) := by
    rw [hW, Finset.coe_erase, Set.insert_sdiff_singleton, Set.insert_eq_of_mem (by simpa using hE)]
  obtain ⟨N, hN, c, hNc⟩ := exists_plane_of_coplanar hplane
  have hEc : ⟪N, E⟫ ≠ c := by
    intro h
    apply hVnc
    refine coplanar_of_plane hN (c := c) ?_
    rw [hVW]
    rintro x (rfl | hx)
    · exact h
    · exact hNc x hx
  have hWnc : ¬ Collinear ℝ (W : Set ℝ³) := fun hcol => hVnc (by
    rw [hVW]; exact hcol.coplanar_insert E)
  obtain ⟨a, ha, b, hb, d, hd, hind⟩ := exists_affineIndependent_triple hWnc
  have hWne : W.Nonempty := ⟨a, ha⟩
  have hcard : (0 : ℝ) < W.card := by exact_mod_cast hWne.card_pos
  set C := ∑ w ∈ W, (1 / (W.card : ℝ)) • w
  have hNC : ⟪N, C⟫ = c := by
    simp only [C, inner_sum, real_inner_smul_right]
    rw [Finset.sum_congr rfl fun w hw => by rw [hNc w hw], Finset.sum_const, nsmul_eq_mul]
    field_simp
  refine isRupert_of_crossing V W (Finset.erase_subset E V) N c hNc ha hb hd hind (C - E)
    (by rw [inner_sub_right, hNC]; exact sub_ne_zero.mpr (Ne.symm hEc)) ?_
  intro v hv hvW
  have hvE : v = E := by
    by_contra h; exact hvW (Finset.mem_erase.mpr ⟨h, hv⟩)
  refine ⟨1, fun _ => 1 / (W.card : ℝ), fun _ _ => by positivity, ?_, ?_⟩
  · rw [Finset.sum_const, nsmul_eq_mul]; field_simp
  · rw [hvE, one_smul, add_sub_cancel]

/-- The view `u = c - E` from the apex through a relative-interior point `c`
of the base is admissible. -/
theorem sub_mem_admissibleViews_of_pyramid (V : Finset ℝ³) (E : ℝ³)
    (hE : E ∉ affineSpan ℝ ((V.erase E : Finset ℝ³) : Set ℝ³)) (c : ℝ³)
    (hc : c ∈ intrinsicInterior ℝ (convexHull ℝ ((V.erase E : Finset ℝ³) : Set ℝ³))) :
    c - E ∈ admissibleViews V (V.erase E) := by
  sorry

/-- **Corollary 5.4 (bipyramid lemma), crossing form.** If every point of
`V \ W` is `D` or `E`, `D` is off the plane of `W`, and the segment `DE` meets
`relint (conv W)`, then `u = E - D` is admissible and `V` is Rupert. -/
theorem isRupert_of_segment_crossing (V W : Finset ℝ³) (D E : ℝ³) (hWV : W ⊆ V)
    (hVW : ∀ v ∈ V, v ∉ W → v = D ∨ v = E) (hW : ¬ Collinear ℝ (W : Set ℝ³))
    (hD : D ∉ affineSpan ℝ (W : Set ℝ³))
    (hX : (segment ℝ D E ∩ intrinsicInterior ℝ (convexHull ℝ (W : Set ℝ³))).Nonempty) :
    IsRupert V := by
  sorry


end SmallRupert

end
