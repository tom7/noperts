module

public import Nopert
public import Minimality
public import Minimality.Planes
public import Pipeline.Similarity

/-!
# Geometric lemmas for the Septopert family census

Three ways to see that a point set is not a nopert, each checkable on integer data:

* `Minimality.coplanar_of_plane`: the points lie on a plane;
* `not_isNopert_of_mem_convexHull_erase`: one point is a convex combination of
  the others, so at most 6 points span the same hull, and every solid with at
  most 6 points is Rupert (`isRupert_of_card_le_six`);
* `isRupert_of_forall_mem_interior` with `mem_interior_convexHull_triangle`: an
  explicit Rupert passage in which every inner shadow point lies strictly
  inside a triangle of outer shadow points.

Also `isNopert_of_isNopert_image`: being a nopert is invariant under
`v ↦ c + s • v` with `s ≠ 0` (translations, scalings, the point reflection), and
`quatRot_mem_SO3`: a nonzero quaternion `q` gives the rotation
`M(q) / |q|²` (`quatMat`), rational when `q` is.
-/

@[expose] public section

namespace SeptopertFamily

open scoped RealInnerProductSpace Matrix

/-! ### Similarities -/

theorem coplanar_image_affine {X : Set ℝ³} (g : ℝ³ →ᵃ[ℝ] ℝ³) (h : Coplanar ℝ X) :
    Coplanar ℝ (g '' X) := by
  rw [coplanar_iff_finrank_le_two] at h ⊢
  rw [← AffineMap.map_vectorSpan]
  exact (Submodule.finrank_map_le _ _).trans h

/-- Being a nopert is invariant under `v ↦ c + s • v`, `s ≠ 0`. -/
theorem isNopert_of_isNopert_image (V : Finset ℝ³) (c : ℝ³) (s : ℝ) (hs : s ≠ 0)
    (h : IsNopert (V.image fun v => c + s • v)) : IsNopert V := by
  refine ⟨fun hcop => h.1 ?_, fun hR => h.2 ?_⟩
  · let g : ℝ³ →ᵃ[ℝ] ℝ³ :=
      (s • (LinearMap.id : ℝ³ →ₗ[ℝ] ℝ³)).toAffineMap + AffineMap.const ℝ ℝ³ c
    have hg : ∀ v, g v = c + s • v := fun v => by
      simp [g, add_comm]
    have := coplanar_image_affine g hcop
    rw [Finset.coe_image]
    convert this using 1
    ext v
    simp [hg]
  · have h1 := Noperts.Pipeline.isRupert_image_smul s hs V hR
    have h2 := Noperts.Pipeline.isRupert_image_add c _ h1
    rwa [Finset.image_image] at h2

/-! ### A point inside the hull of the others -/

/-- If point `i` of `f` is a convex combination of the other points, the
points are not a nopert. -/
theorem not_isNopert_of_mem_convexHull_erase (f : Fin 7 → ℝ³) (i : Fin 7)
    (hi : f i ∈ convexHull ℝ (((Finset.univ.erase i).image f : Finset ℝ³) : Set ℝ³)) :
    ¬ IsNopert (Finset.univ.image f) := by
  intro hN
  set V' := (Finset.univ.erase i).image f
  have hsub : ((Finset.univ.image f : Finset ℝ³) : Set ℝ³) ⊆ convexHull ℝ (V' : Set ℝ³) := by
    intro v hv
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hv
    obtain ⟨k, rfl⟩ := hv
    by_cases hk : k = i
    · subst hk; exact hi
    · apply subset_convexHull
      rw [Finset.mem_coe]
      exact Finset.mem_image_of_mem f (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ _⟩)
  have hhull : convexHull ℝ ((Finset.univ.image f : Finset ℝ³) : Set ℝ³) =
      convexHull ℝ (V' : Set ℝ³) := by
    apply le_antisymm
    · exact convexHull_min hsub (convex_convexHull ℝ _)
    · apply convexHull_mono
      intro v hv
      simp only [V', Finset.coe_image, Set.mem_image, Finset.mem_coe] at hv
      obtain ⟨k, -, rfl⟩ := hv
      simp
  have hint := (not_coplanar_iff_interior_convexHull_nonempty _).mp hN.1
  rw [hhull] at hint
  have hcard : V'.card ≤ 6 := by
    refine (Finset.card_image_le).trans ?_
    rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp
  have hR := isRupert_of_card_le_six V' hcard
    ((not_coplanar_iff_interior_convexHull_nonempty _).mpr hint)
  exact hN.2 ((Minimality.isRupert_congr_hull hhull).mpr hR)

/-! ### Rupert passages -/

/-- A passage: if every inner shadow point of a vertex lies in the interior of
the convex hull of the outer shadow points of the vertices, the set is Rupert. -/
theorem isRupert_of_forall_mem_interior (V : Finset ℝ³) {Ri Ro : Matrix (Fin 3) (Fin 3) ℝ}
    (hRi : Ri ∈ SO3) (hRo : Ro ∈ SO3) (o : ℝ²)
    (h : ∀ v ∈ V, o + proj_xy (Ri.toEuclideanLin v) ∈
      interior (convexHull ℝ ((fun p => proj_xy (Ro.toEuclideanLin p)) '' (V : Set ℝ³)))) :
    IsRupert V := by
  refine ⟨Ri, hRi, o, Ro, hRo, ?_⟩
  dsimp only
  let fi : ℝ³ →ᵃ[ℝ] ℝ² :=
    (Minimality.projL ∘ₗ (Ri.toEuclideanLin : ℝ³ →ₗ[ℝ] ℝ³)).toAffineMap + AffineMap.const ℝ ℝ³ o
  let fo : ℝ³ →ₗ[ℝ] ℝ² := Minimality.projL ∘ₗ (Ro.toEuclideanLin : ℝ³ →ₗ[ℝ] ℝ³)
  have hfi : ∀ p, fi p = o + proj_xy (Ri.toEuclideanLin p) := fun p => by
    simp [fi, Minimality.projL_apply, add_comm]
  have hfo : ∀ p, fo p = proj_xy (Ro.toEuclideanLin p) := fun p => by
    simp [fo, Minimality.projL_apply]
  have hin : { x | ∃ p ∈ convexHull ℝ (V : Set ℝ³), o + proj_xy (Ri.toEuclideanLin p) = x } =
      convexHull ℝ (fi '' (V : Set ℝ³)) := by
    rw [← AffineMap.image_convexHull]
    ext x; simp [hfi]
  have hout : { x | ∃ p ∈ convexHull ℝ (V : Set ℝ³), proj_xy (Ro.toEuclideanLin p) = x } =
      convexHull ℝ ((fun p => proj_xy (Ro.toEuclideanLin p)) '' (V : Set ℝ³)) := by
    have := LinearMap.image_convexHull fo (V : Set ℝ³)
    have e : (fo : ℝ³ → ℝ²) = fun p => proj_xy (Ro.toEuclideanLin p) := funext hfo
    rw [e] at this
    rw [← this]
    ext x; simp
  rw [hin, hout]
  apply convexHull_min _ (convex_convexHull ℝ _).interior
  rintro _ ⟨v, hv, rfl⟩
  rw [hfi]
  exact h v hv

/-- The cross product `u × v = u₀ v₁ − u₁ v₀` of the plane. -/
def cross2 (u v : ℝ²) : ℝ := u 0 * v 1 - u 1 * v 0

/-- A point with positive barycentric areas lies in the interior of the triangle. -/
theorem mem_interior_convexHull_triangle (A B C p : ℝ²)
    (h1 : 0 < cross2 (B - p) (C - p)) (h2 : 0 < cross2 (C - p) (A - p))
    (h3 : 0 < cross2 (A - p) (B - p)) :
    p ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²)) := by
  let U : Set ℝ² := { y | 0 < cross2 (B - y) (C - y) } ∩ { y | 0 < cross2 (C - y) (A - y) } ∩
    { y | 0 < cross2 (A - y) (B - y) }
  have hc : ∀ (P Q : ℝ²), Continuous fun y : ℝ² => cross2 (P - y) (Q - y) := by
    intro P Q
    have h0 : Continuous fun y : ℝ² => y 0 := (EuclideanSpace.proj (0 : Fin 2)).continuous
    have h1 : Continuous fun y : ℝ² => y 1 := (EuclideanSpace.proj (1 : Fin 2)).continuous
    simp only [cross2, PiLp.sub_apply]
    fun_prop
  have hU : IsOpen U :=
    ((isOpen_lt continuous_const (hc B C)).inter (isOpen_lt continuous_const (hc C A))).inter
      (isOpen_lt continuous_const (hc A B))
  have hUsub : U ⊆ convexHull ℝ ({A, B, C} : Set ℝ²) := by
    rintro y ⟨⟨ha, hb⟩, hcc⟩
    simp only [Set.mem_ofPred_eq] at ha hb hcc
    set a := cross2 (B - y) (C - y) with ha_def
    set b := cross2 (C - y) (A - y) with hb_def
    set c := cross2 (A - y) (B - y) with hc_def
    have hs : 0 < a + b + c := by linarith
    have e0 : a * A 0 + b * B 0 + c * C 0 = (a + b + c) * y 0 := by
      simp only [ha_def, hb_def, hc_def, cross2, PiLp.sub_apply]; ring
    have e1 : a * A 1 + b * B 1 + c * C 1 = (a + b + c) * y 1 := by
      simp only [ha_def, hb_def, hc_def, cross2, PiLp.sub_apply]; ring
    have hy : y = (a / (a + b + c)) • A + (b / (a + b + c)) • B + (c / (a + b + c)) • C := by
      ext j
      fin_cases j
      · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.isValue]
        rw [show a / (a + b + c) * A 0 + b / (a + b + c) * B 0 + c / (a + b + c) * C 0 =
          (a * A 0 + b * B 0 + c * C 0) / (a + b + c) by ring, e0, mul_div_cancel_left₀ _ hs.ne']
      · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Fin.mk_one, Fin.isValue]
        rw [show a / (a + b + c) * A 1 + b / (a + b + c) * B 1 + c / (a + b + c) * C 1 =
          (a * A 1 + b * B 1 + c * C 1) / (a + b + c) by ring, e1, mul_div_cancel_left₀ _ hs.ne']
    rw [hy]
    have hconv := convex_convexHull ℝ ({A, B, C} : Set ℝ²)
    have hA : A ∈ convexHull ℝ ({A, B, C} : Set ℝ²) := subset_convexHull ℝ _ (by simp)
    have hB : B ∈ convexHull ℝ ({A, B, C} : Set ℝ²) := subset_convexHull ℝ _ (by simp)
    have hC : C ∈ convexHull ℝ ({A, B, C} : Set ℝ²) := subset_convexHull ℝ _ (by simp)
    have := hconv.sum_mem (t := Finset.univ) (w := ![a / (a + b + c), b / (a + b + c),
      c / (a + b + c)]) (z := ![A, B, C]) (by intro i _; fin_cases i <;> simp <;> apply div_nonneg <;> linarith)
      (by simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
          rw [← add_div, ← add_div, div_self hs.ne'])
      (by intro i _; fin_cases i <;> simp [hA, hB, hC])
    simpa [Fin.sum_univ_three] using this
  exact interior_maximal hUsub hU ⟨⟨h1, h2⟩, h3⟩

/-! ### Quaternion rotations -/

/-- The quaternion matrix: `M(q) = |q|² R(q)` for the rotation `R(q)` of the
quaternion `q = (w, x, y, z)`. Defined over any commutative ring, so that the
integer certificate check uses the same formula. -/
def quatMat {R : Type*} [CommRing R] (q : Fin 4 → R) : Matrix (Fin 3) (Fin 3) R :=
  !![q 0 * q 0 + q 1 * q 1 - q 2 * q 2 - q 3 * q 3, 2 * (q 1 * q 2 - q 0 * q 3),
      2 * (q 1 * q 3 + q 0 * q 2);
     2 * (q 1 * q 2 + q 0 * q 3), q 0 * q 0 - q 1 * q 1 + q 2 * q 2 - q 3 * q 3,
      2 * (q 2 * q 3 - q 0 * q 1);
     2 * (q 1 * q 3 - q 0 * q 2), 2 * (q 2 * q 3 + q 0 * q 1),
      q 0 * q 0 - q 1 * q 1 - q 2 * q 2 + q 3 * q 3]

/-- `quatMat` for the compiler: matrix literals `!![…]` evaluate slowly (`Fin.cases`). -/
def quatMatImpl {R : Type*} [CommRing R] (q : Fin 4 → R) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.of fun r c =>
    if r.val = 0 then
      (if c.val = 0 then q 0 * q 0 + q 1 * q 1 - q 2 * q 2 - q 3 * q 3
       else if c.val = 1 then 2 * (q 1 * q 2 - q 0 * q 3) else 2 * (q 1 * q 3 + q 0 * q 2))
    else if r.val = 1 then
      (if c.val = 0 then 2 * (q 1 * q 2 + q 0 * q 3)
       else if c.val = 1 then q 0 * q 0 - q 1 * q 1 + q 2 * q 2 - q 3 * q 3
       else 2 * (q 2 * q 3 - q 0 * q 1))
    else
      (if c.val = 0 then 2 * (q 1 * q 3 - q 0 * q 2)
       else if c.val = 1 then 2 * (q 2 * q 3 + q 0 * q 1)
       else q 0 * q 0 - q 1 * q 1 - q 2 * q 2 + q 3 * q 3)

@[csimp] theorem quatMat_eq_quatMatImpl : @quatMat = @quatMatImpl := by
  funext R _ q
  ext r c
  fin_cases r <;> fin_cases c <;> rfl

/-- `|q|²`. -/
def quatNorm {R : Type*} [CommRing R] (q : Fin 4 → R) : R :=
  q 0 * q 0 + q 1 * q 1 + q 2 * q 2 + q 3 * q 3

/-- The rotation of a nonzero real quaternion. -/
noncomputable def quatRot (q : Fin 4 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (quatNorm q)⁻¹ • quatMat q

theorem quatMat_mul_transpose {R : Type*} [CommRing R] (q : Fin 4 → R) :
    quatMat q * (quatMat q)ᵀ = (quatNorm q ^ 2) • (1 : Matrix (Fin 3) (Fin 3) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quatMat, quatNorm, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three] <;> ring

theorem det_quatMat {R : Type*} [CommRing R] (q : Fin 4 → R) :
    (quatMat q).det = quatNorm q ^ 3 := by
  simp [quatMat, quatNorm, Matrix.det_fin_three]
  ring

theorem quatRot_mem_SO3 (q : Fin 4 → ℝ) (hq : quatNorm q ≠ 0) : quatRot q ∈ SO3 := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  constructor
  · unfold quatRot
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, quatMat_mul_transpose,
      smul_smul, smul_smul]
    convert one_smul ℝ (1 : Matrix (Fin 3) (Fin 3) ℝ) using 2
    field_simp
  · unfold quatRot
    rw [Matrix.det_smul, det_quatMat]
    simp only [Fintype.card_fin]
    field_simp

end SeptopertFamily

end
