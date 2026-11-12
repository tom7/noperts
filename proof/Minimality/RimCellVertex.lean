module

public import Mathlib
public import Minimality.RimCellView
public import Minimality.Perturb
public import Minimality.Sector

@[expose] public section

/-!
# Rim cells of any size: the vertex leaf

* `isRupert_of_rimCell_zmod`: for a rim `y : ZMod k → ℝ³` (`k ≥ 3`) of a point set `Y` in shape
  coordinates, a view `c` satisfying the strict orientation inequalities and having cyclically
  unimodal depths realises `E Y` as Rupert (the `ZMod k` version of `exists_view_of_rimCell`).
* `isOpen_setOf_isCyclicUnimodal`: cyclic unimodality is an open condition on depth vectors.
* `isRupert_of_rimCell_vertex`: **the vertex leaf.**  If the orientation inequalities hold on an
  open set `A` of views and the depths at a point `g` of `closure A` are cyclically unimodal, then
  `E Y` is Rupert.
-/

set_option autoImplicit false

namespace Minimality.RimCell

open Finset Matrix Filter Topology
open scoped RealInnerProductSpace

/-- The `ZMod k` cell geometry: a view satisfying the strict orientation inequalities of the rim
is realised by a rotation with a ccw rim and every other point strictly inside. -/
theorem exists_view_of_rimCell_zmod {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det)
    (y : ZMod k → Fin 3 → ℝ) (hy : Function.Injective y) (Y : Finset (Fin 3 → ℝ))
    (hyY : ∀ i, y i ∈ Y) (c : Fin 3 → ℝ) (hc : c ≠ 0)
    (hcell : ∀ i : ZMod k, ∀ v ∈ Y, v ≠ y i → v ≠ y (i + 1) →
      0 < (Matrix.of ![y (i + 1) - y i, v - y i, c]).det) :
    ∃ R : Matrix (Fin 3) (Fin 3) ℝ, R ∈ SO3 ∧
      IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (emb E (y i)))) ∧
      (∀ v ∈ Y.image (emb E), (∀ i, v ≠ emb E (y i)) →
        proj_xy (R.toEuclideanLin v) ∈ interior (convexHull ℝ
          (Set.range fun i => proj_xy (R.toEuclideanLin (emb E (y i)))))) ∧
      ∃ μ : ℝ, 0 < μ ∧ ∀ i, (R.toEuclideanLin (emb E (y i))) 2 =
        μ * (((Eᵀ * E) *ᵥ c) ⬝ᵥ y i) := by
  have hEne : E.det ≠ 0 := hE.ne'
  set w : ℝ³ := emb E c with hw
  have hw0 : w ≠ 0 := by
    intro h
    apply hc
    apply Matrix.eq_zero_of_mulVec_eq_zero hEne
    have h' : emb E c = 0 := h
    ext i; simpa [emb_apply] using congrArg (fun v : ℝ³ => v i) h'
  obtain ⟨R, hR, lam, hlam, hRw⟩ := exists_rotation_to_ez_pos w hw0
  have hor : ∀ a b : Fin 3 → ℝ, 0 < (Matrix.of ![a, b, c]).det →
      0 < cross2 (proj_xy (R.toEuclideanLin (emb E a))) (proj_xy (R.toEuclideanLin (emb E b))) := by
    intro a b h
    refine cross2_proj_rot_pos hR hlam hRw ?_
    rw [hw, det3_emb]; exact mul_pos hE h
  have hside : ∀ i : ZMod k, ∀ v ∈ Y, v ≠ y i → v ≠ y (i + 1) →
      0 < cross2 (proj_xy (R.toEuclideanLin (emb E (y (i + 1)))) -
          proj_xy (R.toEuclideanLin (emb E (y i))))
        (proj_xy (R.toEuclideanLin (emb E v)) - proj_xy (R.toEuclideanLin (emb E (y i)))) := by
    intro i v hv h1 h2
    rw [proj_rot_sub, proj_rot_sub, ← emb_sub, ← emb_sub]
    exact hor _ _ (hcell i v hv h1 h2)
  have hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (emb E (y i)))) := by
    refine ⟨hk, ?_⟩
    intro i j hj1 hj2
    exact hside i (y j) (hyY j) (fun h => hj1 (hy h)) (fun h => hj2 (hy h))
  refine ⟨R, hR, hp, ?_, 1 / lam, by positivity, ?_⟩
  · intro v hv hvx
    obtain ⟨u, huY, rfl⟩ := Finset.mem_image.mp hv
    refine hp.mem_interior_of_left fun i => ?_
    exact hside i u huY (fun h => hvx i (by rw [h])) (fun h => hvx (i + 1) (by rw [h]))
  · intro i
    have h1 := inner_toEuclideanLin_SO3 hR (emb E (y i)) w
    rw [hRw, real_inner_smul_right, inner_ez, hw, inner_emb] at h1
    field_simp
    linarith

/-- **A rim cell of any size with unimodal depths gives Rupert.**  `y : ZMod k → ℝ³` (`k ≥ 3`)
is the rim in shape coordinates, all in `Y`; `c ≠ 0` lies strictly left of every rim edge
against every other point of `Y`; the depths `((Eᵀ E) c) ⬝ᵥ y i` are cyclically unimodal. -/
theorem isRupert_of_rimCell_zmod {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det)
    (y : ZMod k → Fin 3 → ℝ) (hy : Function.Injective y) (Y : Finset (Fin 3 → ℝ))
    (hyY : ∀ i, y i ∈ Y) (c : Fin 3 → ℝ) (hc : c ≠ 0)
    (hcell : ∀ i : ZMod k, ∀ v ∈ Y, v ≠ y i → v ≠ y (i + 1) →
      0 < (Matrix.of ![y (i + 1) - y i, v - y i, c]).det)
    (hz : IsCyclicUnimodal (fun i => ((Eᵀ * E) *ᵥ c) ⬝ᵥ y i)) :
    IsRupert (Y.image (emb E)) := by
  obtain ⟨R, hR, hp, hin, μ, hμ, hzμ⟩ := exists_view_of_rimCell_zmod hk E hE y hy Y hyY c hc hcell
  refine isRupert_of_genericUnimodalView (Y.image (emb E)) R hR (fun i => emb E (y i))
    (fun i => Finset.mem_image_of_mem _ (hyY i)) hp hin ?_
  have : (fun i => (R.toEuclideanLin (emb E (y i))) 2) =
      fun i => μ * (((Eᵀ * E) *ᵥ c) ⬝ᵥ y i) := funext hzμ
  rw [this]
  refine ⟨fun a b hab => hz.1 (mul_left_cancel₀ hμ.ne' hab), ?_⟩
  rw [← hz.2]
  congr 1
  exact Finset.filter_congr fun i _ => by simp only [mul_lt_mul_iff_right₀ hμ]

/-- Cyclic unimodality is an open condition on the depth vector. -/
theorem isOpen_setOf_isCyclicUnimodal {k : ℕ} [NeZero k] :
    IsOpen {z : ZMod k → ℝ | IsCyclicUnimodal z} := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  exact eventually_isCyclicUnimodal (z := fun (x : ZMod k → ℝ) => x) (x₀ := z)
    (fun i => (continuous_apply i).continuousAt) hz

/-- **The vertex leaf.**  If the orientation inequalities hold at every view of a set `A`,
and at some `g ∈ closure A` the depths `((Eᵀ E) g) ⬝ᵥ y i` are cyclically unimodal, then
`E Y` is Rupert. -/
theorem isRupert_of_rimCell_vertex {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det)
    (y : ZMod k → Fin 3 → ℝ) (hy : Function.Injective y) (Y : Finset (Fin 3 → ℝ))
    (hyY : ∀ i, y i ∈ Y) {A : Set (Fin 3 → ℝ)}
    (hcell : ∀ c ∈ A, ∀ i : ZMod k, ∀ v ∈ Y, v ≠ y i → v ≠ y (i + 1) →
      0 < (Matrix.of ![y (i + 1) - y i, v - y i, c]).det)
    {g : Fin 3 → ℝ} (hg : g ∈ closure A)
    (hz : IsCyclicUnimodal (fun i => ((Eᵀ * E) *ᵥ g) ⬝ᵥ y i)) :
    IsRupert (Y.image (emb E)) := by
  have hcont : Continuous fun c : Fin 3 → ℝ => fun i : ZMod k => ((Eᵀ * E) *ᵥ c) ⬝ᵥ y i := by
    refine continuous_pi fun i => ?_
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  have hU : IsOpen {c : Fin 3 → ℝ | IsCyclicUnimodal fun i : ZMod k => ((Eᵀ * E) *ᵥ c) ⬝ᵥ y i} :=
    isOpen_setOf_isCyclicUnimodal.preimage hcont
  obtain ⟨c, hcU, hcA⟩ := mem_closure_iff.mp hg _ hU hz
  refine isRupert_of_rimCell_zmod hk E hE y hy Y hyY c ?_ (hcell c hcA) hcU
  intro h0
  have h2 : y 2 ≠ y 0 := fun h => by
    have := zmod_add_ne (k := k) (a := 2) (b := 0) (by omega) (by omega) (by omega) 0
    simp at this
    exact this (hy h)
  have h3 : y 2 ≠ y (0 + 1) := fun h => by
    rw [zero_add] at h
    have := zmod_add_ne (k := k) (a := 2) (b := 1) (by omega) (by omega) (by omega) 0
    simp at this
    exact this (hy h)
  have := hcell c hcA 0 _ (hyY _) h2 h3
  rw [h0] at this
  simp [Matrix.det_fin_three] at this

open MeasureTheory
/-- Depth ties are null sets: for invertible `E` and injective `y`, the set of views with
`z i = z j` (`i ≠ j`) has measure zero. -/
theorem volume_tie_eq_zero (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det)
    (p q : Fin 3 → ℝ) (hpq : p ≠ q) :
    volume {c : Fin 3 → ℝ | ((Eᵀ * E) *ᵥ c) ⬝ᵥ p = ((Eᵀ * E) *ᵥ c) ⬝ᵥ q} = 0 := by
  let L : (Fin 3 → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun c => ((Eᵀ * E) *ᵥ c) ⬝ᵥ (p - q)
      map_add' := fun a b => by simp [Matrix.mulVec_add, add_dotProduct, dotProduct_sub]; ring
      map_smul' := fun r a => by simp [Matrix.mulVec_smul, smul_dotProduct, dotProduct_sub]; ring }
  have hdet : IsUnit (Eᵀ * E).det := by
    rw [Matrix.det_mul, Matrix.det_transpose]
    exact (mul_pos hE hE).ne'.isUnit
  have hne : LinearMap.ker L ≠ ⊤ := by
    intro h
    have hw : p - q ≠ 0 := sub_ne_zero.mpr hpq
    have h1 : L ((Eᵀ * E)⁻¹ *ᵥ (p - q)) = 0 := by
      have : ((Eᵀ * E)⁻¹ *ᵥ (p - q)) ∈ LinearMap.ker L := h ▸ Submodule.mem_top
      exact this
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec] at h1
    exact hw (dotProduct_self_eq_zero.mp h1)
  have h0 := Measure.addHaar_submodule volume (LinearMap.ker L) hne
  convert h0 using 2
  ext c
  simp [L, dotProduct_sub, sub_eq_zero]

/-- **The vertex leaf, robust form.**  As `isRupert_of_rimCell_vertex`, but the depths at `g` need
only be robustly unimodal (`IsRobustUnimodal`: ties allowed, no alternating quartet; implied by
the strict quartet condition `max (z b) (z d) > min (z a) (z c)` and `max (z a) (z c) >
min (z b) (z d)` on cyclically ordered quadruples), and `g` lies in the closure of the
*interior* of `A` (needed to find a view with injective depths).  Any `k ≥ 3`. -/
theorem isRupert_of_rimCell_vertex_robust {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det)
    (y : ZMod k → Fin 3 → ℝ) (hy : Function.Injective y) (Y : Finset (Fin 3 → ℝ))
    (hyY : ∀ i, y i ∈ Y) {A : Set (Fin 3 → ℝ)}
    (hcell : ∀ c ∈ A, ∀ i : ZMod k, ∀ v ∈ Y, v ≠ y i → v ≠ y (i + 1) →
      0 < (Matrix.of ![y (i + 1) - y i, v - y i, c]).det)
    {g : Fin 3 → ℝ} (hg : g ∈ closure (interior A))
    (hz : IsRobustUnimodal (fun i => ((Eᵀ * E) *ᵥ g) ⬝ᵥ y i)) :
    IsRupert (Y.image (emb E)) := by
  set Z : (Fin 3 → ℝ) → ZMod k → ℝ := fun c i => ((Eᵀ * E) *ᵥ c) ⬝ᵥ y i with hZ
  have hcont : ∀ i, Continuous fun c : Fin 3 → ℝ => Z c i := by
    intro i
    simp only [hZ, dotProduct, Matrix.mulVec]
    fun_prop
  have hev : ∀ᶠ c in 𝓝 g, ∀ i j, Z g i < Z g j → Z c i < Z c j := by
    refine Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => ?_
    by_cases h : Z g i < Z g j
    · exact ((hcont i).continuousAt.tendsto.eventually_lt (hcont j).continuousAt.tendsto h).mono
        fun c hc _ => hc
    · exact Filter.Eventually.of_forall fun c h' => absurd h' h
  obtain ⟨U, hUs, hUo, hgU⟩ := mem_nhds_iff.mp hev
  obtain ⟨c0, hc0U, hc0A⟩ := mem_closure_iff.mp hg U hUo hgU
  -- an open set W of good views
  have hW : IsOpen (U ∩ interior A) := hUo.inter isOpen_interior
  have hpos : 0 < volume (U ∩ interior A) := hW.measure_pos volume ⟨c0, hc0U, hc0A⟩
  -- avoid ties
  have hnull : volume (⋃ (ij : {ij : ZMod k × ZMod k // ij.1 ≠ ij.2}),
      {c : Fin 3 → ℝ | Z c ij.1.1 = Z c ij.1.2}) = 0 := by
    refine (measure_iUnion_null fun ij => ?_)
    exact volume_tie_eq_zero E hE _ _ (fun h => ij.2 (hy h))
  obtain ⟨c, hcW, hcn⟩ : ∃ c ∈ U ∩ interior A,
      c ∉ ⋃ (ij : {ij : ZMod k × ZMod k // ij.1 ≠ ij.2}),
        {c : Fin 3 → ℝ | Z c ij.1.1 = Z c ij.1.2} := by
    by_contra hcon
    push Not at hcon
    have : volume (U ∩ interior A) ≤ 0 :=
      hnull ▸ measure_mono (fun c hc => hcon c hc)
    exact absurd hpos (not_lt.mpr this)
  have hinj : Function.Injective (Z c) := by
    intro i j hij
    by_contra hne
    exact hcn (Set.mem_iUnion.mpr ⟨⟨(i, j), hne⟩, hij⟩)
  have hord : ∀ i j, Z g i < Z g j → Z c i < Z c j := hUs hcW.1
  have hcA : c ∈ A := interior_subset hcW.2
  have hU := hz.isCyclicUnimodal_of_order hk hord hinj
  refine isRupert_of_rimCell_zmod hk E hE y hy Y hyY c ?_ (hcell c hcA) hU
  intro h0
  have h2 : y 2 ≠ y 0 := fun h => by
    have := zmod_add_ne (k := k) (a := 2) (b := 0) (by omega) (by omega) (by omega) 0
    simp at this
    exact this (hy h)
  have h3 : y 2 ≠ y (0 + 1) := fun h => by
    rw [zero_add] at h
    have := zmod_add_ne (k := k) (a := 2) (b := 1) (by omega) (by omega) (by omega) 0
    simp at this
    exact this (hy h)
  have := hcell c hcA 0 _ (hyY _) h2 h3
  rw [h0] at this
  simp [Matrix.det_fin_three] at this

end Minimality.RimCell
