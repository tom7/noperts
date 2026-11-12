module

public import Mathlib
public import Minimality.RimCell
public import Minimality.Tilt
public import Minimality.ClusterLimit

@[expose] public section

/-!
# Rim cells in shape (Gram) coordinates

Points are given in shape coordinates `y : Fin 3 → ℝ` and realised as `x = E y` for an
invertible matrix `E` with `0 < det E` (so the metric Gram matrix is `Γ = Eᵀ E`).  A view `c`
(in shape coordinates) looks along `w = E c`.  Then depths are `⟪w, E y⟫ = (Γ c) ⬝ᵥ y`, and
orientations are `det (E a, E b, E c) = det E * det (a, b, c)`.

* `isRupert_of_rimCell_scaled`: `isRupert_of_rimCell` with the corner depths only a positive
  multiple of `(Γ c) ⬝ᵥ y i`.
* `exists_view_of_rimCell`: the cell geometry; a view satisfying the strict orientation
  inequalities is realised by a rotation with a ccw rim and every other point strictly inside.
* `isRupert_of_rimCell_coords`: the corollary with all hypotheses in shape coordinates.
-/

set_option autoImplicit false

namespace Minimality.RimCell

open Finset Matrix
open scoped RealInnerProductSpace

theorem isCyclicUnimodal_smul {μ : ℝ} (hμ : 0 < μ) {z : ZMod 4 → ℝ}
    (h : Minimality.IsCyclicUnimodal z) : Minimality.IsCyclicUnimodal (fun i => μ * z i) := by
  refine ⟨fun a b hab => h.1 (mul_left_cancel₀ hμ.ne' hab), ?_⟩
  have := h.2
  rw [← this]
  congr 1
  apply Finset.filter_congr
  intro i _
  simp only [mul_lt_mul_iff_right₀ hμ]

/-- `isRupert_of_rimCell` with corner depths a positive multiple of `(Γ c) ⬝ᵥ y i`. -/
theorem isRupert_of_rimCell_scaled (V : Finset ℝ³) (x : ZMod 4 → ℝ³) (hxV : ∀ i, x i ∈ V)
    {n : ℕ} (Γ : Matrix (Fin n) (Fin n) ℝ) (hΓ : Γ.det ≠ 0)
    (y : ZMod 4 → Fin n → ℝ) (hy : Function.Injective y)
    (hspan : ∀ w : Fin n → ℝ, (∀ p ∈ diagPairs, w ⬝ᵥ (y p.1 - y p.2) = 0) → w = 0)
    {A : Set (Fin n → ℝ)} (hAo : IsOpen A) (hAc : Convex ℝ A) (hA0 : (0 : Fin n → ℝ) ∉ A)
    (hview : ∀ c ∈ A, ∃ R : Matrix (Fin 3) (Fin 3) ℝ, R ∈ SO3 ∧
      IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))) ∧
      (∀ v ∈ V, (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
        interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i))))) ∧
      ∃ μ : ℝ, 0 < μ ∧ ∀ i, (R.toEuclideanLin (x i)) 2 = μ * ((Γ *ᵥ c) ⬝ᵥ y i))
    {g g' : Fin n → ℝ} (hg : g ∈ closure A) (hg' : g' ∈ closure A)
    (hneg : ∃ p ∈ diagPairs, (Γ *ᵥ g) ⬝ᵥ (y p.1 - y p.2) < 0)
    (hpos : ∃ p ∈ diagPairs, 0 < (Γ *ᵥ g') ⬝ᵥ (y p.1 - y p.2)) :
    IsRupert V := by
  obtain ⟨c, hcA, hcu⟩ := rimCell_exists_unimodal Γ hΓ y hy hspan hAo hAc hA0 hg hg' hneg hpos
  obtain ⟨R, hR, hp, hin, μ, hμ, hz⟩ := hview c hcA
  refine isRupert_of_genericUnimodalView V R hR x hxV hp hin ?_
  have : (fun i => (R.toEuclideanLin (x i)) 2) = fun i => μ * depth Γ y c i := funext hz
  rw [this]; exact isCyclicUnimodal_smul hμ hcu

/-- Embedding of shape coordinates: `u ↦ E u`. -/
noncomputable def emb (E : Matrix (Fin 3) (Fin 3) ℝ) (u : Fin 3 → ℝ) : ℝ³ :=
  WithLp.toLp 2 (E *ᵥ u)

theorem emb_apply (E : Matrix (Fin 3) (Fin 3) ℝ) (u : Fin 3 → ℝ) (i : Fin 3) :
    emb E u i = (E *ᵥ u) i := rfl

theorem emb_sub (E : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3 → ℝ) :
    emb E (a - b) = emb E a - emb E b := by
  ext i; simp [emb_apply, Matrix.mulVec_sub]

theorem inner_emb (E : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3 → ℝ) :
    ⟪emb E a, emb E b⟫ = ((Eᵀ * E) *ᵥ b) ⬝ᵥ a := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec]
  simp [PiLp.inner_apply, Fin.sum_univ_three, emb_apply, dotProduct, mul_comm]

theorem det3_emb (E : Matrix (Fin 3) (Fin 3) ℝ) (a b c : Fin 3 → ℝ) :
    det3 (emb E a) (emb E b) (emb E c) = E.det * (Matrix.of ![a, b, c]).det := by
  rw [det3, inner_cross_eq_det]
  have e : (!![(emb E a) 0, (emb E a) 1, (emb E a) 2; (emb E b) 0, (emb E b) 1, (emb E b) 2;
      (emb E c) 0, (emb E c) 1, (emb E c) 2] : Matrix (Fin 3) (Fin 3) ℝ) =
      Matrix.of ![a, b, c] * Eᵀ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, emb_apply, Matrix.mulVec, dotProduct] <;> ring
  rw [e, Matrix.det_mul, Matrix.det_transpose, mul_comm]

theorem emb_injective {E : Matrix (Fin 3) (Fin 3) ℝ} (hE : E.det ≠ 0) :
    Function.Injective (emb E) := by
  intro a b h
  have : E *ᵥ (a - b) = 0 := by
    rw [Matrix.mulVec_sub]
    have : E *ᵥ a = E *ᵥ b := by
      ext i; simpa [emb_apply] using congrArg (fun v : ℝ³ => v i) h
    rw [this, sub_self]
  have h0 := Matrix.eq_zero_of_mulVec_eq_zero hE this
  exact sub_eq_zero.mp h0

/-- **The cell geometry.**  Let `E` have positive determinant and let `c ≠ 0` satisfy the strict
orientation inequalities of the rim `y 0 → y 1 → y 2 → y 3 → y 0` against every point of `Y`
off the edge.  Then some rotation `R` realises the view `c`: the projected rim is a ccw polygon,
every other point of `E Y` projects strictly inside, and the corner depths are
`(Γ c) ⬝ᵥ y i / ‖E c‖` for `Γ = Eᵀ E`. -/
theorem exists_view_of_rimCell (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det)
    (y : ZMod 4 → Fin 3 → ℝ) (hy : Function.Injective y) (Y : Finset (Fin 3 → ℝ)) (hyY : ∀ i, y i ∈ Y)
    (c : Fin 3 → ℝ) (hc : c ≠ 0)
    (hcell : ∀ i : ZMod 4, ∀ v ∈ Y, v ≠ y i → v ≠ y (i + 1) →
      0 < (Matrix.of ![y (i + 1) - y i, v - y i, c]).det) :
    ∃ R : Matrix (Fin 3) (Fin 3) ℝ, R ∈ SO3 ∧
      IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (emb E (y i)))) ∧
      (∀ v ∈ Y.image (emb E), (∀ i, v ≠ emb E (y i)) →
        proj_xy (R.toEuclideanLin v) ∈ interior (convexHull ℝ
          (Set.range fun i => proj_xy (R.toEuclideanLin (emb E (y i)))))) ∧
      ∃ μ : ℝ, 0 < μ ∧ ∀ i, (R.toEuclideanLin (emb E (y i))) 2 =
        μ * (((Eᵀ * E) *ᵥ c) ⬝ᵥ y i) := by
  have hEne : E.det ≠ 0 := hE.ne'
  have hinj := emb_injective hEne
  set w : ℝ³ := emb E c with hw
  have hw0 : w ≠ 0 := by
    intro h
    apply hc
    apply Matrix.eq_zero_of_mulVec_eq_zero hEne
    have h' : emb E c = 0 := h
    ext i; simpa [emb_apply] using congrArg (fun v : ℝ³ => v i) h'
  obtain ⟨R, hR, lam, hlam, hRw⟩ := exists_rotation_to_ez_pos w hw0
  -- orientation transfer
  have hor : ∀ a b : Fin 3 → ℝ, 0 < (Matrix.of ![a, b, c]).det →
      0 < cross2 (proj_xy (R.toEuclideanLin (emb E a))) (proj_xy (R.toEuclideanLin (emb E b))) := by
    intro a b h
    refine cross2_proj_rot_pos hR hlam hRw ?_
    rw [hw, det3_emb]; exact mul_pos hE h
  have hside : ∀ i : ZMod 4, ∀ v ∈ Y, v ≠ y i → v ≠ y (i + 1) →
      0 < cross2 (proj_xy (R.toEuclideanLin (emb E (y (i + 1)))) -
          proj_xy (R.toEuclideanLin (emb E (y i))))
        (proj_xy (R.toEuclideanLin (emb E v)) - proj_xy (R.toEuclideanLin (emb E (y i)))) := by
    intro i v hv h1 h2
    rw [proj_rot_sub, proj_rot_sub, ← emb_sub, ← emb_sub]
    exact hor _ _ (hcell i v hv h1 h2)
  have hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (emb E (y i)))) := by
    refine ⟨by norm_num, ?_⟩
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

/-- **A rim cell in shape coordinates gives Rupert.**  The points are `E u`, `u ∈ Y`, with
`0 < det E` (metric Gram matrix `Γ = Eᵀ E`), and `y 0, …, y 3 ∈ Y` is the rim.  `A` is an open
convex set of views, `0 ∉ A`, on which every point `v ∈ Y` off the rim edge `y i → y (i+1)` lies
strictly left of it (`0 < det (y (i+1) - y i, v - y i, c)`).  If the Q4 forms take both strict
signs on `closure A`, then `E Y` is Rupert. -/
theorem isRupert_of_rimCell_coords (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det)
    (y : ZMod 4 → Fin 3 → ℝ) (hy : Function.Injective y) (Y : Finset (Fin 3 → ℝ))
    (hyY : ∀ i, y i ∈ Y)
    (hspan : ∀ w : Fin 3 → ℝ, (∀ p ∈ diagPairs, w ⬝ᵥ (y p.1 - y p.2) = 0) → w = 0)
    {A : Set (Fin 3 → ℝ)} (hAo : IsOpen A) (hAc : Convex ℝ A) (hA0 : (0 : Fin 3 → ℝ) ∉ A)
    (hcell : ∀ c ∈ A, ∀ i : ZMod 4, ∀ v ∈ Y, v ≠ y i → v ≠ y (i + 1) →
      0 < (Matrix.of ![y (i + 1) - y i, v - y i, c]).det)
    {g g' : Fin 3 → ℝ} (hg : g ∈ closure A) (hg' : g' ∈ closure A)
    (hneg : ∃ p ∈ diagPairs, ((Eᵀ * E) *ᵥ g) ⬝ᵥ (y p.1 - y p.2) < 0)
    (hpos : ∃ p ∈ diagPairs, 0 < ((Eᵀ * E) *ᵥ g') ⬝ᵥ (y p.1 - y p.2)) :
    IsRupert (Y.image (emb E)) := by
  have hΓ : (Eᵀ * E).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_transpose]; exact mul_ne_zero hE.ne' hE.ne'
  refine isRupert_of_rimCell_scaled (Y.image (emb E)) (fun i => emb E (y i))
    (fun i => Finset.mem_image_of_mem _ (hyY i)) (Eᵀ * E) hΓ y hy hspan hAo hAc hA0 ?_ hg hg'
    hneg hpos
  intro c hc
  exact exists_view_of_rimCell E hE y hy Y hyY c (fun h => hA0 (h ▸ hc)) (hcell c hc)

end Minimality.RimCell
