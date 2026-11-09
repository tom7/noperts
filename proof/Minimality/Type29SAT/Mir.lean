module

public import Minimality.Type29SAT.Ent
public import Minimality.Type21SAT.Lex2
public import Minimality.Type29Bridge
public import Minimality.SilS0XD

@[expose] public section

/-!
# Bridge, part 19: the mirror image of a type 29 shape (for `mirror_step`)

The reflection `mir = diag(1, 1, -1)` takes a type 29 shape `x` to a type 29 shape `mir ∘ x` with the
opposite chirality, and keeps Rupertness.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H29.SAT

/-- The reflection `diag(1, 1, -1)`. -/
noncomputable def mir (v : ℝ³) : ℝ³ := !₂[v 0, v 1, -v 2]

theorem mir_apply0 (v : ℝ³) : mir v 0 = v 0 := by simp [mir]
theorem mir_apply1 (v : ℝ³) : mir v 1 = v 1 := by simp [mir]
theorem mir_apply2 (v : ℝ³) : mir v 2 = - v 2 := by simp [mir]

/-- The reflection is an involution. -/
theorem mir_mir (v : ℝ³) : mir (mir v) = v := by
  ext i; fin_cases i <;> simp [mir]

/-- The reflection is additive. -/
theorem mir_sub (a b : ℝ³) : mir (a - b) = mir a - mir b := by
  ext i; fin_cases i <;> simp [mir] <;> ring

/-- The reflection preserves inner products. -/
theorem mir_inner (a b : ℝ³) : ⟪mir a, mir b⟫ = ⟪a, b⟫ := by
  simp only [inn3, mir_apply0, mir_apply1, mir_apply2]; ring

/-- The reflection negates determinants. -/
theorem mir_det3 (a b c : ℝ³) : det3 (mir a) (mir b) (mir c) = - det3 a b c := by
  simp only [det3_expand, mir_apply0, mir_apply1, mir_apply2]; ring

/-- The reflection reverses the cross product. -/
theorem mir_cross (a b : ℝ³) : cross (mir a) (mir b) = - mir (cross a b) := by
  ext i; fin_cases i <;>
    simp [cross_apply_zero, cross_apply_one, cross_apply_two, mir_apply0, mir_apply1, mir_apply2] <;>
    ring

/-- A type-free facet family of `x` gives one of the mirror image. -/
noncomputable def mirFac {n m : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³} (F : Minimality.H21.S0xFac m S x) :
    Minimality.H21.S0xFac m S (fun i => mir (x i)) where
  f := fun t y => F.f t (mir y)
  N := fun t => mir (F.N t)
  hN := fun t y z => by
    show F.f t (mir y) - F.f t (mir z) = ⟪mir (F.N t), y - z⟫
    rw [F.hN, ← mir_sub]
    have := mir_inner (F.N t) (mir (y - z))
    rw [mir_mir] at this
    exact this.symm
  zero := fun t i hi => by simp only [mir_mir]; exact F.zero t i hi
  neg := fun t i hi => by simp only [mir_mir]; exact F.neg t i hi

/-- The reflection as a matrix. -/
def Mx : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 1, 0; 0, 0, -1]

/-- The matrix acts as `mir`. -/
theorem Mx_lin (v : ℝ³) : Mx.toEuclideanLin v = mir v := by
  ext i; fin_cases i <;>
    simp [Mx, Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_three, mir]

/-- The matrix is orthogonal. -/
theorem Mx_mem : Mx ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Mx, Matrix.mul_apply, Fin.sum_univ_three]

/-- **Rupertness passes to the mirror image.** -/
theorem isRupert_of_mir {x : Fin 7 → ℝ³} (h : IsRupert (univ.image fun i => mir (x i))) :
    IsRupert (univ.image x) := by
  have := Noperts.Pipeline.isRupert_image_similarity 0 1 one_pos Mx Mx_mem _ h
  convert this using 1
  rw [Finset.image_image]
  congr 1
  funext i
  simp [Mx_lin, mir_mir]



end Minimality.H29.SAT
