module

public import Minimality.Type21SAT.TopT

@[expose] public section

/-!
# Bridge, part 19: the mirror image of a type 21 shape (for `mirror_step`)

The reflection `mir = diag(1, 1, -1)` takes a type 21 shape `x` to a type 21 shape `mir ∘ x` with the
opposite chirality, and keeps Rupertness.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H21.SAT

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

/-- A facet of `x` gives a facet of the mirror image. -/
noncomputable def _root_.Minimality.Face16.mir' {x : Fin 7 → ℝ³} {S : Finset (Fin 7)}
    (F : Minimality.Face16 x S) : Minimality.Face16 (fun i => mir (x i)) S where
  f := fun y => F.f (mir y)
  N := mir F.N
  hN := fun y z => by
    show F.f (mir y) - F.f (mir z) = ⟪mir F.N, y - z⟫
    rw [F.hN, ← mir_sub]
    have := mir_inner F.N (mir (y - z))
    rw [mir_mir] at this
    exact this.symm
  zero := fun i hi => by simp only [mir_mir]; exact F.zero i hi
  neg := fun i hi => by simp only [mir_mir]; exact F.neg i hi

/-- The facets of the mirror image of a type 21 shape. -/
noncomputable def _root_.Minimality.Facets21.mir' {x : Fin 7 → ℝ³} (T : Minimality.Facets21 x) :
    Minimality.Facets21 (fun i => mir (x i)) where
  inj := fun i j h => T.inj (by simpa [mir_mir] using congrArg mir h)
  f014 := T.f014.mir'
  f015 := T.f015.mir'
  f0256 := T.f0256.mir'
  f046 := T.f046.mir'
  f134 := T.f134.mir'
  f135 := T.f135.mir'
  f2346 := T.f2346.mir'
  f235 := T.f235.mir'

/-- The chirality determinant flips sign. -/
theorem chir_mir (x : Fin 7 → ℝ³) :
    det3 (mir (x 0) - mir (x 2)) (mir (x 3) - mir (x 2)) (mir (x 6) - mir (x 2)) =
      - det3 (x 0 - x 2) (x 3 - x 2) (x 6 - x 2) := by
  rw [← mir_sub, ← mir_sub, ← mir_sub, mir_det3]

/-- The reflection as a matrix. -/
def Mx : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 1, 0; 0, 0, -1]

/-- The matrix acts as `mir`. -/
theorem Mx_lin (v : ℝ³) : Mx.toEuclideanLin v = mir v := by
  ext i; fin_cases i <;>
    simp [Mx, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, mir]

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


/-- **Case A, both chiralities.**  If the numbered clauses of core A are unsatisfiable, every shape with `Facets21 x`
and `D`, `H` not parallel is Rupert (the other chirality by the reflection). -/
theorem caseA_all (hA : CoreUnsatA) {x : Fin 7 → ℝ³} (T : Facets21 x)
    (hDH : ¬ ∃ r : ℝ, T.f046.N = r • T.f235.N) : IsRupert (univ.image x) := by
  by_cases hc : 0 < det3 (x 0 - x 2) (x 3 - x 2) (x 6 - x 2)
  · exact caseA_of_unsat_T hA T hc hDH
  · have hne := T.det_ne
    have hneg : det3 (x 0 - x 2) (x 3 - x 2) (x 6 - x 2) < 0 :=
      lt_of_le_of_ne (not_lt.mp hc) hne
    have hc' : 0 < det3 (mir (x 0) - mir (x 2)) (mir (x 3) - mir (x 2)) (mir (x 6) - mir (x 2)) := by
      rw [chir_mir]; linarith
    refine isRupert_of_mir (caseA_of_unsat_T hA T.mir' hc' ?_)
    rintro ⟨r, hr⟩
    apply hDH
    refine ⟨r, ?_⟩
    have h : mir (T.f046.N) = r • mir (T.f235.N) := hr
    have := congrArg mir h
    rw [mir_mir] at this
    rw [this]
    ext i; fin_cases i <;> simp [mir]

end Minimality.H21.SAT

