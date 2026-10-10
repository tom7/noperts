module

public import Septopert.Group

@[expose] public section

/-!
# The C3v cell of relative rotations at a view

At a view u, the relative rotation R may be replaced by R c_k (c_k ∈ C3, the
inner copy's rotations) and by H_u R Q_i (the mirror ties, `MirrorTie.lean`).
These six candidates are closed under both operations (the group table
below), so the candidate of largest trace lies in the cell

  tr(R c_k) ≤ tr R for all k, and tr(H_u R Q_i) ≤ tr R for all i

(`exists_c3v_reduction`), as `exists_halfTurn_ico_reduction` does for the
icosahedral group with 120 candidates. Inside the cell the only trivial
pose is the identity; the mirror ties are images of the identity on the
cell's boundary.
-/

namespace Septopert
open Noperts

open scoped Matrix
open Noperts.Pipeline

/-- The negation in Fin 3, as a table (literal subtraction does not reduce
inside the matrix definitions). -/
def negIdx : Fin 3 → Fin 3
  | 0 => 0
  | 1 => 2
  | 2 => 1

theorem mirrorQ_mul_c3 (i k : Fin 3) : mirrorQMat i * c3Mat k = mirrorQMat (i + negIdx k) := by
  fin_cases i <;> fin_cases k <;> simp only [negIdx, Fin.reduceAdd, Fin.isValue] <;> ext a b <;>
    fin_cases a <;> fin_cases b <;>
    simp [c3Mat, mirrorQMat, mirrorMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]

theorem mirrorQ_mul_mirrorQ (i j : Fin 3) : mirrorQMat i * mirrorQMat j = c3Mat (i + negIdx j) := by
  fin_cases i <;> fin_cases j <;> simp only [negIdx, Fin.reduceAdd, Fin.isValue] <;> ext a b <;>
    fin_cases a <;> fin_cases b <;>
    simp [c3Mat, mirrorQMat, mirrorMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]

/-- The cell: no candidate has a larger trace. -/
def InC3vCell (u : Fin 3 → ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  (∀ k : Fin 3, Matrix.trace (R * c3Mat k) ≤ Matrix.trace R) ∧
    ∀ i : Fin 3, Matrix.trace (halfTurnMat u * R * mirrorQMat i) ≤ Matrix.trace R

/-- The candidate (b, j): R c_j if not b, H_u R Q_j if b. -/
noncomputable def c3vCandidate (u : Fin 3 → ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ) (b : Bool) (j : Fin 3) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  if b then halfTurnMat u * R * mirrorQMat j else R * c3Mat j

theorem exists_c3v_reduction (u : Fin 3 → ℝ) (hu : ∑ k, u k ^ 2 ≠ 0) (R : Matrix (Fin 3) (Fin 3) ℝ) :
    ∃ b j, InC3vCell u (c3vCandidate u R b j) := by
  obtain ⟨⟨b, j⟩, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun bj : Bool × Fin 3 => Matrix.trace (c3vCandidate u R bj.1 bj.2)) Finset.univ_nonempty
  have hH := halfTurnMat_mul_self u hu
  refine ⟨b, j, fun k => ?_, fun i => ?_⟩
  · cases b
    · have := hmax (false, j + k) (Finset.mem_univ _)
      simp only [c3vCandidate, Bool.false_eq_true, if_false] at this ⊢
      rwa [Matrix.mul_assoc, c3_mul_c3]
    · have := hmax (true, j + negIdx k) (Finset.mem_univ _)
      simp only [c3vCandidate, if_true] at this ⊢
      rwa [Matrix.mul_assoc, mirrorQ_mul_c3]
  · cases b
    · have := hmax (true, i + j) (Finset.mem_univ _)
      simp only [c3vCandidate, Bool.false_eq_true, if_false, if_true] at this ⊢
      have heq : halfTurnMat u * (R * c3Mat j) * mirrorQMat i = halfTurnMat u * R * mirrorQMat (i + j) := by
        rw [Matrix.mul_assoc (halfTurnMat u), Matrix.mul_assoc R, c3_mul_mirrorQ, ← Matrix.mul_assoc]
      rwa [heq]
    · have := hmax (false, j + negIdx i) (Finset.mem_univ _)
      simp only [c3vCandidate, if_true, Bool.false_eq_true, if_false] at this ⊢
      have heq : halfTurnMat u * (halfTurnMat u * R * mirrorQMat j) * mirrorQMat i =
          R * c3Mat (j + negIdx i) := by
        calc halfTurnMat u * (halfTurnMat u * R * mirrorQMat j) * mirrorQMat i
            = (halfTurnMat u * halfTurnMat u) * R * (mirrorQMat j * mirrorQMat i) := by
              simp only [Matrix.mul_assoc]
          _ = R * c3Mat (j + negIdx i) := by rw [hH, mirrorQ_mul_mirrorQ, Matrix.one_mul]
      rwa [heq]

end Septopert
