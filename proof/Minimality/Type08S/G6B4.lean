module

public import Minimality.Type08TouchN2
public import Minimality.Type08TouchT4
public import Minimality.Type08
public import Minimality.Type08Codim
public import Minimality.Type08R0
public import Minimality.Type08Rd
public import Minimality.Type08Flat

@[expose] public section

set_option autoImplicit true

/-!
# G6' bridge, part 4: Rupertness is invariant under a reflection
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- The reflection matrix `I - 2 e eᵀ`. -/
noncomputable def reflM (e : ℝ³) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => (if i = j then 1 else 0) - 2 * e i * e j

theorem reflM_apply (e : ℝ³) (x : ℝ³) :
    (reflM e).toEuclideanLin x = x - (2 * ⟪x, e⟫) • e := by
  ext i
  fin_cases i <;>
  simp [reflM, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    PiLp.inner_apply] <;> ring

theorem reflM_orth (e : ℝ³) (he : ⟪e, e⟫ = 1) :
    reflM e ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff']
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial] at he
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reflM, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three] <;>
    first
    | linear_combination (4 * e.ofLp 0 * e.ofLp 0) * he
    | linear_combination (4 * e.ofLp 1 * e.ofLp 1) * he
    | linear_combination (4 * e.ofLp 2 * e.ofLp 2) * he
    | linear_combination (4 * e.ofLp 0 * e.ofLp 1) * he
    | linear_combination (4 * e.ofLp 0 * e.ofLp 2) * he
    | linear_combination (4 * e.ofLp 1 * e.ofLp 2) * he

theorem isRupert_of_reflect (e : ℝ³) (he : ⟪e, e⟫ = 1) (V : Finset ℝ³)
    (h : IsRupert (V.image fun x => x - (2 * ⟪x, e⟫) • e)) : IsRupert V := by
  classical
  have h1 := Noperts.Pipeline.isRupert_image_similarity 0 1 one_pos (reflM e) (reflM_orth e he) _ h
  convert h1 using 1
  ext x
  simp only [Finset.mem_image]
  constructor
  · intro hx
    refine ⟨x - (2 * ⟪x, e⟫) • e, ⟨x, hx, rfl⟩, ?_⟩
    rw [reflM_apply]
    have : ⟪x - (2 * ⟪x, e⟫) • e, e⟫ = -⟪x, e⟫ := by
      rw [inner_sub_left, real_inner_smul_left, he]; ring
    rw [this]; simp only [zero_add, one_smul]; module
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    rw [reflM_apply]
    have : ⟪z - (2 * ⟪z, e⟫) • e - (2 * ⟪z - (2 * ⟪z, e⟫) • e, e⟫) • e, e⟫ = ⟪z, e⟫ := by
      simp only [inner_sub_left, real_inner_smul_left, he]; ring
    have h2 : z - (2 * ⟪z, e⟫) • e - (2 * ⟪z - (2 * ⟪z, e⟫) • e, e⟫) • e = z := by
      simp only [inner_sub_left, real_inner_smul_left, he]
      module
    simpa [h2] using hz

end Type08Sp
end Minimality
