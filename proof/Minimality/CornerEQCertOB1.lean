module

public import Mathlib
public import Minimality.CornerEQCert
public import Minimality.CornerKernel
public import Minimality.RimCellView
public import Minimality.SplitRows

/-!
# Metric-free EQ certificates for the OB1 cone and shape-coordinate SplitRows

* `isRupert_of_eq_cert_ob1`: OB1-cone Farkas certificate (`certMatrix L + μ` PSD and nonzero,
  off-diagonal `μ ≥ 0`, diagonal `μ = 0`) refutes every `E` with `0 < E.det` and off-diagonal
  `(Eᵀ * E) ≤ 0`.
* `SplitRowsG`, `splitRows_emb_iff`: shape-coordinate form of `Minimality.Split.SplitRows`.
-/

set_option autoImplicit false

namespace Minimality.CornerEQ

open Finset Matrix
open Minimality.RimCell
open scoped RealInnerProductSpace

@[expose] public section

section OB1

private theorem pairing_pos_of_psd (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.PosSemidef)
    (hM0 : M ≠ 0) (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det) :
    0 < ∑ a, ∑ b, M a b * (Eᵀ * E) a b := by
  have hP : (E * M * Eᴴ).PosSemidef := hM.mul_mul_conjTranspose_same E
  have hU : IsUnit E := Matrix.isUnit_iff_isUnit_det _ |>.2 (isUnit_iff_ne_zero.2 hE.ne')
  have hN : E * M * Eᴴ ≠ 0 := by
    intro h
    apply hM0
    have h1 : E⁻¹ * (E * M * Eᴴ) * (Eᴴ)⁻¹ = M := by
      have hU' : IsUnit Eᴴ := by
        rw [Matrix.isUnit_iff_isUnit_det] at hU ⊢
        simpa [Matrix.det_conjTranspose] using hU
      calc _ = (E⁻¹ * E) * M * (Eᴴ * (Eᴴ)⁻¹) := by simp only [Matrix.mul_assoc]
        _ = _ := by
          rw [Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hU),
            Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hU')]
          simp
    rw [← h1, h]; simp
  have htr : 0 < (E * M * Eᴴ).trace := by
    refine lt_of_le_of_ne hP.trace_nonneg fun h => hN ?_
    exact (hP.trace_eq_zero_iff.1 h.symm)
  have : (E * M * Eᴴ).trace = ∑ a, ∑ b, M a b * (Eᵀ * E) a b := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.conjTranspose_apply, Matrix.transpose_apply, star_trivial]
    ring
  rwa [this] at htr

/-- **OB1-cone EQ certificate.**  `certMatrix L + μ` positive semidefinite and nonzero with
off-diagonal `μ ≥ 0` and zero diagonal: every `E` with `det E > 0` and `(Eᵀ * E) a b ≤ 0` for
`a ≠ b` gives a Rupert `E Y`. -/
theorem isRupert_of_eq_cert_ob1 {Y : Finset (Fin 3 → ℝ)} {ι : Type*} [Fintype ι] (L : ι → EQLeaf Y)
    (μ : Matrix (Fin 3) (Fin 3) ℝ) (hμ : ∀ a b, a ≠ b → 0 ≤ μ a b) (hμd : ∀ a, μ a a = 0)
    (hS : (certMatrix L + μ).PosSemidef) (hS0 : certMatrix L + μ ≠ 0)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det) (hob : ∀ a b, a ≠ b → (Eᵀ * E) a b ≤ 0) :
    IsRupert (Y.image (emb E)) := by
  have hpos := pairing_pos_of_psd (certMatrix L + μ) hS hS0 E hE
  have hμ_nonpos : ∑ a, ∑ b, μ a b * (Eᵀ * E) a b ≤ 0 := by
    refine Finset.sum_nonpos fun a _ => Finset.sum_nonpos fun b _ => ?_
    by_cases hab : a = b
    · subst hab; simp [hμd a]
    · exact mul_nonpos_of_nonneg_of_nonpos (hμ a b hab) (hob a b hab)
  have hS_pos : 0 < ∑ a, ∑ b, certMatrix L a b * (Eᵀ * E) a b := by
    have hsplit : ∑ a, ∑ b, (certMatrix L + μ) a b * (Eᵀ * E) a b =
        (∑ a, ∑ b, certMatrix L a b * (Eᵀ * E) a b) + ∑ a, ∑ b, μ a b * (Eᵀ * E) a b := by
      simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib]
    linarith
  exact isRupert_of_neg_leaf L E hE hS_pos

end OB1

section SplitRowsG

private theorem split_det3_eq_det3 (a b c : ℝ³) :
    Minimality.Split.det3 a b c = Minimality.det3 a b c := by
  rw [Minimality.Split.det3, Minimality.det3, Minimality.Split.inner3,
    Minimality.Split.cross_0, Minimality.Split.cross_1, Minimality.Split.cross_2]

/-- Shape-coordinate form of `Minimality.Split.SplitRows` for the Gram matrix `G = Eᵀ * E`. -/
def SplitRowsG {k : ℕ} (G : Matrix (Fin 3) (Fin 3) ℝ) (y : ZMod k → Fin 3 → ℝ) (u : Fin 3 → ℝ)
    (a c : ZMod k) (σ : ℝ) : Prop :=
  ∀ i j : ZMod k, i ≠ a → (j = i ∨ j = i + 1) → j ≠ c →
    0 < σ * (((G *ᵥ u) ⬝ᵥ (y j - y c)) * (Matrix.of ![y (i + 1) - y i, y (a + 1) - y a, u]).det)

theorem splitRows_emb_iff {k : ℕ} (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det)
    (y : ZMod k → Fin 3 → ℝ) (u : Fin 3 → ℝ) (a c : ZMod k) (σ : ℝ) :
    Minimality.Split.SplitRows (fun i => emb E (y i)) (emb E u) a c σ ↔ SplitRowsG (Eᵀ * E) y u a c σ := by
  simp only [Minimality.Split.SplitRows, SplitRowsG]
  refine forall₅_congr fun i j _ _ _ => ?_
  rw [← emb_sub, ← emb_sub, ← emb_sub, inner_emb, split_det3_eq_det3, det3_emb]
  have hmul : σ * ((((Eᵀ * E) *ᵥ u) ⬝ᵥ (y j - y c)) *
      (E.det * (Matrix.of ![y (i + 1) - y i, y (a + 1) - y a, u]).det)) =
      E.det * (σ * ((((Eᵀ * E) *ᵥ u) ⬝ᵥ (y j - y c)) *
        (Matrix.of ![y (i + 1) - y i, y (a + 1) - y a, u]).det)) := by ring
  rw [hmul, mul_pos_iff_of_pos_left hE]

end SplitRowsG

end

end Minimality.CornerEQ
