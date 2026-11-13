module

public import Minimality.Type24SAT.K24.ParBoxHel
public import Minimality.Type24SAT.K24.ParBoxRecI
public import Minimality.Type24SAT.K24.ParBoxRecIV
public import Minimality.Type24SAT.K24.ParBoxRecIII
public import Minimality.Type24SAT.K24.ParBoxRecL
public import Pipeline.Similarity
public import EuclideanSpaceNotation

@[expose] public section

/-!
# Type 24 box corner `R₄'`: all of it in box coordinates

`box_rupert`: the box corner with `L, c, y₂, y₆ > 0`, `0 < ξ, ζ` and vertex `1` between the planes `026` and `H` is Rupert.
Cases: `y₆ < y₂` (recipe I if `b < y₂`, else IV or III), `y₂ = y₆` (recipe L if `b ≤ y₂`, else IV or III), `y₂ < y₆` by the
coordinate swap `x ↔ z` (view along `g`), an orthogonal map (`isRupert_image_similarity`). Also `rupert_of_frame`: the
transport from an orthonormal frame, of either orientation.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace Matrix
open Finset
namespace Minimality.T24.Par

theorem inner3 (a b : ℝ³) : ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]; ring

/-- The matrix with rows `f₁, f₂, f₃`. -/
noncomputable def frameMat (f1 f2 f3 : ℝ³) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![f1 0, f1 1, f1 2; f2 0, f2 1, f2 2; f3 0, f3 1, f3 2]

theorem frameMat_apply (f1 f2 f3 p : ℝ³) :
    (frameMat f1 f2 f3).toEuclideanLin p = !₂[⟪f1, p⟫, ⟪f2, p⟫, ⟪f3, p⟫] := by
  ext i
  fin_cases i <;> simp [frameMat, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, inner3] <;> ring

theorem frameMat_orth {f1 f2 f3 : ℝ³} (h11 : ⟪f1, f1⟫ = 1) (h22 : ⟪f2, f2⟫ = 1) (h33 : ⟪f3, f3⟫ = 1)
    (h12 : ⟪f1, f2⟫ = 0) (h13 : ⟪f1, f3⟫ = 0) (h23 : ⟪f2, f3⟫ = 0) :
    frameMat f1 f2 f3 ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  rw [inner3] at h11 h22 h33 h12 h13 h23
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frameMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;>
    first | linarith | (rw [← h11]; ring) | skip

/-- Completeness: `⟪a, b⟫ = Σ ⟪fₖ, a⟫ ⟪fₖ, b⟫` for an orthonormal frame. -/
theorem frame_inner {f1 f2 f3 : ℝ³} (h11 : ⟪f1, f1⟫ = 1) (h22 : ⟪f2, f2⟫ = 1) (h33 : ⟪f3, f3⟫ = 1)
    (h12 : ⟪f1, f2⟫ = 0) (h13 : ⟪f1, f3⟫ = 0) (h23 : ⟪f2, f3⟫ = 0) (a b : ℝ³) :
    ⟪a, b⟫ = ⟪f1, a⟫ * ⟪f1, b⟫ + ⟪f2, a⟫ * ⟪f2, b⟫ + ⟪f3, a⟫ * ⟪f3, b⟫ := by
  have hQ := frameMat_orth h11 h22 h33 h12 h13 h23
  have hQt : (frameMat f1 f2 f3)ᵀ * frameMat f1 f2 f3 = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hQ
  have e : ∀ i j, ((frameMat f1 f2 f3)ᵀ * frameMat f1 f2 f3) i j = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := by
    intro i j; rw [hQt]
  have e00 := e 0 0; have e01 := e 0 1; have e02 := e 0 2
  have e11 := e 1 1; have e12 := e 1 2; have e22 := e 2 2
  simp [frameMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] at e00 e01 e02 e11 e12 e22
  simp only [inner3]
  have e10 : f1 1 * f1 0 + f2 1 * f2 0 + f3 1 * f3 0 = 0 := by linarith
  have e20 : f1 2 * f1 0 + f2 2 * f2 0 + f3 2 * f3 0 = 0 := by linarith
  have e21 : f1 2 * f1 1 + f2 2 * f2 1 + f3 2 * f3 1 = 0 := by linarith
  linear_combination (-(a 0 * b 0)) * e00 - (a 0 * b 1) * e01 - (a 0 * b 2) * e02 - (a 1 * b 0) * e10 -
    (a 1 * b 1) * e11 - (a 1 * b 2) * e12 - (a 2 * b 0) * e20 - (a 2 * b 1) * e21 - (a 2 * b 2) * e22

/-- **Frame transport.** -/
theorem rupert_of_frame {n : ℕ} (x : Fin n → ℝ³) (f1 f2 f3 O : ℝ³) (h11 : ⟪f1, f1⟫ = 1) (h22 : ⟪f2, f2⟫ = 1)
    (h33 : ⟪f3, f3⟫ = 1) (h12 : ⟪f1, f2⟫ = 0) (h13 : ⟪f1, f3⟫ = 0) (h23 : ⟪f2, f3⟫ = 0)
    (h : IsRupert (univ.image fun i => (!₂[⟪f1, x i - O⟫, ⟪f2, x i - O⟫, ⟪f3, x i - O⟫] : ℝ³))) :
    IsRupert (univ.image x) := by
  have hQ := frameMat_orth h11 h22 h33 h12 h13 h23
  have hMQ : (frameMat f1 f2 f3)ᵀ ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
    rw [Matrix.mem_orthogonalGroup_iff]
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hQ
  have h2 := Noperts.Pipeline.isRupert_image_similarity O 1 one_pos _ hMQ _ h
  rw [Finset.image_image] at h2
  convert h2 using 2
  funext i
  have hQt : (frameMat f1 f2 f3)ᵀ * frameMat f1 f2 f3 = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hQ
  have := frameMat_apply f1 f2 f3 (x i - O)
  simp only [Function.comp, one_smul]
  rw [← this]
  simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec, hQt]
end Minimality.T24.Par

set_option autoImplicit false
namespace Minimality.T24.Par

theorem facC_xi {L c y2 xi ze b p q r f4 f1v : ℝ} (hL : 0 < L) (hc : 0 < c) (hy2 : 0 < y2)
    (a5 : r * c = 0) (a2 : q * y2 + r * c = 0) (a4 : p * L = f4) (a1 : p * (xi * L) + q * b + r * (ze * c) = f1v)
    (n4 : f4 < 0) (n1 : f1v < 0) : 0 < xi := by
  have hr : r = 0 := by
    rcases mul_eq_zero.1 a5 with h | h
    · exact h
    · exact absurd h hc.ne'
  have hq : q = 0 := by
    rw [hr] at a2
    have : q * y2 = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h hy2.ne'
  subst hr hq
  by_contra hx
  push Not at hx
  nlinarith [mul_nonneg_of_nonpos_of_nonpos hx (by linarith : p * L ≤ 0)]

theorem facE_ze {L c y6 xi ze b p q r f5 f1v : ℝ} (hL : 0 < L) (hc : 0 < c) (hy6 : 0 < y6)
    (a4 : p * L = 0) (a6 : p * L + q * y6 = 0) (a5 : r * c = f5) (a1 : p * (xi * L) + q * b + r * (ze * c) = f1v)
    (n5 : f5 < 0) (n1 : f1v < 0) : 0 < ze := by
  have hp : p = 0 := by
    rcases mul_eq_zero.1 a4 with h | h
    · exact h
    · exact absurd h hL.ne'
  have hq : q = 0 := by
    rw [hp] at a6
    have : q * y6 = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h hy6.ne'
  subst hp hq
  have hr : r < 0 := by
    by_contra h; push Not at h; nlinarith [mul_nonneg h hc.le]
  by_contra hx
  push Not at hx
  nlinarith [mul_nonneg_of_nonpos_of_nonpos hr.le hx, mul_pos hc hc]

theorem facA_lo {L c y2 y6 xi ze b p q r f4 f5 f6 : ℝ} (hL : 0 < L) (hc : 0 < c) (hy2 : 0 < y2) (hxi : 0 < xi)
    (a2 : q * y2 + r * c = 0) (a1 : p * (xi * L) + q * b + r * (ze * c) = 0) (a4 : p * L = f4)
    (a5 : r * c = f5) (a6 : p * L + q * y6 = f6) (n4 : f4 < 0) (n5 : f5 < 0) (n6 : f6 < 0) :
    y6 * xi + y2 * ze < b := by
  have hq : 0 < q := by
    by_contra h; push Not at h; nlinarith [mul_nonneg (neg_nonneg.2 h) hy2.le]
  -- q b = - p L xi + q y2 ze
  have key : q * b = -(p * L) * xi + q * y2 * ze := by
    have : r * (ze * c) = -(q * y2) * ze := by
      have : r * c = -(q * y2) := by linarith
      calc r * (ze * c) = (r * c) * ze := by ring
        _ = _ := by rw [this]
    nlinarith
  have h2 : q * y6 * xi < -(p * L) * xi := by nlinarith
  have : q * (y6 * xi + y2 * ze) < q * b := by nlinarith
  exact lt_of_mul_lt_mul_left this hq.le

theorem facH_hi {L c y2 y6 xi ze b p q r f0 f1v : ℝ} (hy2 : 0 < y2) (hy6 : 0 < y6) (hL : 0 < L) (hc : 0 < c)
    (a2 : 0 - f0 = q * y2 + r * c) (a3 : 0 - f0 = p * L + r * c) (a6 : 0 - f0 = p * L + q * y6)
    (a1 : f1v - f0 = p * (xi * L) + q * b + r * (ze * c)) (n0 : f0 < 0) (n1 : f1v < 0) :
    b < y2 * (1 - xi) + y6 * (1 - ze) := by
  have hpL : p * L = q * y2 := by linarith
  have hrc : r * c = q * y6 := by linarith
  have hf0 : f0 = -(q * (y2 + y6)) := by nlinarith
  have hq : 0 < q := by
    by_contra h; push Not at h; nlinarith [mul_nonneg (neg_nonneg.2 h) (add_pos hy2 hy6).le]
  have e1 : p * (xi * L) = q * y2 * xi := by rw [← hpL]; ring
  have e2 : r * (ze * c) = q * y6 * ze := by rw [← hrc]; ring
  have : q * b < q * (y2 * (1 - xi) + y6 * (1 - ze)) := by nlinarith
  exact lt_of_mul_lt_mul_left this hq.le
end Minimality.T24.Par

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset
namespace Minimality.T24.Par
open Minimality.Split Minimality.Split.HEL
open Minimality (cross)

/-- The box corner with `y6 ≤ y2`. -/
theorem box_rupert_ge {L c y2 y6 xi ze b : ℝ} (hL : 0 < L) (hc : 0 < c) (hy6 : 0 < y6) (hy : y6 ≤ y2)
    (hxi : 0 < xi) (hze : 0 < ze) (hlo : y6 * xi + y2 * ze < b) (hhi : b < y2 * (1 - xi) + y6 * (1 - ze)) :
    IsRupert (univ.image (boxCfg L c y2 y6 xi ze b)) := by
  rcases hy.lt_or_eq with hy' | hy'
  · by_cases hb : b < y2
    · exact rec_I hL hc hy6 hy' hxi hze hlo hhi hb
    · push Not at hb
      by_cases hiv : ze * c * (c - ze * c) < b * (b - y6)
      · exact rec_IV hL hc hy6 hy hxi hze hlo hhi hb hiv
      · exact rec_III hL hc hy6 hy hxi hze hlo hhi hb (by linarith) (not_lt.1 hiv)
  · by_cases hb : b ≤ y2
    · exact rec_L hL hc hy6 hy'.symm hxi hze hlo hhi hb
    · push Not at hb
      by_cases hiv : ze * c * (c - ze * c) < b * (b - y6)
      · exact rec_IV hL hc hy6 hy hxi hze hlo hhi hb.le hiv
      · exact rec_III hL hc hy6 hy hxi hze hlo hhi hb.le (by linarith) (not_lt.1 hiv)

/-- The coordinate swap `x ↔ z`. -/
def swapXZ : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

theorem swapXZ_mem : swapXZ ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i j; fin_cases i <;> fin_cases j <;> simp [swapXZ, Matrix.mul_apply, Fin.sum_univ_three]

theorem swapXZ_apply (p : ℝ³) : swapXZ.toEuclideanLin p = !₂[p 2, p 1, p 0] := by
  ext i; fin_cases i <;> simp [swapXZ, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem box_swap {L c y2 y6 xi ze b : ℝ} :
    (univ.image (boxCfg c L y6 y2 ze xi b)).image (fun p => (0 : ℝ³) + (1 : ℝ) • swapXZ.toEuclideanLin p) =
      univ.image (boxCfg L c y2 y6 xi ze b) := by
  let σ : Fin 7 → Fin 7 := ![0, 1, 6, 3, 5, 4, 2]
  have hσ : ∀ i, (0 : ℝ³) + (1 : ℝ) • swapXZ.toEuclideanLin (boxCfg c L y6 y2 ze xi b i) =
      boxCfg L c y2 y6 xi ze b (σ i) := by
    intro i
    fin_cases i <;> (simp only [swapXZ_apply]; ext j; fin_cases j <;> simp [boxCfg, σ]) <;> ring
  rw [Finset.image_image]
  have : ((fun p : ℝ³ => (0 : ℝ³) + (1 : ℝ) • swapXZ.toEuclideanLin p) ∘ boxCfg c L y6 y2 ze xi b) =
      boxCfg L c y2 y6 xi ze b ∘ σ := funext hσ
  rw [this, ← Finset.image_image]
  have hu : (univ : Finset (Fin 7)).image σ = univ := by decide
  rw [hu]

theorem box_rupert {L c y2 y6 xi ze b : ℝ} (hL : 0 < L) (hc : 0 < c) (hy2 : 0 < y2) (hy6 : 0 < y6)
    (hxi : 0 < xi) (hze : 0 < ze) (hlo : y6 * xi + y2 * ze < b) (hhi : b < y2 * (1 - xi) + y6 * (1 - ze)) :
    IsRupert (univ.image (boxCfg L c y2 y6 xi ze b)) := by
  rcases le_total y6 y2 with hy | hy
  · exact box_rupert_ge hL hc hy6 hy hxi hze hlo hhi
  · have h := box_rupert_ge (L := c) (c := L) (y2 := y6) (y6 := y2) (xi := ze) (ze := xi) (b := b) hc hL hy2 hy hze hxi
      (by linarith) (by linarith)
    have h2 := Noperts.Pipeline.isRupert_image_similarity 0 1 one_pos swapXZ swapXZ_mem _ h
    rwa [box_swap] at h2

end Minimality.T24.Par
