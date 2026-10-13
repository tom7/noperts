module

public import Pipeline.KCapChart

@[expose] public section

/-!
# The cap domain is covered by the charts

`cap_point_cover`: with an orthogonal view frame (x, e₁, e₂) and an
orthogonal rotation frame (Z, E₁, X), every pose of the cap domain — a view
u with `⟪u, x⟫ > 0` and `|⟪u, e_f⟫| / |e_f|² ≤ μ₀ ⟪u, x⟫ / |x|²`, and a
Cayley vector w whose frame coordinates are at most `R μ₀` — is a chart
point: some chart of the cap has a point y of its root box with
`chartU y = (1 / a) u` (a > 0) and `chartW y = w`. Points of the F_e chart
are moreover outside the identity cone and (on the tie's side) outside the
tie cone, which the cone charts cover. The decomposition is the DH's
(`Cap.view_side`, `Cap.weighted_cube`) with every rotation weight 1.
-/

namespace Noperts.Pipeline

namespace KCap

open Noperts.Pipeline.KCap.PVec
open scoped Matrix

/-! ### Orthogonal frames over ℝ -/

/-- Coordinates in an orthogonal (unnormalized) frame: `v = Σ (⟪v, f_i⟫ / |f_i|²) f_i`.
(With G the matrix of rows f_i and D = diag |f_i|², orthogonality is
G Gᵀ D⁻¹ = 1, hence Gᵀ D⁻¹ G = 1.) -/
theorem decomp3 (f0 f1 f2 v : Fin 3 → ℝ)
    (h01 : rdot f0 f1 = 0) (h02 : rdot f0 f2 = 0) (h12 : rdot f1 f2 = 0)
    (hn0 : rdot f0 f0 ≠ 0) (hn1 : rdot f1 f1 ≠ 0) (hn2 : rdot f2 f2 ≠ 0) :
    v = (rdot v f0 / rdot f0 f0) • f0 + (rdot v f1 / rdot f1 f1) • f1 +
      (rdot v f2 / rdot f2 f2) • f2 := by
  let G : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of ![f0, f1, f2]
  let Dinv : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.diagonal ![1 / rdot f0 f0, 1 / rdot f1 f1, 1 / rdot f2 f2]
  have hsym : ∀ a b, rdot a b = rdot b a := by intro a b; simp [rdot]; ring
  have hGG : G * (G.transpose * Dinv) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [G, Dinv, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal, Matrix.transpose_apply] <;>
      (field_simp; simp [rdot] at *; nlinarith [h01, h02, h12, hsym f0 f1, hsym f0 f2, hsym f1 f2])
  have hcomm : (G.transpose * Dinv) * G = 1 := mul_eq_one_comm.mp hGG
  funext k
  have hk := congrFun (congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M *ᵥ v) hcomm) k
  simp only [Matrix.one_mulVec] at hk
  rw [← hk]
  simp [G, Dinv, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal,
    Matrix.transpose_apply, rdot]
  fin_cases k <;> simp <;> ring

/-- The cap's view region: `⟪u, x⟫ > 0` and the tangent coordinates
`(⟪u, e_f⟫ / |e_f|²) / (⟪u, x⟫ / |x|²)` at most μ₀ in absolute value. -/
def InCapView (x e1 e2 : Fin 3 → ℝ) (μ0 : ℝ) (u : Fin 3 → ℝ) : Prop :=
  0 < rdot u x ∧
    |rdot u e1 / rdot e1 e1| ≤ μ0 * (rdot u x / rdot x x) ∧
    |rdot u e2 / rdot e2 e2| ≤ μ0 * (rdot u x / rdot x x)

/-- The cap's rotation region: the frame coordinates of the Cayley vector
are at most `R μ₀` in absolute value. -/
def InCapRot (Z E1 X : Fin 3 → ℝ) (Rμ : ℝ) (w : Fin 3 → ℝ) : Prop :=
  |rdot w Z / rdot Z Z| ≤ Rμ ∧ |rdot w E1 / rdot E1 E1| ≤ Rμ ∧ |rdot w X / rdot X X| ≤ Rμ

/-- A view of the region, scaled by `1 / a` (a = ⟪u, x⟫ / |x|²), is
`x + t₁ e₁ + t₂ e₂` with `|t_f| ≤ μ₀`. -/
theorem capView_decomp (x e1 e2 : Fin 3 → ℝ) (μ0 : ℝ)
    (h01 : rdot x e1 = 0) (h02 : rdot x e2 = 0) (h12 : rdot e1 e2 = 0)
    (hn0 : 0 < rdot x x) (hn1 : rdot e1 e1 ≠ 0) (hn2 : rdot e2 e2 ≠ 0)
    (u : Fin 3 → ℝ) (hu : InCapView x e1 e2 μ0 u) :
    ∃ a t1 t2 : ℝ, 0 < a ∧ |t1| ≤ μ0 ∧ |t2| ≤ μ0 ∧
      (1 / a) • u = x + t1 • e1 + t2 • e2 := by
  obtain ⟨hpos, h1, h2⟩ := hu
  set a := rdot u x / rdot x x with ha
  have ha0 : 0 < a := div_pos hpos hn0
  refine ⟨a, (rdot u e1 / rdot e1 e1) / a, (rdot u e2 / rdot e2 e2) / a, ha0, ?_, ?_, ?_⟩
  · rw [abs_div, abs_of_pos ha0, div_le_iff₀ ha0]; exact h1
  · rw [abs_div, abs_of_pos ha0, div_le_iff₀ ha0]; exact h2
  · have hd := decomp3 x e1 e2 u h01 h02 h12 hn0.ne' hn1 hn2
    conv_lhs => rw [hd]
    funext k
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, ha]
    field_simp

/-- A Cayley vector of the region is `c₀ Z + c₁ E₁ + c₂ X` with `|c_i| ≤ R μ₀`. -/
theorem capRot_decomp (Z E1 X : Fin 3 → ℝ) (Rμ : ℝ)
    (h01 : rdot Z E1 = 0) (h02 : rdot Z X = 0) (h12 : rdot E1 X = 0)
    (hn0 : rdot Z Z ≠ 0) (hn1 : rdot E1 E1 ≠ 0) (hn2 : rdot X X ≠ 0)
    (w : Fin 3 → ℝ) (hw : InCapRot Z E1 X Rμ w) :
    ∃ c : Fin 3 → ℝ, (∀ i, |c i| ≤ Rμ) ∧ w = c 0 • Z + (c 1 • E1 + c 2 • X) := by
  obtain ⟨h0, h1, h2⟩ := hw
  refine ⟨![rdot w Z / rdot Z Z, rdot w E1 / rdot E1 E1, rdot w X / rdot X X], ?_, ?_⟩
  · intro i; fin_cases i <;> simpa
  · have hd := decomp3 Z E1 X w h01 h02 h12 hn0 hn1 hn2
    conv_lhs => rw [hd]
    simp [add_assoc]

end KCap

end Noperts.Pipeline

end
