module

public import Mathlib
public import Minimality.CornerKite

/-!
# The h-fibre and the foot gauge: Lemmas HF and FG

* **Lemma HF** (`fibre_mulVec_foot`, `fibre_bilin`, `foot_fibre_mem_cellSet`).  For `G n = 1` and
  `G_t = G + t 11ᵀ`: `G_t n = (1 + t ∑ n) 1` (the foot direction is constant), and
  `ρᵀ G_t σ = ρᵀ G σ + t (∑ρ)(∑σ)`.  The first two hold for any `Fintype`; the cell corollary is for
  `cellSet Y y` (which is a cone, `cellSet_smul`).  No inverse, no definiteness, no symmetry is used.
  Not proved here: (C1)-(C4) and the PD / obtuse interval `(-h², m]` of 2.1 (i).
* **Lemma FG** (`foot_gauge`, `footCombo_*`), `Fin 3`, both directions.  For symmetric `G` with `G n = κ 1`,
  `n > 0`: `G = κ D_n + ∑_{a<b} (-G_ab) Q_ab(n)` (`foot_gauge`).  Conversely every combination
  `κ D_n + ∑ λ_ab Q_ab(n)` with `κ > 0`, `λ ≥ 0` is symmetric, obtuse, positive definite and has
  `G n = κ 1` (`footCombo_symm`, `footCombo_offdiag_nonpos`, `footCombo_posDef`, `footCombo_mulVec`).
  Positivity of `n` is needed for `D_n`; `κ` is only used through `G n = κ 1` (no positivity needed
  for the identity).  GEN and AO of 3.1 are not done.
-/

set_option autoImplicit false

namespace Minimality.CornerEQ

open Finset Matrix
open Minimality.RimCell

@[expose] public section

section HF

variable {ι : Type*} [Fintype ι]

/-- **HF (i).**  `(G + t 11ᵀ) n = (1 + t ∑ n) 1` when `G n = 1`. -/
theorem fibre_mulVec_foot (G : Matrix ι ι ℝ) (n : ι → ℝ) (hn : G *ᵥ n = fun _ => 1) (t : ℝ) :
    (G + t • vecMulVec (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))) *ᵥ n
      = (1 + t * ∑ i, n i) • (fun _ : ι => (1 : ℝ)) := by
  ext i
  have h := congrFun hn i
  simp only [mulVec, dotProduct] at h ⊢
  simp only [Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, Pi.smul_apply,
    add_mul, Finset.sum_add_distrib, h, mul_one]
  rw [← Finset.mul_sum]

/-- **HF (ii).**  `ρᵀ G_t σ = ρᵀ G σ + t (∑ρ)(∑σ)`. -/
theorem fibre_bilin (G : Matrix ι ι ℝ) (t : ℝ) (ρ σ : ι → ℝ) :
    ((G + t • vecMulVec (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))) *ᵥ σ) ⬝ᵥ ρ
      = (G *ᵥ σ) ⬝ᵥ ρ + t * (∑ i, ρ i) * (∑ i, σ i) := by
  simp only [mulVec, dotProduct, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul,
    mul_one, add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end HF

section Cell

/-- `cellSet` is a cone: the orientation determinants are linear in the view. -/
theorem cellSet_smul {k : ℕ} {Y : Finset (Fin 3 → ℝ)} {y : ZMod k → Fin 3 → ℝ} {q : Fin 3 → ℝ}
    (hq : q ∈ cellSet Y y) {c : ℝ} (hc : 0 < c) : c • q ∈ cellSet Y y := by
  intro i v hv h1 h2
  have h := hq i v hv h1 h2
  have : (Matrix.of ![y (i + 1) - y i, v - y i, c • q]).det
      = c * (Matrix.of ![y (i + 1) - y i, v - y i, q]).det := by
    have e : (Matrix.of ![y (i + 1) - y i, v - y i, c • q])
        = Matrix.updateRow (Matrix.of ![y (i + 1) - y i, v - y i, q]) 2 (c • q) := by
      ext a b; fin_cases a <;> simp [Matrix.updateRow_apply]
    rw [e, Matrix.det_updateRow_smul]
    have e2 : Matrix.updateRow (Matrix.of ![y (i + 1) - y i, v - y i, q]) 2 q
        = Matrix.of ![y (i + 1) - y i, v - y i, q] := by
      ext a b; fin_cases a <;> simp [Matrix.updateRow_apply]
    rw [e2]
  rw [this]; exact mul_pos hc h

/-- **HF, KITE form.**  If `G n = 1`, `n ∈ cellSet Y y` and `1 + t ∑ n > 0`, the scaled foot
`n / (1 + t ∑ n)` of `G + t 11ᵀ` (i.e. the vector it maps to `1`) lies in the same cell. -/
theorem foot_fibre_mem_cellSet {k : ℕ} {Y : Finset (Fin 3 → ℝ)} {y : ZMod k → Fin 3 → ℝ}
    (G : Matrix (Fin 3) (Fin 3) ℝ) {n : Fin 3 → ℝ} (hn : G *ᵥ n = fun _ => 1)
    (hc : n ∈ cellSet Y y) (t : ℝ) (ht : 0 < 1 + t * ∑ i, n i) :
    ∃ m ∈ cellSet Y y,
      (G + t • vecMulVec (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))) *ᵥ m = fun _ => 1 := by
  refine ⟨(1 + t * ∑ i, n i)⁻¹ • n, cellSet_smul hc (inv_pos.2 ht), ?_⟩
  rw [mulVec_smul, fibre_mulVec_foot G n hn t, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]

end Cell

section FG

variable {n : Fin 3 → ℝ}

/-- `D_n = diag (1/n_a)`. -/
noncomputable def Dn (n : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal fun a => (n a)⁻¹

/-- `Q_ab(n) = q qᵀ / (n_a n_b)`, `q = n_b e_a - n_a e_b`. -/
noncomputable def Qab (n : Fin 3 → ℝ) (a b : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  (n a * n b)⁻¹ • vecMulVec (n b • Pi.single a (1 : ℝ) - n a • Pi.single b (1 : ℝ))
    (n b • Pi.single a (1 : ℝ) - n a • Pi.single b (1 : ℝ))

/-- The combination `κ D_n + λ₀₁ Q₀₁ + λ₀₂ Q₀₂ + λ₁₂ Q₁₂`. -/
noncomputable def footCombo (n : Fin 3 → ℝ) (κ l01 l02 l12 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  κ • Dn n + l01 • Qab n 0 1 + l02 • Qab n 0 2 + l12 • Qab n 1 2

/-- **Lemma FG (foot gauge).**  `G` symmetric, `n > 0`, `G n = κ 1`:
`G = κ D_n + ∑_{a<b} (-G_ab) Q_ab(n)`. -/
theorem foot_gauge {G : Matrix (Fin 3) (Fin 3) ℝ} (hs : Gᵀ = G) (hn : ∀ i, 0 < n i) {κ : ℝ}
    (hG : G *ᵥ n = fun _ => κ) : G = footCombo n κ (-G 0 1) (-G 0 2) (-G 1 2) := by
  have s01 : G 1 0 = G 0 1 := by simpa using congrFun (congrFun hs 0) 1
  have s02 : G 2 0 = G 0 2 := by simpa using congrFun (congrFun hs 0) 2
  have s12 : G 2 1 = G 1 2 := by simpa using congrFun (congrFun hs 1) 2
  have e0 := congrFun hG 0
  have e1 := congrFun hG 1
  have e2 := congrFun hG 2
  simp [mulVec, dotProduct, Fin.sum_univ_three] at e0 e1 e2
  rw [s01] at e1
  rw [s02, s12] at e2
  have h0 := (hn 0).ne'
  have h1 := (hn 1).ne'
  have h2 := (hn 2).ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [footCombo, Dn, Qab, vecMulVec_apply, s01, s02, s12]
    <;> field_simp
    <;> linarith

variable {κ l01 l02 l12 : ℝ}

theorem footCombo_symm : (footCombo n κ l01 l02 l12)ᵀ = footCombo n κ l01 l02 l12 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [footCombo, Dn, Qab, vecMulVec_apply] <;> (try ring) <;> simp

theorem footCombo_mulVec (hn : ∀ i, 0 < n i) :
    footCombo n κ l01 l02 l12 *ᵥ n = fun _ => κ := by
  have h0 := (hn 0).ne'
  have h1 := (hn 1).ne'
  have h2 := (hn 2).ne'
  ext i
  fin_cases i <;>
    simp [footCombo, Dn, Qab, mulVec, dotProduct, vecMulVec_apply, Fin.sum_univ_three,
      Matrix.diagonal_apply, Pi.single_apply] <;> field_simp <;> ring

theorem footCombo_offdiag_nonpos (hn : ∀ i, 0 < n i) (hl01 : 0 ≤ l01) (hl02 : 0 ≤ l02)
    (hl12 : 0 ≤ l12) (a b : Fin 3) (hab : a ≠ b) : footCombo n κ l01 l02 l12 a b ≤ 0 := by
  have p0 := hn 0
  have p1 := hn 1
  have p2 := hn 2
  fin_cases a <;> fin_cases b <;> try exact absurd rfl hab
  all_goals
    simp [footCombo, Dn, Qab, vecMulVec_apply]
  all_goals positivity

/-- The quadratic form of `footCombo`. -/
theorem footCombo_quad (hn : ∀ i, 0 < n i) (x : Fin 3 → ℝ) :
    x ⬝ᵥ (footCombo n κ l01 l02 l12 *ᵥ x)
      = κ * (x 0 ^ 2 / n 0 + x 1 ^ 2 / n 1 + x 2 ^ 2 / n 2)
        + l01 * ((n 1 * x 0 - n 0 * x 1) ^ 2 / (n 0 * n 1))
        + l02 * ((n 2 * x 0 - n 0 * x 2) ^ 2 / (n 0 * n 2))
        + l12 * ((n 2 * x 1 - n 1 * x 2) ^ 2 / (n 1 * n 2)) := by
  have h0 := (hn 0).ne'
  have h1 := (hn 1).ne'
  have h2 := (hn 2).ne'
  simp [footCombo, Dn, Qab, mulVec, dotProduct, vecMulVec_apply, Fin.sum_univ_three,
    Matrix.diagonal_apply, Pi.single_apply]
  field_simp
  ring

/-- **FG, easy direction.**  For `n > 0`, `κ > 0`, `λ ≥ 0`, `κ D_n + ∑ λ_ab Q_ab(n)` is positive
definite (and by `footCombo_offdiag_nonpos`, `footCombo_mulVec` obtuse with foot `n`). -/
theorem footCombo_posDef (hn : ∀ i, 0 < n i) (hκ : 0 < κ) (hl01 : 0 ≤ l01) (hl02 : 0 ≤ l02)
    (hl12 : 0 ≤ l12) : (footCombo n κ l01 l02 l12).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · simpa [Matrix.IsHermitian] using footCombo_symm (n := n) (κ := κ) (l01 := l01) (l02 := l02)
      (l12 := l12)
  · simp only [star_trivial]
    rw [footCombo_quad hn]
    have p0 := hn 0
    have p1 := hn 1
    have p2 := hn 2
    have hpos : 0 < x 0 ^ 2 / n 0 + x 1 ^ 2 / n 1 + x 2 ^ 2 / n 2 := by
      by_contra hcon
      apply hx
      have a0 : 0 ≤ x 0 ^ 2 / n 0 := by positivity
      have a1 : 0 ≤ x 1 ^ 2 / n 1 := by positivity
      have a2 : 0 ≤ x 2 ^ 2 / n 2 := by positivity
      have z0 : x 0 ^ 2 / n 0 = 0 := by linarith
      have z1 : x 1 ^ 2 / n 1 = 0 := by linarith
      have z2 : x 2 ^ 2 / n 2 = 0 := by linarith
      simp [p0.ne', p1.ne', p2.ne'] at z0 z1 z2
      ext i; fin_cases i <;> simp [z0, z1, z2]
    have := mul_pos hκ hpos
    have b01 : 0 ≤ l01 * ((n 1 * x 0 - n 0 * x 1) ^ 2 / (n 0 * n 1)) := by positivity
    have b02 : 0 ≤ l02 * ((n 2 * x 0 - n 0 * x 2) ^ 2 / (n 0 * n 2)) := by positivity
    have b12 : 0 ≤ l12 * ((n 2 * x 1 - n 1 * x 2) ^ 2 / (n 1 * n 2)) := by positivity
    linarith

end FG

end

end Minimality.CornerEQ
