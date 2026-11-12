module

public import Mathlib

/-!
# The coupling identities (N4, M1, M2, M4, M5, Z2, Bianchi, P-row)

Purely algebraic identities about a symmetric `3 × 3` matrix `G` (the metric Gram matrix) and
vectors `a, b, … : Fin 3 → ℝ` (normals, edges, line views), with `⨯₃` the cross product.  Notation:

* `T G u v = u ⬝ᵥ G v` (the sign atoms `T` of the encoder),
* `H G a b = (adj G a) ⬝ᵥ b` (the adjugate form `H = adj G`),
* `P G n f g = n ⬝ᵥ (G f ⨯₃ G g) = det (n, G f, G g)`.

* `T_minor`, `M1`: `T(u₁,f)T(u₂,g) - T(u₁,g)T(u₂,f) = (u₁ × u₂) ⬝ᵥ (Gf × Gg)`, and `λ P(f,g)` when
  `u₁ × u₂ = λ n`.
* `M4`: the Laplace expansion `T(u,v₁)P(v₂,v₃) + T(u,v₂)P(v₃,v₁) + T(u,v₃)P(v₁,v₂) = det G (n ⬝ᵥ u) [v₁ v₂ v₃]`.
* `Z2`: for `u₁ × u₂ = λ_u n`, `v₁ × v₂ = λ_v n`, the minor of `T` equals `λ_u λ_v H(n,n)`.
* `adjMinor` (M5, M6, M2g and the like are instances): `H(a,c)H(b,d) - H(a,d)H(b,c) = det G · T(a × b, c × d)`.
* `M2`: `P(n_s; f,g)P(n_t; f,h) - P(n_t; f,g)P(n_s; f,h) = det G [f g h] T(n_s × n_t, f)`.
* `N4`: `T(a×b, c×d) - T(a×c, b×d) + T(a×d, b×c) = 0` for symmetric `G`; the Bianchi identity of
  `H` (BI) is the same statement for `G := H = adj G'`.
* `pRow`: for a linear form `φ` and four vectors, `Σ (-1)^i [f_others] φ(f_i) = 0` (the P-row
  relation: `φ = P(·; g)`).
-/

@[expose] public section

set_option autoImplicit false

namespace Minimality.Coupling

open Matrix

/-- The sign atom `T(u, v) = u ⬝ᵥ G v`. -/
def T (G : Matrix (Fin 3) (Fin 3) ℝ) (u v : Fin 3 → ℝ) : ℝ := u ⬝ᵥ (G *ᵥ v)

/-- The atom `P(n; f, g) = n ⬝ᵥ (G f ⨯₃ G g)`. -/
def P (G : Matrix (Fin 3) (Fin 3) ℝ) (n f g : Fin 3 → ℝ) : ℝ :=
  n ⬝ᵥ ((G *ᵥ f) ⨯₃ (G *ᵥ g))

/-- The adjugate form `H(a, b) = (adj G a) ⬝ᵥ b`. -/
def H (G : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3 → ℝ) : ℝ := (adjugate G *ᵥ a) ⬝ᵥ b

/-- The triple product `[a b c]`. -/
def tri (a b c : Fin 3 → ℝ) : ℝ := a ⬝ᵥ (b ⨯₃ c)

theorem T_minor (G : Matrix (Fin 3) (Fin 3) ℝ) (u₁ u₂ f g : Fin 3 → ℝ) :
    T G u₁ f * T G u₂ g - T G u₁ g * T G u₂ f = (u₁ ⨯₃ u₂) ⬝ᵥ ((G *ᵥ f) ⨯₃ (G *ᵥ g)) := by
  rw [cross_dot_cross]; simp only [T]

/-- **M1.** -/
theorem M1 (G : Matrix (Fin 3) (Fin 3) ℝ) (u₁ u₂ n f g : Fin 3 → ℝ) (l : ℝ)
    (h : u₁ ⨯₃ u₂ = l • n) :
    T G u₁ f * T G u₂ g - T G u₁ g * T G u₂ f = l * P G n f g := by
  rw [T_minor, h, smul_dotProduct, smul_eq_mul]; rfl

/-- Laplace: `Σ_cyc x₁ (x₂ × x₃)ᵀ = [x₁ x₂ x₃] I`, contracted with `u` and `n`. -/
theorem laplace (u n x₁ x₂ x₃ : Fin 3 → ℝ) :
    (u ⬝ᵥ x₁) * (n ⬝ᵥ (x₂ ⨯₃ x₃)) + (u ⬝ᵥ x₂) * (n ⬝ᵥ (x₃ ⨯₃ x₁)) +
      (u ⬝ᵥ x₃) * (n ⬝ᵥ (x₁ ⨯₃ x₂)) = (u ⬝ᵥ n) * tri x₁ x₂ x₃ := by
  simp only [tri, dotProduct, cross_apply, Fin.sum_univ_three]
  simp
  ring

theorem tri_mulVec (G : Matrix (Fin 3) (Fin 3) ℝ) (v₁ v₂ v₃ : Fin 3 → ℝ) :
    tri (G *ᵥ v₁) (G *ᵥ v₂) (G *ᵥ v₃) = G.det * tri v₁ v₂ v₃ := by
  simp only [tri, triple_product_eq_det]
  have : (Matrix.of ![G *ᵥ v₁, G *ᵥ v₂, G *ᵥ v₃] : Matrix (Fin 3) (Fin 3) ℝ) =
      Matrix.of ![v₁, v₂, v₃] * Gᵀ := by
    ext i j
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_three] <;> ring
  rw [show (![G *ᵥ v₁, G *ᵥ v₂, G *ᵥ v₃] : Fin 3 → Fin 3 → ℝ) = (Matrix.of ![G *ᵥ v₁, G *ᵥ v₂, G *ᵥ v₃]) from rfl,
    this, det_mul, det_transpose, mul_comm]
  rfl

/-- **M4 (Laplace).** -/
theorem M4 (G : Matrix (Fin 3) (Fin 3) ℝ) (u n v₁ v₂ v₃ : Fin 3 → ℝ) :
    T G u v₁ * P G n v₂ v₃ + T G u v₂ * P G n v₃ v₁ + T G u v₃ * P G n v₁ v₂ =
      G.det * (u ⬝ᵥ n) * tri v₁ v₂ v₃ := by
  have h := laplace u n (G *ᵥ v₁) (G *ᵥ v₂) (G *ᵥ v₃)
  rw [tri_mulVec] at h
  unfold T P
  linarith

/-- The cofactor identity for symmetric `G`: `G v × G w = adj G (v × w)`. -/
theorem cross_mulVec_symm {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : Gᵀ = G) (v w : Fin 3 → ℝ) :
    (G *ᵥ v) ⨯₃ (G *ᵥ w) = adjugate G *ᵥ (v ⨯₃ w) := by
  have h : ∀ i j, G i j = G j i := fun i j => by
    have := congrFun (congrFun hG i) j; simpa [transpose_apply] using this.symm
  have h10 := h 1 0; have h20 := h 2 0; have h21 := h 2 1
  ext i
  fin_cases i <;>
    simp [cross_apply, mulVec, dotProduct, Fin.sum_univ_three, adjugate_fin_three, h10, h20, h21] <;>
    ring

/-- `P(n; f, g) = H(n, f × g)` for symmetric `G`. -/
theorem P_eq_H {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : Gᵀ = G) (n f g : Fin 3 → ℝ) :
    P G n f g = n ⬝ᵥ (adjugate G *ᵥ (f ⨯₃ g)) := by
  rw [P, cross_mulVec_symm hG]

/-- **Z2.** -/
theorem Z2 {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : Gᵀ = G) (u₁ u₂ v₁ v₂ n : Fin 3 → ℝ)
    (lu lv : ℝ) (hu : u₁ ⨯₃ u₂ = lu • n) (hv : v₁ ⨯₃ v₂ = lv • n) :
    T G u₁ v₁ * T G u₂ v₂ - T G u₁ v₂ * T G u₂ v₁ = lu * lv * H G n n := by
  rw [M1 G u₁ u₂ n v₁ v₂ lu hu, P_eq_H hG, hv, mulVec_smul, dotProduct_smul, smul_eq_mul, H,
    dotProduct_comm]
  ring

theorem T_smul_right (G : Matrix (Fin 3) (Fin 3) ℝ) (u v : Fin 3 → ℝ) (k : ℝ) :
    T G u (k • v) = k * T G u v := by
  simp [T, mulVec_smul, dotProduct_smul]

/-- The adjugate minors (the common tool of M5, M6, M2g): for symmetric `G`,
`H(a,c) H(b,d) - H(a,d) H(b,c) = det G · T(a × b, c × d)`. -/
theorem adjMinor {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : Gᵀ = G) (a b c d : Fin 3 → ℝ) :
    H G a c * H G b d - H G a d * H G b c = G.det * T G (a ⨯₃ b) (c ⨯₃ d) := by
  have hA : (adjugate G)ᵀ = adjugate G := by rw [adjugate_transpose, hG]
  have h1 := cross_mulVec_symm hA a b
  have h2 : adjugate (adjugate G) = G.det • G := by
    rw [adjugate_adjugate G (by simp)]; simp
  rw [h2] at h1
  have h3 := cross_dot_cross (adjugate G *ᵥ a) (adjugate G *ᵥ b) c d
  rw [h1] at h3
  simp only [H, T]
  have hs : ∀ x y : Fin 3 → ℝ, (G *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (G *ᵥ y) := by
    intro x y; rw [dotProduct_mulVec, ← vecMul_transpose, hG]
  rw [smul_mulVec, smul_dotProduct, smul_eq_mul, hs] at h3
  linarith

/-- **M2.** `P(n_s; f,g) P(n_t; f,h) - P(n_t; f,g) P(n_s; f,h) = det G [f g h] T(n_s × n_t, f)`. -/
theorem M2 {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : Gᵀ = G) (ns nt f g h : Fin 3 → ℝ) :
    P G ns f g * P G nt f h - P G nt f g * P G ns f h =
      G.det * tri f g h * T G (ns ⨯₃ nt) f := by
  have h1 := adjMinor hG ns nt (f ⨯₃ g) (f ⨯₃ h)
  have h2 : (f ⨯₃ g) ⨯₃ (f ⨯₃ h) = tri f g h • f := by
    simp only [tri, dotProduct, cross_apply, Fin.sum_univ_three]
    ext i; fin_cases i <;> simp <;> ring
  rw [h2, T_smul_right] at h1
  have hA : (adjugate G)ᵀ = adjugate G := by rw [adjugate_transpose, hG]
  have hs : ∀ x y : Fin 3 → ℝ, (adjugate G *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (adjugate G *ᵥ y) := by
    intro x y; rw [dotProduct_mulVec, ← vecMul_transpose, hA]
  have hP : ∀ n u v : Fin 3 → ℝ, P G n u v = H G n (u ⨯₃ v) := by
    intro n u v; rw [P_eq_H hG, H, hs]
  simp only [hP]
  linarith

/-- **N4.** For symmetric `G` and any four vectors (the outward normals of four faces):
`T(a×b, c×d) - T(a×c, b×d) + T(a×d, b×c) = 0`.  The same statement for `G := H = adj G'` is the
Bianchi identity of `H` (BI). -/
theorem N4 {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : Gᵀ = G) (a b c d : Fin 3 → ℝ) :
    T G (a ⨯₃ b) (c ⨯₃ d) - T G (a ⨯₃ c) (b ⨯₃ d) + T G (a ⨯₃ d) (b ⨯₃ c) = 0 := by
  have h : ∀ i j, G i j = G j i := fun i j => by
    have := congrFun (congrFun hG i) j; simpa [transpose_apply] using this.symm
  have h10 := h 1 0; have h20 := h 2 0; have h21 := h 2 1
  simp only [T, cross_apply, mulVec, dotProduct, Fin.sum_univ_three, h10, h20, h21]
  simp
  ring

/-- Cramer's rule for four vectors in `ℝ³`: `Σ (-1)^i [f_others] f_i = 0`. -/
theorem cramer4 (f₁ f₂ f₃ f₄ : Fin 3 → ℝ) :
    tri f₂ f₃ f₄ • f₁ - tri f₁ f₃ f₄ • f₂ + tri f₁ f₂ f₄ • f₃ - tri f₁ f₂ f₃ • f₄ = 0 := by
  ext i
  simp only [tri, dotProduct, cross_apply, Fin.sum_univ_three]
  fin_cases i <;> simp <;> ring

/-- **P-row.**  For a linear form `φ` (for instance `f ↦ P G n f g`) on four vectors:
`[f₂ f₃ f₄] φ(f₁) - [f₁ f₃ f₄] φ(f₂) + [f₁ f₂ f₄] φ(f₃) - [f₁ f₂ f₃] φ(f₄) = 0`. -/
theorem pRow (φ : (Fin 3 → ℝ) →ₗ[ℝ] ℝ) (f₁ f₂ f₃ f₄ : Fin 3 → ℝ) :
    tri f₂ f₃ f₄ * φ f₁ - tri f₁ f₃ f₄ * φ f₂ + tri f₁ f₂ f₄ * φ f₃ - tri f₁ f₂ f₃ * φ f₄ = 0 := by
  have := congrArg φ (cramer4 f₁ f₂ f₃ f₄)
  simpa [map_add, map_sub, map_smul] using this

end Minimality.Coupling
