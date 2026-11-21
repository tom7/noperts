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

/-- **Adjugate cross identity.** For symmetric `G`, `(adj G) a ⨯₃ (adj G) b = det G · G (a ⨯₃ b)`. -/
theorem adjCross {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : Gᵀ = G) (a b : Fin 3 → ℝ) :
    (adjugate G *ᵥ a) ⨯₃ (adjugate G *ᵥ b) = G.det • (G *ᵥ (a ⨯₃ b)) := by
  have hA : (adjugate G)ᵀ = adjugate G := by rw [adjugate_transpose, hG]
  have h1 := cross_mulVec_symm hA a b
  have h2 : adjugate (adjugate G) = G.det • G := by
    rw [adjugate_adjugate G (by simp)]; simp
  rw [h2, smul_mulVec] at h1
  exact h1

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

private theorem OC_of_det_ne_zero {G : Matrix (Fin 3) (Fin 3) ℝ} (hdet : G.det ≠ 0)
    (w v₁ v₂ v₃ : Fin 3 → ℝ) (hv : tri v₁ v₂ v₃ ≠ 0)
    (h1 : T G w v₁ = 0) (h2 : T G w v₂ = 0) (h3 : T G w v₃ = 0) : w = 0 := by
  have hGw : Gᵀ *ᵥ w = 0 := by
    have hlap := laplace (Gᵀ *ᵥ w) (Gᵀ *ᵥ w) v₁ v₂ v₃
    have hd : ∀ v : Fin 3 → ℝ, (Gᵀ *ᵥ w) ⬝ᵥ v = T G w v := fun v => by
      simp only [T, mulVec, dotProduct, transpose_apply, Fin.sum_univ_three]; ring
    rw [hd v₁, hd v₂, hd v₃, h1, h2, h3] at hlap
    simp only [zero_mul, add_zero] at hlap
    have hsq : (Gᵀ *ᵥ w) ⬝ᵥ (Gᵀ *ᵥ w) = 0 := (mul_eq_zero.mp hlap.symm).resolve_right hv
    exact dotProduct_self_eq_zero.mp hsq
  have hdetT : Gᵀ.det ≠ 0 := by rwa [det_transpose]
  have hinv : adjugate Gᵀ *ᵥ (Gᵀ *ᵥ w) = Gᵀ.det • w := by
    rw [mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec]
  rw [hGw, mulVec_zero] at hinv
  exact (smul_eq_zero.mp hinv.symm).resolve_left hdetT

/-- **OC.** If `G` is positive definite and `T(w, v_i) = 0` for three vectors with `[v₁ v₂ v₃] ≠ 0`,
then `w = 0`. -/
theorem OC {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : G.PosDef) (w v₁ v₂ v₃ : Fin 3 → ℝ)
    (hv : tri v₁ v₂ v₃ ≠ 0) (h1 : T G w v₁ = 0) (h2 : T G w v₂ = 0) (h3 : T G w v₃ = 0) :
    w = 0 :=
  OC_of_det_ne_zero hG.det_pos.ne' w v₁ v₂ v₃ hv h1 h2 h3

private theorem cross_eq_zero_of_cross_eq_zero (a b n : Fin 3 → ℝ) (hn : n ≠ 0)
    (ha : a ⨯₃ n = 0) (hb : b ⨯₃ n = 0) : a ⨯₃ b = 0 := by
  have ha0 := congrFun ha 0; have ha1 := congrFun ha 1; have ha2 := congrFun ha 2
  have hb0 := congrFun hb 0; have hb1 := congrFun hb 1; have hb2 := congrFun hb 2
  simp only [cross_apply, Pi.zero_apply] at ha0 ha1 ha2 hb0 hb1 hb2
  simp at ha0 ha1 ha2 hb0 hb1 hb2
  have hcomp : n 0 ≠ 0 ∨ n 1 ≠ 0 ∨ n 2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hn
    ext i; fin_cases i <;> simp [h.1, h.2.1, h.2.2]
  ext i
  rcases hcomp with h0 | h1 | h2
  · have hk : n 0 ^ 2 * (a ⨯₃ b) i = 0 := by
      have hA1 : a 1 * n 0 = a 0 * n 1 := by linarith
      have hA2 : a 2 * n 0 = a 0 * n 2 := by linarith
      have hB1 : b 1 * n 0 = b 0 * n 1 := by linarith
      have hB2 : b 2 * n 0 = b 0 * n 2 := by linarith
      fin_cases i <;> simp only [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      · calc n 0 ^ 2 * (a 1 * b 2 - a 2 * b 1)
            = (a 1 * n 0) * (b 2 * n 0) - (a 2 * n 0) * (b 1 * n 0) := by ring
          _ = 0 := by rw [hA1, hA2, hB1, hB2]; ring
      · calc n 0 ^ 2 * (a 2 * b 0 - a 0 * b 2)
            = n 0 * ((a 2 * n 0) * b 0 - a 0 * (b 2 * n 0)) := by ring
          _ = 0 := by rw [hA2, hB2]; ring
      · calc n 0 ^ 2 * (a 0 * b 1 - a 1 * b 0)
            = n 0 * (a 0 * (b 1 * n 0) - (a 1 * n 0) * b 0) := by ring
          _ = 0 := by rw [hA1, hB1]; ring
    exact (mul_eq_zero.mp hk).resolve_left (pow_ne_zero 2 h0)
  · have hk : n 1 ^ 2 * (a ⨯₃ b) i = 0 := by
      have hA0 : a 0 * n 1 = a 1 * n 0 := by linarith
      have hA2 : a 2 * n 1 = a 1 * n 2 := by linarith
      have hB0 : b 0 * n 1 = b 1 * n 0 := by linarith
      have hB2 : b 2 * n 1 = b 1 * n 2 := by linarith
      fin_cases i <;> simp only [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      · calc n 1 ^ 2 * (a 1 * b 2 - a 2 * b 1)
            = n 1 * (a 1 * (b 2 * n 1) - (a 2 * n 1) * b 1) := by ring
          _ = 0 := by rw [hA2, hB2]; ring
      · calc n 1 ^ 2 * (a 2 * b 0 - a 0 * b 2)
            = (a 2 * n 1) * (b 0 * n 1) - (a 0 * n 1) * (b 2 * n 1) := by ring
          _ = 0 := by rw [hA0, hA2, hB0, hB2]; ring
      · calc n 1 ^ 2 * (a 0 * b 1 - a 1 * b 0)
            = n 1 * ((a 0 * n 1) * b 1 - a 1 * (b 0 * n 1)) := by ring
          _ = 0 := by rw [hA0, hB0]; ring
    exact (mul_eq_zero.mp hk).resolve_left (pow_ne_zero 2 h1)
  · have hk : n 2 ^ 2 * (a ⨯₃ b) i = 0 := by
      have hA0 : a 0 * n 2 = a 2 * n 0 := by linarith
      have hA1 : a 1 * n 2 = a 2 * n 1 := by linarith
      have hB0 : b 0 * n 2 = b 2 * n 0 := by linarith
      have hB1 : b 1 * n 2 = b 2 * n 1 := by linarith
      fin_cases i <;> simp only [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      · calc n 2 ^ 2 * (a 1 * b 2 - a 2 * b 1)
            = n 2 * ((a 1 * n 2) * b 2 - a 2 * (b 1 * n 2)) := by ring
          _ = 0 := by rw [hA1, hB1]; ring
      · calc n 2 ^ 2 * (a 2 * b 0 - a 0 * b 2)
            = n 2 * (a 2 * (b 0 * n 2) - (a 0 * n 2) * b 2) := by ring
          _ = 0 := by rw [hA0, hB0]; ring
      · calc n 2 ^ 2 * (a 0 * b 1 - a 1 * b 0)
            = (a 0 * n 2) * (b 1 * n 2) - (a 1 * n 2) * (b 0 * n 2) := by ring
          _ = 0 := by rw [hA0, hA1, hB0, hB1]; ring
    exact (mul_eq_zero.mp hk).resolve_left (pow_ne_zero 2 h2)

private theorem Z0_of_symm_det_ne_zero {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : Gᵀ = G)
    (hdet : G.det ≠ 0) (u₁ u₂ v₁ v₂ : Fin 3 → ℝ)
    (hu : u₁ ⨯₃ u₂ ≠ 0) (hv : v₁ ⨯₃ v₂ ≠ 0)
    (h11 : T G u₁ v₁ = 0) (h12 : T G u₁ v₂ = 0)
    (h21 : T G u₂ v₁ = 0) (h22 : T G u₂ v₂ = 0) : False := by
  have hcross_ortho : ∀ x : Fin 3 → ℝ, x ⬝ᵥ v₁ = 0 → x ⬝ᵥ v₂ = 0 → x ⨯₃ (v₁ ⨯₃ v₂) = 0 := by
    intro x hx1 hx2
    ext i
    simp only [cross_apply, dotProduct, Fin.sum_univ_three, Pi.zero_apply] at hx1 hx2 ⊢
    fin_cases i <;> simp
    · linear_combination v₁ 0 * hx2 - v₂ 0 * hx1
    · linear_combination v₁ 1 * hx2 - v₂ 1 * hx1
    · linear_combination v₁ 2 * hx2 - v₂ 2 * hx1
  have hs : ∀ u v : Fin 3 → ℝ, (G *ᵥ u) ⬝ᵥ v = T G u v := fun u v => by
    rw [T, dotProduct_mulVec, ← vecMul_transpose, hG, dotProduct_comm]
  have hn1 : (G *ᵥ u₁) ⨯₃ (v₁ ⨯₃ v₂) = 0 :=
    hcross_ortho (G *ᵥ u₁) (by rw [hs, h11]) (by rw [hs, h12])
  have hn2 : (G *ᵥ u₂) ⨯₃ (v₁ ⨯₃ v₂) = 0 :=
    hcross_ortho (G *ᵥ u₂) (by rw [hs, h21]) (by rw [hs, h22])
  have hpar : (G *ᵥ u₁) ⨯₃ (G *ᵥ u₂) = 0 :=
    cross_eq_zero_of_cross_eq_zero (G *ᵥ u₁) (G *ᵥ u₂) (v₁ ⨯₃ v₂) hv hn1 hn2
  rw [cross_mulVec_symm hG] at hpar
  have hmul : G *ᵥ (adjugate G *ᵥ (u₁ ⨯₃ u₂)) = G.det • (u₁ ⨯₃ u₂) := by
    rw [mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec]
  rw [hpar, mulVec_zero] at hmul
  exact hu ((smul_eq_zero.mp hmul.symm).resolve_left hdet)

/-- **Z0.** For positive definite `G`, two non-parallel pairs `(u₁, u₂)` and `(v₁, v₂)` cannot have
all four `T(u_i, v_j) = 0`. -/
theorem Z0 {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : G.PosDef) (u₁ u₂ v₁ v₂ : Fin 3 → ℝ)
    (hu : u₁ ⨯₃ u₂ ≠ 0) (hv : v₁ ⨯₃ v₂ ≠ 0)
    (h11 : T G u₁ v₁ = 0) (h12 : T G u₁ v₂ = 0)
    (h21 : T G u₂ v₁ = 0) (h22 : T G u₂ v₂ = 0) : False :=
  Z0_of_symm_det_ne_zero (by simpa using hG.isHermitian.eq) hG.det_pos.ne' u₁ u₂ v₁ v₂ hu hv
    h11 h12 h21 h22

/-- **Z3.** `det [T(u_i, v_j)] = det G · [u₀ u₁ u₂] · [v₀ v₁ v₂]`. -/
theorem Z3 (G : Matrix (Fin 3) (Fin 3) ℝ) (u v : Fin 3 → Fin 3 → ℝ) :
    (Matrix.of fun i j => T G (u i) (v j)).det =
      G.det * tri (u 0) (u 1) (u 2) * tri (v 0) (v 1) (v 2) := by
  have hM : Matrix.of (fun i j => T G (u i) (v j)) = Matrix.of u * G * (Matrix.of v)ᵀ := by
    ext i j
    simp only [T, Matrix.mul_apply, Matrix.of_apply, transpose_apply, mulVec, dotProduct,
      Fin.sum_univ_three]
    ring
  rw [hM, det_mul, det_mul, det_transpose]
  simp only [tri, triple_product_eq_det]
  have hu : Matrix.of u = Matrix.of ![u 0, u 1, u 2] := by ext i j; fin_cases i <;> simp
  have hv : Matrix.of v = Matrix.of ![v 0, v 1, v 2] := by ext i j; fin_cases i <;> simp
  rw [hu, hv]
  show (Matrix.of ![u 0, u 1, u 2]).det * G.det * (Matrix.of ![v 0, v 1, v 2]).det =
    G.det * (Matrix.of ![u 0, u 1, u 2]).det * (Matrix.of ![v 0, v 1, v 2]).det
  ring

/-- **PD1** (1-line consequence of `OC` for `adjugate G`). If `G` is positive definite and
`P(n; f, g) = P(n; f, h) = P(n; g, h) = 0` with `[f g h] ≠ 0`, then `n = 0`. -/
theorem PD1 {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : G.PosDef) (n f g h : Fin 3 → ℝ)
    (hfgh : tri f g h ≠ 0)
    (h1 : P G n f g = 0) (h2 : P G n f h = 0) (h3 : P G n g h = 0) : n = 0 := by
  have hdet : (adjugate G).det ≠ 0 := by
    rw [det_adjugate, Fintype.card_fin]; exact pow_ne_zero 2 hG.det_pos.ne'
  have htri : tri (f ⨯₃ g) (f ⨯₃ h) (g ⨯₃ h) ≠ 0 := by
    have heq : tri (f ⨯₃ g) (f ⨯₃ h) (g ⨯₃ h) = tri f g h ^ 2 := by
      simp only [tri, dotProduct, cross_apply, Fin.sum_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      ring
    rw [heq]; exact pow_ne_zero 2 hfgh
  have hP : ∀ a b : Fin 3 → ℝ, P G n a b = T (adjugate G) n (a ⨯₃ b) := fun a b =>
    P_eq_H (by simpa using hG.isHermitian.eq) n a b
  exact OC_of_det_ne_zero hdet n (f ⨯₃ g) (f ⨯₃ h) (g ⨯₃ h) htri
    (by rwa [← hP]) (by rwa [← hP]) (by rwa [← hP])

/-- **PD0** (1-line consequence of `Z0` for `adjugate G`). For positive definite `G`, non-parallel
normals `ns, nt` cannot both kill two non-parallel bivectors `f ⨯₃ g` and `f' ⨯₃ g'`. -/
theorem PD0 {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : G.PosDef)
    (ns nt f g f' g' : Fin 3 → ℝ)
    (hn : ns ⨯₃ nt ≠ 0) (hfg : (f ⨯₃ g) ⨯₃ (f' ⨯₃ g') ≠ 0)
    (h1 : P G ns f g = 0) (h2 : P G ns f' g' = 0)
    (h3 : P G nt f g = 0) (h4 : P G nt f' g' = 0) : False := by
  have hGs : Gᵀ = G := by simpa using hG.isHermitian.eq
  have hA : (adjugate G)ᵀ = adjugate G := by rw [adjugate_transpose, hGs]
  have hdet : (adjugate G).det ≠ 0 := by
    rw [det_adjugate, Fintype.card_fin]; exact pow_ne_zero 2 hG.det_pos.ne'
  have hP : ∀ n a b : Fin 3 → ℝ, P G n a b = T (adjugate G) n (a ⨯₃ b) := fun n a b =>
    P_eq_H hGs n a b
  exact Z0_of_symm_det_ne_zero hA hdet ns nt (f ⨯₃ g) (f' ⨯₃ g') hn hfg
    (by rwa [← hP]) (by rwa [← hP]) (by rwa [← hP]) (by rwa [← hP])

/-- **BI (Bianchi identity for `H`, 1-line consequence of `N4` for `adjugate G`).** -/
theorem BI {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : Gᵀ = G) (a b c d : Fin 3 → ℝ) :
    H G (a ⨯₃ b) (c ⨯₃ d) - H G (a ⨯₃ c) (b ⨯₃ d) + H G (a ⨯₃ d) (b ⨯₃ c) = 0 := by
  have hA : (adjugate G)ᵀ = adjugate G := by rw [adjugate_transpose, hG]
  have hHT : ∀ x y : Fin 3 → ℝ, H G x y = T (adjugate G) x y := fun x y => by
    rw [H, T, dotProduct_mulVec, ← vecMul_transpose, hA, dotProduct_comm]
  simp only [hHT]
  exact N4 hA a b c d

end Minimality.Coupling
