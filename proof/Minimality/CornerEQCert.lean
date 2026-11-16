module

public import Mathlib
public import Minimality.RimCellConv

/-!
# Lemma D (strict form) and the EQ certificate schema

**Lemma D.**  Let `S`, `G` be real `n × n` matrices (`n` any finite index type) with `S_aa > 0`,
`S_ab < √S_aa √S_bb` for `a ≠ b`, `G` positive semidefinite and nonzero with `G_ab ≤ 0` for `a ≠ b`.
Then `∑_{a,b} S_ab G_ab > 0` (`pairing_pos_of_psd_obtuse`; non-strict form
`pairing_nonneg_of_psd_obtuse`).  Write `S = s sᵀ + N`, `s_a = √S_aa`; `sᵀ G s ≥ 0` by
semidefiniteness, `N · G = ∑_{a≠b} N_ab G_ab ≥ 0` with equality only for diagonal `G`, and a nonzero
diagonal PSD `G` has a positive entry.  Symmetry of `S` is not used (only the pairing with `G`).

**EQ certificate schema.**  A finite family of leaves `i` (`EQLeaf`), each with a rim `y_i`, a point
`ρ_i` of the closed cell of `y_i`, a point `σ_i` of the closed cone `Conv(y_i)` and a weight
`λ_i ≥ 0`, gives the matrix `S = - ∑ λ_i sym(σ_i ρ_iᵀ)` (`certMatrix`).  Then
`∑ S_ab G_ab = - ∑ λ_i (G σ_i) ⬝ ρ_i` for symmetric `G` (`pairing_certMatrix`).
* `isRupert_of_eq_cert`: if `S` satisfies the strict conditions of Lemma D, every shape `E Y` with
  `det E > 0` and obtuse Gram matrix `Eᵀ E` (off-diagonal entries `≤ 0`) is Rupert.  Only Lemma D's
  hypotheses on `S` are used; no other obtuseness hypothesis.
* `isRupert_of_eq_cert_posDef`: if `S` is positive definite, the same certificate works for every
  `E` with `det E > 0`, obtuse or not (Lemma D replaced by plain positive definiteness).
-/

set_option autoImplicit false

namespace Minimality.CornerEQ

open Finset Matrix
open Minimality.RimCell

@[expose] public section

section LemmaD

variable {n : Type*} [Fintype n]

omit [Fintype n] in
/-- The two splitting facts: `(S_ab - s_a s_b) G_ab ≥ 0` termwise, `s = √ diag S`. -/
theorem split_term_nonneg (S G : Matrix n n ℝ) (hSd : ∀ a, 0 ≤ S a a)
    (hSo : ∀ a b, a ≠ b → S a b ≤ √(S a a) * √(S b b))
    (hGo : ∀ a b, a ≠ b → G a b ≤ 0) (a b : n) :
    0 ≤ (S a b - √(S a a) * √(S b b)) * G a b := by
  by_cases h : a = b
  · subst h
    rw [Real.mul_self_sqrt (hSd a)]; simp
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (hSo a b h)) (hGo a b h)

theorem pairing_split (S G : Matrix n n ℝ) :
    ∑ a, ∑ b, S a b * G a b =
      ∑ a, ∑ b, (S a b - √(S a a) * √(S b b)) * G a b +
        ∑ a, ∑ b, √(S a a) * √(S b b) * G a b := by
  rw [← sum_add_distrib]
  refine sum_congr rfl fun a _ => ?_
  rw [← sum_add_distrib]
  exact sum_congr rfl fun b _ => by ring

theorem rank_one_nonneg (G : Matrix n n ℝ) (hG : G.PosSemidef) (s : n → ℝ) :
    0 ≤ ∑ a, ∑ b, s a * s b * G a b := by
  have h := hG.dotProduct_mulVec_nonneg s
  have : ∑ a, ∑ b, s a * s b * G a b = star s ⬝ᵥ (G *ᵥ s) := by
    simp only [dotProduct, mulVec, star_trivial, Finset.mul_sum]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
  rw [this]; exact h

/-- **Lemma D, non-strict form.** -/
theorem pairing_nonneg_of_psd_obtuse (S G : Matrix n n ℝ) (hSd : ∀ a, 0 ≤ S a a)
    (hSo : ∀ a b, a ≠ b → S a b ≤ √(S a a) * √(S b b))
    (hG : G.PosSemidef) (hGo : ∀ a b, a ≠ b → G a b ≤ 0) :
    0 ≤ ∑ a, ∑ b, S a b * G a b := by
  rw [pairing_split]
  refine add_nonneg (sum_nonneg fun a _ => sum_nonneg fun b _ => ?_) (rank_one_nonneg G hG _)
  exact split_term_nonneg S G hSd hSo hGo a b

variable [DecidableEq n]

/-- **Lemma D, strict form.**  `S_aa > 0`, `S_ab < √S_aa √S_bb` off the diagonal, `G` positive
semidefinite, nonzero, with nonpositive off-diagonal entries: the Frobenius pairing is positive. -/
theorem pairing_pos_of_psd_obtuse (S G : Matrix n n ℝ) (hSd : ∀ a, 0 < S a a)
    (hSo : ∀ a b, a ≠ b → S a b < √(S a a) * √(S b b))
    (hG : G.PosSemidef) (hG0 : G ≠ 0) (hGo : ∀ a b, a ≠ b → G a b ≤ 0) :
    0 < ∑ a, ∑ b, S a b * G a b := by
  have hSd' : ∀ a, 0 ≤ S a a := fun a => (hSd a).le
  have hSo' : ∀ a b, a ≠ b → S a b ≤ √(S a a) * √(S b b) := fun a b h => (hSo a b h).le
  have hN := split_term_nonneg S G hSd' hSo' hGo
  have hA : 0 ≤ ∑ a, ∑ b, (S a b - √(S a a) * √(S b b)) * G a b :=
    sum_nonneg fun a _ => sum_nonneg fun b _ => hN a b
  have hB := rank_one_nonneg G hG (fun a => √(S a a))
  rw [pairing_split]
  by_cases h : ∃ a b, a ≠ b ∧ G a b ≠ 0
  · obtain ⟨a₀, b₀, hne, hne0⟩ := h
    have hlt : G a₀ b₀ < 0 := lt_of_le_of_ne (hGo _ _ hne) hne0
    have hpos : 0 < (S a₀ b₀ - √(S a₀ a₀) * √(S b₀ b₀)) * G a₀ b₀ :=
      mul_pos_of_neg_of_neg (sub_neg.2 (hSo _ _ hne)) hlt
    have hrow : 0 < ∑ b, (S a₀ b - √(S a₀ a₀) * √(S b b)) * G a₀ b :=
      sum_pos' (fun b _ => hN a₀ b) ⟨b₀, mem_univ _, hpos⟩
    have : 0 < ∑ a, ∑ b, (S a b - √(S a a) * √(S b b)) * G a b :=
      sum_pos' (fun a _ => sum_nonneg fun b _ => hN a b) ⟨a₀, mem_univ _, hrow⟩
    linarith
  · push Not at h
    have hdiag : ∀ a, G a a ≠ 0 → 0 < G a a := fun a ha => lt_of_le_of_ne hG.diag_nonneg (Ne.symm ha)
    obtain ⟨a₀, ha₀⟩ : ∃ a, G a a ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hG0
      ext a b
      by_cases hab : a = b
      · subst hab; exact hc a
      · exact h a b hab
    have hred : ∑ a, ∑ b, √(S a a) * √(S b b) * G a b = ∑ a, √(S a a) * √(S a a) * G a a := by
      refine sum_congr rfl fun a _ => ?_
      rw [Finset.sum_eq_single a]
      · intro b _ hb; rw [h a b (Ne.symm hb)]; simp
      · simp
    have hss : ∀ a, 0 < √(S a a) * √(S a a) := fun a => by
      rw [Real.mul_self_sqrt (hSd' a)]; exact hSd a
    have : 0 < ∑ a, √(S a a) * √(S a a) * G a a :=
      sum_pos' (fun a _ => mul_nonneg (hss a).le hG.diag_nonneg)
        ⟨a₀, mem_univ _, mul_pos (hss a₀) (hdiag a₀ ha₀)⟩
    rw [hred]; linarith

end LemmaD

section Schema

/-- One leaf of an EQ certificate over the vertex set `Y`: a rim `y` of `Y` (`k ≥ 3` distinct
points of `Y` in cyclic order), a point `ρ` of the closed cell of `y`, a point `σ` of the closed cone
`Conv(y)` and a weight `λ ≥ 0`. -/
structure EQLeaf (Y : Finset (Fin 3 → ℝ)) where
  k : ℕ
  hk : 3 ≤ k
  y : ZMod k → Fin 3 → ℝ
  hy : Function.Injective y
  hyY : ∀ j, y j ∈ Y
  ρ : Fin 3 → ℝ
  σ : Fin 3 → ℝ
  hρ : ρ ∈ closure (cellSet Y y)
  hσ : σ ∈ closure (convSet y)
  lam : ℝ
  hlam : 0 ≤ lam

variable {Y : Finset (Fin 3 → ℝ)} {ι : Type*} [Fintype ι]

/-- The certificate matrix `S_ab = - ∑_i λ_i (σ_i,a ρ_i,b + σ_i,b ρ_i,a) / 2`. -/
noncomputable def certMatrix (L : ι → EQLeaf Y) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun a b => - ∑ i, (L i).lam * ((L i).σ a * (L i).ρ b + (L i).σ b * (L i).ρ a) / 2

theorem leaf_pairing (G : Matrix (Fin 3) (Fin 3) ℝ) (hsym : ∀ a b, G a b = G b a)
    (lam : ℝ) (σ ρ : Fin 3 → ℝ) :
    ∑ a, ∑ b, lam * ((σ a * ρ b + σ b * ρ a) / 2 * G a b) = lam * ((G *ᵥ σ) ⬝ᵥ ρ) := by
  simp only [Fin.sum_univ_three, dotProduct, mulVec, Fin.sum_univ_three]
  rw [hsym 1 0, hsym 2 0, hsym 2 1]
  ring

/-- For symmetric `G`: `∑ S_ab G_ab = - ∑ λ_i (G σ_i) ⬝ ρ_i`. -/
theorem pairing_certMatrix (L : ι → EQLeaf Y) (G : Matrix (Fin 3) (Fin 3) ℝ)
    (hsym : ∀ a b, G a b = G b a) :
    ∑ a, ∑ b, certMatrix L a b * G a b = - ∑ i, (L i).lam * ((G *ᵥ (L i).σ) ⬝ᵥ (L i).ρ) := by
  have h1 : ∀ a b, certMatrix L a b * G a b =
      - ∑ i, (L i).lam * (((L i).σ a * (L i).ρ b + (L i).σ b * (L i).ρ a) / 2 * G a b) := by
    intro a b
    simp only [certMatrix, neg_mul, Finset.sum_mul, mul_div_assoc, mul_assoc]
  have h2 : ∀ i, ∑ a, ∑ b, (L i).lam * (((L i).σ a * (L i).ρ b + (L i).σ b * (L i).ρ a) / 2 *
      G a b) = (L i).lam * ((G *ᵥ (L i).σ) ⬝ᵥ (L i).ρ) := fun i =>
    leaf_pairing G hsym _ _ _
  simp only [h1, Finset.sum_neg_distrib]
  congr 1
  calc _ = ∑ a, ∑ i, ∑ b, (L i).lam * (((L i).σ a * (L i).ρ b + (L i).σ b * (L i).ρ a) / 2 *
        G a b) := sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i, ∑ a, ∑ b, (L i).lam * (((L i).σ a * (L i).ρ b + (L i).σ b * (L i).ρ a) / 2 *
        G a b) := Finset.sum_comm
    _ = _ := sum_congr rfl fun i _ => h2 i

theorem gram_symm (E : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3) :
    (Eᵀ * E) a b = (Eᵀ * E) b a := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  exact sum_congr rfl fun c _ => mul_comm _ _

/-- From a positive pairing to a leaf with `(G σ_i) ⬝ ρ_i < 0`, hence to Rupert. -/
theorem isRupert_of_neg_leaf (L : ι → EQLeaf Y) (E : Matrix (Fin 3) (Fin 3) ℝ)
    (hE : 0 < E.det) (hpos : 0 < ∑ a, ∑ b, certMatrix L a b * (Eᵀ * E) a b) :
    IsRupert (Y.image (emb E)) := by
  rw [pairing_certMatrix L _ (gram_symm E)] at hpos
  obtain ⟨i, hi⟩ : ∃ i, (L i).lam * (((Eᵀ * E) *ᵥ (L i).σ) ⬝ᵥ (L i).ρ) < 0 := by
    by_contra hc
    push Not at hc
    have := sum_nonneg fun i (_ : i ∈ (univ : Finset ι)) => hc i
    linarith
  have hneg : ((Eᵀ * E) *ᵥ (L i).σ) ⬝ᵥ (L i).ρ < 0 := by
    by_contra hc
    push Not at hc
    exact absurd hi (not_lt.2 (mul_nonneg (L i).hlam hc))
  have : NeZero (L i).k := ⟨by have := (L i).hk; omega⟩
  exact isRupert_of_conv_pair_closure (L i).hk E hE (L i).y (L i).hy Y (L i).hyY (L i).hρ
    (L i).hσ hneg

theorem gram_psd (E : Matrix (Fin 3) (Fin 3) ℝ) : (Eᵀ * E).PosSemidef := by
  simpa using Matrix.posSemidef_conjTranspose_mul_self E

theorem gram_ne_zero (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det) : Eᵀ * E ≠ 0 := by
  intro h
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_zero] at this
  nlinarith

/-- **EQ certificate schema.**  If the matrix `S = - ∑ λ_i sym(σ_i ρ_iᵀ)` satisfies the strict
conditions of Lemma D, then every `E` with `det E > 0` and obtuse Gram matrix `Eᵀ E` makes `E Y`
Rupert.  (Only `det E > 0` and the sign pattern of the Gram matrix are used.) -/
theorem isRupert_of_eq_cert (L : ι → EQLeaf Y)
    (hSd : ∀ a, 0 < certMatrix L a a)
    (hSo : ∀ a b, a ≠ b → certMatrix L a b < √(certMatrix L a a) * √(certMatrix L b b))
    (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det)
    (hGo : ∀ a b, a ≠ b → (Eᵀ * E) a b ≤ 0) :
    IsRupert (Y.image (emb E)) :=
  isRupert_of_neg_leaf L E hE
    (pairing_pos_of_psd_obtuse _ _ hSd hSo (gram_psd E) (gram_ne_zero E hE) hGo)

/-- **PD variant.**  If `S = - ∑ λ_i sym(σ_i ρ_iᵀ)` is positive definite, the same certificate
works for every `E` with `det E > 0`: no obtuseness is needed. -/
theorem isRupert_of_eq_cert_posDef (L : ι → EQLeaf Y) (hS : (certMatrix L).PosDef)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det) :
    IsRupert (Y.image (emb E)) := by
  apply isRupert_of_neg_leaf L E hE
  have hinj : Function.Injective E.vecMul := by
    rw [Matrix.vecMul_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.2 hE.ne'
  have hP := (hS.mul_mul_conjTranspose_same hinj).trace_pos
  have : (E * certMatrix L * Eᴴ).trace = ∑ a, ∑ b, certMatrix L a b * (Eᵀ * E) a b := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.conjTranspose_apply, Matrix.transpose_apply, star_trivial]
    ring
  rwa [this] at hP

end Schema

end

end Minimality.CornerEQ
