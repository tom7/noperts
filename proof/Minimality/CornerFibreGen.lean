module

public import Mathlib
public import Minimality.CornerFibre

/-!
# The generator test and the anti-ordered literal: Lemmas GEN and AO

Source: `CORNER-EQ-IDEAS2-FABLE.md` 3.1.  Namespace `Minimality.CornerEQ`, `Fin 3`.

* `pair S G = ∑ᵢⱼ S_ij G_ij` is the linear functional of a matrix `S`; the literal `(G σ)⬝ρ` is
  `pair (ρσᵀ) G` (`pair_vecMulVec`).
* `FootFibre n G`: `G` positive definite, obtuse, `G n = κ 1` for some `κ`.  `footFibre_iff`: these are
  exactly `κ D_n + ∑ λ_ab Q_ab(n)`, `κ > 0`, `λ ≥ 0` (FG both ways).
* **Lemma GEN** (`gen_test`), both directions: `pair S G > 0` on the whole fibre iff `pair S D_n > 0` and
  `pair S Q_ab(n) ≥ 0` for the three pairs.  `gen_test_of_gens` is the direction used to certify
  (generators to fibre); `gen_gens_of_test` the converse (necessity).  Explicit generator values:
  `pair_Dn`, `pair_Qab_vecMulVec`.  No symmetry of `S` is needed.
* **Lemma AO** (`ao_literal`), both directions: `(G σ)⬝ρ < 0` on the whole fibre iff
  `∑ ρ_a σ_a / n_a < 0` and `(ρ_a/n_a - ρ_b/n_b)(σ_a/n_a - σ_b/n_b) ≤ 0` for the three pairs.
  `ao_of_conditions` is the "if" direction (certifies leaves).  Positivity of `n` is the only hypothesis.
-/

set_option autoImplicit false

namespace Minimality.CornerEQ

open Finset Matrix

@[expose] public section

/-- The linear functional `G ↦ ∑ S_ij G_ij`. -/
def pair (S G : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := ∑ i, ∑ j, S i j * G i j

theorem pair_add (S A B : Matrix (Fin 3) (Fin 3) ℝ) : pair S (A + B) = pair S A + pair S B := by
  simp [pair, mul_add, Finset.sum_add_distrib]

theorem pair_smul (S A : Matrix (Fin 3) (Fin 3) ℝ) (c : ℝ) : pair S (c • A) = c * pair S A := by
  simp [pair, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem pair_neg_left (S G : Matrix (Fin 3) (Fin 3) ℝ) : pair ((-1 : ℝ) • S) G = - pair S G := by
  simp [pair]

theorem pair_vecMulVec (ρ σ : Fin 3 → ℝ) (G : Matrix (Fin 3) (Fin 3) ℝ) :
    pair (vecMulVec ρ σ) G = (G *ᵥ σ) ⬝ᵥ ρ := by
  simp only [pair, vecMulVec_apply, mulVec, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem pair_footCombo (S : Matrix (Fin 3) (Fin 3) ℝ) (n : Fin 3 → ℝ) (κ l01 l02 l12 : ℝ) :
    pair S (footCombo n κ l01 l02 l12)
      = κ * pair S (Dn n) + l01 * pair S (Qab n 0 1) + l02 * pair S (Qab n 0 2)
        + l12 * pair S (Qab n 1 2) := by
  simp only [footCombo, pair_add, pair_smul]

theorem pair_Dn (S : Matrix (Fin 3) (Fin 3) ℝ) (n : Fin 3 → ℝ) :
    pair S (Dn n) = S 0 0 / n 0 + S 1 1 / n 1 + S 2 2 / n 2 := by
  simp [pair, Dn, Fin.sum_univ_three, Matrix.diagonal_apply, div_eq_mul_inv]

theorem pair_vecMulVec_vecMulVec (ρ σ p q : Fin 3 → ℝ) :
    pair (vecMulVec ρ σ) (vecMulVec p q) = (ρ ⬝ᵥ p) * (σ ⬝ᵥ q) := by
  simp [pair, vecMulVec_apply, dotProduct, Fin.sum_univ_three]
  ring

/-- Explicit generator values for a rank-one `S = ρσᵀ`:
`pair (ρσᵀ) Q_ab = (n_b ρ_a - n_a ρ_b)(n_b σ_a - n_a σ_b)/(n_a n_b)`. -/
theorem pair_Qab_vecMulVec (ρ σ n : Fin 3 → ℝ) (a b : Fin 3) :
    pair (vecMulVec ρ σ) (Qab n a b)
      = (n a * n b)⁻¹ * ((n b * ρ a - n a * ρ b) * (n b * σ a - n a * σ b)) := by
  have key : ∀ x : Fin 3 → ℝ,
      x ⬝ᵥ (n b • Pi.single a (1 : ℝ) - n a • Pi.single b (1 : ℝ)) = n b * x a - n a * x b := by
    intro x
    simp [dotProduct_sub, dotProduct_smul]
  rw [Qab, pair_smul, pair_vecMulVec_vecMulVec, key, key]

/-- The obtuse positive definite metrics with foot direction `n`. -/
def FootFibre (n : Fin 3 → ℝ) (G : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  G.PosDef ∧ (∀ a b, a ≠ b → G a b ≤ 0) ∧ ∃ κ : ℝ, G *ᵥ n = fun _ => κ

/-- `FootFibre n` is exactly the open simplicial cone of FG. -/
theorem footFibre_iff {n : Fin 3 → ℝ} (hn : ∀ i, 0 < n i) {G : Matrix (Fin 3) (Fin 3) ℝ} :
    FootFibre n G ↔ ∃ κ l01 l02 l12 : ℝ, 0 < κ ∧ 0 ≤ l01 ∧ 0 ≤ l02 ∧ 0 ≤ l12 ∧
      G = footCombo n κ l01 l02 l12 := by
  constructor
  · rintro ⟨hpd, hob, κ, hκ⟩
    have hs : Gᵀ = G := by simpa [Matrix.IsHermitian] using hpd.1
    have hsum : 0 < ∑ i, n i := Finset.sum_pos (fun i _ => hn i) ⟨0, Finset.mem_univ _⟩
    have hn0 : n ≠ 0 := fun h => (hn 0).ne' (by simp [h])
    have h1 := hpd.dotProduct_mulVec_pos hn0
    rw [hκ] at h1
    have h2 : n ⬝ᵥ (fun _ : Fin 3 => κ) = κ * ∑ i, n i := by
      simp [dotProduct, ← Finset.mul_sum, mul_comm]
    simp only [star_trivial] at h1
    rw [h2] at h1
    refine ⟨κ, -G 0 1, -G 0 2, -G 1 2, pos_of_mul_pos_left h1 hsum.le, ?_, ?_, ?_,
      foot_gauge hs hn hκ⟩
    all_goals linarith [hob 0 1 (by decide), hob 0 2 (by decide), hob 1 2 (by decide)]
  · rintro ⟨κ, l01, l02, l12, hκ, h01, h02, h12, rfl⟩
    exact ⟨footCombo_posDef hn hκ h01 h02 h12, footCombo_offdiag_nonpos hn h01 h02 h12,
      κ, footCombo_mulVec hn⟩

private theorem nonneg_of_forall {d q : ℝ} (h : ∀ l : ℝ, 0 ≤ l → 0 < d + l * q) : 0 ≤ q := by
  by_contra hq
  rw [not_le] at hq
  have hnq : 0 < -q := by linarith
  have := h ((|d| + 1) / (-q)) (by positivity)
  have hq0 : q ≠ 0 := hq.ne
  have e : (|d| + 1) / (-q) * q = -(|d| + 1) := by
    field_simp
  have := neg_abs_le d
  linarith [le_abs_self d]

/-- **Lemma GEN, "if" direction (the one used to certify).**  Generators positive resp. nonnegative
imply `pair S G > 0` on the whole fibre.  Needs `n > 0` only (FG); `S` arbitrary. -/
theorem gen_test_of_gens {n : Fin 3 → ℝ} (hn : ∀ i, 0 < n i) {S : Matrix (Fin 3) (Fin 3) ℝ}
    (hD : 0 < pair S (Dn n)) (h01 : 0 ≤ pair S (Qab n 0 1)) (h02 : 0 ≤ pair S (Qab n 0 2))
    (h12 : 0 ≤ pair S (Qab n 1 2)) {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : FootFibre n G) :
    0 < pair S G := by
  obtain ⟨κ, l01, l02, l12, hκ, a, b, c, rfl⟩ := (footFibre_iff hn).1 hG
  rw [pair_footCombo]
  have := mul_pos hκ hD
  have := mul_nonneg a h01
  have := mul_nonneg b h02
  have := mul_nonneg c h12
  linarith

/-- **Lemma GEN, "only if" direction.**  If `pair S G > 0` on the whole fibre, the generators are
positive (`D_n`) resp. nonnegative (`Q_ab`): the fibre is a cone, so the faces at infinity are
tested too. -/
theorem gen_gens_of_test {n : Fin 3 → ℝ} (hn : ∀ i, 0 < n i) {S : Matrix (Fin 3) (Fin 3) ℝ}
    (h : ∀ G, FootFibre n G → 0 < pair S G) :
    0 < pair S (Dn n) ∧ 0 ≤ pair S (Qab n 0 1) ∧ 0 ≤ pair S (Qab n 0 2) ∧
      0 ≤ pair S (Qab n 1 2) := by
  have key : ∀ l01 l02 l12 : ℝ, 0 ≤ l01 → 0 ≤ l02 → 0 ≤ l12 →
      0 < pair S (Dn n) + l01 * pair S (Qab n 0 1) + l02 * pair S (Qab n 0 2)
        + l12 * pair S (Qab n 1 2) := by
    intro l01 l02 l12 a b c
    have := h _ ((footFibre_iff hn).2 ⟨1, l01, l02, l12, one_pos, a, b, c, rfl⟩)
    rw [pair_footCombo] at this
    linarith
  have k0 := key 0 0 0 le_rfl le_rfl le_rfl
  refine ⟨by simpa using k0, ?_, ?_, ?_⟩
  · exact nonneg_of_forall fun l hl => by simpa using key l 0 0 hl le_rfl le_rfl
  · exact nonneg_of_forall fun l hl => by simpa using key 0 l 0 le_rfl hl le_rfl
  · exact nonneg_of_forall fun l hl => by simpa using key 0 0 l le_rfl le_rfl hl

/-- **Lemma GEN** (both directions): `pair S G > 0` on the fibre iff it holds on `D_n` and is `≥ 0`
on the three `Q_ab(n)`. -/
theorem gen_test {n : Fin 3 → ℝ} (hn : ∀ i, 0 < n i) {S : Matrix (Fin 3) (Fin 3) ℝ} :
    (∀ G, FootFibre n G → 0 < pair S G) ↔
      0 < pair S (Dn n) ∧ 0 ≤ pair S (Qab n 0 1) ∧ 0 ≤ pair S (Qab n 0 2) ∧
        0 ≤ pair S (Qab n 1 2) :=
  ⟨gen_gens_of_test hn, fun ⟨a, b, c, d⟩ _ hG => gen_test_of_gens hn a b c d hG⟩

/-- **Lemma AO (anti-ordered literal)**, both directions.  `(G σ)⬝ρ < 0` on the whole fibre iff
`∑ ρ_a σ_a / n_a < 0` and `ρ/n`, `σ/n` are oppositely (weakly) ordered on each pair. -/
theorem ao_literal {n : Fin 3 → ℝ} (hn : ∀ i, 0 < n i) (ρ σ : Fin 3 → ℝ) :
    (∀ G, FootFibre n G → (G *ᵥ σ) ⬝ᵥ ρ < 0) ↔
      ρ 0 * σ 0 / n 0 + ρ 1 * σ 1 / n 1 + ρ 2 * σ 2 / n 2 < 0 ∧
      (ρ 0 / n 0 - ρ 1 / n 1) * (σ 0 / n 0 - σ 1 / n 1) ≤ 0 ∧
      (ρ 0 / n 0 - ρ 2 / n 2) * (σ 0 / n 0 - σ 2 / n 2) ≤ 0 ∧
      (ρ 1 / n 1 - ρ 2 / n 2) * (σ 1 / n 1 - σ 2 / n 2) ≤ 0 := by
  have p0 := hn 0
  have p1 := hn 1
  have p2 := hn 2
  have e : ∀ G, (G *ᵥ σ) ⬝ᵥ ρ < 0 ↔ 0 < pair ((-1 : ℝ) • vecMulVec ρ σ) G := by
    intro G
    rw [pair_neg_left, pair_vecMulVec]
    constructor <;> intro h <;> linarith
  have gen := gen_test hn (S := (-1 : ℝ) • vecMulVec ρ σ)
  simp only [e]
  rw [gen]
  simp only [pair_neg_left, pair_Dn, pair_Qab_vecMulVec, Matrix.smul_apply, vecMulVec_apply,
    smul_eq_mul]
  have f : ∀ a b : Fin 3, 0 < n a → 0 < n b →
      (n a * n b)⁻¹ * ((n b * ρ a - n a * ρ b) * (n b * σ a - n a * σ b))
        = n a * n b * ((ρ a / n a - ρ b / n b) * (σ a / n a - σ b / n b)) := by
    intro a b ha hb
    field_simp
  rw [f 0 1 p0 p1, f 0 2 p0 p2, f 1 2 p1 p2]
  have m01 := mul_pos p0 p1
  have m02 := mul_pos p0 p2
  have m12 := mul_pos p1 p2
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨by linarith [h0, show (-1 : ℝ) * (ρ 0 * σ 0) / n 0 + -1 * (ρ 1 * σ 1) / n 1
      + -1 * (ρ 2 * σ 2) / n 2 = -(ρ 0 * σ 0 / n 0 + ρ 1 * σ 1 / n 1 + ρ 2 * σ 2 / n 2) by ring],
      ?_, ?_, ?_⟩
    · nlinarith
    · nlinarith
    · nlinarith
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨by linarith [show (-1 : ℝ) * (ρ 0 * σ 0) / n 0 + -1 * (ρ 1 * σ 1) / n 1
      + -1 * (ρ 2 * σ 2) / n 2 = -(ρ 0 * σ 0 / n 0 + ρ 1 * σ 1 / n 1 + ρ 2 * σ 2 / n 2) by ring],
      ?_, ?_, ?_⟩
    · nlinarith
    · nlinarith
    · nlinarith

/-- **Lemma AO, "if" direction**, in the form used to certify leaves. -/
theorem ao_of_conditions {n : Fin 3 → ℝ} (hn : ∀ i, 0 < n i) (ρ σ : Fin 3 → ℝ)
    (h0 : ρ 0 * σ 0 / n 0 + ρ 1 * σ 1 / n 1 + ρ 2 * σ 2 / n 2 < 0)
    (h01 : (ρ 0 / n 0 - ρ 1 / n 1) * (σ 0 / n 0 - σ 1 / n 1) ≤ 0)
    (h02 : (ρ 0 / n 0 - ρ 2 / n 2) * (σ 0 / n 0 - σ 2 / n 2) ≤ 0)
    (h12 : (ρ 1 / n 1 - ρ 2 / n 2) * (σ 1 / n 1 - σ 2 / n 2) ≤ 0)
    {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : FootFibre n G) : (G *ᵥ σ) ⬝ᵥ ρ < 0 :=
  (ao_literal hn ρ σ).2 ⟨h0, h01, h02, h12⟩ G hG

end

end Minimality.CornerEQ
