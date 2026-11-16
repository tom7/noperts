module

public import Mathlib
public import Minimality.CornerLift

/-!
# Lemma R2 (type 29, apex confined to `plane(145)`)

Source: `CORNER-EQ-IDEAS3-FABLE.md` 1.2, Lemma R2.  Namespace `Minimality.CornerEQ`, `Fin 3`.
Index roles (K1 frame): `c` is the index with `ν_c = 0` (the plane constraint; `3` in the note), `a, b` the
other two (`4, 5`); `a b c` pairwise distinct, so they list `Fin 3`.  `G` is the Gram matrix at the apex and
`G' = Mᵀ G M` (`M = liftM ν`) the Gram matrix of the lifted apex.

* `r2_max_ab` (`G_ab = 0`): every `ν ≥ 0`, `ν ≠ 0` with `ν_c = 0` has `G'_ab > 0`, exactly
  `G'_ab = G_aa ν_a (1 + ν_a) + G_bb ν_b (1 + ν_b)` (the note's `ε (ν_4 G_44 + ν_5 G_55)` is the first
  order part; the exact value only adds the positive quadratic terms).  Only `G_aa, G_bb > 0` is used, so
  positive definiteness is the hypothesis; symmetry is then a consequence (`G.PosDef` includes it) and
  `G_ac`, `G_bc`, `ν_c = 0`'s companion data play no role.
* `r2_max_cc` (`G_ca = G_cb = 0`): maximal for every `ν ≥ 0`, `ν ≠ 0`; this is `lift_two_zeros` with the
  roles `(c, a, b)`.  The plane constraint `ν_c = 0` is NOT needed (exactness of R1), so it is dropped.
* `r2_not_max` (`G_ab < 0`, `G_ca = 0 > G_cb`): `ν = ε e_b` (so `ν_c = 0` holds since `b ≠ c`) makes all
  three off-diagonals `G'_ab, G'_ca, G'_cb` negative; this is `lift_one_zero` with the roles `(c, a, b)`.
  Only symmetry of `G` is used (not positive definiteness).  The case with `a, b` exchanged is the same
  statement with the names swapped.
-/

set_option autoImplicit false

namespace Minimality.CornerEQ

open Finset Matrix

@[expose] public section

theorem r2_max_ab (G : Matrix (Fin 3) (Fin 3) ℝ) (hpd : G.PosDef) {a b c : Fin 3}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (h0 : G a b = 0)
    (ν : Fin 3 → ℝ) (hν : 0 ≤ ν) (hν0 : ν ≠ 0) (hc : ν c = 0) :
    0 < ((liftM ν)ᵀ * G * liftM ν) a b := by
  have hG : G.IsSymm := by
    have := hpd.isHermitian
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using this
  have hs : ∀ i j, G i j = G j i := fun i j => (hG.apply j i)
  have hpos : ∀ w : Fin 3 → ℝ, w ≠ 0 → 0 < w ⬝ᵥ (G *ᵥ w) := fun w hw => by
    simpa using hpd.dotProduct_mulVec_pos hw
  have mv : ∀ (w : Fin 3 → ℝ) (i : Fin 3), (G *ᵥ w) i = G i a * w a + G i b * w b + G i c * w c := by
    intro w i
    simp only [Matrix.mulVec, dotProduct]; exact sum3 hab hac hbc _
  have dp : ∀ w : Fin 3 → ℝ, w ⬝ᵥ (G *ᵥ w) = w a * (G *ᵥ w) a + w b * (G *ᵥ w) b + w c * (G *ᵥ w) c := by
    intro w; simp only [dotProduct]; exact sum3 hab hac hbc _
  have hGaa : 0 < G a a := by
    have := hpos (Pi.single a 1) (by simp)
    rw [dp] at this
    simp [mv, hab.symm, hac.symm] at this
    simpa using this
  have hGbb : 0 < G b b := by
    have := hpos (Pi.single b 1) (by simp)
    rw [dp] at this
    simp [mv, hab, hbc.symm] at this
    simpa using this
  have hba : G b a = 0 := by rw [hs, h0]
  have e : ((liftM ν)ᵀ * G * liftM ν) a b
      = G a a * ν a * (1 + ν a) + G b b * ν b * (1 + ν b) := by
    rw [lift_gram_apply G hG, dp, mv, mv, mv]
    simp only [h0, hba, hc]
    ring
  rw [e]
  have ha := hν a
  have hb := hν b
  simp only [Pi.zero_apply] at ha hb
  have h1 : 0 ≤ G a a * ν a * (1 + ν a) := by positivity
  have h2 : 0 ≤ G b b * ν b * (1 + ν b) := by positivity
  by_contra hcon
  have e1 : G a a * ν a * (1 + ν a) = 0 := by linarith
  have e2 : G b b * ν b * (1 + ν b) = 0 := by linarith
  have na : ν a = 0 := by
    rcases mul_eq_zero.1 e1 with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h hGaa.ne'
      · exact h
    · linarith
  have nb : ν b = 0 := by
    rcases mul_eq_zero.1 e2 with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h hGbb.ne'
      · exact h
    · linarith
  apply hν0
  ext i
  have hi : i = a ∨ i = b ∨ i = c := by omega
  rcases hi with h | h | h <;> simp [h, na, nb, hc]

theorem r2_max_cc (G : Matrix (Fin 3) (Fin 3) ℝ) (hpd : G.PosDef) {a b c : Fin 3}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (h1 : G c a = 0) (h2 : G c b = 0)
    (ν : Fin 3 → ℝ) (hν : 0 ≤ ν) (hν0 : ν ≠ 0) :
    ¬ (((liftM ν)ᵀ * G * liftM ν) c a ≤ 0 ∧ ((liftM ν)ᵀ * G * liftM ν) c b ≤ 0) :=
  lift_two_zeros G (by simpa [Matrix.IsHermitian, Matrix.IsSymm] using hpd.isHermitian) hpd hac.symm hbc.symm hab h1 h2 ν hν hν0

theorem r2_not_max (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.IsSymm) {a b c : Fin 3}
    (hbc : b ≠ c) (h0 : G c a = 0) (h1 : G c b < 0) (h2 : G a b < 0) :
    ∃ ε : ℝ, 0 < ε ∧ (Pi.single b ε : Fin 3 → ℝ) c = 0 ∧
      ((liftM (Pi.single b ε))ᵀ * G * liftM (Pi.single b ε)) a b < 0 ∧
      ((liftM (Pi.single b ε))ᵀ * G * liftM (Pi.single b ε)) c a < 0 ∧
      ((liftM (Pi.single b ε))ᵀ * G * liftM (Pi.single b ε)) c b < 0 := by
  obtain ⟨ε, he, x1, x2, x3⟩ := lift_one_zero G hG h0 h1 h2
  exact ⟨ε, he, by simp [hbc], x3, x1, x2⟩

end

end Minimality.CornerEQ
