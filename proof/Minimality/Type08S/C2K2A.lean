module

public import Minimality.Type08S.C2FJ

@[expose] public section

/-!
# C2 / K2A: the 5-cycle `(a, d, b, a', b')` at the edge view `a - d` (frame form)

Frame `p = b - d`, `q = c - d`, `r = a - d` (the base view), coordinates over `d`:
`b = (1,0,0), c = (0,1,0), a = (0,0,1), c' = (β1,0,α1), b' = (0,1,α4)` (`γ4 = 1`), `a' = (β6,γ6,0)`
(`γ6 ≤ 1`: `T'` has `γ6 < 1`, `T` has `γ6 = 1`).  `B' = ⟪p, r⟫ = 0`, `D_c = ⟪q, p⟫ > 0`.
Screen: `a`, `d` coincide (edge `a → d ∥ r`), `c` hides behind `b'`, `c'` lies on `[d, b]` (`β1 < 1`).
Tilt `v = λ p - q`, `λ ∈ (0, min (D_c / |p|²) β6)`.
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem lexLt_trans_K2 {p q s : ℝ × ℝ} (h1 : LexLt p q) (h2 : LexLt q s) : LexLt p s := by
  unfold LexLt at *
  rcases h1 with h | ⟨h, h'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · exact Or.inl (by linarith)
  · exact Or.inl (by linarith)
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨by linarith, by linarith⟩

/-- **5-cycle, candidate peaks `4, 0` (adjacent), `3` conditional.**  `P1 < P0`, `P2 < P1`, and `P3 < P2` or
`P3 < P4`: exactly one peak (at `0` or `4`). -/
theorem lexUni5_adj (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h10 : LexLt (z 1, w 1) (z 0, w 0)) (h21 : LexLt (z 2, w 2) (z 1, w 1))
    (h3 : LexLt (z 3, w 3) (z 2, w 2) ∨ LexLt (z 3, w 3) (z 4, w 4)) : LexUni z w := by
  classical
  refine ⟨hinj, ?_⟩
  have h04 : (z 0, w 0) ≠ (z 4, w 4) := by
    intro h; have := hinj 0 4 (congrArg Prod.fst h) (congrArg Prod.snd h); exact absurd this (by decide)
  rw [Finset.card_filter]
  have hs : ∀ g : ZMod 5 → ℕ, ∑ i, g i = g 0 + g 1 + g 2 + g 3 + g 4 := fun g => Fin.sum_univ_five (f := g)
  rw [hs]
  have e0 : (0 : ZMod 5) - 1 = 4 := by decide
  have e1 : (1 : ZMod 5) - 1 = 0 := by decide
  have e2 : (2 : ZMod 5) - 1 = 1 := by decide
  have e3 : (3 : ZMod 5) - 1 = 2 := by decide
  have e4 : (4 : ZMod 5) - 1 = 3 := by decide
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  show (if LexLt (z (0 - 1), w (0 - 1)) (z 0, w 0) ∧ LexLt (z (0 + 1), w (0 + 1)) (z 0, w 0) then 1 else 0) +
    (if LexLt (z (1 - 1), w (1 - 1)) (z 1, w 1) ∧ LexLt (z (1 + 1), w (1 + 1)) (z 1, w 1) then 1 else 0) +
    (if LexLt (z (2 - 1), w (2 - 1)) (z 2, w 2) ∧ LexLt (z (2 + 1), w (2 + 1)) (z 2, w 2) then 1 else 0) +
    (if LexLt (z (3 - 1), w (3 - 1)) (z 3, w 3) ∧ LexLt (z (3 + 1), w (3 + 1)) (z 3, w 3) then 1 else 0) +
    (if LexLt (z (4 - 1), w (4 - 1)) (z 4, w 4) ∧ LexLt (z (4 + 1), w (4 + 1)) (z 4, w 4) then 1 else 0) = 1
  rw [e0, e1, e2, e3, e4, f0, f1, f2, f3, f4]
  have a10 := lexLt_asymm h10
  have a21 := lexLt_asymm h21
  have h20 := lexLt_trans_K2 h21 h10
  rcases lexLt_total h04 with h | h <;> have a := lexLt_asymm h
  · -- `0 < 4`: the peak is `4`
    have h34 : LexLt (z 3, w 3) (z 4, w 4) := by
      rcases h3 with h3 | h3
      · exact lexLt_trans_K2 h3 (lexLt_trans_K2 h20 h)
      · exact h3
    have a34 := lexLt_asymm h34
    simp [h, a, h34, a34, h10, a10, h21, a21]
  · -- `4 < 0`: the peak is `0`
    rcases h3 with h3 | h3 <;> have a3 := lexLt_asymm h3 <;>
      simp [h, a, h3, a3, h10, a10, h21, a21]

/-- The ccw cycle `(a, d, b, a', b')` in the `a - d` frame, `γ4 = 1`. -/
def kCyc (β6 γ6 α4 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ := pc5 (0, 0, 1) (0, 0, 0) (1, 0, 0) (β6, γ6, 0) (0, 1, α4)

set_option maxHeartbeats 1600000 in
theorem k2_cyc {D β6 γ6 α4 v1 v2 v3 : ℝ} (hD : 0 < D) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hs : 1 < β6 + γ6)
    (hv1 : 0 < v1) (hv2 : v2 < 0) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (kCyc β6 γ6 α4 (i + 1) - kCyc β6 γ6 α4 i) (kCyc β6 γ6 α4 j - kCyc β6 γ6 α4 i) (v1, v2, v3) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have k1 := hD
  have kb6 := mul_pos hD hβ6
  have kg6 := mul_pos hD hγ6
  have ks := mul_pos hD (sub_pos.2 hs)
  have kv1 := mul_pos hD hv1
  have kv2 := mul_pos hD (neg_pos.2 hv2)
  have kgv := mul_pos (mul_pos hD hγ6) hv1
  have kbv := mul_pos (mul_pos hD hβ6) (neg_pos.2 hv2)
  intro i j h1 h2'
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2' (by decide)).elim
    | (simp only [TSc, d3, kCyc, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 1600000 in
theorem k2_rest {D α1 β1 α4 β6 γ6 v1 v2 v3 : ℝ} (hD : 0 < D) (hα1 : 0 < α1) (hβ1 : 0 < β1) (hβ11 : β1 < 1)
    (hα4 : 0 < α4) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 ≤ 1) (hs : 1 < β6 + γ6)
    (hv1 : 0 < v1) (hv2 : v2 < 0) (hcone : (1 - γ6) * v1 + β6 * v2 < 0) :
    (∀ i : ZMod 5, TSc D (kCyc β6 γ6 α4 (i + 1) - kCyc β6 γ6 α4 i) ((0, 1, 0) - kCyc β6 γ6 α4 i) (v1, v2, v3)) ∧
    (∀ i : ZMod 5, TSc D (kCyc β6 γ6 α4 (i + 1) - kCyc β6 γ6 α4 i) ((β1, 0, α1) - kCyc β6 γ6 α4 i)
      (v1, v2, v3)) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have k1 := hD
  have kb6 := mul_pos hD hβ6
  have kg6 := mul_pos hD hγ6
  have ks := mul_pos hD (sub_pos.2 hs)
  have kv1 := mul_pos hD hv1
  have kv2 := mul_pos hD (neg_pos.2 hv2)
  have kgv := mul_pos (mul_pos hD hγ6) hv1
  have kbv := mul_pos (mul_pos hD hβ6) (neg_pos.2 hv2)
  have ka4v1 := mul_pos (mul_pos hD hα4) hv1
  have ka1v2 := mul_pos (mul_pos hD hα1) (neg_pos.2 hv2)
  have kb1v2 := mul_pos (mul_pos hD hβ1) (neg_pos.2 hv2)
  have kcone := mul_pos (mul_pos hD hα4) (neg_pos.2 hcone)
  have kg61 := mul_pos (mul_pos hD hγ6) (sub_pos.2 hβ11)
  have kc2 := mul_nonneg (mul_nonneg hD.le (sub_nonneg.2 hγ61)) (sub_pos.2 hβ11).le
  have kc3 := mul_pos hD hβ1
  refine ⟨?_, ?_⟩ <;> intro i <;>
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, kCyc, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
