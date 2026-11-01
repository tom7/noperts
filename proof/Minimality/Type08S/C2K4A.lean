module

public import Minimality.Type08S.C2K2E
public import Minimality.Type08S.C2FC1

@[expose] public section

/-!
# C2 / K4A: the 6-cycle `(a, c', b, a', c, b')` at the edge view `a - d` (frame form), `T'`, `γ4 = 1`, `B' = 0`

Frame `p = b - d`, `q = c - d`, `r = a - d`, coordinates over `d`:
`b = (1,0,0), c = (0,1,0), a = (0,0,1), c' = (β1,0,1) (T'), b' = (0,1,α4), a' = (β6,γ6,0)`.
`B' = ⟪p, r⟫ = 0`, `D_c = ⟪q, p⟫ < 0`.  On the screen `a, d` coincide, `c' ∈ [d, b]`, `c, b'` coincide.
Tilt `v = λ p + q`, `0 < λ < -D_c / |p|²`.
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

def pc6 {α : Type*} (p₀ p₁ p₂ p₃ p₄ p₅ : α) : ZMod 6 → α := ![p₀, p₁, p₂, p₃, p₄, p₅]

theorem pc6_0 {α : Type*} {w0 w1 w2 w3 w4 w5 : α} : pc6 w0 w1 w2 w3 w4 w5 0 = w0 := rfl
theorem pc6_1 {α : Type*} {w0 w1 w2 w3 w4 w5 : α} : pc6 w0 w1 w2 w3 w4 w5 1 = w1 := rfl
theorem pc6_2 {α : Type*} {w0 w1 w2 w3 w4 w5 : α} : pc6 w0 w1 w2 w3 w4 w5 2 = w2 := rfl
theorem pc6_3 {α : Type*} {w0 w1 w2 w3 w4 w5 : α} : pc6 w0 w1 w2 w3 w4 w5 3 = w3 := rfl
theorem pc6_4 {α : Type*} {w0 w1 w2 w3 w4 w5 : α} : pc6 w0 w1 w2 w3 w4 w5 4 = w4 := rfl
theorem pc6_5 {α : Type*} {w0 w1 w2 w3 w4 w5 : α} : pc6 w0 w1 w2 w3 w4 w5 5 = w5 := rfl

/-- Shifting the cycle preserves lex unimodality. -/
theorem lexUni_shift {k : ℕ} [NeZero k] {z w : ZMod k → ℝ} (s : ZMod k) (h : LexUni z w) :
    LexUni (fun i => z (i + s)) (fun i => w (i + s)) := by
  classical
  refine ⟨fun i j h1 h2 => add_right_cancel (h.1 _ _ h1 h2), ?_⟩
  rw [← h.2]
  refine Finset.card_nbij' (fun i => i + s) (fun i => i - s) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rw [show i + s - 1 = i - 1 + s by ring, show i + s + 1 = i + 1 + s by ring]
    exact hi
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rw [show i - s - 1 + s = i - 1 by ring, show i - s + 1 + s = i + 1 by ring,
      show i - s + s = i by ring]
    exact hi
  · intro i _; simp
  · intro i _; simp

/-- The ccw cycle `(a, c', b, a', c, b')` in the `a - d` frame, `γ4 = 1`, `T'`. -/
def k4Cyc (β1 β6 γ6 α4 : ℝ) : ZMod 6 → ℝ × ℝ × ℝ :=
  pc6 (0, 0, 1) (β1, 0, 1) (1, 0, 0) (β6, γ6, 0) (0, 1, 0) (0, 1, α4)

set_option maxHeartbeats 1600000 in
theorem k4_cyc {D β1 β6 γ6 α4 v1 v2 v3 : ℝ} (hD : 0 < D) (hβ1 : 0 < β1) (hβ11 : β1 < 1) (hβ6 : 0 < β6)
    (hγ6 : 0 < γ6) (hγ61 : γ6 ≤ 1) (hs : 1 < β6 + γ6) (hα4 : 0 < α4) (hv1 : 0 < v1) (hv2 : 0 < v2) :
    ∀ i j : ZMod 6, j ≠ i → j ≠ i + 1 →
      TSc D (k4Cyc β1 β6 γ6 α4 (i + 1) - k4Cyc β1 β6 γ6 α4 i)
        (k4Cyc β1 β6 γ6 α4 j - k4Cyc β1 β6 γ6 α4 i) (v1, v2, v3) := by
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := z6_add_one
  have k1 := hD
  have kb1 := mul_pos hD hβ1
  have kb11 := mul_pos hD (sub_pos.2 hβ11)
  have kb6 := mul_pos hD hβ6
  have kg6 := mul_pos hD hγ6
  have ks := mul_pos hD (sub_pos.2 hs)
  have kv1 := mul_pos hD hv1
  have kv2 := mul_pos hD hv2
  have kb1v2 := mul_pos (mul_pos hD hβ1) hv2
  have kg6b := mul_pos (mul_pos hD hγ6) (sub_pos.2 hβ11)
  have ka4v1 := mul_pos (mul_pos hD hα4) hv1
  have ka4v2 := mul_pos (mul_pos hD hα4) hv2
  have ka4b1v2 := mul_pos (mul_pos (mul_pos hD hα4) hβ1) hv2
  have kcone : 0 < D * α4 * ((1 - γ6) * v1 + β6 * v2) :=
    mul_pos (mul_pos hD hα4) (by nlinarith [mul_nonneg (sub_nonneg.2 hγ61) hv1.le, mul_pos hβ6 hv2])
  have kmix : 0 < D * (β6 - (1 - γ6) * β1) :=
    mul_pos hD (by nlinarith [mul_nonneg (sub_nonneg.2 hγ61) (sub_pos.2 hβ11).le])
  intro i j h1 h2'
  rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2' (by decide)).elim
    | (simp only [TSc, d3, k4Cyc, s0, s1, s2, s3, s4, s5, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 1600000 in
theorem k4_rest {D β1 β6 γ6 α4 v1 v2 v3 : ℝ} (hD : 0 < D) (hβ1 : 0 < β1) (hβ11 : β1 < 1) (hβ6 : 0 < β6)
    (hγ6 : 0 < γ6) (hα4 : 0 < α4) (hv1 : 0 < v1) (hv2 : 0 < v2) :
    ∀ i : ZMod 6, TSc D (k4Cyc β1 β6 γ6 α4 (i + 1) - k4Cyc β1 β6 γ6 α4 i)
      ((0, 0, 0) - k4Cyc β1 β6 γ6 α4 i) (v1, v2, v3) := by
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := z6_add_one
  have k1 := hD
  have kb1 := mul_pos hD hβ1
  have kb11 := mul_pos hD (sub_pos.2 hβ11)
  have kb6 := mul_pos hD hβ6
  have kg6 := mul_pos hD hγ6
  have kv1 := mul_pos hD hv1
  have kv2 := mul_pos hD hv2
  have kb1v2 := mul_pos (mul_pos hD hβ1) hv2
  have ka4v1 := mul_pos (mul_pos hD hα4) hv1
  intro i
  rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, k4Cyc, s0, s1, s2, s3, s4, s5, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
