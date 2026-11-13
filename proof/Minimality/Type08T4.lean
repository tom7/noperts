module

public import Minimality.Type08Cases

@[expose] public section

/-!
# Type 08: the T4 case of Theorem 10.1

At the view along the QQ edge `d b`, with far ends `c'` (of `Q_ab`) and `c` (of
`Q_bc`), the middles are `a` and `a'`, and `K_v ⊂ K − a` (a T4).  In the frame
`d; a, c, b` everything is explicit: `b' = d + α (a − d) + β (c − d)`
(`IsCap.Qac_coords'`), `c' = d + α₁ (a − d) + β₁ (b − d)` with `α₁ > 1` (the far end
`c'`), and every determinant test at the view is a multiple of
`E = det3 (a − d) (c − d) (b − d)` (`IsCap.det_Qac_ne`).  The sign of
`κ' = α + α₁ (β − 1)` decides whether `b'` is a corner (`κ' > 0`, the rim
`v, c, b', c'`) or hidden (`κ' < 0`, the rim is a triangle).  At a corner, Lemma 5
is Lemma 9.3's closing with `x = d`, `y = b`: the T4 edge `d → b` is not bad
(`type08_t4_not_bad`: Lemmas 9.7, 4, 3), and the claim of Lemma 9.3 uses the face
`Q_ac` through `d b'` (`quad_lower_of_face`).
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- **The claim of Lemma 9.3** (the lower boundary over the crossing of the
diagonals of the edge view along `y − x`), from one affine function `G` vanishing on
`x`, `y'` and one far end, negative at the other far end and at `y`. -/
theorem quad_lower_of_face {x y y' p p' : ℝ³} {G : ℝ³ → ℝ} {N : ℝ³}
    (hG : ∀ s t, G s - G t = ⟪N, s - t⟫) (hxy : x ≠ y) (hGx : G x = 0) (hGy' : G y' = 0)
    (hGy : G y < 0)
    (hS₂ : 0 < det3 (y' - x) (p' - x) (y - x)) (hS₄ : 0 < det3 (p - x) (y' - x) (y - x))
    (hface : (G p = 0 ∧ G p' < 0) ∨ (G p' = 0 ∧ G p < 0)) :
    det3 (y' - p) (p' - p) (y - x) * ⟪x, y - x⟫ + det3 (p - x) (p' - x) (y - x) * ⟪y', y - x⟫ <
      det3 (y' - x) (p' - x) (y - x) * ⟪p, y - x⟫ + det3 (p - x) (y' - x) (y - x) * ⟪p', y - x⟫ := by
  set u := y - x
  have hu : u ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  set S₁ := det3 (y' - p) (p' - p) u
  set S₂ := det3 (y' - x) (p' - x) u
  set S₃ := det3 (p - x) (p' - x) u
  set S₄ := det3 (p - x) (y' - x) u
  have hpar := four_point_parallel x p y' p' u hu
  have hsum := four_point_sum x p y' p' u
  set L := S₁ • x - S₂ • p + S₃ • y' - S₄ • p'
  set lam := ⟪L, u⟫ / ⟪u, u⟫
  have hL : L = -S₂ • (p - x) + S₃ • (y' - x) - S₄ • (p' - x) := by
    have : S₁ = S₂ - S₃ + S₄ := by linarith
    simp only [L, this]; module
  have hGL : ⟪N, L⟫ = -S₂ * G p - S₄ * G p' := by
    rw [hL, inner_sub_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, ← hG, ← hG, ← hG, hGx, hGy']
    ring
  have hGu : ⟪N, u⟫ = G y := by rw [← hG, hGx, sub_zero]
  have hpos : 0 < ⟪N, L⟫ := by
    rw [hGL]
    rcases hface with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1]; nlinarith
    · rw [h1]; nlinarith
  have hlam : lam < 0 := by
    have e : ⟪N, L⟫ = lam * G y := by
      rw [← hGu, ← real_inner_smul_right, ← hpar]
    rw [e] at hpos
    nlinarith
  have huu : 0 < ⟪u, u⟫ := real_inner_self_pos.mpr hu
  have hLu : ⟪L, u⟫ < 0 := by
    have : ⟪L, u⟫ = lam * ⟪u, u⟫ := by
      conv_lhs => rw [hpar]
      rw [real_inner_smul_left]
    rw [this]; nlinarith
  simp only [L, inner_sub_left, inner_add_left, real_inner_smul_left] at hLu
  linarith

theorem tri_injective {α : Type*} {p₀ p₁ p₂ : α} (h01 : p₀ ≠ p₁) (h02 : p₀ ≠ p₂)
    (h12 : p₁ ≠ p₂) : Function.Injective (tri p₀ p₁ p₂) := by
  intro i j hij
  rcases zmod3_cases i with rfl | rfl | rfl <;> rcases zmod3_cases j with rfl | rfl | rfl <;>
    simp_all [tri_0, tri_1, tri_2]

theorem tri_inner (p₀ p₁ p₂ u : ℝ³) :
    (fun i => ⟪tri p₀ p₁ p₂ i, u⟫) = tri ⟪p₀, u⟫ ⟪p₁, u⟫ ⟪p₂, u⟫ := by
  funext i; rcases zmod3_cases i with rfl | rfl | rfl <;> rfl

theorem zmod3_zero_add_one : (0 : ZMod 3) + 1 = 1 := by decide
theorem zmod3_zero_sub_one : (0 : ZMod 3) - 1 = 2 := by decide

/-- The determinant tests of the T4 case, as multiples of `E`. -/
theorem t4_dets {a b c d b' c' : ℝ³} {α β α₁ β₁ : ℝ}
    (hb' : b' = d + α • (a - d) + β • (c - d)) (hc' : c' = d + α₁ • (a - d) + β₁ • (b - d)) :
    let E := det3 (a - d) (c - d) (b - d)
    let κ := α + α₁ * (β - 1)
    det3 (c - d) (b' - d) (b - d) = -(α * E) ∧
    det3 (c - d) (c' - d) (b - d) = -(α₁ * E) ∧
    det3 (b' - c) (c' - c) (b - d) = -(κ * E) ∧
    det3 (b' - c) (d - c) (b - d) = -(α * E) ∧
    det3 (c' - b') (d - b') (b - d) = -(α₁ * β * E) ∧
    det3 (c' - b') (c - b') (b - d) = -(κ * E) ∧
    det3 (d - c') (c - c') (b - d) = -(α₁ * E) ∧
    det3 (d - c') (b' - c') (b - d) = -(α₁ * β * E) ∧
    det3 (c' - c) (d - c) (b - d) = -(α₁ * E) ∧
    det3 (c' - c) (b' - c) (b - d) = κ * E ∧
    det3 (c' - d) (b' - d) (b - d) = α₁ * β * E ∧
    det3 (c' - d) (c - d) (b - d) = α₁ * E ∧
    det3 (b' - c') (c - c') (b - d) = κ * E ∧
    det3 (b' - c') (d - c') (b - d) = α₁ * β * E ∧
    det3 (c - b') (d - b') (b - d) = α * E ∧
    det3 (c - b') (c' - b') (b - d) = κ * E ∧
    det3 (d - c) (c' - c) (b - d) = α₁ * E ∧
    det3 (d - c) (b' - c) (b - d) = α * E ∧
    det3 (c - c') (d - c') (b - d) = α₁ * E ∧
    det3 (c - c') (b' - c') (b - d) = -(κ * E) ∧
    det3 (b' - d) (c' - d) (b - d) = -(α₁ * β * E) ∧
    det3 (b' - d) (c - d) (b - d) = α * E ∧
    det3 (b - d) (b' - d) (c - d) = α * E ∧
    det3 (b - d) (b' - d) (c' - d) = -(α₁ * β * E) := by
  intro E κ
  subst hb' hc'
  simp only [E, κ, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩ <;> ring

end Minimality

end
