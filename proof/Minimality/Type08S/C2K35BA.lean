module

public import Minimality.Type08S.C2K14D
public import Minimality.Type08S.C2K16E
public import Minimality.Type08S.C2K22ZA
public import Minimality.Type08S.C2K19G
public import Minimality.Type08S.C2K18A
public import Minimality.Type08S.C2K25Tie

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- Cycle `(b', a, c', a', c)` in the frame `((a-d)/κ, (b-d)/κ, -u0/κ)`, `κ = b1 Ez`,
`x = (a1-1)(Fz-Ez)`, `y = b1 Fz`. -/
def k28h5bY (a1 b1 b6 g6 Ez Fz : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  ![(a1 * (b1 * Ez) + b1 * ((a1 - 1) * (Fz - Ez)), b1 * (b1 * Fz), b1), (b1 * Ez, 0, 0),
    (a1 * (b1 * Ez), b1 * (b1 * Ez), 0),
    (g6 * ((a1 - 1) * (Fz - Ez)), b6 * (b1 * Ez) + g6 * (b1 * Fz), g6), ((a1 - 1) * (Fz - Ez), b1 * Fz, 1)]

theorem k28h5bY_0 : k28h5bY a1 b1 b6 g6 Ez Fz 0 = (a1 * (b1 * Ez) + b1 * ((a1 - 1) * (Fz - Ez)), b1 * (b1 * Fz), b1) := rfl
theorem k28h5bY_1 : k28h5bY a1 b1 b6 g6 Ez Fz 1 = (b1 * Ez, 0, 0) := rfl
theorem k28h5bY_2 : k28h5bY a1 b1 b6 g6 Ez Fz 2 = (a1 * (b1 * Ez), b1 * (b1 * Ez), 0) := rfl
theorem k28h5bY_3 : k28h5bY a1 b1 b6 g6 Ez Fz 3 =
    (g6 * ((a1 - 1) * (Fz - Ez)), b6 * (b1 * Ez) + g6 * (b1 * Fz), g6) := rfl
theorem k28h5bY_4 : k28h5bY a1 b1 b6 g6 Ez Fz 4 = ((a1 - 1) * (Fz - Ez), b1 * Fz, 1) := rfl

theorem k28h5bY_inj {a1 b1 b6 g6 Ez Fz : ℝ} (ha1 : 1 < a1) (hb1 : 1 < b1) (hg6 : 0 < g6) (hg61 : g6 < 1)
    (hE : 0 < Ez) : ∀ i j, k28h5bY a1 b1 b6 g6 Ez Fz i = k28h5bY a1 b1 b6 g6 Ez Fz j → i = j := by
  have hk : 0 < b1 * Ez := mul_pos (by linarith) hE
  have hk2 : 0 < (a1 - 1) * (b1 * Ez) := mul_pos (by linarith) hk
  intro i j h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k28h5bY_0, k28h5bY_1, k28h5bY_2, k28h5bY_3, k28h5bY_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith)

set_option maxHeartbeats 12800000 in
theorem k28h5b_tsc {D a1 b1 b6 g6 Ez Fz v1 v2 : ℝ} (hD : 0 < D) (ha1 : 1 < a1) (hb1 : 1 < b1)
    (hb6 : 0 < b6) (hb61 : b6 < 1) (hg6 : 0 < g6) (hg61 : g6 < 1) (hσ : b1 < b6 + g6)
    (hE : 0 < Ez) (hF : Fz < 0)
    (H1 : 0 < g6 * (a1 + b1 - 1) * Fz + (a1 * b1 * (g6 + b6 - 1) - g6 * (a1 + b1 - 1)) * Ez)
    (H2 : 0 < g6 * Fz + Ez * (g6 * (a1 - 1) + a1 * b6))
    (H3 : 0 < Ez * b6 * (b1 + a1 - 1) + Fz * (b6 * (1 - b1 - a1) + a1 * b1 * (b6 + g6 - 1)))
    (hv : 0 < b1 * v1 - (a1 - 1) * v2) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (k28h5bY a1 b1 b6 g6 Ez Fz (i + 1) - k28h5bY a1 b1 b6 g6 Ez Fz i)
        (k28h5bY a1 b1 b6 g6 Ez Fz j - k28h5bY a1 b1 b6 g6 Ez Fz i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (0, b1 * Ez, 0)], ∀ i : ZMod 5,
      TSc D (k28h5bY a1 b1 b6 g6 Ez Fz (i + 1) - k28h5bY a1 b1 b6 g6 Ez Fz i)
        (t - k28h5bY a1 b1 b6 g6 Ez Fz i) (v1, v2, 0)) := by
  obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
  have a0 : 0 < a1 - 1 := by linarith
  have b0 : 0 < b1 - 1 := by linarith
  have nF : 0 < -Fz := by linarith
  have oEF : 0 < Ez - Fz := by linarith
  have b1p : 0 < b1 := by linarith
  have a1p : 0 < a1 := by linarith
  have sg : 0 < b6 + g6 - 1 := by linarith
  have sg1 : 0 < b6 + g6 := by linarith
  have hk : 0 < D * (b1 * Ez) := mul_pos hD (mul_pos b1p hE)
  have g1 : 0 < 1 - g6 := by linarith
  have sb : 0 < b1 + a1 - 1 := by linarith
  have m1 := mul_pos sg1 a0
  have sc : 0 < (b6 + g6) * (a1 - 1) + b1 := by linarith
  have sc' : 0 < b1 + (b6 + g6) * (a1 - 1) := by linarith
  have hB : 0 < b6 * (a1 - 1) + b1 * (1 - g6) := add_pos (mul_pos hb6 a0) (mul_pos b1p g1)
  have hA : 0 < b6 * (a1 - 1) + b1 * (1 - g6) + a1 * b1 * (b6 + g6 - 1) := by
    have := mul_pos (mul_pos a1p b1p) sg
    linarith
  have o1 := mul_pos (mul_pos b1p nF) sb
  have o3 := mul_pos (pow_pos b1p 2) nF
  have o5 := mul_pos (mul_pos b1p nF) sc
  have o6 := mul_pos (mul_pos b1p hE) sb
  have o7 := mul_pos (pow_pos b1p 2) hE
  have o8 := mul_pos (mul_pos b1p hE) sc'
  have o13 := add_pos (mul_pos hE hA) (mul_pos nF hB)
  have o12 := mul_pos (mul_pos b1p oEF) sc'
  have o15 := add_pos (mul_pos nF hB) (mul_pos (mul_pos hE hb6) sb)
  have o16 := mul_pos (mul_pos oEF sg) a0
  have o17 := mul_pos (mul_pos hb6 a0) oEF
  have o20 := mul_pos oEF sb
  have o21 := mul_pos (mul_pos a1p b1p) nF
  have o22 := mul_pos (mul_pos b1p oEF) sb
  have k1 := mul_pos hk o1
  have k3 := mul_pos hk o3
  have k5 := mul_pos hk o5
  have k6 := mul_pos hk o6
  have k7 := mul_pos hk o7
  have k8 := mul_pos hk o8
  have k12 := mul_pos hk o12
  have k13 := mul_pos hk o13
  have k15 := mul_pos hk o15
  have k16 := mul_pos hk o16
  have k17 := mul_pos hk o17
  have k20 := mul_pos hk o20
  have k21 := mul_pos hk o21
  have k22 := mul_pos hk o22
  have kH1 := mul_pos hk H1
  have kH2 := mul_pos (mul_pos hk b1p) H2
  have kH3 := mul_pos hk H3
  have kz := mul_pos (mul_pos hk (mul_pos b1p b1p)) hv
  have kz2 := mul_pos (mul_pos hk (mul_pos b1p b1p)) hv
  refine ⟨?_, ?_⟩
  · intro i j h1 h2'
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, e0, e1, e2, e3, e4, f0, f1, f2, f3, f4, k28h5bY_0, k28h5bY_1, k28h5bY_2,
            k28h5bY_3, k28h5bY_4, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; linarith)
         | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, e0, e1, e2, e3, e4, f0, f1, f2, f3, f4, k28h5bY_0, k28h5bY_1, k28h5bY_2,
            k28h5bY_3, k28h5bY_4, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; linarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
