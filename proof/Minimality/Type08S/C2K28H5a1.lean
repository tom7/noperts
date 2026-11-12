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

/-- Screen cycle `a, c', a', c, d` of the H5 residue cell A in the frame `(a-d, b-d, u0)`. -/
def k28h5aY (A B β γ g κ ζ : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  ![(1, 0, 0), (A, B, 0), (-(γ * g), β + γ * κ, -(γ * ζ)), (-g, κ, -ζ), (0, 0, 0)]

theorem k28h5aY_0 : k28h5aY A B β γ g κ ζ 0 = (1, 0, 0) := rfl
theorem k28h5aY_1 : k28h5aY A B β γ g κ ζ 1 = (A, B, 0) := rfl
theorem k28h5aY_2 : k28h5aY A B β γ g κ ζ 2 = (-(γ * g), β + γ * κ, -(γ * ζ)) := rfl
theorem k28h5aY_3 : k28h5aY A B β γ g κ ζ 3 = (-g, κ, -ζ) := rfl
theorem k28h5aY_4 : k28h5aY A B β γ g κ ζ 4 = (0, 0, 0) := rfl

theorem k28h5aY_inj {A B β γ g κ ζ : ℝ} (hA : 1 < A) (hγ : 0 < γ) (hγ1 : γ < 1) (hg : 0 < g) (hζ : 0 < ζ)
    (hκ : 0 < κ) (hB : 1 < B) :
    ∀ i j, k28h5aY A B β γ g κ ζ i = k28h5aY A B β γ g κ ζ j → i = j := by
  have k1 := mul_pos hγ hg
  have k2 := mul_pos hg (sub_pos.2 hγ1)
  have k3 := mul_pos hγ hζ
  intro i j h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k28h5aY_0, k28h5aY_1, k28h5aY_2, k28h5aY_3, k28h5aY_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith)

set_option maxHeartbeats 12800000 in
theorem k28h5a_tsc {D A B β γ g κ ζ v1 v2 : ℝ} (hD : 0 < D) (hA : 1 < A) (hB : 1 < B) (hβ : 0 < β)
    (hβ1 : β < 1) (hγ : 0 < γ) (hγ1 : γ < 1) (hσ : B < β + γ) (hg : 0 < g) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hζ : 0 < ζ) (hrb : 0 < γ * g * (B - 1) + A * (β + γ * κ - 1))
    (hv : 0 < (-B) * v1 + (A - 1) * v2) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (k28h5aY A B β γ g κ ζ (i + 1) - k28h5aY A B β γ g κ ζ i)
        (k28h5aY A B β γ g κ ζ j - k28h5aY A B β γ g κ ζ i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (1 : ℝ), (0 : ℝ)), (1 + (A - 1) * κ, B * κ, -(B * ζ))], ∀ i : ZMod 5,
      TSc D (k28h5aY A B β γ g κ ζ (i + 1) - k28h5aY A B β γ g κ ζ i) (t - k28h5aY A B β γ g κ ζ i) (v1, v2, 0)) := by
  obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
  have ha1 : 0 < A - 1 := by linarith
  have hk1 : 0 < 1 - κ := by linarith
  have hg1 : 0 < 1 - γ := by linarith
  have hB0 : 0 < B := by linarith
  have hm : 0 < β + γ * κ := by nlinarith [mul_pos hγ hκ]
  have hs1 : 0 < β + γ - 1 := by linarith
  have hn : 0 < β - κ * (1 - γ) := by nlinarith [mul_pos hk1 hg1]
  have hh : 0 < β - B * (1 - γ) := by nlinarith [mul_pos hγ (sub_pos.2 hB)]
  have q1 := mul_pos ha1 hm
  have q2 := mul_pos (mul_pos hB0 hγ) hg
  have q3 := mul_pos ha1 hκ
  have q4 := mul_pos hB0 hg
  have q5 := mul_pos hg hh
  have q6 := mul_pos (by linarith : (0:ℝ) < A) hn
  have q7 := mul_pos (by linarith : (0:ℝ) < A) hm
  have q8 := mul_pos hk1 q1
  have q9 := mul_pos hk1 q2
  have q10 := mul_pos hk1 hB0
  have q11 := mul_pos (mul_pos hg hg1) hm
  have q12 := mul_pos hn (mul_pos hγ hg)
  have q14 := mul_pos hg hs1
  have q15 := mul_pos (mul_pos (mul_pos hg hg1) hB0) hk1
  have q16 := mul_pos hn q3
  have q17 := mul_pos (by linarith : (0:ℝ) < A) hκ
  have q18 := mul_pos hg hβ
  have q19 := mul_pos hκ q4
  have q20 := mul_pos hκ q3
  have q21 := mul_pos hB0 hκ
  have q22 := mul_pos (mul_pos hB0 hζ) hv
  have q23 := mul_pos hn (mul_pos hg hγ)
  refine ⟨?_, ?_⟩
  · intro i j h1 h2'
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, e0, e1, e2, e3, e4, f0, f1, f2, f3, f4, k28h5aY_0, k28h5aY_1, k28h5aY_2,
          k28h5aY_3, k28h5aY_4, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         left; apply mul_pos hD; first | linarith | nlinarith)
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, e0, e1, e2, e3, e4, f0, f1, f2, f3, f4, k28h5aY_0, k28h5aY_1, k28h5aY_2,
          k28h5aY_3, k28h5aY_4, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; apply mul_pos hD; first | linarith | nlinarith)
       | (right; refine ⟨by ring, mul_pos hD ?_⟩; first | linarith | nlinarith))

end C2
end Type08Sp
end Minimality
