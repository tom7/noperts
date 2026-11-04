module

public import Minimality.Type08S.C2K22ZA
public import Minimality.Type08S.C2K19G
public import Minimality.Type08S.C2K18A

@[expose] public section


set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- Pentagon `d, a, c', a', c` in the frame `(a-d, b-d, R)`, `R = -s (a-d) - (c-d)` (`α1 = 1 + β1 s`). -/
def k24mtdY (b1 s h6 g : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  ![(0, 0, 0), (1, 0, 0), (1 + b1 * s, b1, 0), (-(g * s), h6, -g), (-s, 0, -1)]

theorem k24mtdY_0 : k24mtdY b1 s h6 g 0 = (0, 0, 0) := rfl
theorem k24mtdY_1 : k24mtdY b1 s h6 g 1 = (1, 0, 0) := rfl
theorem k24mtdY_2 : k24mtdY b1 s h6 g 2 = (1 + b1 * s, b1, 0) := rfl
theorem k24mtdY_3 : k24mtdY b1 s h6 g 3 = (-(g * s), h6, -g) := rfl
theorem k24mtdY_4 : k24mtdY b1 s h6 g 4 = (-s, 0, -1) := rfl

theorem k24mtdY_inj {b1 s h6 g : ℝ} (hb1 : 1 < b1) (hs : 0 < s) (hg : 0 < g) (hh6 : 1 < h6) :
    ∀ i j, k24mtdY b1 s h6 g i = k24mtdY b1 s h6 g j → i = j := by
  intro i j h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k24mtdY_0, k24mtdY_1, k24mtdY_2, k24mtdY_3, k24mtdY_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith) | (exfalso; linarith [h.1, h.2.1, h.2.2]) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; nlinarith)

set_option maxHeartbeats 12800000 in
theorem k24mtd_tsc {D b1 s h6 g v1 v2 : ℝ} (hD : 0 < D) (hb1 : 1 < b1) (hs : 0 < s) (hg : 0 < g) (hg1 : g < 1)
    (hh6 : 1 < h6) (hv2 : 0 < v2) (hv : 0 < s * v2 - v1) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (k24mtdY b1 s h6 g (i + 1) - k24mtdY b1 s h6 g i) (k24mtdY b1 s h6 g j - k24mtdY b1 s h6 g i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (1 : ℝ), (0 : ℝ)), (1, 0, -b1)], ∀ i : ZMod 5,
      TSc D (k24mtdY b1 s h6 g (i + 1) - k24mtdY b1 s h6 g i) (t - k24mtdY b1 s h6 g i) (v1, v2, 0)) := by
  obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
  have hb : 0 < b1 := by linarith
  have hB : 0 < b1 - 1 := by linarith
  have hh : 0 < h6 - 1 := by linarith
  have hg' : 0 < 1 - g := by linarith
  have k1 := hD
  have p1 := mul_pos hD hb
  have p2 := mul_pos hD hs
  have p3 := mul_pos hD hg
  have p4 := mul_pos hD hg'
  have p5 := mul_pos hD (by linarith : (0:ℝ) < h6)
  have p6 := mul_pos hD hB
  have p7 := mul_pos hD hh
  have q1 := mul_pos (mul_pos hD hb) hs
  have q2 := mul_pos (mul_pos hD hb) hg
  have q3 := mul_pos (mul_pos hD hb) (by linarith : (0:ℝ) < h6)
  have q4 := mul_pos (mul_pos hD hs) hg
  have q5 := mul_pos (mul_pos hD hs) (by linarith : (0:ℝ) < h6)
  have q6 := mul_pos (mul_pos hD hs) hg'
  have q7 := mul_pos (mul_pos hD hs) hh
  have q8 := mul_pos (mul_pos hD hs) hB
  have q9 := mul_pos (mul_pos hD hg) hB
  have q10 := mul_pos (mul_pos hD hg') hh
  have q11 := mul_pos (mul_pos hD hg) (by linarith : (0:ℝ) < h6)
  have q12 := mul_pos (mul_pos hD hb) hh
  have r1 := mul_pos (mul_pos (mul_pos hD hb) hs) hg
  have r2 := mul_pos (mul_pos (mul_pos hD hb) hs) (by linarith : (0:ℝ) < h6)
  have r3 := mul_pos (mul_pos (mul_pos hD hs) hg) hB
  have r4 := mul_pos (mul_pos (mul_pos hD hb) hs) hh
  have r5 := mul_pos (mul_pos (mul_pos hD hb) hs) hg'
  have r6 := mul_pos (mul_pos (mul_pos hD hb) hs) hB
  have r7 := mul_pos (mul_pos (mul_pos hD hs) hh) hb
  have r8 := mul_pos (mul_pos (mul_pos hD hs) hg') hb
  have r9 := mul_pos (mul_pos (mul_pos hD hs) hh) hg'
  have r10 := mul_pos (mul_pos (mul_pos hD hs) hh) hg
  have kv2 := mul_pos hD hv2
  have kv := mul_pos hD hv
  have kbv2 := mul_pos (mul_pos hD hb) hv2
  have kbv := mul_pos (mul_pos hD hb) hv
  have kbbv := mul_pos (mul_pos (mul_pos hD hb) hb) hv
  have ksv2 := mul_pos (mul_pos hD hs) hv2
  have kbsv2 := mul_pos (mul_pos (mul_pos hD hb) hs) hv2
  have kBv2 := mul_pos (mul_pos hD hB) hv2
  refine ⟨?_, ?_⟩
  · intro i j h1 h2'
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, e0, e1, e2, e3, e4, f0, f1, f2, f3, f4, k24mtdY_0, k24mtdY_1, k24mtdY_2, k24mtdY_3,
          k24mtdY_4, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; nlinarith)
         | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, e0, e1, e2, e3, e4, f0, f1, f2, f3, f4, k24mtdY_0, k24mtdY_1, k24mtdY_2, k24mtdY_3,
          k24mtdY_4, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

/-- Depth algebra in frame quantities `xr = ⟪a-d,R⟫`, `yr = ⟪b-d,R⟫`, `nr = ⟪R,R⟫`; `zr = ⟪c-d,R⟫ = -s xr - nr`. -/
theorem k24mtd_depth {s g h6 b1 xr yr nr : ℝ} (hs : 0 < s) (hb1 : 1 < b1) (hh6 : 1 < h6) (hg : 0 < g) (hg1 : g < 1)
    (hYZ : -s * xr - nr < yr)
    (T1 : (1 - g) * (-s * xr - nr) - h6 * yr = 0)
    (T2 : (1 + b1 * s) * xr + (b1 - h6) * yr - g * (-s * xr - nr) = 0) :
    -s * xr - nr < 0 ∧ b1 * (s * xr + yr) < 0 ∧
      -(g * s) * xr + h6 * yr + -g * nr = (1 + b1 * s) * xr + b1 * yr := by
  have hZ : -s * xr - nr < 0 := by nlinarith
  have hid : (1 + b1 * s) * (h6 + g - 1) * (-(s * xr + yr)) =
      ((1 - g) + s * h6) * (yr - (-s * xr - nr)) := by
    linear_combination (-(h6 + g - 1) * s) * T2 + (1 + s * (h6 + g)) * T1
  have hW : 0 < -(s * xr + yr) := by
    have h1 : 0 < ((1 - g) + s * h6) * (yr - (-s * xr - nr)) := mul_pos (by nlinarith) (by linarith)
    rw [← hid] at h1
    by_contra hn
    push Not at hn
    nlinarith [mul_pos (by nlinarith : 0 < 1 + b1 * s) (by linarith : 0 < h6 + g - 1)]
  refine ⟨hZ, by nlinarith, ?_⟩
  linear_combination (-1 : ℝ) * T2

end C2
end Type08Sp
end Minimality
