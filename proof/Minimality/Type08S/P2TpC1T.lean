module

public import Minimality.Type08S.P2TpU1

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# T'X, cell C1: the orientation tests of the 6-cycle `(d, a, b', c, a', b)` and of `c'`
Frame coordinates relative to the paper's picture (`d = (-v1, 0, 0)`, `b = d + ν e3`, ...).
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- The cell-`C1` rim `(d, a, b', c, a', b)` in frame coordinates. -/
def c1rim (ν v1 ha w1 w3 C0 α4 γ4 β6 γ6 : ℝ) : ZMod 6 → ℝ × ℝ × ℝ :=
  six (-v1, 0, 0) (-v1 + w1, ha, w3) (-v1 * (1 - γ4) + α4 * w1, α4 * ha, α4 * w3 + γ4 * C0)
    (0, 0, C0) (-v1 * (1 - γ6), 0, γ6 * C0 + β6 * ν) (-v1, 0, ν)

set_option maxHeartbeats 1600000 in
theorem tpC1_cyc {σ t1 t2 ν v1 ha w1 w3 C0 α4 γ4 β6 γ6 : ℝ}
    (hν : 0 < ν) (hha : 0 < ha) (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hE : 1 < α4 + γ4)
    (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hconv : 1 < β6 + γ6)
    (hv : σ * v1 < 0) (hp : 0 < σ * (ha * t1 - w1 * t2)) (ht2 : 0 < t2)
    (h2 : 0 < σ * ((α4 - 1) * ha * t1 - (γ4 * v1 + (α4 - 1) * w1) * t2)) :
    ∀ i j : ZMod 6, j ≠ i → j ≠ i + 1 →
      LT σ t1 t2 (c1rim ν v1 ha w1 w3 C0 α4 γ4 β6 γ6 i) (c1rim ν v1 ha w1 w3 C0 α4 γ4 β6 γ6 (i + 1))
        (c1rim ν v1 ha w1 w3 C0 α4 γ4 β6 γ6 j) := by
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := z6_add_one
  have hr : 0 < -(σ * v1) := by linarith
  have k1 := mul_pos (mul_pos hr hha) hγ4
  have k2 := mul_pos hr hha
  have k3 := mul_pos (mul_pos hr hha) hγ6
  have k4 := mul_pos (mul_pos hr hha) (sub_pos.2 hE)
  have hg : 0 < γ4 + γ6 * (α4 - 1) := by nlinarith
  have k5 := mul_pos (mul_pos hr hha) hg
  have k6 := mul_pos (mul_pos (mul_pos hr hha) hα4) (sub_pos.2 hγ61)
  have k7 := mul_pos (mul_pos hr hha) hα4
  have k8 := mul_pos (mul_pos hr hha) (sub_pos.2 hγ61)
  have k9 := mul_pos (mul_pos (mul_pos hr hha) hα4) hγ6
  have f1 := mul_pos (mul_pos hr ht2) (mul_pos hν (sub_pos.2 hconv))
  have f2 := mul_pos (mul_pos hr ht2) hν
  have f3 := mul_pos (mul_pos hr ht2) (mul_pos hν hγ6)
  have f4 := mul_pos hν hp
  have f5 := mul_pos hν h2
  have f6 := mul_pos hr (mul_pos ht2 (mul_pos hν hγ6))
  have f7 := mul_pos (mul_pos hr ht2) (mul_pos hν (sub_pos.2 hconv))
  have f8 := mul_pos hν (mul_pos hα4 hp)
  have f9 := mul_pos (mul_pos hr ht2) (mul_pos hν hγ4)
  have f10 := mul_pos hr (mul_pos ht2 hν)
  have f11 := mul_pos (mul_pos hr ht2) (mul_pos hν (sub_pos.2 hconv))
  have f12 := mul_pos (mul_pos hr ht2) (mul_pos hν hβ6)
  intro i j h1 h2'
  rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2' (by decide)).elim
    | (simp only [LT, ori, fo, c1rim, s0, s1, s2, s3, s4, s5, six_0, six_1, six_2, six_3, six_4, six_5]
       first
       | (left; linarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 1600000 in
theorem tpC1_rest {σ t1 t2 ν v1 ha w1 w3 C0 α4 γ4 β1 β6 γ6 : ℝ}
    (hν : 0 < ν) (hha : 0 < ha) (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hE : 1 < α4 + γ4) (hβ1 : 0 < β1)
    (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hv : σ * v1 < 0) (hp : 0 < σ * (ha * t1 - w1 * t2))
    (h2 : 0 < σ * ((α4 - 1) * ha * t1 - (γ4 * v1 + (α4 - 1) * w1) * t2)) :
    ∀ i : ZMod 6,
      LT σ t1 t2 (c1rim ν v1 ha w1 w3 C0 α4 γ4 β6 γ6 i) (c1rim ν v1 ha w1 w3 C0 α4 γ4 β6 γ6 (i + 1))
        (-v1 + w1, ha, w3 + β1 * ν) := by
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := z6_add_one
  have hr : 0 < -(σ * v1) := by linarith
  have k2 := mul_pos hr hha
  have k4 := mul_pos (mul_pos hr hha) (sub_pos.2 hE)
  have k8 := mul_pos (mul_pos hr hha) (sub_pos.2 hγ61)
  have k3 := mul_pos (mul_pos hr hha) hγ6
  have f4 := mul_pos (mul_pos hβ1 hν) hp
  have f5 := mul_pos (mul_pos hβ1 hν) h2
  have f6 := mul_pos hν hp
  intro i
  rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [LT, ori, fo, c1rim, s0, s1, s2, s3, s4, s5, six_0, six_1, six_2, six_3, six_4, six_5]
     first
     | (left; linarith)
     | (right; refine ⟨by ring, by linarith⟩))

end Type08Sp
end Minimality
