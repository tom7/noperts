module

public import Minimality.Type08S.P2TpU2

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# T'X, cell C2: the orientation tests of the 5-cycle `(d, a, c', b', c)` and of `a'`, `b`
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- The cell-`C2` rim `(d, a, c', b', c)` in frame coordinates. -/
def c2rim (v1 ha w1 w3 C0 α4 γ4 β1 ν : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  quint (-v1, 0, 0) (-v1 + w1, ha, w3) (-v1 + w1, ha, w3 + β1 * ν)
    (-v1 * (1 - γ4) + α4 * w1, α4 * ha, α4 * w3 + γ4 * C0) (0, 0, C0)

set_option maxHeartbeats 1600000 in
theorem tpC2_cyc {σ t1 t2 ν v1 ha w1 w3 C0 α4 γ4 β1 : ℝ}
    (hν : 0 < ν) (hha : 0 < ha) (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hE : 1 < α4 + γ4) (hβ1 : 0 < β1)
    (hv : σ * v1 < 0) (hp : 0 < σ * (ha * t1 - w1 * t2)) (ht2 : t2 < 0)
    (h2 : σ * ((α4 - 1) * ha * t1 - (γ4 * v1 + (α4 - 1) * w1) * t2) < 0) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      LT σ t1 t2 (c2rim v1 ha w1 w3 C0 α4 γ4 β1 ν i) (c2rim v1 ha w1 w3 C0 α4 γ4 β1 ν (i + 1))
        (c2rim v1 ha w1 w3 C0 α4 γ4 β1 ν j) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := zmod5_add_one
  have hr : 0 < -(σ * v1) := by linarith
  have ht : 0 < -t2 := by linarith
  have k1 := mul_pos (mul_pos hr hha) hγ4
  have k2 := mul_pos hr hha
  have k4 := mul_pos (mul_pos hr hha) (sub_pos.2 hE)
  have k7 := mul_pos (mul_pos hr hha) hα4
  have f1 := mul_pos (mul_pos hβ1 hν) hp
  have f2 := mul_pos (mul_pos hβ1 hν) (neg_pos.2 h2)
  have f3 := mul_pos (mul_pos hβ1 hν) (mul_pos hr ht)
  have f4 := mul_pos (mul_pos hβ1 hν) hp
  intro i j h1 h2'
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2' (by decide)).elim
    | (simp only [LT, ori, fo, c2rim, s0, s1, s2, s3, s4, quint_0, quint_1, quint_2, quint_3,
        quint_4]
       first
       | (left; linarith)
       | (right; refine ⟨by ring, by linarith⟩))

set_option maxHeartbeats 1600000 in
theorem tpC2_rest {σ t1 t2 ν v1 ha w1 w3 C0 α4 γ4 β1 β6 γ6 : ℝ}
    (hν : 0 < ν) (hha : 0 < ha) (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hE : 1 < α4 + γ4) (hβ1 : 0 < β1)
    (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hv : σ * v1 < 0) (hp : 0 < σ * (ha * t1 - w1 * t2)) (ht2 : t2 < 0)
    (h2 : σ * ((α4 - 1) * ha * t1 - (γ4 * v1 + (α4 - 1) * w1) * t2) < 0) :
    ∀ i : ZMod 5,
      (LT σ t1 t2 (c2rim v1 ha w1 w3 C0 α4 γ4 β1 ν i) (c2rim v1 ha w1 w3 C0 α4 γ4 β1 ν (i + 1))
        (-v1 * (1 - γ6), 0, γ6 * C0 + β6 * ν)) ∧
      (LT σ t1 t2 (c2rim v1 ha w1 w3 C0 α4 γ4 β1 ν i) (c2rim v1 ha w1 w3 C0 α4 γ4 β1 ν (i + 1))
        (-v1, 0, ν)) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := zmod5_add_one
  have hr : 0 < -(σ * v1) := by linarith
  have ht : 0 < -t2 := by linarith
  have hg : 0 < γ4 + γ6 * (α4 - 1) := by nlinarith
  have k1 := mul_pos (mul_pos hr hha) hγ4
  have k2 := mul_pos hr hha
  have k3 := mul_pos (mul_pos hr hha) hγ6
  have k4 := mul_pos (mul_pos hr hha) (sub_pos.2 hE)
  have k5 := mul_pos (mul_pos hr hha) hg
  have k6 := mul_pos (mul_pos (mul_pos hr hha) hα4) (sub_pos.2 hγ61)
  have k7 := mul_pos (mul_pos hr hha) hα4
  have f1 := mul_pos (mul_pos hβ1 hν) hp
  have f2 := mul_pos (mul_pos hβ1 hν) (neg_pos.2 h2)
  have f3 := mul_pos (mul_pos hβ1 hν) (mul_pos hr ht)
  have f5 := mul_pos (mul_pos hβ1 hν) (mul_pos (mul_pos hr ht) hγ6)
  have f6 := mul_pos (mul_pos hr ht) (mul_pos hν hβ6)
  have f7 := mul_pos (mul_pos hr ht) hν
  have f8 := mul_pos hν hp
  intro i
  constructor <;>
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [LT, ori, fo, c2rim, s0, s1, s2, s3, s4, quint_0, quint_1, quint_2, quint_3, quint_4]
     first
     | (left; linarith)
     | (right; refine ⟨by ring, by linarith⟩))

end Type08Sp
end Minimality
