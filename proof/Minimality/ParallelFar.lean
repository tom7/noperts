module

public import Minimality.TriShadow2Chord

@[expose] public section

/-!
# A segment parallel to the view line at a far end (codimension-2 tail)

Lemma T's general position includes "no segment of `V` parallel to the view
line". At a far end `(ca m, 0, cz m)` of the first face's chain, a second
vertex `(ca m, 0, z)` of that face on the same vertical (a segment parallel
to the view line) lies on the far edge's line at the untilted view. It is
still strictly inside the tilted shadow when it is on the chain's side
(`s * (z - cz m) < 0`) and the tilt `(-s α, s β)` of
`isRupert_triShadow2_tilt` leans toward the second face (`ca m * β < cb n * α`);
likewise at the second face's far end with the opposite ratio. Both at once
is Corollary T1's rectangle exception (FEWER-FACES-PROOFS.md §7). See
FEWER-FACES.md §11, step (ii).
-/

namespace Minimality

/-- A vertical companion of the first face's far end, on the chain's side. -/
theorem tiltOK_farComp1 {s A B zp zq zy α β : ℝ} (hc : s * (zy - zp) < 0)
    (hr : A * β < B * α) :
    TiltOK A 0 zp 0 B zq A 0 zy (-s * α) (s * β) := by
  right
  refine ⟨by ring, ?_⟩
  have e : (zq - zp) * ((A - A) * (s * β) - (0 - 0) * (-s * α)) -
      (zy - zp) * ((0 - A) * (s * β) - (B - 0) * (-s * α)) =
      (s * (zy - zp)) * (A * β - B * α) := by ring
  rw [e]
  exact mul_pos_of_neg_of_neg hc (by linarith)

/-- A vertical companion of the second face's far end, on that chain's side
(the second chain carries the sign `-s`). -/
theorem tiltOK_farComp2 {s A B zp zq zy α β : ℝ} (hc : 0 < s * (zy - zq))
    (hr : B * α < A * β) :
    TiltOK A 0 zp 0 B zq 0 B zy (-s * α) (s * β) := by
  right
  refine ⟨by ring, ?_⟩
  have e : (zq - zp) * ((0 - A) * (s * β) - (B - 0) * (-s * α)) -
      (zy - zp) * ((0 - A) * (s * β) - (B - 0) * (-s * α)) =
      (s * (zy - zq)) * (A * β - B * α) := by ring
  rw [e]
  exact mul_pos hc (by linarith)

end Minimality

end
