module

public import Minimality.TriShadow

@[expose] public section

/-!
# The triangle-shadow lemma over an edge

Lemma T of `FEWER-FACES-PROOFS.md` §7 when two vertices lie over the apex: an
edge of `K` parallel to the view (an edge view, as in Theorems E–L).  The cycle
of the tilt `-s r1 + s r2` is `C1` from the apex vertex `C1 0` out along the first
ray to `A`, then `C2` reversed from `B` in along the second ray to the other apex
vertex `C2 0`, then the vertical edge back to `C1 0`; `s z(C2 0) < s z(C1 0)`.
-/

namespace Minimality

open Finset Filter Topology
open scoped RealInnerProductSpace

/-- The cycle position `v` over an edge apex: `C1 v` for `v ≤ m`, else
`C2 (m + n + 1 - v)`. -/
noncomputable def triPt2 (O r1 r2 : ℝ²) (m n : ℕ) (ca cz cb dz : ℕ → ℝ) (v : ℕ) : ℝ³ :=
  if v ≤ m then oblPt O r1 r2 (ca v) 0 (cz v)
  else oblPt O r1 r2 0 (cb (m + n + 1 - v)) (dz (m + n + 1 - v))

noncomputable def triZ2 (m n : ℕ) (cz dz : ℕ → ℝ) (v : ℕ) : ℝ :=
  if v ≤ m then cz v else dz (m + n + 1 - v)

/-- The test of Lemma 8.0 (β) for the vertical edge over the apex. -/
theorem vert_tiltOK {s zp zq ay by' zy : ℝ} (h : 0 < s * (zq - zp)) (hy : 0 < ay + by') :
    TiltOK 0 0 zp 0 0 zq ay by' zy (-s) s := by
  right; refine ⟨by ring, ?_⟩
  nlinarith [mul_pos h hy]

end Minimality

end
