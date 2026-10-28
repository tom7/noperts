module

public import Minimality.Type08S.Defs08
public import Minimality.Type08S.G6Tp
public import Minimality.Type08S.G6O

@[expose] public section

set_option autoImplicit true

/-!
# G6' : closings at `T` and `T'` (revised plan, consolidation.md §4)

PROVED here (frame level):
* `thm08Tp_frame` : Theorem 08.T' of sp08b §4a, in the Euclidean frame at `ℓ` of PROOFS §41.2,
  as an instance of `isRupert_of_motionCert` (explicit motion of Lemma 08.S, spin `θ = κ`):
  weak-order hypotheses of Lemma 08.2' (derived here from robustness by `lemma082p`) and the two
  inequalities (1) of Lemma 08.1 (`σ(L) < B`, `C < σ(0)`) give `IsRupert`.  NO tie condition and no
  HDN condition other than R1's class-(d) one (encoded in `Btw` for the foot depth `z*`).
* `lemma08S_core` (G6Lem.lean): the split-corner criterion itself (any affine `F` with the 8 signs).
* `lemma082p` (G6O.lean): Lemma 08.2'.

STATED (superseded by later groups): the closings in the `Norm08` labelling, with the companion sets of the revised plan.
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- **Theorem 08.T' (frame form).**  Frame at `ℓ` as in §41.2: `2 = (L,0,W)`, `b = (L,0,B)`,
`c = (0,0,C)`, `a' = (0,0,A)`, `b' = (X0,h,P)`, `c' = (X1,h,R)`, `a` on the open side
`[q, c']` below the edge `b c'` of `Q_ab`.  `zs` is the depth of the foot `P*` of R1's class-(d)
HDN; `R1` robust, `R2'` and `X_ba'` not robust; `σ(X) = P + κ (X - X0)` the line of `S*`. -/
theorem thm08Tp_frame (hF : Fr e1 e2 e3) (o : ℝ³)
    {L h X0 X1 C W B A P R t za κ zs : ℝ}
    (hL : 0 < L) (hh : 0 < h) (hX : X0 < X1) (hWB : W < B) (hCA : C < A)
    (ht0 : 0 < t) (ht1 : t < 1) (hza : za < B + t * (R - B))
    (hR1 : ¬ Sep B P C R) (hR2' : Sep W P R C) (hXba' : Sep B P R A)
    (hz1 : Btw C B zs) (hz2 : Btw P R zs)
    (hκ : κ * (X1 - X0) = R - P)
    (hσL : P + κ * (L - X0) < B) (hσ0 : C < P + κ * (0 - X0)) :
    IsRupert ({pt e1 e2 e3 o L 0 W, pt e1 e2 e3 o (L + t * (X1 - L)) (t * h) za,
      pt e1 e2 e3 o 0 0 A, pt e1 e2 e3 o L 0 B, pt e1 e2 e3 o X0 h P, pt e1 e2 e3 o 0 0 C,
      pt e1 e2 e3 o X1 h R} : Finset ℝ³) := by
  obtain ⟨hWC, hPC, hCB, hBR, -, -⟩ := lemma082p hR1 hR2' hXba' hz1 hz2 hWB
  exact thm08Tp_core hF o hL hh hX hWB hCA ht0 ht1 hza hWC hPC hCB hBR hκ hσL hσ0

/-! ### Companion sets of the revised plan (consolidation §4: tie parts of `CoT` dropped) -/

/-- Two distinct tied pairs among the six depths at `ℓ` (18.5's "two ties"). -/
def TwoTies (a' b b' c c' d : ℝ³) : Prop :=
  ∃ p ∈ ({d, b, c, a', b', c'} : Finset ℝ³), ∃ q ∈ ({d, b, c, a', b', c'} : Finset ℝ³),
  ∃ r ∈ ({d, b, c, a', b', c'} : Finset ℝ³), ∃ s ∈ ({d, b, c, a', b', c'} : Finset ℝ³),
    p ≠ q ∧ r ≠ s ∧ ({p, q} : Finset ℝ³) ≠ {r, s} ∧
    ⟪p, b - d⟫ = ⟪q, b - d⟫ ∧ ⟪r, b - d⟫ = ⟪s, b - d⟫

/-- Class-(d) HDN of R1 on H1 with a foot at an END of a segment (closed parameters, one at 0/1). -/
def FootEnd1 (b b' c c' d : ℝ³) : Prop :=
  H1 b b' c c' d ∧ ∃ s t : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ 0 ≤ t ∧ t ≤ 1 ∧ (s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) ∧
    ⟪(c' + s • (b' - c')) - (c + t • (b - c)), b - d⟫ = 0 ∧
    ⟪(c' + s • (b' - c')) - (c + t • (b - c)), c - d⟫ = 0

/-- Same for R2' on H2. -/
def FootEnd2 (a b b' c c' d : ℝ³) : Prop :=
  H2 a b b' c d ∧ ∃ s t : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ 0 ≤ t ∧ t ≤ 1 ∧ (s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) ∧
    ⟪(b' + s • (c - b')) - (d + t • (c' - d)), a - d⟫ = 0 ∧
    ⟪(b' + s • (c - b')) - (d + t • (c' - d)), b - d⟫ = 0

/-- **Revised companion set at `T`** (consolidation §4, G6' row).  Dropped from the old `CoT`:
`Tie6` alone, `IsT'` (empty under `Norm08`, G2 `norm08_tieTT'`).  Kept: `H1 ∩ H2` (until SC),
class-(d) foot at a segment end, two independent HDNs, `β = 1` / level face (item (e)), and the
18.1-branch exceptions: two ties, a tie at an HDN of a corner polygon (`Tie6 ∧ PolyHDN`), a
non-class-(d) HDN.  The last two are a superset of what 18.1/18.5 excludes (the exact list
depends on which polygon is robust; see handoff G6'). -/
def CoT2 (a a' b b' c c' d : ℝ³) : Prop :=
  (H1 b b' c c' d ∧ H2 a b b' c d) ∨ FootEnd1 b b' c c' d ∨ FootEnd2 a b b' c c' d ∨
    PolyHDN2 a' b b' c c' d ∨ TwoTies a' b b' c c' d ∨ (Tie6 a' b b' c c' d ∧ PolyHDN a' b b' c c' d) ∨
    (PolyHDN a' b b' c c' d ∧ ¬ (ClassD1 b b' c c' d ∨ ClassD2 a b b' c c' d)) ∨
    det3 (a - d) (b' - c) (b - d) = 0 ∨ (⟪a - d, b - d⟫ = 0 ∧ ⟪c - d, b - d⟫ = 0)

/-- **Revised companion set at `T'`** (29.13; codimension 3).  After G6' `close_T'2'`: an HDN of the
planar corner polygon `X_2a = (d, a, b', c)` (one metric condition on `T'`), or the level face of
`Q_ac` (`a`, `c` at the depth of `d`).  The old `TwoTies`, `Tie6 ∧ HDN`, `det3 (b' - a) (c - d) (b - d) = 0`
items are no longer needed (the planar polygon is robust unless level; a middle over `[c, d]` and
doubles over `d`, `a` are automatic). -/
def CoT'2 (a a' b b' c c' d : ℝ³) : Prop :=
  ¬ NoHDNAt ({d, a, b', c} : Finset ℝ³) (b - d) ∨ (⟪a - d, b - d⟫ = 0 ∧ ⟪c - d, b - d⟫ = 0)

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.thm08Tp_frame
