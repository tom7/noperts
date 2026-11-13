module

public import Minimality.Type08TouchN2
public import Minimality.Type08TouchT4
public import Minimality.Type08
public import Minimality.Type08Codim
public import Minimality.Type08R0
public import Minimality.Type08Rd
public import Minimality.Type08Flat

@[expose] public section

set_option autoImplicit true

/-!
# Type 08 (phase 1): shared definitions and the residual set `Resid08`

Shared definitions for type 08 (`Minimality.lean`, residual `Resid08Final` of `G9_Final`).
All statements are in the *used labelling* `(a, b, c)` of Lemma 6
(`Norm08`: `κ_a, κ_b > 0`, `κ_c ≠ 0`, `[b c] < 0`), pairs `(a,a')`, `(b,b')`, `(c,c')`, cap `d`.
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- The hypotheses of `isRupert_type08_slide_normalized`: the labelling of Lemma 6. -/
structure Norm08 (a a' b b' c c' d : ℝ³) where
  F : OctFacets a a' b b' c c'
  hd : IsCap F d
  G : GaleData a a' b b' c c'
  hκa : 0 < galeD G.l G.m a a'
  hκb : 0 < galeD G.l G.m b b'
  hκc : galeD G.l G.m c c' ≠ 0
  hU : galeD G.l G.m b c < 0

/-- The 14 fields of `Type08Gen`. -/
inductive F08 | tieTT | routeT | routeT' | touchN2 | touchT4 | touchTie | levelQ
  | slideN2c | slideN2a' | slideQ | slideT4b | slideT4d | flatN2 | flatT4
  deriving DecidableEq

/-- The proposition of a field of `Type08Gen`, copied from `Type08Codim.lean`. -/
def FP (a a' b b' c c' d : ℝ³) : F08 → Prop
  | .tieTT => ¬ ((∃ r : ℝ, c - a' = r • (b - d)) ∧ ∃ r : ℝ, c' - a = r • (b - d))
  | .routeT => (∃ r : ℝ, c - a' = r • (b - d)) → RouteT a a' b b' c c' d
  | .routeT' => (∃ r : ℝ, c' - a = r • (b - d)) → RouteT' a a' b b' c c' d
  | .touchN2 => (⟪b, c - a'⟫ = ⟪c', c - a'⟫ ∧ ⟪b', c - a'⟫ = ⟪c', c - a'⟫) →
      Touch30N2 a a' b b' c c' d
  | .touchT4 => (⟪c, b - d⟫ = ⟪b', b - d⟫ ∧ ⟪c', b - d⟫ = ⟪b', b - d⟫) → Touch30T4 a a' b b' c c' d
  | .touchTie => (⟪c, b - d⟫ = ⟪b', b - d⟫ ∧ ⟪c', b - d⟫ = ⟪b', b - d⟫) →
      ¬ ((∃ r : ℝ, c - a' = r • (b - d)) ∨ ∃ r : ℝ, c' - a = r • (b - d))
  | .levelQ => ⟪a - d, b - d⟫ ≠ 0 ∨ ⟪c - d, b - d⟫ ≠ 0
  | .slideN2c => NoBadNormal (quad c b c' b') (c - a') (b - c) ∨
      (UniOrSep (quint c d b c' b') (c - a') ∧
        NoBadNormal (quint c d b c' b') (c - a') (b' - c)) ∨
      RdCond c d b c' b' a'
  | .slideN2a' => NoBadNormal (quad a' b c' b') (c - a') (b - a') ∨
      NoBadNormal (quad a' b c' b') (c - a') (b' - a')
  | .slideQ => NoBadNormal (quad d a b' c) (b - d) (a - d) ∨
      NoBadNormal (quad d a b' c) (b - d) (c - d)
  | .slideT4b => NoBadNormal (quad b c' b' c) (b - d) (c - d) ∨
      (UniOrSep (quint b c' b' c a') (b - d) ∧
        NoBadNormal (quint b c' b' c a') (b - d) (a - d)) ∨
      RdCond b a' c b' c' d
  | .slideT4d => NoBadNormal (quad d c' b' c) (b - d) (a - d) ∨
      ((UniOrSep (quint d a c' b' c) (b - d) ∨
          (det3 (d - b) (c' - d) (b' - c) = 0 ∧
            ¬ NWS4 (quad ⟪b, b - d⟫ ⟪c', b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫) ∧
            ∀ i, ⟪quint d a c' b' c i, b - d⟫ ≠ ⟪quint d a c' b' c (i + 1), b - d⟫)) ∧
        NoBadNormal (quint d a c' b' c) (b - d) (c - d))
  | .flatN2 => det3 (c - b) (b' - b) (c' - b) = 0 →
      ¬ (⟪b, c - a'⟫ = ⟪b', c - a'⟫ ∧ ⟪c, c - a'⟫ = ⟪c', c - a'⟫)
  | .flatT4 => det3 (c - b) (b' - b) (c' - b) = 0 →
      ¬ (⟪b, b - d⟫ = ⟪b', b - d⟫ ∧ ⟪c, b - d⟫ = ⟪c', b - d⟫)

/-! ### The special positions T, T' and their companions at the view `ℓ` along `b - d` -/

/-- `T`: `a' c ∥ d b`. -/
def IsT (a' b c d : ℝ³) : Prop := ∃ r : ℝ, c - a' = r • (b - d)
/-- `T'`: `a c' ∥ d b`. -/
def IsT' (a b c' d : ℝ³) : Prop := ∃ r : ℝ, c' - a = r • (b - d)

/-- `H1`: the far edge `c'b'` is parallel to the plane of `Q_bc` (`α1 = α4`, §41). -/
def H1 (b b' c c' d : ℝ³) : Prop := det3 (c' - b') (b - d) (c - d) = 0
/-- `H2`: `b'c` is parallel to the plane of `Q_ab` (`γ4 = 1`, §41; at `T` equivalent to
`Q_ab ∥ a'b'c`). -/
def H2 (a b b' c d : ℝ³) : Prop := det3 (c - b') (a - d) (b - d) = 0

/-- A depth tie among `d, b, c, a', b', c'` at `ℓ` (E, first item). -/
def Tie6 (a' b b' c c' d : ℝ³) : Prop :=
  ∃ p ∈ ({d, b, c, a', b', c'} : Finset ℝ³), ∃ q ∈ ({d, b, c, a', b', c'} : Finset ℝ³),
    p ≠ q ∧ ⟪p, b - d⟫ = ⟪q, b - d⟫

/-- Class (d) HDN of `R1 = (b, c', b', c)` on `H1`: a common perpendicular of `[c', b']` and the
diagonal `[c, b]` to the plane of `Q_bc`, with both feet interior (§41.1). -/
def ClassD1 (b b' c c' d : ℝ³) : Prop :=
  H1 b b' c c' d ∧ ∃ s t : ℝ, 0 < s ∧ s < 1 ∧ 0 < t ∧ t < 1 ∧
    ⟪(c' + s • (b' - c')) - (c + t • (b - c)), b - d⟫ = 0 ∧
    ⟪(c' + s • (b' - c')) - (c + t • (b - c)), c - d⟫ = 0

/-- Class (d) HDN of `R2' = (d, c', b', c)` on `H2`: a common perpendicular of `[b', c]` and the
side `[d, c']` over `Q_ab` to the plane of `Q_ab`, both feet interior. -/
def ClassD2 (a b b' c c' d : ℝ³) : Prop :=
  H2 a b b' c d ∧ ∃ s t : ℝ, 0 < s ∧ s < 1 ∧ 0 < t ∧ t < 1 ∧
    ⟪(b' + s • (c - b')) - (d + t • (c' - d)), a - d⟫ = 0 ∧
    ⟪(b' + s • (c - b')) - (d + t • (c' - d)), b - d⟫ = 0

/-- Some corner polygon `R1, R2', X_ba', X_2a'` at `ℓ` has a horizontal double normal. -/
def PolyHDN (a' b b' c c' d : ℝ³) : Prop :=
  ¬ NoHDNAt ({b, c', b', c} : Finset ℝ³) (b - d) ∨ ¬ NoHDNAt ({d, c', b', c} : Finset ℝ³) (b - d) ∨
  ¬ NoHDNAt ({b, c', b', a'} : Finset ℝ³) (b - d) ∨ ¬ NoHDNAt ({d, c', b', a'} : Finset ℝ³) (b - d)

/-- At least two corner polygons at `ℓ` have a horizontal double normal. -/
def PolyHDN2 (a' b b' c c' d : ℝ³) : Prop :=
  (∃ S₁ S₂ : Finset ℝ³, S₁ ≠ S₂ ∧
    S₁ ∈ ({{b, c', b', c}, {d, c', b', c}, {b, c', b', a'}, {d, c', b', a'}} : Finset (Finset ℝ³)) ∧
    S₂ ∈ ({{b, c', b', c}, {d, c', b', c}, {b, c', b', a'}, {d, c', b', a'}} : Finset (Finset ℝ³)) ∧
    ¬ NoHDNAt S₁ (b - d) ∧ ¬ NoHDNAt S₂ (b - d))

/-! ### The residual set -/

/-- A far triple tie of a named closing that Proposition 30.4 does not close: `Touch30N2`,
`Touch30T4` fail, or touching together with `T`, `T'` (`Σ₃′`'s touching part). -/
def RTouch (a a' b b' c c' d : ℝ³) : Prop :=
  ¬ FP a a' b b' c c' d .touchN2 ∨ ¬ FP a a' b b' c c' d .touchT4 ∨
    ¬ FP a a' b b' c c' d .touchTie

end Type08Sp
end Minimality
