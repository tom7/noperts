module

public import Minimality.Type08S.G1_Sel
public import Minimality.Type08S.G3p
public import Minimality.Type08S.GT_Wrap28

@[expose] public section

set_option autoImplicit true

/-!
# G9: final assembly of type 08 (scratch)

`norm08_rupert_or_resN`: in the labelling of `Norm08`, Rupert or `ResN`.
`type08_rupert_or_resid`: facet form; Rupert or `Resid08Final`.
-/

set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- The far triple tie of N2 (`z b = z c' = z b'` along `c - a'`). -/
def TieN2 (a a' b b' c c' : ℝ³) : Prop :=
  ⟪b, c - a'⟫ = ⟪c', c - a'⟫ ∧ ⟪b', c - a'⟫ = ⟪c', c - a'⟫

/-- The far triple tie of T4 (`z c = z b' = z c'` along `b - d`). -/
def TieT4 (b b' c c' d : ℝ³) : Prop :=
  ⟪c, b - d⟫ = ⟪b', b - d⟫ ∧ ⟪c', b - d⟫ = ⟪b', b - d⟫

/-- The hypotheses of `gt_far_N2''` other than the tie (the far triple tie is Rupert when they hold). -/
def N2Closable {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) : Prop :=
  N.F.abc'.f a' < N.F.abc'.f c ∧ N.F.ab'c'.f a' < N.F.ab'c'.f c ∧
    ⟪a', c - a'⟫ < ⟪b', c - a'⟫ ∧ ⟪b', c - a'⟫ ≤ ⟪c, c - a'⟫

/-- The hypotheses of `gt_far_T4'` other than the tie. -/
def T4Closable {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) : Prop :=
  N.F.abc'.f c < N.F.abc'.f a' ∧ N.F.a'bc.f c' < N.F.a'bc.f a ∧
    ⟪d, b - d⟫ < ⟪c, b - d⟫ ∧ ⟪c, b - d⟫ ≤ ⟪b, b - d⟫

/-- At most two independent depth ties, covering all ties of the three closing groups
(the hypotheses `q ≤ 2`, `hties`, `hind`, `hcover` of `isRupert_type08_limit_hdn`). -/
def TieOK (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ q : ℕ, q ≤ 2 ∧ ∃ ties : Fin q → Fin 3 × Fin 7 × Fin 7,
    (∀ t, ⟪pts08 a a' b b' c c' d (ties t).2.1 - pts08 a a' b b' c c' d (ties t).2.2,
      (grp08 (ties t).1).view (pts08 a a' b b' c c' d)⟫ = 0) ∧
    TieIndep (fun t => pts08 a a' b b' c c' d (ties t).2.1 - pts08 a a' b b' c c' d (ties t).2.2)
      (fun t => (grp08 (ties t).1).view (pts08 a a' b b' c c' d)) ∧
    (∀ i, ∀ T ∈ (grp08 i).tests, ∀ u v : ZMod T.k,
      T.depth (pts08 a a' b b' c c' d) u = T.depth (pts08 a a' b b' c c' d) v →
      Relation.EqvGen (fun p p' => ∃ t, (ties t).1 = i ∧ (ties t).2 = (p, p')) (T.lab u) (T.lab v))

/-- Two planar equators (`S3`). -/
def PlanarTwo (a a' b b' c c' : ℝ³) : Prop :=
  ¬ (¬ (det3 (c - b) (b' - b) (c' - b) = 0 ∧ det3 (c - a) (a' - a) (c' - a) = 0) ∧
      ¬ (det3 (c - b) (b' - b) (c' - b) = 0 ∧ det3 (b - a) (a' - a) (b' - a) = 0) ∧
      ¬ (det3 (c - a) (a' - a) (c' - a) = 0 ∧ det3 (b - a) (a' - a) (b' - a) = 0))

/-- A planar equator together with a failure of the old general position `GenSelFlat`. -/
def PlanarGen (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ (F : OctFacets a a' b b' c c') (_ : IsCap F d) (G : GaleData a a' b b' c c'),
    (galeD G.l G.m a a' = 0 ∨ galeD G.l G.m b b' = 0 ∨ galeD G.l G.m c c' = 0) ∧ ¬ GenSelFlat G d

end Type08Sp
end Minimality

