module

public import Minimality.Type08S.SCm

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# Type 08, plan 2: definitions of the codimension-≥4 residual `Resid08Sigma4` (scratch, 2026-10-29)

Paper: `sp08f/draft.md` §8 (Σ₄), `sp08e` §2 (Proposition T*), §9; `sp08d` §4.3.  See `plan2/map.md`.
All predicates are on the seven points in the labelling `(a, a', b, b', c, c', d)` of a (weak) `Norm08`;
`ℓ := b - d` is the T4 view (and, at `T`, also the N2 view).  Paper vertex `2` is Lean `d`.

Corner polygons at `ℓ` (29.12, 29.13):
* at `T`:  `R1 = {b,c',b',c}`, `R2' = {d,c',b',c}`, `X_ba' = {b,c',b',a'}`, `X_2a' = {d,c',b',a'}`;
* at `T'`: `X_bc' = {b,c',b',c}`, `X_2c' = {d,c',b',c}`, `X_ba = {b,a,b',c}`, `X_2a = Q_ac = {d,a,b',c}`.
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-! ### Weak labelling (closure of Lemma 6's regions; planar equators allowed) -/

/-- **Provisional** closure of `Norm08`: Gale signs weak.  Package P5 must confirm (or correct) that this
is exactly what the planar-equator shapes (`PlanarTwo`, `PlanarGen`) satisfy in some labelling, and that
the limit theorem applies on it (approximation from the open region). -/
structure Norm08w (a a' b b' c c' d : ℝ³) where
  F : OctFacets a a' b b' c c'
  hd : IsCap F d
  G : GaleData a a' b b' c c'
  hκa : 0 ≤ galeD G.l G.m a a'
  hκb : 0 ≤ galeD G.l G.m b b'
  hU : galeD G.l G.m b c ≤ 0

def Norm08.toW {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) : Norm08w a a' b b' c c' d :=
  ⟨N.F, N.hd, N.G, N.hκa.le, N.hκb.le, N.hU.le⟩

/-! ### Regions of the three certificates (culJ: `γ6 > 1` N2, `γ6 < 1 < α1` T4, `γ6, α1 < 1` Q) -/

/-- N2 region (`γ6 > 1`; `hfar` of `gt_far_N2''`). -/
def RegN2 {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c') : Prop := F.abc'.f a' < F.abc'.f c

/-- T4 region (`γ6 < 1 < α1`; `hfc`, `hfc'` of `gt_far_T4'`). -/
def RegT4 {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c') : Prop :=
  F.abc'.f c < F.abc'.f a' ∧ F.a'bc.f c' < F.a'bc.f a

/-- Q region (`γ6 < 1`, `α1 < 1`; the hypotheses of `close_caseQ`). -/
def RegQ {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c') : Prop :=
  F.abc'.f c < F.abc'.f a' ∧ F.a'bc.f a < F.a'bc.f c'

/-! ### Ties of one certificate group (refinement of `TieOK`, which is global over the three groups) -/

/-! ### The HDN outcome of the refined limit theorem (robust corner rim with its own HDN) -/

/-- The single-circle closing `t` has a limit corner rim (cyclic sub-sequence `σ` of its labels) at its
view, robustly unimodal there, and this rim (not some other polygon of `V`) has a horizontal double
normal.  This is what 29.1 (ii) / 18.3 actually leave; `¬ NoHDNAt V` of `ResNC` is weaker. -/
def RobHDN (a a' b b' c c' d : ℝ³) (t : Fin 3 × Bool × Bool) : Prop :=
  ∃ (k' : ℕ) (_ : NeZero k') (σ : ZMod k' → ZMod (test08 t.1 t.2.1 t.2.2).k),
    RimCertAt (pts08 a a' b b' c c' d) ((test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d))
      ((test08 t.1 t.2.1 t.2.2).lab ∘ σ) ∧
    IsRobustUnimodal (fun i => ⟪pts08 a a' b b' c c' d ((test08 t.1 t.2.1 t.2.2).lab (σ i)),
      (test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d)⟫) ∧
    ¬ NoHDNRim (fun i => pts08 a a' b b' c c' d ((test08 t.1 t.2.1 t.2.2).lab (σ i)))
      ((test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d))

/-! ### Σ₄ items (sp08f §8) -/

/-- Level face of `Q_ac` at `ℓ` (`a`, `c` at the depth of `d`; then `b'` too). -/
def LevelQac (a b c d : ℝ³) : Prop := ⟪a - d, b - d⟫ = 0 ∧ ⟪c - d, b - d⟫ = 0

/-- The `ℓ`-maximum of `Q_ac = (d, a, b', c)` is attained both in `{d, c}` and in `{a, b'}`
(sp08f Lemma T′X's exception; includes the level face). -/
def QacTop (a b b' c d : ℝ³) : Prop :=
  max ⟪d, b - d⟫ ⟪c, b - d⟫ = max ⟪a, b - d⟫ ⟪b', b - d⟫

/-- Same for R4″ at `T'` (short edge `[c', a]` against `[c, b]` along `Q_bc`'s normal; `RouteT'.r4p`). -/
def R4ppEnd (a b c c' d : ℝ³) : Prop :=
  ∃ Y ∈ segment ℝ c' a, ∃ Y' ∈ segment ℝ c b, Y' ≠ Y ∧ ⟪Y' - Y, b - d⟫ = 0 ∧
    ⟪Y' - Y, c - d⟫ = 0 ∧ (Y = c' ∨ Y = a ∨ Y' = c ∨ Y' = b)

/-- Two distinct corner polygons at `T'` with an HDN at `ℓ`. -/
def TpHDN2 (a b b' c c' d : ℝ³) : Prop :=
  ∃ S₁ S₂ : Finset ℝ³, S₁ ≠ S₂ ∧
    S₁ ∈ ({{b, c', b', c}, {d, c', b', c}, {b, a, b', c}, {d, a, b', c}} : Finset (Finset ℝ³)) ∧
    S₂ ∈ ({{b, c', b', c}, {d, c', b', c}, {b, a, b', c}, {d, a, b', c}} : Finset (Finset ℝ³)) ∧
    ¬ NoHDNAt S₁ (b - d) ∧ ¬ NoHDNAt S₂ (b - d)

/-- **Σ₄ item 1** (sp08f §8): at `T'`, the top of `Q_ac` tied between `{d, c}` and `{a, b'}`, with the
level face and an HDN of `R1 = X_bc'`, or with an HDN of `X_2a` and a second HDN, `α = 1`, or R4″'s
end-boundary.  (Superset up to HDNs shared by two polygons; see map.md.) -/
def S4Tp (a a' b b' c c' d : ℝ³) : Prop :=
  IsT' a b c' d ∧ QacTop a b b' c d ∧
    ((LevelQac a b c d ∧ ¬ NoHDNAt ({b, c', b', c} : Finset ℝ³) (b - d)) ∨
     (¬ NoHDNAt ({d, a, b', c} : Finset ℝ³) (b - d) ∧
       (TpHDN2 a b b' c c' d ∨ det3 (b' - a) (c - d) (b - d) = 0 ∨ R4ppEnd a b c c' d)))

end Type08Sp
end Minimality
