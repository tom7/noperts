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

/-- At most two independent ties at the view of group `i`, covering every tie among the labels of
group `i`'s tests (`TieOK` restricted to one group). -/
def TieOKG (i : Fin 3) (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ q : ℕ, q ≤ 2 ∧ ∃ ties : Fin q → Fin 7 × Fin 7,
    (∀ t, ⟪pts08 a a' b b' c c' d (ties t).1 - pts08 a a' b b' c c' d (ties t).2,
      (grp08 i).view (pts08 a a' b b' c c' d)⟫ = 0) ∧
    TieIndep (fun t => pts08 a a' b b' c c' d (ties t).1 - pts08 a a' b b' c c' d (ties t).2)
      (fun _ => (grp08 i).view (pts08 a a' b b' c c' d)) ∧
    (∀ T ∈ (grp08 i).tests, ∀ u v : ZMod T.k,
      T.depth (pts08 a a' b b' c c' d) u = T.depth (pts08 a a' b b' c c' d) v →
      Relation.EqvGen (fun p p' => ∃ t, ties t = (p, p')) (T.lab u) (T.lab v))

/-- **Gap (codim 3, NO paper proof):** three or more ties, or two dependent ties, at the view of the
certificate in use (29.1 (i) with ≥ 3 ties; not in 29.14's Σ₃ list nor in sp08b–f). -/
def ThreeTies {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c') (d : ℝ³) : Prop :=
  (RegN2 F ∧ ¬ TieOKG 0 a a' b b' c c' d) ∨ (RegT4 F ∧ ¬ TieOKG 1 a a' b b' c c' d)

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

/-- S2 (quadruple tie at a planar equator `b b' c c'`) at the N2 view or at the T4 view. -/
def S2any (a' b b' c c' d : ℝ³) : Prop :=
  (det3 (c - b) (b' - b) (c' - b) = 0 ∧ ⟪b, c - a'⟫ = ⟪b', c - a'⟫ ∧ ⟪c, c - a'⟫ = ⟪c', c - a'⟫) ∨
  (det3 (c - b) (b' - b) (c' - b) = 0 ∧ ⟪b, b - d⟫ = ⟪b', b - d⟫ ∧ ⟪c, b - d⟫ = ⟪c', b - d⟫)

/-- Boundary of R2″'s persistent double normal (short edge `[a', c]` against `[d, c']` along `Q_ab`'s
normal) with a foot at an end (`RouteT.r2p`'s antecedent plus an end condition; S5e). -/
def R2ppEnd (a a' b c c' d : ℝ³) : Prop :=
  ∃ Y ∈ segment ℝ d c', ∃ Y' ∈ segment ℝ a' c, Y' ≠ Y ∧ ⟪Y' - Y, b - d⟫ = 0 ∧
    ⟪Y' - Y, a - d⟫ = 0 ∧ (Y = d ∨ Y = c' ∨ Y' = a' ∨ Y' = c)

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

/-- **Σ₄ item 2 + S2 ∩ T** (sp08f §8; provisional superset, see map.md): at `T`,
(a) touching with an HDN of a corner polygon, (Q) the level face with an HDN of `R1`, S2 ∩ T,
(R2″) its end-boundary with HDNs of `R2'` and `X_ba'`. -/
def S4T (a a' b b' c c' d : ℝ³) : Prop :=
  IsT a' b c d ∧
    ((Touch a a' b b' c c' d ∧ PolyHDN a' b b' c c' d) ∨
     (LevelQac a b c d ∧ ¬ NoHDNAt ({b, c', b', c} : Finset ℝ³) (b - d)) ∨
     S2any a' b b' c c' d ∨
     (R2ppEnd a a' b c c' d ∧ ¬ NoHDNAt ({d, c', b', c} : Finset ℝ³) (b - d) ∧
       ¬ NoHDNAt ({b, c', b', a'} : Finset ℝ³) (b - d)))

/-- **Σ₄ item 1** (sp08f §8): at `T'`, the top of `Q_ac` tied between `{d, c}` and `{a, b'}`, with the
level face and an HDN of `R1 = X_bc'`, or with an HDN of `X_2a` and a second HDN, `α = 1`, or R4″'s
end-boundary.  (Superset up to HDNs shared by two polygons; see map.md.) -/
def S4Tp (a a' b b' c c' d : ℝ³) : Prop :=
  IsT' a b c' d ∧ QacTop a b b' c d ∧
    ((LevelQac a b c d ∧ ¬ NoHDNAt ({b, c', b', c} : Finset ℝ³) (b - d)) ∨
     (¬ NoHDNAt ({d, a, b', c} : Finset ℝ³) (b - d) ∧
       (TpHDN2 a b b' c c' d ∨ det3 (b' - a) (c - d) (b - d) = 0 ∨ R4ppEnd a b c c' d)))

/-- **Σ₄ item 3, `T ∩ T'`** (only possible at `κ_b = 0`, i.e. for `Norm08w`).  DOUBT: `T ∩ T'` is
codimension 2 (`T`, `T'` one affine condition each, `κ_b = 0` automatic by (T3)), so with one HDN or
one tie this is codimension 3, not 4 as sp08f §8 says. -/
def TTp (a a' b b' c c' d : ℝ³) : Prop :=
  IsT a' b c d ∧ IsT' a b c' d ∧ (PolyHDN a' b b' c c' d ∨ Tie6 a' b b' c c' d)

/-- **The residual in the labelling of `N`** (weak labelling). -/
def Sig4N {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d) : Prop :=
  S4T a a' b b' c c' d ∨ S4Tp a a' b b' c c' d ∨ TTp a a' b b' c c' d ∨ ThreeTies N.F d

/-- `Sig4N` in some weak labelling `(a, b, c)`. -/
def Sig4L (a a' b b' c c' d : ℝ³) : Prop := ∃ N : Norm08w a a' b b' c c' d, Sig4N N

/-- **`Resid08Sigma4`**: the codimension-≥4 residual of type 08 (sp08f §8), plus the codim-3 gap
`ThreeTies` (no paper proof) and the doubtful `TTp`. -/
def Resid08Sigma4 (a a' b b' c c' d : ℝ³) : Prop :=
  Sig4L a a' b b' c c' d ∨ Sig4L b b' a a' c c' d ∨ Sig4L a a' c c' b b' d ∨
  Sig4L c c' a a' b b' d ∨ Sig4L b b' c c' a a' d ∨ Sig4L c c' b b' a a' d

end Type08Sp
end Minimality
