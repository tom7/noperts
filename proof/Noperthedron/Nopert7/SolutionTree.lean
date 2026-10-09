module

public import Noperthedron.PentagonalHexecontahedron.AtlasProjectiveEdgeCertificate
public import Noperthedron.PentagonalHexecontahedron.AtlasLocalCertificate
public import Noperthedron.PentagonalHexecontahedron.AtlasProjectiveLocalCertificate
public import Noperthedron.PentagonalHexecontahedron.AtlasProjectiveLocalViewTree
public import Noperthedron.PentagonalHexecontahedron.AtlasProjectiveGlobalCertificate
public import Noperthedron.PentagonalHexecontahedron.AtlasProjectiveMixedGlobalCertificate
public import Noperthedron.ParallelBool
public import Noperthedron.Nopert7.CellPrune
public import Noperthedron.Nopert7.ViewCoverData
public import Noperthedron.Nopert7.CapLeaf

@[expose] public section

/-!
# Solution trees for the 7-vertex solid

The DH's `AtlasProjectiveSolutionTree` re-targeted to K (`solid`): a chart
table's rows cover the atlas root box `AtlasPose.rootInterval` (all four
charts, no fivefold narrowing) for the poses the C3v reduction
(`exists_c3v_atlas_translated_pose_solid`) leaves: Cayley-bounded, relative
rotation chart · cayley in the C3v cell at the view (`InCell`), view in D′
(`InDomain`). Rows:

- splits (`cayleySplit`, `cayleySplitAt`, `viewSplit`), `regionRelax`, and
  `codeRoot` (the view of D′ lies over a code triangle in its root,
  `ViewCover.codeTriangles_cover`, checked in the kernel);
- certificate leaves as in the DH (`projective`, `projectiveGlobal`,
  `projectiveMixedGlobal`, `symmetryLocal`, `projectiveLocal`,
  `symmetryTube` against the shared identity-tube tables, `radiusPrune`),
  for the exact model (`exactModel`, whose hull is `solid`);
- `c3Prune` (pack tag 13, journal `pi`) and `mirrorPrune` (tag 14, journal
  `ph`): the exact cell prunes of `CellPrune`;
- `capLeaf` (tag 16, journal `cl`): `capLeaf_sound`, given a checked cap
  certificate (`CapOk`).

No fivefold/icosahedral/half-turn/upper-view predicates, no tie rows.
-/

namespace Noperthedron.Nopert7.SolutionTree

open Noperthedron.PentagonalHexecontahedron
open CayleyAtlas AtlasProjectiveView
open Noperthedron.Atlas.ProjectiveView

abbrev Interval := AtlasInterval ℚ
abbrev Triangle := AtlasProjectiveView.Triangle ℚ

/-- The view of an atlas pose (row 2 of its outer rotation). -/
noncomputable def poseView (p : AtlasPose ℝ) : Fin 3 → ℝ := fun k => rotRM_mat p.θ p.φ 0 2 k

/-- The relative rotation lies in the C3v cell at the view. -/
def InCell (chart : ChartIndex) (p : AtlasPose ℝ) : Prop :=
  InC3vCell (poseView p) (chartMatrix chart * cayleyMatrix p.x p.y p.z)

/-- The view lies in D′. -/
def InDomain (p : AtlasPose ℝ) : Prop := InC3vViewDomain (poseView p)

/-- A checked cap certificate exists (`Caps.certOk`). -/
def CapOk : Prop := ∃ c : Cap.CapCert, certOk c = true

/-- The identity-tube tables, one per code triangle, in
`ViewCover.codeTriangles` order. -/
abbrev SharedLocalTables := Array AtlasProjectiveLocalViewTree.Table

def SharedLocalValid (shared : SharedLocalTables) : Prop :=
  ∀ index (h : index < shared.size), shared[index].Valid

instance (shared : SharedLocalTables) :
    Decidable (SharedLocalValid shared) := by
  unfold SharedLocalValid
  infer_instance

inductive Region where
  | sphere
  | triangle (root : Fin 8) (value : Triangle)
deriving DecidableEq

def Region.Mem : Region → AtlasPose ℝ → Prop
  | .sphere, _ => True
  | .triangle root value, p =>
      1 ≤ viewScale root p ∧
        InTriangle (toReal value) (normalizedView root p)

def NoRupert (chart : ChartIndex) (interval : Interval) (region : Region) : Prop :=
  ¬ ∃ p ∈ interval.toReal, p.CayleyBounded ∧ InCell chart p ∧ InDomain p ∧
    ∃ offset : ℝ², region.Mem p ∧ RupertPose (p.matrixPoseWithOffset chart offset) solid

theorem noRupert_halves (chart : ChartIndex) (interval : Interval)
    (region : Region) (coordinate : Fin 5)
    (hlower : NoRupert chart (interval.lowerHalf coordinate) region)
    (hupper : NoRupert chart (interval.upperHalf coordinate) region) :
    NoRupert chart interval region := by
  rintro ⟨p, hp, hrest⟩
  rcases AtlasInterval.mem_imp_mem_lowerHalf_or_upperHalf coordinate hp with hl | hu
  · exact hlower ⟨p, hl, hrest⟩
  · exact hupper ⟨p, hu, hrest⟩

theorem noRupert_cut (chart : ChartIndex) (interval : Interval)
    (region : Region) (coordinate : Fin 5) (t : ℚ)
    (hlower : NoRupert chart (interval.lowerAt coordinate t) region)
    (hupper : NoRupert chart (interval.upperAt coordinate t) region) :
    NoRupert chart interval region := by
  rintro ⟨p, hp, hrest⟩
  rcases AtlasInterval.mem_imp_mem_lowerAt_or_upperAt coordinate t hp with hl | hu
  · exact hlower ⟨p, hl, hrest⟩
  · exact hupper ⟨p, hu, hrest⟩

def minAbsBound (lo hi : ℚ) : ℚ :=
  if lo ≤ 0 ∧ 0 ≤ hi then 0 else min |lo| |hi|

def Interval.outsideCayleyBall (interval : Interval) : Prop :=
  minAbsBound interval.min.x interval.max.x ^ 2 +
    minAbsBound interval.min.y interval.max.y ^ 2 +
    minAbsBound interval.min.z interval.max.z ^ 2 > 3

instance (interval : Interval) : Decidable interval.outsideCayleyBall := by
  unfold Interval.outsideCayleyBall minAbsBound
  infer_instance

private theorem minAbsBound_le_abs {lo hi : ℚ} {x : ℝ}
    (hx : x ∈ Set.Icc (lo : ℝ) (hi : ℝ)) :
    (minAbsBound lo hi : ℚ) ≤ |x| := by
  unfold minAbsBound
  split_ifs with hcross
  · norm_num
  · by_cases hlo : lo ≤ 0
    · have hhi : ¬ 0 ≤ hi := fun hhi => hcross ⟨hlo, hhi⟩
      have hhiQ : hi < 0 := lt_of_not_ge hhi
      have hhiR : (hi : ℝ) < 0 := by exact_mod_cast hhiQ
      have hx0 : x < 0 := hx.2.trans_lt hhiR
      have hmin : min |lo| |hi| ≤ |hi| := min_le_right _ _
      have hminR : ((min |lo| |hi| : ℚ) : ℝ) ≤ ((|hi| : ℚ) : ℝ) := by
        exact_mod_cast hmin
      exact hminR.trans (by
        rw [Rat.cast_abs, abs_of_neg hhiR, abs_of_neg hx0]
        linarith [hx.2])
    · have hloQ : 0 < lo := lt_of_not_ge hlo
      have hloR : (0 : ℝ) < lo := by exact_mod_cast hloQ
      have hx0 : 0 < x := hloR.trans_le hx.1
      have hmin : min |lo| |hi| ≤ |lo| := min_le_left _ _
      have hminR : ((min |lo| |hi| : ℚ) : ℝ) ≤ ((|lo| : ℚ) : ℝ) := by
        exact_mod_cast hmin
      exact hminR.trans (by
        rw [Rat.cast_abs, abs_of_pos hloR, abs_of_pos hx0]
        exact hx.1)

theorem noRupert_of_outsideCayleyBall (chart : ChartIndex)
    (interval : Interval) (region : Region)
    (h : interval.outsideCayleyBall) : NoRupert chart interval region := by
  rintro ⟨p, hp, hbounded, -⟩
  have hmem := AtlasInterval.mem_toReal_iff.mp hp
  have hx := minAbsBound_le_abs (hmem 2)
  have hy := minAbsBound_le_abs (hmem 3)
  have hz := minAbsBound_le_abs (hmem 4)
  have hx0 : (0 : ℝ) ≤ (minAbsBound interval.min.x interval.max.x : ℚ) := by
    unfold minAbsBound
    split_ifs <;> positivity
  have hy0 : (0 : ℝ) ≤ (minAbsBound interval.min.y interval.max.y : ℚ) := by
    unfold minAbsBound
    split_ifs <;> positivity
  have hz0 : (0 : ℝ) ≤ (minAbsBound interval.min.z interval.max.z : ℚ) := by
    unfold minAbsBound
    split_ifs <;> positivity
  have hxsq := (sq_le_sq₀ hx0 (abs_nonneg p.x)).2 hx
  have hysq := (sq_le_sq₀ hy0 (abs_nonneg p.y)).2 hy
  have hzsq := (sq_le_sq₀ hz0 (abs_nonneg p.z)).2 hz
  simp only [sq_abs] at hxsq hysq hzsq
  have hout : (3 : ℝ) <
      (minAbsBound interval.min.x interval.max.x : ℚ) ^ 2 +
      (minAbsBound interval.min.y interval.max.y : ℚ) ^ 2 +
      (minAbsBound interval.min.z interval.max.z : ℚ) ^ 2 := by
    exact_mod_cast h
  unfold AtlasPose.CayleyBounded at hbounded
  nlinarith

/-! ## Relaxed view triangles (as in the DH) -/

def cornerWeights (outer : Triangle) (point : AtlasProjectiveView.Vector ℚ) : ℚ × ℚ :=
  let ax := outer 1 0 - outer 0 0
  let ay := outer 1 1 - outer 0 1
  let bx := outer 2 0 - outer 0 0
  let by_ := outer 2 1 - outer 0 1
  let px := point 0 - outer 0 0
  let py := point 1 - outer 0 1
  let det := ax * by_ - ay * bx
  ((px * by_ - py * bx) / det, (ax * py - ay * px) / det)

def cornerInWith (outer : Triangle) (point : AtlasProjectiveView.Vector ℚ)
    (su : ℚ × ℚ) : Bool :=
  decide (0 ≤ su.1 ∧ 0 ≤ su.2 ∧ su.1 + su.2 ≤ 1 ∧
    ∀ c : Fin 3, point c =
      (1 - su.1 - su.2) * outer 0 c + su.1 * outer 1 c + su.2 * outer 2 c)

def cornerInB (outer : Triangle) (point : AtlasProjectiveView.Vector ℚ) : Bool :=
  cornerInWith outer point (cornerWeights outer point)

def triangleWithinB (outer inner : Triangle) : Bool :=
  cornerInB outer (inner 0) && cornerInB outer (inner 1) && cornerInB outer (inner 2)

theorem inTriangle_of_cornerInWith {outer : Triangle}
    {point : AtlasProjectiveView.Vector ℚ} {su : ℚ × ℚ}
    (h : cornerInWith outer point su = true) :
    InTriangle (toReal outer) (fun c => (point c : ℝ)) := by
  unfold cornerInWith at h
  rw [decide_eq_true_iff] at h
  obtain ⟨hs, hu, hsum, heq⟩ := h
  refine ⟨![((1 - su.1 - su.2 : ℚ) : ℝ), (su.1 : ℝ), (su.2 : ℝ)], ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp <;> norm_cast <;> linarith
  · simp [Fin.sum_univ_three]
    ring
  · funext c
    have hc := congrArg (fun q : ℚ => (q : ℝ)) (heq c)
    simp only [affinePoint, toReal, Fin.sum_univ_three]
    rw [hc]
    push_cast
    simp

theorem inTriangle_of_triangleWithinB {outer inner : Triangle}
    (h : triangleWithinB outer inner = true) {point : AtlasProjectiveView.Vector ℝ}
    (hmem : InTriangle (toReal inner) point) :
    InTriangle (toReal outer) point := by
  simp only [triangleWithinB, Bool.and_eq_true] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  obtain ⟨v0, hv0, hs0, he0⟩ := inTriangle_of_cornerInWith h0
  obtain ⟨v1, hv1, hs1, he1⟩ := inTriangle_of_cornerInWith h1
  obtain ⟨v2, hv2, hs2, he2⟩ := inTriangle_of_cornerInWith h2
  obtain ⟨w, hw, hsum, hpoint⟩ := hmem
  simp only [Fin.sum_univ_three] at hs0 hs1 hs2 hsum
  refine ⟨fun i => w 0 * v0 i + w 1 * v1 i + w 2 * v2 i, ?_, ?_, ?_⟩
  · intro i
    have := hw 0; have := hw 1; have := hw 2
    have := hv0 i; have := hv1 i; have := hv2 i
    positivity
  · simp only [Fin.sum_univ_three]
    linear_combination w 0 * hs0 + w 1 * hs1 + w 2 * hs2 + hsum
  · rw [hpoint]
    funext c
    have e0 := congrFun he0 c
    have e1 := congrFun he1 c
    have e2 := congrFun he2 c
    simp only [affinePoint, toReal, Fin.sum_univ_three] at e0 e1 e2 ⊢
    rw [e0, e1, e2]
    ring

/-! ## The cell at a view given by a projective region -/

theorem inCell_of_region {p : AtlasPose ℝ} {chart : ChartIndex} {root : Fin 8}
    {T : Triangle} (hcell : InCell chart p) (hscale : 1 ≤ viewScale root p)
    {w : Fin 3 → ℝ} (hw : normalizedView root p = affinePoint (toReal T) w) :
    InC3vCell (MirrorPrune.viewOf T w) (chartMatrix chart * cayleyMatrix p.x p.y p.z) := by
  have hκ : viewScale root p ≠ 0 := by linarith
  apply inC3vCell_smul hκ
  have hview : viewScale root p • MirrorPrune.viewOf T w = poseView p := by
    funext k
    have hk := congrFun hw k
    simp only [normalizedView] at hk
    simp only [Pi.smul_apply, smul_eq_mul, MirrorPrune.viewOf, poseView]
    have : (∑ c, w c * (T c k : ℝ)) = affinePoint (toReal T) w k := by
      simp [affinePoint, toReal]
    rw [this, ← hk, mul_div_cancel₀ _ hκ, ViewCover.viewVector_eq]
  rw [hview]
  exact hcell

/-! ## Rows -/

/-- The default code triangle (never used by a valid `codeRoot`). -/
def defaultCode : Fin 8 × Triangle := (0, rootTriangle 0)

inductive Row where
  | cayleySplit (id lowerChild upperChild : ℕ) (coordinate : Fin 5)
      (interval : Interval) (region : Region)
  | viewSplit (id : ℕ) (children : Fin 4 → ℕ)
      (interval : Interval) (root : Fin 8) (triangle : Triangle)
  | projective (id : ℕ) (box : AtlasProjectiveEdgeCertificate.Box)
  | projectiveGlobal (id : ℕ) (box : AtlasProjectiveGlobalCertificate.Box)
  | projectiveMixedGlobal (id : ℕ) (box : AtlasProjectiveMixedGlobalCertificate.Box)
  | symmetryLocal (id : ℕ) (box : AtlasLocalCertificate.Box) (region : Region)
  | projectiveLocal (id : ℕ) (box : AtlasProjectiveLocalCertificate.Box)
  /-- Rigidity-tube leaf (pack tag 6): the view region is a sub-triangle
  (along `path`) of the identity-tube table `sharedIndex`'s base triangle, and
  the tube is within the radius certified at the deepest table node on that
  path. -/
  | symmetryTube (id : ℕ) (tube : AtlasProjectiveLocalViewTree.Tube)
      (sharedIndex : ℕ) (path : List (Fin 4)) (region : Region)
  /-- Split D′ into the code triangles (`ViewCover.codeTriangles`, each in
  its root); child `t` gets code triangle `t` (pack tag 10). -/
  | codeRoot (id : ℕ) (children : Array ℕ) (interval : Interval)
  | radiusPrune (id : ℕ) (interval : Interval) (region : Region)
  /-- C3 cell prune (pack tag 13, journal `pi n`): tr(R c_{n+1}) > tr R on the box. -/
  | c3Prune (id : ℕ) (box : C3Prune.Box) (region : Region)
  /-- Replace the view triangle by a larger `outer` one (pack tag 11). -/
  | regionRelax (id child : ℕ) (interval : Interval) (root : Fin 8)
      (triangle outer : Triangle)
  /-- Split one coordinate at a rational point (pack tag 12). -/
  | cayleySplitAt (id lowerChild upperChild : ℕ) (coordinate : Fin 5) (cut : ℚ)
      (interval : Interval) (region : Region)
  /-- Mirror prune (pack tag 14, journal `ph g`): over the view triangle and
  the box, tr(H_u R Q_g) > tr R. -/
  | mirrorPrune (id : ℕ) (box : MirrorPrune.Box) (root : Fin 8)
  /-- Cap leaf (pack tag 16, journal `cl`): a chart-0 box and view triangle
  inside the certified cap (`capLeafOk`). -/
  | capLeaf (id : ℕ) (interval : Interval) (root : Fin 8) (triangle : Triangle) (cap : ℕ)

def Row.id : Row → ℕ
  | .cayleySplit id .. | .viewSplit id .. | .projective id .. | .projectiveGlobal id .. |
      .projectiveMixedGlobal id .. | .symmetryLocal id .. | .projectiveLocal id .. |
      .symmetryTube id .. | .codeRoot id .. | .radiusPrune id .. | .c3Prune id .. |
      .regionRelax id .. | .cayleySplitAt id .. | .mirrorPrune id .. | .capLeaf id .. => id

def Row.interval : Row → Interval
  | .cayleySplit _ _ _ _ interval _ => interval
  | .viewSplit _ _ interval _ _ => interval
  | .projective _ box => box.interval
  | .projectiveGlobal _ box => box.interval
  | .projectiveMixedGlobal _ box => box.interval
  | .symmetryLocal _ box _ => box.interval
  | .projectiveLocal _ box => box.interval
  | .symmetryTube _ tube .. => tube.interval
  | .codeRoot _ _ interval => interval
  | .radiusPrune _ interval _ => interval
  | .c3Prune _ box _ => box.interval
  | .regionRelax _ _ interval _ _ _ => interval
  | .cayleySplitAt _ _ _ _ _ interval _ => interval
  | .mirrorPrune _ box _ => box.interval
  | .capLeaf _ interval _ _ _ => interval

def Row.region : Row → Region
  | .cayleySplit _ _ _ _ _ region => region
  | .viewSplit _ _ _ root triangle => .triangle root triangle
  | .projective _ box => .triangle box.root box.triangle
  | .projectiveGlobal _ box => .triangle box.root box.triangle
  | .projectiveMixedGlobal _ box => .triangle box.root box.triangle
  | .symmetryLocal _ _ region => region
  | .projectiveLocal _ box => .triangle box.root box.triangle
  | .symmetryTube _ _ _ _ region => region
  | .codeRoot .. => .sphere
  | .radiusPrune _ _ region => region
  | .c3Prune _ _ region => region
  | .regionRelax _ _ _ root triangle _ => .triangle root triangle
  | .cayleySplitAt _ _ _ _ _ _ region => region
  | .mirrorPrune _ box root => .triangle root box.triangle
  | .capLeaf _ _ root triangle _ => .triangle root triangle

instance : Inhabited Row where
  default := .radiusPrune 0 (AtlasPose.rootInterval ℚ) .sphere

def SymmetryTubeMatches (tube : AtlasProjectiveLocalViewTree.Tube)
    (path : List (Fin 4)) (region : Region) : Option AtlasProjectiveLocalViewTree.Table → Prop
  | none => False
  | some table =>
      tube.symmetryIndex = table.symmetryIndex ∧
      match table.findNodePrefix path with
      | none => False
      | some (nodeId, rest) =>
          nodeId < table.size ∧ tube.r ≤ (table.get nodeId).rLower ∧
          region = .triangle (table.get nodeId).root
            (AtlasProjectiveLocalViewTree.splitPath (table.get nodeId).triangle rest)

instance (tube : AtlasProjectiveLocalViewTree.Tube) (path : List (Fin 4)) (region : Region)
    (table : Option AtlasProjectiveLocalViewTree.Table) :
    Decidable (SymmetryTubeMatches tube path region table) := by
  cases table
  · simp only [SymmetryTubeMatches]
    infer_instance
  · simp only [SymmetryTubeMatches]
    split <;> infer_instance

def Row.ValidAt (chart : ChartIndex) (get : ℕ → Row)
    (size : ℕ) (shared : SharedLocalTables) : Row → Prop
  | .cayleySplit id lowerChild upperChild coordinate interval region =>
      id < lowerChild ∧ id < upperChild ∧
      lowerChild < size ∧ upperChild < size ∧
      (get lowerChild).interval = interval.lowerHalf coordinate ∧
      (get upperChild).interval = interval.upperHalf coordinate ∧
      (get lowerChild).region = region ∧
      (get upperChild).region = region
  | .viewSplit id children interval root triangle => ∀ child,
      id < children child ∧ children child < size ∧
      (get (children child)).interval = interval ∧
      (get (children child)).region = .triangle root (split triangle child)
  | .projective _ box => box.chart = chart ∧ box.Valid
  | .projectiveGlobal _ box => box.chart = chart ∧ box.Valid
  | .projectiveMixedGlobal _ box => box.chart = chart ∧ box.Valid
  | .symmetryLocal _ box _ => box.chart = chart ∧ box.Valid
  | .projectiveLocal _ box => box.chart = chart ∧ box.Valid
  | .symmetryTube _ tube sharedIndex path region =>
      tube.chart = chart ∧ tube.Valid ∧
        SymmetryTubeMatches tube path region shared[sharedIndex]?
  | .radiusPrune _ interval _ => interval.outsideCayleyBall
  | .c3Prune _ box _ => box.chart = chart ∧ box.Valid
  | .cayleySplitAt id lowerChild upperChild coordinate cut interval region =>
      id < lowerChild ∧ id < upperChild ∧
      lowerChild < size ∧ upperChild < size ∧
      (get lowerChild).interval = interval.lowerAt coordinate cut ∧
      (get upperChild).interval = interval.upperAt coordinate cut ∧
      (get lowerChild).region = region ∧
      (get upperChild).region = region
  | .regionRelax id child interval root triangle outer =>
      id < child ∧ child < size ∧
      (get child).interval = interval ∧
      (get child).region = .triangle root outer ∧
      triangleWithinB outer triangle = true
  | .mirrorPrune _ box _ => box.chart = chart ∧ box.Valid
  | .capLeaf _ interval _ triangle _ => chart = 0 ∧ capLeafOk interval triangle = true
  | .codeRoot id children interval =>
      children.size = ViewCover.codeTriangles.size ∧
      ∀ t (ht : t < children.size),
        id < children[t] ∧ children[t] < size ∧
        (get children[t]).interval = interval ∧
        (get children[t]).region = .triangle (ViewCover.codeTriangles.getD t defaultCode).1
          (ViewCover.codeTriangles.getD t defaultCode).2

instance (chart : ChartIndex) (get : ℕ → Row) (size : ℕ)
    (shared : SharedLocalTables) (row : Row) :
    Decidable (row.ValidAt chart get size shared) := by
  cases row <;> simp only [Row.ValidAt] <;> infer_instance

def RowsValidAt (chart : ChartIndex) (get : ℕ → Row)
    (size : ℕ) (shared : SharedLocalTables) : Prop :=
  ∀ i : Fin size, (get i).id = i ∧ (get i).ValidAt chart get size shared

instance (chart : ChartIndex) (get : ℕ → Row) (size : ℕ)
    (shared : SharedLocalTables) :
    Decidable (RowsValidAt chart get size shared) := by
  unfold RowsValidAt
  infer_instance

/-- The certificate leaves' conclusions for the exact model, about `solid`. -/
theorem not_rupert_solid {p : AtlasPose ℝ} {chart : ChartIndex} {offset : ℝ²}
    (h : ¬ RupertPose (p.matrixPoseWithOffset chart offset) exactModel.polyhedron.hull) :
    ¬ RupertPose (p.matrixPoseWithOffset chart offset) solid := by
  rwa [exactModel_hull_eq_solid] at h

theorem valid_imp_noRupert_ix (chart : ChartIndex) (get : ℕ → Row)
    (size : ℕ) (shared : SharedLocalTables)
    (sharedValid : SharedLocalValid shared) (hcap : CapOk)
    (rowsValid : RowsValidAt chart get size shared)
    (i : ℕ) (hi : i < size) :
    NoRupert chart (get i).interval (get i).region := by
  obtain ⟨hid, hvalid⟩ := rowsValid ⟨i, hi⟩
  generalize hrow : get i = row at hid hvalid ⊢
  cases row with
  | projective id box =>
      rintro ⟨p, hp, hbounded, -, -, offset, hregion, hrupert⟩
      obtain ⟨hchart, hbox⟩ := hvalid
      subst hchart
      exact not_rupert_solid (box.valid_imp_not_translated_rupert (P := exactModel) hbox hp
        hbounded offset hregion.1 hregion.2) hrupert
  | projectiveGlobal id box =>
      rintro ⟨p, hp, hbounded, -, -, offset, hregion, hrupert⟩
      obtain ⟨hchart, hbox⟩ := hvalid
      subst hchart
      exact not_rupert_solid (box.valid_imp_not_translated_rupert (P := exactModel) hbox p hp
        hbounded hregion.1 hregion.2 offset) hrupert
  | projectiveMixedGlobal id box =>
      rintro ⟨p, hp, hbounded, -, -, offset, hregion, hrupert⟩
      obtain ⟨hchart, hbox⟩ := hvalid
      subst hchart
      exact not_rupert_solid (box.valid_imp_not_translated_rupert (P := exactModel) hbox p hp
        hbounded hregion.1 hregion.2 offset) hrupert
  | symmetryLocal id box region =>
      rintro ⟨p, hp, -, -, -, offset, -, hrupert⟩
      obtain ⟨hchart, hbox⟩ := hvalid
      subst hchart
      exact not_rupert_solid (box.valid_imp_not_translated_rupert (P := exactModel) hbox p hp
        offset) hrupert
  | projectiveLocal id box =>
      rintro ⟨p, hp, -, -, -, offset, hregion, hrupert⟩
      obtain ⟨hchart, hbox⟩ := hvalid
      subst hchart
      exact not_rupert_solid (box.valid_imp_not_translated_rupert (P := exactModel) hbox hp
        offset hregion.1 hregion.2) hrupert
  | symmetryTube id tube sharedIndex path region =>
      rintro ⟨p, hp, -, -, -, offset, hregion, hrupert⟩
      obtain ⟨hchart, htube, hmatch⟩ := hvalid
      subst hchart
      cases hshared : shared[sharedIndex]? with
      | none => simp [SymmetryTubeMatches, hshared] at hmatch
      | some table =>
          obtain ⟨hidx, htableEq⟩ := Array.getElem?_eq_some_iff.mp hshared
          have htable : table.Valid := htableEq ▸ sharedValid sharedIndex hidx
          rw [hshared] at hmatch
          obtain ⟨hsymmetry, hfind⟩ := hmatch
          split at hfind
          · exact hfind.elim
          · rename_i nodeId rest _
            obtain ⟨hnode, hradius, hregionEq⟩ := hfind
            rw [hregionEq] at hregion
            exact not_rupert_solid (table.valid_imp_not_translated_rupert_below_node
              (P := exactModel) htable nodeId hnode rest tube hsymmetry hradius htube hp offset
              hregion.1 hregion.2) hrupert
  | codeRoot id children interval =>
      rintro ⟨p, hp, hbounded, hcell, hdom, offset, -, hrupert⟩
      obtain ⟨t, root, tri, hget, hscale, hin⟩ := ViewCover.codeTriangles_cover p hdom
      obtain ⟨htlt, htri⟩ := Array.getElem?_eq_some_iff.mp hget
      obtain ⟨hsize, hall⟩ := hvalid
      have ht : t < children.size := hsize ▸ htlt
      obtain ⟨hforward, hchildSize, hchildInterval, hchildRegion⟩ := hall t ht
      have hchild := valid_imp_noRupert_ix chart get size shared sharedValid hcap rowsValid
        children[t] hchildSize
      rw [hchildInterval, hchildRegion] at hchild
      have hgetD : ViewCover.codeTriangles.getD t defaultCode = (root, tri) := by
        simp [Array.getD, htlt, htri]
      rw [hgetD] at hchild
      exact hchild ⟨p, hp, hbounded, hcell, hdom, offset, ⟨hscale, hin⟩, hrupert⟩
  | cayleySplit id lowerChild upperChild coordinate interval region =>
      obtain ⟨hlower, hupper, hlowerSize, hupperSize,
        hlowerInterval, hupperInterval, hlowerRegion, hupperRegion⟩ := hvalid
      apply noRupert_halves chart interval region coordinate
      · rw [← hlowerInterval, ← hlowerRegion]
        exact valid_imp_noRupert_ix chart get size shared sharedValid hcap rowsValid
          lowerChild hlowerSize
      · rw [← hupperInterval, ← hupperRegion]
        exact valid_imp_noRupert_ix chart get size shared sharedValid hcap rowsValid
          upperChild hupperSize
  | viewSplit id children interval root triangle =>
      rintro ⟨p, hp, hbounded, hcell, hdom, offset, hregion, hrupert⟩
      obtain ⟨child, hchildMem⟩ := mem_split hregion.2
      obtain ⟨hforward, hchildSize, hchildInterval, hchildRegion⟩ := hvalid child
      have hchild := valid_imp_noRupert_ix chart get size shared sharedValid hcap rowsValid
        (children child) hchildSize
      rw [hchildInterval, hchildRegion] at hchild
      exact hchild ⟨p, hp, hbounded, hcell, hdom, offset, ⟨hregion.1, hchildMem⟩, hrupert⟩
  | cayleySplitAt id lowerChild upperChild coordinate cut interval region =>
      obtain ⟨hlower, hupper, hlowerSize, hupperSize,
        hlowerInterval, hupperInterval, hlowerRegion, hupperRegion⟩ := hvalid
      apply noRupert_cut chart interval region coordinate cut
      · rw [← hlowerInterval, ← hlowerRegion]
        exact valid_imp_noRupert_ix chart get size shared sharedValid hcap rowsValid
          lowerChild hlowerSize
      · rw [← hupperInterval, ← hupperRegion]
        exact valid_imp_noRupert_ix chart get size shared sharedValid hcap rowsValid
          upperChild hupperSize
  | regionRelax id child interval root triangle outer =>
      rintro ⟨p, hp, hbounded, hcell, hdom, offset, hregion, hrupert⟩
      obtain ⟨hforward, hchildSize, hchildInterval, hchildRegion, hwithin⟩ := hvalid
      have hchild := valid_imp_noRupert_ix chart get size shared sharedValid hcap rowsValid
        child hchildSize
      rw [hchildInterval, hchildRegion] at hchild
      exact hchild ⟨p, hp, hbounded, hcell, hdom, offset,
        ⟨hregion.1, inTriangle_of_triangleWithinB hwithin hregion.2⟩, hrupert⟩
  | radiusPrune id interval region =>
      exact noRupert_of_outsideCayleyBall chart interval region hvalid
  | c3Prune id box region =>
      rintro ⟨p, hp, -, hcell, -⟩
      obtain ⟨hchart, hbox⟩ := hvalid
      subst hchart
      exact box.valid_imp_not_inCell hbox hp _ hcell
  | mirrorPrune id box root =>
      rintro ⟨p, hp, -, hcell, -, -, hregion, -⟩
      obtain ⟨hchart, hbox⟩ := hvalid
      obtain ⟨w, hw0, hw1, hw⟩ := hregion.2
      subst hchart
      exact box.valid_imp_not_inCell hbox hp w hw0 (by rw [hw1]; norm_num)
        (inCell_of_region hcell hregion.1 hw)
  | capLeaf id interval root triangle cap =>
      rintro ⟨p, hp, -, hcell, -, offset, hregion, hrupert⟩
      obtain ⟨hchart, hok⟩ := hvalid
      subst hchart
      obtain ⟨c, hc⟩ := hcap
      exact capLeaf_sound c hc interval root triangle hok p hp hcell
        (lt_of_lt_of_le one_pos hregion.1) hregion.2 offset hrupert
termination_by size - i
decreasing_by
  all_goals
    have : id = i := by simpa [Row.id, hrow] using hid
    omega

structure Table where
  chart : ChartIndex
  get : ℕ → Row
  size : ℕ
  sharedLocal : SharedLocalTables := #[]

def Table.Valid (table : Table) : Prop :=
  0 < table.size ∧
    RowsValidAt table.chart table.get table.size table.sharedLocal ∧
    (table.get 0).interval = AtlasPose.rootInterval ℚ ∧
    (table.get 0).region = .sphere ∧
    SharedLocalValid table.sharedLocal

instance (table : Table) : Decidable table.Valid := by
  unfold Table.Valid
  infer_instance

/-! ## Parallel executable checker -/

def validIxAtB (chart : ChartIndex) (get : ℕ → Row) (size : ℕ)
    (shared : SharedLocalTables) (i : ℕ) : Bool :=
  if i < size then
    decide ((get i).id = i ∧ (get i).ValidAt chart get size shared)
  else true

theorem validIxAtB_eq_true_iff (chart : ChartIndex) (get : ℕ → Row)
    (size : ℕ) (shared : SharedLocalTables) (i : ℕ) :
    validIxAtB chart get size shared i = true ↔
      (i < size → (get i).id = i ∧ (get i).ValidAt chart get size shared) := by
  unfold validIxAtB
  split
  · rename_i h
    rw [decide_eq_true_iff]
    exact ⟨fun hv _ => hv, fun hv => hv h⟩
  · rename_i h
    simp only [true_iff]
    exact fun h' => absurd h' h

def rowsValidAtParB (chart : ChartIndex) (get : ℕ → Row) (size : ℕ)
    (shared : SharedLocalTables) (taskCount : ℕ) : Bool :=
  Noperthedron.ParallelBool.allParB (validIxAtB chart get size shared) size taskCount

theorem rowsValidAt_of_parB {chart : ChartIndex} {get : ℕ → Row}
    {size : ℕ} {shared : SharedLocalTables} {taskCount : ℕ}
    (h : rowsValidAtParB chart get size shared taskCount = true) :
    RowsValidAt chart get size shared := by
  intro i
  have hindex := Noperthedron.ParallelBool.all_of_parB h i.val i.isLt
  rw [validIxAtB_eq_true_iff] at hindex
  exact hindex i.isLt

def tableRootB (table : Table) : Bool :=
  decide (0 < table.size ∧ (table.get 0).interval = AtlasPose.rootInterval ℚ ∧
    (table.get 0).region = .sphere)

def tableCoreValidParB (table : Table) (taskCount : ℕ) : Bool :=
  tableRootB table &&
    rowsValidAtParB table.chart table.get table.size table.sharedLocal taskCount

/-- The native row tasks used by `tableCoreValidWithTasksB`. -/
def tableCoreTasks (table : Table) (taskCount : ℕ) : List (Task Bool) :=
  let chunkSize := table.size / taskCount + 1
  Noperthedron.ParallelBool.chunkTasks
    (validIxAtB table.chart table.get table.size table.sharedLocal) taskCount chunkSize

def tableCoreValidWithTasksB (table : Table) (taskCount : ℕ)
    (tasks : List (Task Bool)) : Bool :=
  let chunkSize := table.size / taskCount + 1
  tableRootB table && Noperthedron.ParallelBool.allWithTasksB table.size taskCount chunkSize tasks

theorem Table.Valid.of_parB {table : Table} {taskCount : ℕ}
    (hshared : SharedLocalValid table.sharedLocal)
    (h : tableCoreValidParB table taskCount = true) : table.Valid := by
  unfold tableCoreValidParB tableRootB at h
  rw [Bool.and_eq_true, decide_eq_true_iff] at h
  exact ⟨h.1.1, rowsValidAt_of_parB h.2, h.1.2.1, h.1.2.2, hshared⟩

theorem Table.Valid.of_withTasksB {table : Table} {taskCount : ℕ}
    (hshared : SharedLocalValid table.sharedLocal)
    (h : tableCoreValidWithTasksB table taskCount (tableCoreTasks table taskCount) = true) :
    table.Valid := by
  apply Table.Valid.of_parB hshared
  exact h

/-! ## Soundness of the tables -/

theorem Table.valid_imp_no_chart_translated_pose (table : Table) (h : table.Valid)
    (hcap : CapOk) :
    ¬ ∃ p ∈ AtlasPose.rootInterval ℝ, p.CayleyBounded ∧ InCell table.chart p ∧ InDomain p ∧
      ∃ offset : ℝ², RupertPose (p.matrixPoseWithOffset table.chart offset) solid := by
  obtain ⟨hnonempty, hrows, hrootInterval, hrootRegion, hshared⟩ := h
  have hchecked := valid_imp_noRupert_ix table.chart table.get table.size
    table.sharedLocal hshared hcap hrows 0 hnonempty
  rw [hrootInterval, hrootRegion] at hchecked
  rintro ⟨p, hp, hbounded, hcell, hdom, offset, hrupert⟩
  exact hchecked ⟨p, by rw [AtlasInterval.rootInterval_toReal]; exact hp, hbounded, hcell, hdom,
    offset, trivial, hrupert⟩

/-- Four valid chart tables and a checked cap certificate exclude every matrix
pose of `solid` (via the C3v reduction `exists_c3v_atlas_translated_pose_solid`). -/
theorem no_matrixPose_of_valid_tables (table : ChartIndex → Table)
    (hchart : ∀ chart, (table chart).chart = chart)
    (hvalid : ∀ chart, (table chart).Valid) (hcap : CapOk) :
    ¬ ∃ p : MatrixPose, RupertPose p solid := by
  rintro ⟨p, hrupert⟩
  obtain ⟨chart, q, offset, hq, hbounded, -, hdom, hcell, heq⟩ :=
    exists_c3v_atlas_translated_pose_solid p
  have hno := (table chart).valid_imp_no_chart_translated_pose (hvalid chart) hcap
  rw [hchart chart] at hno
  exact hno ⟨q, hq, hbounded, hcell, hdom, offset, heq.mpr hrupert⟩

end Noperthedron.Nopert7.SolutionTree
