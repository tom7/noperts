module

public import Pipeline.KCapTree

@[expose] public section

/-!
# Charts of a cap along an arc of views

The cap of `Pipeline.KCapChart` blows up the poses near one view U and the
identity. Near a special view with a one-parameter flex the certificates need
more: a blow-up of an arc of views. With an apex frame E₁, E₂, X (orthogonal, of
equal length, here of squared length `3²` so that (E₁, E₂, X)/3 is orthonormal),
views and Cayley vectors are written

  u = X − a E₁ − b E₂,   w = (w_x E₁ + w_y E₂ + w_z X) / 3.

*The U cap* (`ChartId.u`, side 0 or 3 of the square): the chart variables are
(μ, τ, p₂, p₃, p₄), (a, b) = μ e (1, τ) or μ e (τ, −1), and the rotation is
weighted (1, 1, 2): w_x = −μ s₁ / 2, w_y = μ s₀ / 2, w_z = μ² s₂. `(e, s)` as in
`KCapChart`: `fe`, `face` (ranges `rng`), `cone` (the anisotropic identity cone
`rc`).

*The wedge* (`ChartId.w`, four pieces): the variables are (ν, p₁, p₂, p₃, p₄),
the view is (a, b) = (t, b) with t, b per piece (`pT`, `pB`), and with the flex
f(t) (`pF`)

  w = (m₁/2) (1, f, t) + (m₂/2) (0, 1, 0) + m₃ (0, 0, 1)   (apex coordinates),
  m₁ = ν t s₁,  m₂ = ν² t s₂,  m₃ = ν² t² s₃.

`(α, s)` lie on the boundary of the cube [−1, 1] × ∏ [−R_i, R_i], and s₁ is split
at ±Z ν (`WKind`).

A checked tree of a chart makes every point of the root box `Good`
(`chart_good`): no pose over it is Rupert, whatever the view's scale and the
offset. Leaves are `Leaf.checkBy` with the chart's division `red`; the `.cone`
leaves of a tree are boxes lying in another chart (`coneOk`).
-/

namespace Noperts.Pipeline

namespace ArcCap

open Noperts.Pipeline.KCap
open Noperts.Pipeline.KCap.PVec

variable {K : Type} [ExactScalarOps K]

local infixl:65 " +ₚ " => KPoly.add 5
local infixl:65 " -ₚ " => KPoly.sub 5
local infixl:70 " *ₚ " => KPoly.mul 5

/-- The apex frame. -/
structure Frame (K : Type) where
  E1 : KCap.KVec K
  E2 : KCap.KVec K
  X : KCap.KVec K

/-- The parameters: the U cap's radius μ₀, ranges R, S and identity cone Rc, Sc;
the wedge's radius ν₀, ranges R₁, R₂, R₃ and ratio Z; the arc's regime change t*
with the margin z_h, the mid chart's radius z_m and view scale b_m; the views
t_s (the end of the second flex's piece W1) and t_e; the flexes f = c + d t. -/
structure Params where
  mu0 : ℚ
  R : ℚ
  S : ℚ
  Rc : ℚ
  Sc : ℚ
  nu0 : ℚ
  R1 : ℚ
  R2 : ℚ
  R3 : ℚ
  Z : ℚ
  tstar : ℚ
  zh : ℚ
  zmid : ℚ
  bmid : ℚ
  tsplit : ℚ
  tend : ℚ
  f0c : ℚ
  f0d : ℚ
  f1c : ℚ
  f1d : ℚ

def Params.Ok (pr : Params) : Prop :=
  0 ≤ pr.mu0 ∧ 0 ≤ pr.R ∧ 0 ≤ pr.S ∧ 0 ≤ pr.nu0 ∧ 0 ≤ pr.R1 ∧ 0 ≤ pr.R2 ∧ 0 ≤ pr.R3 ∧ 0 ≤ pr.Z ∧ 0 ≤ pr.zmid

/-! ### Chart ids -/

/-- The kinds of a U chart. -/
inductive UKind where
  | fe
  | face (ax : ℕ) (sg : Bool)
  | cone (ax : ℕ) (sg : Bool)
deriving DecidableEq, Repr

/-- How s₁ depends on a variable p: inner s₁ = ν p, or ±(Z ν + p). -/
inductive S1 where
  | i | p | m
deriving DecidableEq, Repr

/-- The kinds of a wedge chart. `fe α pos`: α = ±1, s₁ = ±(Z ν + p₂), s₂, s₃ = p₃, p₄.
`cone α ax sg`: α = ±1, s₁ = ν r, (r, s₂, s₃) = p₂ (Z, R₂, R₃) σ with σ on the face (ax, sg)
of [−1, 1]³. `face0 sg`: α = p₂, s₁ = ±R₁. `face1 x sg`: α = p₂, s₂ = ±R₂, s₃ = p₄, s₁ by x
from p₃; `face2 x sg`: the same with s₃ = ±R₃, s₂ = p₄. -/
inductive WKind where
  | fe (al pos : Bool)
  | cone (al : Bool) (ax : ℕ) (sg : Bool)
  | face0 (sg : Bool)
  | face1 (x : S1) (sg : Bool)
  | face2 (x : S1) (sg : Bool)
deriving DecidableEq, Repr

/-- The wedge's pieces: W0, Wm (the first flex), W1, W2 (the second). -/
inductive Piece where
  | w0 | wm | w1 | w2
deriving DecidableEq, Repr

/-- `u side k`: side true is (a, b) = μ e (1, τ), false is μ e (τ, −1). -/
inductive ChartId where
  | u (side : Bool) (k : UKind)
  | w (π : Piece) (k : WKind)
deriving DecidableEq, Repr

/-- The ranges of the U cube and of its identity cone. -/
def rng (pr : Params) : ℕ → ℚ
  | 0 => pr.R
  | 1 => pr.R
  | _ => pr.S

def rc (pr : Params) : ℕ → ℚ
  | 0 => pr.Rc
  | 1 => pr.Rc
  | _ => pr.Sc

/-- The inner cone's ranges of the wedge. -/
def wrc (pr : Params) : ℕ → ℚ
  | 0 => pr.Z
  | 1 => pr.R2
  | _ => pr.R3

/-! ### The polynomial charts -/

/-- The view X − a E₁ − b E₂. -/
def uOf (fr : Frame K) (a b : KPoly K 5) : KCap.PVec K :=
  KCap.PVec.sub (KCap.PVec.sub (KCap.PVec.const fr.X) (KCap.PVec.smul a (KCap.PVec.const fr.E1))) (KCap.PVec.smul b (KCap.PVec.const fr.E2))

/-- The Cayley vector (x E₁ + y E₂ + z X) / 3. -/
def wOf (fr : Frame K) (x y z : KPoly K 5) : KCap.PVec K :=
  KCap.PVec.smul (pconst (1 / 3))
    (KCap.PVec.add (KCap.PVec.smul x (KCap.PVec.const fr.E1))
      (KCap.PVec.add (KCap.PVec.smul y (KCap.PVec.const fr.E2)) (KCap.PVec.smul z (KCap.PVec.const fr.X))))

/-- The apex coordinates of a chart. -/
structure Coords (K : Type) where
  a : KPoly K 5
  b : KPoly K 5
  x : KPoly K 5
  y : KPoly K 5
  z : KPoly K 5

def uE : UKind → KPoly K 5
  | .face _ _ => pvar 2
  | _ => kOne

def uS (pr : Params) : UKind → ℕ → KPoly K 5
  | .fe, 0 => pvar 2
  | .fe, 1 => pvar 3
  | .fe, _ => pvar 4
  | .face ax sg, i => faceCoord 3 ax sg (rng pr ax) i
  | .cone ax sg, i => pconst (rc pr i) *ₚ (pvar 2 *ₚ faceCoord 3 ax sg 1 i)

/-- (a, b) on a side of the square, from the radius m. -/
def uCoords (pr : Params) (side : Bool) (k : UKind) : Coords K :=
  let me := pvar 0 *ₚ uE k
  let s := uS (K := K) pr k
  ⟨if side then me else me *ₚ pvar 1, if side then me *ₚ pvar 1 else pconst (-1) *ₚ me,
    pconst (-1 / 2) *ₚ (pvar 0 *ₚ s 1), pconst (1 / 2) *ₚ (pvar 0 *ₚ s 0),
    (pvar 0 *ₚ pvar 0) *ₚ s 2⟩

/-- α of a wedge chart. -/
def wAl : WKind → KPoly K 5
  | .fe al _ => pconst (signQ al)
  | .cone al _ _ => pconst (signQ al)
  | _ => pvar 2

/-- s₁ from a variable, by the mode. -/
def s1Of (pr : Params) (x : S1) (v : Fin 5) : KPoly K 5 :=
  match x with
  | .i => pvar 0 *ₚ pvar v
  | .p => pconst pr.Z *ₚ pvar 0 +ₚ pvar v
  | .m => pconst (-1) *ₚ (pconst pr.Z *ₚ pvar 0 +ₚ pvar v)

def wCone (pr : Params) (ax : ℕ) (sg : Bool) (i : ℕ) : KPoly K 5 :=
  pconst (wrc pr i) *ₚ (pvar 2 *ₚ faceCoord 3 ax sg 1 i)

def wS1 (pr : Params) : WKind → KPoly K 5
  | .fe _ pos => s1Of pr (if pos then .p else .m) 2
  | .cone _ ax sg => pvar 0 *ₚ wCone pr ax sg 0
  | .face0 sg => pconst (signQ sg * pr.R1)
  | .face1 x _ => s1Of pr x 3
  | .face2 x _ => s1Of pr x 3

def wS2 (pr : Params) : WKind → KPoly K 5
  | .fe _ _ => pvar 3
  | .cone _ ax sg => wCone pr ax sg 1
  | .face0 _ => pvar 3
  | .face1 _ sg => pconst (signQ sg * pr.R2)
  | .face2 _ _ => pvar 4

def wS3 (pr : Params) : WKind → KPoly K 5
  | .fe _ _ => pvar 4
  | .cone _ ax sg => wCone pr ax sg 2
  | .face0 _ => pvar 4
  | .face1 _ _ => pvar 4
  | .face2 _ sg => pconst (signQ sg * pr.R3)

/-- The view coordinate t of a piece, from α. -/
def pT (pr : Params) (π : Piece) (al : KPoly K 5) : KPoly K 5 :=
  match π with
  | .w0 => (pconst pr.tstar *ₚ (kOne -ₚ pconst pr.zh *ₚ pvar 0)) *ₚ pvar 1
  | .wm => pconst pr.tstar *ₚ (kOne -ₚ pconst pr.bmid *ₚ (pvar 0 *ₚ al) +ₚ pvar 0 *ₚ pvar 1)
  | .w1 =>
    let lo := pconst pr.tstar *ₚ (kOne +ₚ pconst pr.zh *ₚ pvar 0)
    lo +ₚ (pconst pr.tsplit -ₚ lo) *ₚ pvar 1
  | .w2 => pconst pr.tsplit +ₚ pconst (pr.tend - pr.tsplit) *ₚ pvar 1

/-- The view coordinate b of a piece, from t and α. -/
def pB (pr : Params) (π : Piece) (t al : KPoly K 5) : KPoly K 5 :=
  match π with
  | .wm => pconst pr.bmid *ₚ (pvar 0 *ₚ al)
  | _ => t *ₚ (pvar 0 *ₚ al)

/-- The flex of a piece, at t. -/
def pF (pr : Params) (π : Piece) (t : KPoly K 5) : KPoly K 5 :=
  match π with
  | .w0 | .wm => pconst pr.f0c +ₚ pconst pr.f0d *ₚ t
  | .w1 | .w2 => pconst pr.f1c +ₚ pconst pr.f1d *ₚ t

def wCoords (pr : Params) (π : Piece) (k : WKind) : Coords K :=
  let al := wAl (K := K) k
  let t := pT pr π al
  let ν := pvar (K := K) 0
  let m1 := (ν *ₚ t) *ₚ wS1 pr k
  let m2 := (ν *ₚ ν) *ₚ (t *ₚ wS2 pr k)
  let m3 := ((ν *ₚ ν) *ₚ (t *ₚ t)) *ₚ wS3 pr k
  ⟨t, pB pr π t al, pconst (1 / 2) *ₚ m1, pconst (1 / 2) *ₚ (m1 *ₚ pF pr π t +ₚ m2),
    pconst (1 / 2) *ₚ (m1 *ₚ t) +ₚ m3⟩

def coords (pr : Params) : ChartId → Coords K
  | .u side k => uCoords pr side k
  | .w π k => wCoords pr π k

def chartU (fr : Frame K) (pr : Params) (id : ChartId) : KCap.PVec K :=
  uOf fr (coords pr id).a (coords pr id).b

def chartW (fr : Frame K) (pr : Params) (id : ChartId) : KCap.PVec K :=
  wOf fr (coords pr id).x (coords pr id).y (coords pr id).z

/-! ### Root boxes, divisions, certificates -/

/-- The symmetric interval [−r, r], as (lower end, width). -/
def sym (r : ℚ) : ℚ × ℚ := (-r, 2 * r)

def s1Box (pr : Params) : S1 → ℚ × ℚ
  | .i => sym pr.Z
  | _ => (0, pr.R1)

/-- The ranges of the free coordinates of a U face. -/
def faceFree (pr : Params) (ax : ℕ) : ℚ × ℚ :=
  match ax with
  | 0 => (rng pr 1, rng pr 2)
  | 1 => (rng pr 0, rng pr 2)
  | _ => (rng pr 0, rng pr 1)

def rootBox (pr : Params) : ChartId → Box
  | .u _ .fe => ![(0, pr.mu0), (-1, 2), sym pr.R, sym pr.R, sym pr.S]
  | .u _ (.face ax _) => ![(0, pr.mu0), (-1, 2), (0, 1), sym (faceFree pr ax).1, sym (faceFree pr ax).2]
  | .u _ (.cone _ _) => ![(0, pr.mu0), (-1, 2), (0, 1), (-1, 2), (-1, 2)]
  | .w π k =>
    let p1 : ℚ × ℚ := if π = .wm then sym pr.zmid else (0, 1)
    match k with
    | .fe _ _ => ![(0, pr.nu0), p1, (0, pr.R1), sym pr.R2, sym pr.R3]
    | .cone _ _ _ => ![(0, pr.nu0), p1, (0, 1), (-1, 2), (-1, 2)]
    | .face0 _ => ![(0, pr.nu0), p1, (-1, 2), sym pr.R2, sym pr.R3]
    | .face1 x _ => ![(0, pr.nu0), p1, (-1, 2), s1Box pr x, sym pr.R3]
    | .face2 x _ => ![(0, pr.nu0), p1, (-1, 2), s1Box pr x, sym pr.R2]

/-- The chart variables divided out of a tuple polynomial: all ≥ 0 on the root box. -/
def redVars : ChartId → List (Fin 5)
  | .u _ (.cone _ _) => [0, 2]
  | .u _ _ => [0]
  | .w .wm (.cone _ _ _) => [0, 2]
  | .w .wm _ => [0]
  | .w _ (.cone _ _ _) => [0, 1, 2]
  | .w _ _ => [0, 1]

def red (id : ChartId) (q : KPoly K 5) : KPoly K 5 :=
  (redVars id).foldl (fun q i => KPoly.divOut 5 i 64 q) q

/-- The box is inside the chart side's wedge: on the cone (1, −) of side true,
|τ| ≤ ν₀, Rc t' ≤ R₁ ν₀, Rc t' |σ₁ − f(μ)| ≤ R₂ ν₀², t' |Sc σ₃ − Rc/2| ≤ R₃ ν₀²
(t' = p₂, σ₁ = p₃, σ₃ = p₄, f the first flex, decreasing). -/
def wedgeBoxOk (pr : Params) (box : Box) : Bool :=
  let hi : Fin 5 → ℚ := fun i => (box i).1 + (box i).2
  let lo : Fin 5 → ℚ := fun i => (box i).1
  let dsig := max |lo 3 - (pr.f0c + pr.f0d * lo 0)| |hi 3 - (pr.f0c + pr.f0d * hi 0)|
  let dspin := max |pr.Sc * lo 4 - pr.Rc / 2| |pr.Sc * hi 4 - pr.Rc / 2|
  decide (max |lo 1| |hi 1| ≤ pr.nu0) && decide (pr.Rc * hi 2 ≤ pr.R1 * pr.nu0) &&
    decide (pr.Rc * hi 2 * dsig ≤ pr.R2 * pr.nu0 ^ 2) && decide (hi 2 * dspin ≤ pr.R3 * pr.nu0 ^ 2)

/-- The boxes a tree may leave to another chart: F_e boxes in the identity cone, and boxes of
the cone (1, −) of side true in the wedge. -/
def coneOk (pr : Params) : ChartId → Box → Bool
  | .u _ .fe, box => withinB box 2 0 pr.Rc && withinB box 3 0 pr.Rc && withinB box 4 0 pr.Sc
  | .u true (.cone 1 false), box => wedgeBoxOk pr box
  | _, _ => false

/-- The chart data, the view and the Cayley vector forced once. -/
def chartCd (V : Array (KCap.KVec K)) (fr : Frame K) (pr : Params) (id : ChartId) : ChartData K :=
  chartDataOf (KCap.PVec.force (chartU fr pr id)) (KCap.PVec.force (chartW fr pr id)) V

def chartCheck (V : Array (KCap.KVec K)) (fr : Frame K) (pr : Params) (id : ChartId) (t : KTree) : Bool :=
  let cd := chartCd V fr pr id
  t.check (fun l box => l.checkBy V (red id) cd box) (coneOk pr id) (rootBox pr id)

/-- The U kinds and the wedge kinds. -/
def uKinds : List UKind :=
  .fe :: (List.range 3).flatMap fun ax => [true, false].flatMap fun sg => [.face ax sg, .cone ax sg]

def wKinds : List WKind :=
  ([true, false].flatMap fun al => [true, false].map fun pos => WKind.fe al pos) ++
  ([true, false].flatMap fun al => (List.range 3).flatMap fun ax => [true, false].map fun sg => .cone al ax sg) ++
  ([true, false].flatMap fun sg => .face0 sg ::
    [S1.i, .p, .m].flatMap fun x => [.face1 x sg, .face2 x sg])

def requiredCharts : List ChartId :=
  ([true, false].flatMap fun side => uKinds.map (.u side)) ++
  ([Piece.w0, .wm, .w1, .w2].flatMap fun π => wKinds.map (.w π))

/-- A certificate: a tree per chart. -/
abbrev Cert := List (ChartId × KTree)

def certCheck (V : Array (KCap.KVec K)) (fr : Frame K) (pr : Params) (c : Cert) : Bool :=
  requiredCharts.all fun id => c.any fun e => decide (e.1 = id) && chartCheck V fr pr id e.2

/-! ### The real poses -/

section real

variable [ExactScalarVal K]

/-- The solid. -/
noncomputable def hull (V : Array (KCap.KVec K)) : Set ℝ³ :=
  convexHull ℝ {v | ∃ vj ∈ V.toList.map kval, v = Cap.toEuc vj}

noncomputable def uR (fr : Frame K) (a b : ℝ) : Fin 3 → ℝ :=
  kval fr.X - a • kval fr.E1 - b • kval fr.E2

noncomputable def wR (fr : Frame K) (x y z : ℝ) : Fin 3 → ℝ :=
  (1 / 3 : ℝ) • (x • kval fr.E1 + (y • kval fr.E2 + z • kval fr.X))

/-- No pose over these apex coordinates is Rupert. -/
def Good (V : Array (KCap.KVec K)) (fr : Frame K) (a b x y z : ℝ) : Prop :=
  ∀ (p : MatrixPose) (ξ : ℝ), p.view = ξ • uR fr a b →
    p.relativeRotation = cayleyMatrix (wR fr x y z 0) (wR fr x y z 1) (wR fr x y z 2) →
    ¬ RupertPose p (hull V)

theorem eval_uOf (fr : Frame K) (a b : KPoly K 5) (y : Fin 5 → ℝ) :
    (uOf fr a b).eval y = uR fr (KPoly.eval 5 a y) (KPoly.eval 5 b y) := by
  simp only [uOf, KCap.PVec.eval_sub, KCap.PVec.eval_smul, KCap.PVec.eval_const, uR]

theorem eval_wOf (fr : Frame K) (a b c : KPoly K 5) (y : Fin 5 → ℝ) :
    (wOf fr a b c).eval y = wR fr (KPoly.eval 5 a y) (KPoly.eval 5 b y) (KPoly.eval 5 c y) := by
  simp only [wOf, KCap.PVec.eval_add, KCap.PVec.eval_smul, KCap.PVec.eval_const, wR, eval_pconst]
  push_cast
  rfl

/-- The apex coordinates' values at a chart point. -/
def PointGood (V : Array (KCap.KVec K)) (fr : Frame K) (pr : Params) (id : ChartId) (y : Fin 5 → ℝ) : Prop :=
  Good V fr (KPoly.eval 5 (coords (K := K) pr id).a y) (KPoly.eval 5 (coords (K := K) pr id).b y)
    (KPoly.eval 5 (coords (K := K) pr id).x y) (KPoly.eval 5 (coords (K := K) pr id).y y)
    (KPoly.eval 5 (coords (K := K) pr id).z y)

theorem eval_red_nonneg (vars : List (Fin 5)) (y : Fin 5 → ℝ) (hv : ∀ i ∈ vars, 0 ≤ y i) (q : KPoly K 5)
    (h : 0 ≤ KPoly.eval 5 (vars.foldl (fun q i => KPoly.divOut 5 i 64 q) q) y) : 0 ≤ KPoly.eval 5 q y := by
  induction vars generalizing q with
  | nil => simpa using h
  | cons i vs ih =>
    simp only [List.foldl_cons] at h
    have h1 := ih (fun j hj => hv j (List.mem_cons_of_mem _ hj)) _ h
    obtain ⟨m, hm⟩ := KPoly.eval_divOut 5 i y 64 q
    rw [hm]
    exact mul_nonneg (pow_nonneg (hv i List.mem_cons_self) m) h1

theorem rootBox_width {pr : Params} (hp : pr.Ok) (id : ChartId) : ∀ i, 0 ≤ (rootBox pr id i).2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hp
  have hS : ∀ r : ℚ, 0 ≤ r → 0 ≤ (sym r).2 := fun r hr => by simp [sym]; exact hr
  have hx : ∀ x, 0 ≤ (s1Box pr x).2 := by
    intro x; cases x <;> simp [s1Box, hS, h8, h5]
  have hf : ∀ ax, 0 ≤ (faceFree pr ax).1 ∧ 0 ≤ (faceFree pr ax).2 := by
    intro ax
    rcases ax with _ | _ | ax <;> simp [faceFree, rng, h2, h3]
  have hp1 : ∀ π : Piece, 0 ≤ (if π = .wm then sym pr.zmid else ((0, 1) : ℚ × ℚ)).2 := by
    intro π; split_ifs
    · exact hS _ h9
    · norm_num
  intro i
  cases id with
  | u side k =>
    cases k <;> fin_cases i <;> simp [rootBox, h1, h2, h3, hS, (hf _).1, (hf _).2]
  | w π k =>
    cases k <;> fin_cases i <;> simp [rootBox, h4, h5, h6, h7, hS, hx] <;> first | exact hp1 π | skip

theorem rootBox_red {pr : Params} (id : ChartId) (y : Fin 5 → ℝ) (hy : KPoly.InBox (rootBox pr id) y) :
    ∀ i ∈ redVars id, 0 ≤ y i := by
  have h0 : 0 ≤ y 0 := by
    have := (hy 0).1
    cases id with
    | u side k => cases k <;> simpa [rootBox] using this
    | w π k => cases k <;> simpa [rootBox] using this
  have h2c : ∀ s a b, id = .u s (.cone a b) → 0 ≤ y 2 := by
    rintro s a b rfl; simpa [rootBox] using (hy 2).1
  have h2w : ∀ π al a b, id = .w π (.cone al a b) → 0 ≤ y 2 := by
    rintro π al a b rfl; simpa [rootBox] using (hy 2).1
  have h1w : ∀ π k, π ≠ .wm → id = .w π k → 0 ≤ y 1 := by
    rintro π k hπ rfl
    have := (hy 1).1
    cases k <;> simpa [rootBox, hπ] using this
  intro i hi
  cases id with
  | u side k =>
    cases k <;> simp [redVars] at hi <;> rcases hi with rfl | rfl <;> first | exact h0 | exact h2c _ _ _ rfl
  | w π k =>
    cases π <;> cases k <;> simp [redVars] at hi <;> (try rcases hi with rfl | rfl | rfl) <;>
      (try rcases hi with rfl | rfl) <;> (try subst hi) <;>
      first | exact h0 | exact h2w _ _ _ _ rfl | exact h1w _ _ (by simp) rfl

theorem chart_leaf_good (V : Array (KCap.KVec K)) (fr : Frame K) (pr : Params) (id : ChartId) (l : Leaf) (box : Box)
    (h : l.checkBy V (red id) (chartCd V fr pr id) box = true) (hb : ∀ i, 0 ≤ (box i).2)
    (y : Fin 5 → ℝ) (hy : KPoly.InBox box y) (hr : KPoly.InBox (rootBox pr id) y) : PointGood V fr pr id y := by
  intro p ξ hview hR
  simp only [chartCd, KCap.PVec.force_eq] at h
  refine Leaf.checkBy_soundOf _ _ (red id) V l box h hb y hy
    (fun q hq => eval_red_nonneg _ y (rootBox_red id y hr) q hq) _ rfl p ξ ?_ ?_
  · rw [chartU, eval_uOf]; exact hview
  · rw [chartW, eval_wOf]; exact hR

/-- **A checked tree closes its chart**, leaving the boxes of its `.cone` leaves to `hcone`. -/
theorem chart_good (V : Array (KCap.KVec K)) (fr : Frame K) (pr : Params) (hp : pr.Ok) (id : ChartId) (t : KTree)
    (ht : chartCheck V fr pr id t = true)
    (hcone : ∀ box, coneOk pr id box = true → ∀ y, KPoly.InBox box y → KPoly.InBox (rootBox pr id) y →
      PointGood V fr pr id y) :
    ∀ y, KPoly.InBox (rootBox pr id) y → PointGood V fr pr id y := by
  intro y hy
  refine KTree.check_sound (fun l box => l.checkBy V (red id) (chartCd V fr pr id) box) (coneOk pr id)
    (fun y => KPoly.InBox (rootBox pr id) y → PointGood V fr pr id y) ?_ ?_ t (rootBox pr id)
    (rootBox_width hp id) ht y hy hy
  · intro l box hb hl y hyb hyr
    exact chart_leaf_good V fr pr id l box hl hb y hyb hyr
  · intro box _ hc y hyb hyr
    exact hcone box hc y hyb hyr

end real

end ArcCap

end Noperts.Pipeline

end
