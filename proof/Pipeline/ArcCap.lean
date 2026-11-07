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
  /-- The Cayley weights: w = k₁ x E₁ + k₂ y E₂ + k₃ z X. -/
  k1 : ℚ
  k2 : ℚ
  k3 : ℚ
  /-- The rotation basis: w = k₁ x W₁ + k₂ y W₂ + k₃ z W₃ (by default the apex frame E₁, E₂, X). -/
  W1 : KCap.KVec K := E1
  W2 : KCap.KVec K := E2
  W3 : KCap.KVec K := X

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
  /-- Whether the boxes of the cone (1, −) of side 0 inside the wedge are left to the wedge
  (`wedgeBoxOk`): the arc caps, not the axis cap. -/
  wedge : Bool
  /-- The P cap (`ChartId.pu`, `ChartId.p`): the upper end of the view scale t of the wedge `p`, and whether
  the boxes of side 0 inside the wedge are left to it (`wpTest`). -/
  thi : ℚ := 0
  pwp : Bool := false

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

/-- The kinds of a chart of the wedge along a circle of views, `ChartId.p`: `fp al k sg`: α = ±1 and the
rotation on the cone over the face (k, sg) of the cube; `face0 sg`, `face1 sg`: α = p₂ and s₁ resp. s₂ = ±R;
`face2 m sg`: s₃ = ±R₃ and (s₁, s₂) by the mode m (0: both inner, 1: s₁ = ±(Z ν + p), 2: the same negative,
3, 4: the same for s₂). -/
inductive PKind where
  | fp (al : Bool) (k : ℕ) (sg : Bool)
  | face0 (sg : Bool)
  | face1 (sg : Bool)
  | face2 (m : ℕ) (sg : Bool)
deriving DecidableEq, Repr

/-- `u side k`: the side of the square, (a, b) = μ e (1, τ) (side 0), μ e (−1, τ) (side 1),
μ e (τ, 1) (side 2), μ e (τ, −1) (side 3 and above). -/
inductive ChartId where
  | u (side : ℕ) (k : UKind)
  | w (π : Piece) (k : WKind)
  /-- The U cap of the P frame: the charts `u` with the boxes of side 0 left to the wedge `p` (`coneOk`). -/
  | pu (side : ℕ) (k : UKind)
  /-- The wedge along the circle of views. -/
  | p (k : PKind)
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

/-- The Cayley vector k₁ x E₁ + k₂ y E₂ + k₃ z X. -/
def wOf (fr : Frame K) (x y z : KPoly K 5) : KCap.PVec K :=
  KCap.PVec.add (KCap.PVec.smul (pconst fr.k1 *ₚ x) (KCap.PVec.const fr.W1))
    (KCap.PVec.add (KCap.PVec.smul (pconst fr.k2 *ₚ y) (KCap.PVec.const fr.W2))
      (KCap.PVec.smul (pconst fr.k3 *ₚ z) (KCap.PVec.const fr.W3)))

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
def uCoords (pr : Params) (side : ℕ) (k : UKind) : Coords K :=
  let me := pvar 0 *ₚ uE k
  let s := uS (K := K) pr k
  ⟨if side = 0 then me else if side = 1 then pconst (-1) *ₚ me else me *ₚ pvar 1,
   if side = 0 ∨ side = 1 then me *ₚ pvar 1 else if side = 2 then me else pconst (-1) *ₚ me,
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

/-- The ranges R₁, R₂, R₃ of the wedge `p`. -/
def pR (pr : Params) : ℕ → ℚ
  | 0 => pr.R1
  | 1 => pr.R2
  | _ => pr.R3

/-- α of a chart of the wedge `p`. -/
def pAl : PKind → KPoly K 5
  | .fp al _ _ => pconst (signQ al)
  | _ => pvar 2

/-- The cone over the face (k, sg) of the cube, in the ranges R. -/
def pCone (pr : Params) (k : ℕ) (sg : Bool) (i : ℕ) : KPoly K 5 :=
  pconst (pR pr i) *ₚ (pvar 2 *ₚ faceCoord 3 k sg 1 i)

/-- s₁, s₂, s₃ of a chart of the wedge `p`, with the mode of (s₁, s₂) of `face2`. -/
def pS (pr : Params) : PKind → ℕ → KPoly K 5
  | .fp _ k sg, i => pCone pr k sg i
  | .face0 sg, i => if i = 0 then pconst (signQ sg * pr.R1) else if i = 1 then pvar 3 else pvar 4
  | .face1 sg, i => if i = 0 then pvar 3 else if i = 1 then pconst (signQ sg * pr.R2) else pvar 4
  | .face2 m sg, i =>
    if i = 2 then pconst (signQ sg * pr.R3) else
    let zp : KPoly K 5 := pconst pr.Z *ₚ pvar 0
    match m, i with
    | 0, 0 => pvar 0 *ₚ pvar 3
    | 0, _ => pvar 0 *ₚ pvar 4
    | 1, 0 => zp +ₚ pvar 3
    | 1, _ => pvar 4
    | 2, 0 => pconst (-1) *ₚ (zp +ₚ pvar 3)
    | 2, _ => pvar 4
    | 3, 0 => pvar 0 *ₚ pvar 3
    | 3, _ => zp +ₚ pvar 4
    | _, 0 => pvar 0 *ₚ pvar 3
    | _, _ => pconst (-1) *ₚ (zp +ₚ pvar 4)

/-- The chart of the wedge `p`: the view (a, b) = (t, t ν α), t = thi p₁, and
the rotation (x, y, z) = (ν t s₁, ν t s₂, ν² t² s₃) in the rotation basis. -/
def pCoords (pr : Params) (k : PKind) : Coords K :=
  let t : KPoly K 5 := pconst pr.thi *ₚ pvar 1
  let ν : KPoly K 5 := pvar 0
  ⟨t, (t *ₚ ν) *ₚ pAl k, (ν *ₚ t) *ₚ pS pr k 0, (ν *ₚ t) *ₚ pS pr k 1,
    ((ν *ₚ ν) *ₚ (t *ₚ t)) *ₚ pS pr k 2⟩

def coords (pr : Params) : ChartId → Coords K
  | .u side k => uCoords pr side k
  | .w π k => wCoords pr π k
  | .pu side k => uCoords pr side k
  | .p k => pCoords pr k

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

/-- The range of p₁. -/
def p1Box (pr : Params) (π : Piece) : ℚ × ℚ := if π = .wm then sym pr.zmid else (0, 1)

def rootBox (pr : Params) : ChartId → Box
  | .u _ .fe => ![(0, pr.mu0), (-1, 2), sym pr.R, sym pr.R, sym pr.S]
  | .u _ (.face ax _) => ![(0, pr.mu0), (-1, 2), (0, 1), sym (faceFree pr ax).1, sym (faceFree pr ax).2]
  | .u _ (.cone _ _) => ![(0, pr.mu0), (-1, 2), (0, 1), (-1, 2), (-1, 2)]
  | .w π (.fe _ _) => ![(0, pr.nu0), p1Box pr π, (0, pr.R1), sym pr.R2, sym pr.R3]
  | .w π (.cone _ _ _) => ![(0, pr.nu0), p1Box pr π, (0, 1), (-1, 2), (-1, 2)]
  | .w π (.face0 _) => ![(0, pr.nu0), p1Box pr π, (-1, 2), sym pr.R2, sym pr.R3]
  | .w π (.face1 x _) => ![(0, pr.nu0), p1Box pr π, (-1, 2), s1Box pr x, sym pr.R3]
  | .w π (.face2 x _) => ![(0, pr.nu0), p1Box pr π, (-1, 2), s1Box pr x, sym pr.R2]
  | .pu _ .fe => ![(0, pr.mu0), (-1, 2), sym pr.R, sym pr.R, sym pr.S]
  | .pu _ (.face ax _) => ![(0, pr.mu0), (-1, 2), (0, 1), sym (faceFree pr ax).1, sym (faceFree pr ax).2]
  | .pu _ (.cone _ _) => ![(0, pr.mu0), (-1, 2), (0, 1), (-1, 2), (-1, 2)]
  | .p (.fp _ _ _) => ![(0, pr.nu0), (0, 1), (0, 1), (-1, 2), (-1, 2)]
  | .p (.face0 _) => ![(0, pr.nu0), (0, 1), (-1, 2), sym pr.R2, sym pr.R3]
  | .p (.face1 _) => ![(0, pr.nu0), (0, 1), (-1, 2), sym pr.R1, sym pr.R3]
  | .p (.face2 m _) =>
    if m = 0 then ![(0, pr.nu0), (0, 1), (-1, 2), sym pr.Z, sym pr.Z]
    else if m ≤ 2 then ![(0, pr.nu0), (0, 1), (-1, 2), (0, pr.R1), sym pr.R2]
    else ![(0, pr.nu0), (0, 1), (-1, 2), sym pr.Z, (0, pr.R2)]

/-- The chart variables divided out of a tuple polynomial: all ≥ 0 on the root box. -/
def redVars : ChartId → List (Fin 5)
  | .u _ (.cone _ _) => [0, 2]
  | .u _ _ => [0]
  | .w .wm (.cone _ _ _) => [0, 2]
  | .w .wm _ => [0]
  | .w _ (.cone _ _ _) => [0, 1, 2]
  | .w _ _ => [0, 1]
  | .pu _ (.cone _ _) => [0, 2]
  | .pu _ _ => [0]
  | .p (.fp _ _ _) => [0, 1, 2]
  | .p _ => [0, 1]

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

/-- The largest absolute value of coordinate i on a box. -/
def mxB (box : Box) (i : Fin 5) : ℚ := max |(box i).1| |(box i).1 + (box i).2|

/-- The least and the greatest e of a U chart's box. -/
def uElo (box : Box) : UKind → ℚ
  | .face _ _ => (box 2).1
  | _ => 1

def uEhi (box : Box) : UKind → ℚ
  | .face _ _ => (box 2).1 + (box 2).2
  | _ => 1

/-- Bounds of |s_i| of a U chart on a box. -/
def uSmax (pr : Params) (box : Box) : UKind → Fin 3 → ℚ
  | .fe => ![mxB box 2, mxB box 3, mxB box 4]
  | .face ax _ => fun i => if i.val = ax then |rng pr i| else mxB box (freeVar 3 ax i)
  | .cone ax _ => fun i => rc pr i * (mxB box 2 * (if i.val = ax then 1 else mxB box (freeVar 3 ax i)))

/-- The box of a U chart's side 0 lies in the wedge `p` (weighted cube of radius ν₀): with e at least
e_lo > 0, |τ| ≤ ν₀, |s₁| ≤ 2 ν₀ R₁ e, |s₀| ≤ 2 ν₀ R₂ e, |s₂| ≤ ν₀² R₃ e² and μ e ≤ thi (x = −μ s₁/2 =
ν t s₁', t = μ e, α = τ/ν₀, s₁' = −s₁/(2 ν₀ e), …). -/
def wpTest (pr : Params) (box : Box) (k : UKind) : Bool :=
  decide (0 < uElo box k ∧ mxB box 1 ≤ pr.nu0 ∧ uSmax pr box k 1 ≤ 2 * pr.nu0 * pr.R1 * uElo box k ∧
    uSmax pr box k 0 ≤ 2 * pr.nu0 * pr.R2 * uElo box k ∧ uSmax pr box k 2 ≤ pr.nu0 ^ 2 * pr.R3 * uElo box k ^ 2 ∧
    ((box 0).1 + (box 0).2) * uEhi box k ≤ pr.thi)

/-- The boxes a tree may leave to another chart: F_e boxes in the identity cone, and boxes of
the cone (1, −) of side true in the wedge. -/
def coneOk (pr : Params) : ChartId → Box → Bool
  | .u _ .fe, box => withinB box 2 0 pr.Rc && withinB box 3 0 pr.Rc && withinB box 4 0 pr.Sc
  | .u 0 (.cone 1 false), box => pr.wedge && wedgeBoxOk pr box
  | .pu side k, box =>
    (match k with
      | .fe => withinB box 2 0 pr.Rc && withinB box 3 0 pr.Rc && withinB box 4 0 pr.Sc
      | _ => false) || (pr.pwp && decide (side = 0) && wpTest pr box k)
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

/-- The U charts of some sides of the square. -/
def uCharts (sides : List ℕ) : List ChartId :=
  sides.flatMap fun side => uKinds.map (.u side)

/-- The charts of an arc cap: the sides 0 and 3 of the half square and the wedge. -/
def requiredCharts : List ChartId :=
  uCharts [0, 3] ++ ([Piece.w0, .wm, .w1, .w2].flatMap fun π => wKinds.map (.w π))

/-- The kinds of the wedge `p`. -/
def pKinds : List PKind :=
  ([true, false].flatMap fun al => (List.range 3).flatMap fun k => [true, false].map fun sg => .fp al k sg) ++
  ([true, false].flatMap fun sg => [.face0 sg, .face1 sg] ++ (List.range 5).map fun m => .face2 m sg)

/-- The charts of the P cap: the four sides of the square and the wedge. -/
def pCharts : List ChartId :=
  ([0, 1, 2, 3].flatMap fun side => uKinds.map (.pu side)) ++ pKinds.map .p

/-- The charts of an axis cap: the four sides of the square. -/
def axisCharts : List ChartId := uCharts [0, 1, 2, 3]

/-- A certificate: a tree per chart. -/
abbrev Cert := List (ChartId × KTree)

/-- Every chart of `req` has a checked tree. -/
def certCheckOn (req : List ChartId) (V : Array (KCap.KVec K)) (fr : Frame K) (pr : Params) (c : Cert) : Bool :=
  req.all fun id => c.any fun e => decide (e.1 = id) && chartCheck V fr pr id e.2

def certCheck (V : Array (KCap.KVec K)) (fr : Frame K) (pr : Params) (c : Cert) : Bool :=
  certCheckOn requiredCharts V fr pr c

/-! ### The real poses -/

section real

variable [ExactScalarVal K]

/-- The solid. -/
noncomputable def hull (V : Array (KCap.KVec K)) : Set ℝ³ :=
  convexHull ℝ {v | ∃ vj ∈ V.toList.map kval, v = Cap.toEuc vj}

noncomputable def uR (fr : Frame K) (a b : ℝ) : Fin 3 → ℝ :=
  kval fr.X - a • kval fr.E1 - b • kval fr.E2

noncomputable def wR (fr : Frame K) (x y z : ℝ) : Fin 3 → ℝ :=
  ((fr.k1 : ℝ) * x) • kval fr.W1 + (((fr.k2 : ℝ) * y) • kval fr.W2 + ((fr.k3 : ℝ) * z) • kval fr.W3)

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
  simp only [wOf, KCap.PVec.eval_add, KCap.PVec.eval_smul, KCap.PVec.eval_const, wR, eval_pconst,
    KPoly.eval_mul]

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
  have hp1 : ∀ π : Piece, 0 ≤ (p1Box pr π).2 := by
    intro π; unfold p1Box; split_ifs
    · exact hS _ h9
    · norm_num
  intro i
  cases id with
  | u side k =>
    cases k <;> fin_cases i <;> simp [rootBox, h1, h2, h3, hS, (hf _).1, (hf _).2]
  | w π k =>
    cases k <;> fin_cases i <;> simp [rootBox, h4, h5, h6, h7, hS, hx] <;> first | exact hp1 π | skip
  | pu side k =>
    cases k <;> fin_cases i <;> simp [rootBox, h1, h2, h3, hS, (hf _).1, (hf _).2]
  | p k =>
    cases k with
    | face2 m sg =>
      fin_cases i <;> simp only [rootBox] <;> split_ifs <;> simp [h4, h5, h6, h7, h8, hS]
    | _ => fin_cases i <;> simp [rootBox, h4, h5, h6, h7, h8, hS]

theorem rootBox_red {pr : Params} (id : ChartId) (y : Fin 5 → ℝ) (hy : KPoly.InBox (rootBox pr id) y) :
    ∀ i ∈ redVars id, 0 ≤ y i := by
  have h0 : 0 ≤ y 0 := by
    have := (hy 0).1
    cases id with
    | u side k => cases k <;> simpa [rootBox] using this
    | w π k => cases k <;> simpa [rootBox] using this
    | pu side k => cases k <;> simpa [rootBox] using this
    | p k =>
      cases k with
      | face2 m sg => simp only [rootBox] at this; split_ifs at this <;> simpa using this
      | _ => simpa [rootBox] using this
  have h2c : ∀ s a b, id = .u s (.cone a b) → 0 ≤ y 2 := by
    rintro s a b rfl; simpa [rootBox] using (hy 2).1
  have h2pc : ∀ s a b, id = .pu s (.cone a b) → 0 ≤ y 2 := by
    rintro s a b rfl; simpa [rootBox] using (hy 2).1
  have h2p : ∀ al k sg, id = .p (.fp al k sg) → 0 ≤ y 2 := by
    rintro al k sg rfl; simpa [rootBox] using (hy 2).1
  have h1p : ∀ k, id = .p k → 0 ≤ y 1 := by
    rintro k rfl
    have := (hy 1).1
    cases k with
    | face2 m sg => simp only [rootBox] at this; split_ifs at this <;> simpa using this
    | _ => simpa [rootBox] using this
  have h2w : ∀ π al a b, id = .w π (.cone al a b) → 0 ≤ y 2 := by
    rintro π al a b rfl; simpa [rootBox] using (hy 2).1
  have h1w : ∀ π k, π ≠ .wm → id = .w π k → 0 ≤ y 1 := by
    rintro π k hπ rfl
    have := (hy 1).1
    cases k <;> simpa [rootBox, p1Box, hπ] using this
  intro i hi
  cases id with
  | u side k =>
    cases k <;> simp [redVars] at hi <;> rcases hi with rfl | rfl <;> first | exact h0 | exact h2c _ _ _ rfl
  | w π k =>
    cases π <;> cases k <;> simp [redVars] at hi <;> (try rcases hi with rfl | rfl | rfl) <;>
      (try rcases hi with rfl | rfl) <;> (try subst hi) <;>
      first | exact h0 | exact h2w _ _ _ _ rfl | exact h1w _ _ (by simp) rfl
  | pu side k =>
    cases k <;> simp [redVars] at hi <;> rcases hi with rfl | rfl <;> first | exact h0 | exact h2pc _ _ _ rfl
  | p k =>
    cases k <;> simp [redVars] at hi <;> (try rcases hi with rfl | rfl | rfl) <;> (try rcases hi with rfl | rfl) <;>
      first | exact h0 | exact h2p _ _ _ rfl | exact h1p _ rfl

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
