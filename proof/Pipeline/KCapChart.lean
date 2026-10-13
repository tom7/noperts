module

public import Pipeline.KCapPoly
public import Pipeline.CapCover

@[expose] public section

/-!
# The charts of a balanced cap certificate

A cap around a degenerate view x blows up the poses near (x, identity)
(`nopert229/sccap.cc`; the snub cube's cap at its view u*). With an
orthogonal view frame (x, e₁, e₂) and a rotation frame (Z, E₁, X), the
chart variables are (μ, τ, p₀, p₁, p₂) and

  view      u = x + μ e (A + τ B),  (A, B) the side's pair
            (e₁, e₂), (−e₁, e₂), (e₂, e₁), (−e₂, e₁) (`sideA`, `sideB`);
  rotation  Cayley vector w = μ (s₀ Z + s₁ E₁ + s₂ X)

(every rotation component has weight 1), where (e, s) depend on the chart
kind:

* `fe`: e = 1, s = (p₀, p₁, p₂);
* `face` (axis a, sign σ): e = p₀ ∈ [0, 1], s_a = σ R, the other two s = (p₁, p₂);
* `cone` (axis a, sign σ, the identity cone): e = 1, s = (R/2) p₀ σ̂ with σ̂
  on the face (a, σ) of [−1, 1]³ (its other coordinates p₁, p₂);
* `tcone` (axis a ∈ 0…3, sign σ, the tie cone, on the tie's side): e = 1,
  (τ, s₀ − s₀*, s₁, s₂) = τ' σ̂ with τ' = the variable 1 (`τ` is not a
  variable here) and σ̂ on the face (a, σ) of [−1, 1]⁴ (its other
  coordinates p₀, p₁, p₂).

`chartU`, `chartW` are these maps as polynomial vectors, and `eval_chartU`,
`eval_chartW` their real values.
-/

namespace Noperts.Pipeline

namespace KCap

open PVec
open Noperts.Pipeline.Cap (sideA sideB view_side weighted_cube)

variable {K : Type} [ExactScalarOps K]

/-- The frames of a cap: the view frame (x, e₁, e₂), orthogonal, and the
rotation frame (Z, E₁, X), orthogonal. -/
structure Frame (K : Type) where
  x : KVec K
  e1 : KVec K
  e2 : KVec K
  Z : KVec K
  E1 : KVec K
  X : KVec K

/-- The chart parameters: the rotation range R (|s_i| ≤ R), the identity
cone's radius t₀ (it covers |s|∞ ≤ t₀ R / 2), and the tie: its side, its
s₀ (at τ = 0, s₁ = s₂ = 0), and its cone's radius. -/
structure Params where
  R : ℚ
  t0 : ℚ
  tieSide : ℕ
  tieS0 : ℚ
  tieT0 : ℚ

inductive Kind where
  | fe | face | cone | tcone
deriving DecidableEq, Repr

structure ChartId where
  kind : Kind
  side : ℕ
  axis : ℕ
  /-- true: +1, false: −1. -/
  sign : Bool
deriving DecidableEq, Repr

def signQ (b : Bool) : ℚ := if b then 1 else -1

/-- The side's pair (A, B) of view-frame vectors. -/
def sideVecs (fr : Frame K) : ℕ → KVec K × KVec K
  | 0 => (fr.e1, fr.e2)
  | 1 => (fun i => ExactScalarOps.scale (-1) (fr.e1 i), fr.e2)
  | 2 => (fr.e2, fr.e1)
  | _ => (fun i => ExactScalarOps.scale (-1) (fr.e2 i), fr.e1)

def pvar (i : Fin 5) : KPoly K 5 := KPoly.var 5 i
def pconst (q : ℚ) : KPoly K 5 := KPoly.scale 5 q kOne

/-- The chart variable of the free coordinate `i` (≠ `axis`) when the free
coordinates are numbered from `first`: `first + i` below the axis, `first +
i − 1` above (clamped to a valid index). -/
def freeVar (first axis i : ℕ) : Fin 5 :=
  ⟨min 4 (if i < axis then first + i else first + i - 1), by omega⟩

/-- A coordinate fixed on the face (axis, sign) or free. -/
def faceCoord (first axis : ℕ) (sign : Bool) (c : ℚ) (i : ℕ) : KPoly K 5 :=
  if i = axis then pconst (signQ sign * c) else pvar (freeVar first axis i)

/-- The polynomial (e, τ, s) of a chart. -/
structure ChartParams (K : Type) where
  e : KPoly K 5
  tau : KPoly K 5
  s : Fin 3 → KPoly K 5

/-- (e, τ, s₀, s₁, s₂) of a chart, as polynomials. -/
def chartParams (pr : Params) (id : ChartId) : ChartParams K :=
  match id.kind with
  | .fe => ⟨kOne, pvar 1, fun i => pvar (i.succ.succ)⟩
  | .face => ⟨pvar 2, pvar 1, fun i => faceCoord 3 id.axis id.sign pr.R i.val⟩
  | .cone => ⟨kOne, pvar 1, fun i =>
      KPoly.mul 5 (pconst (pr.R / 2)) (KPoly.mul 5 (pvar 2) (faceCoord 3 id.axis id.sign 1 i.val))⟩
  | .tcone =>
      -- σ̂ over (τ, s₀, s₁, s₂): coordinate `axis` fixed, the others p₀, p₁, p₂ (vars 2-4).
      let sig : ℕ → KPoly K 5 := faceCoord 2 id.axis id.sign 1
      ⟨kOne, KPoly.mul 5 (pvar 1) (sig 0), fun i =>
        if i.val = 0 then KPoly.add 5 (pconst pr.tieS0) (KPoly.mul 5 (pvar 1) (sig 1))
        else KPoly.mul 5 (pvar 1) (sig (i.val + 1))⟩

/-- The view u = x + μ e (A + τ B). -/
def chartU (fr : Frame K) (pr : Params) (id : ChartId) : PVec K :=
  let cp := chartParams (K := K) pr id
  let AB := sideVecs fr id.side
  PVec.add (PVec.const fr.x)
    (PVec.smul (KPoly.mul 5 (pvar 0) cp.e) (PVec.add (PVec.const AB.1) (PVec.smul cp.tau (PVec.const AB.2))))

/-- The Cayley vector w = μ (s₀ Z + s₁ E₁ + s₂ X). -/
def chartW (fr : Frame K) (pr : Params) (id : ChartId) : PVec K :=
  let cp := chartParams (K := K) pr id
  PVec.smul (pvar 0)
    (PVec.add (PVec.smul (cp.s 0) (PVec.const fr.Z))
      (PVec.add (PVec.smul (cp.s 1) (PVec.const fr.E1)) (PVec.smul (cp.s 2) (PVec.const fr.X))))

/-! ### Real values -/

theorem eval_pvar [ExactScalarVal K] (i : Fin 5) (y : Fin 5 → ℝ) : KPoly.eval 5 (pvar (K := K) i) y = y i :=
  KPoly.eval_var 5 i y

theorem eval_pconst [ExactScalarVal K] (q : ℚ) (y : Fin 5 → ℝ) : KPoly.eval 5 (pconst (K := K) q) y = q := by
  simp [pconst, KPoly.eval_scale, eval_kOne]

theorem kval_scale [ExactScalarVal K] (q : ℚ) (v : KVec K) :
    kval (fun i => ExactScalarOps.scale q (v i)) = (q : ℝ) • kval v := by
  funext i; simp [kval, ExactScalarVal.val_scale]

/-- The real side pair. -/
noncomputable def rSideVecs [ExactScalarVal K] (fr : Frame K) (side : ℕ) : (Fin 3 → ℝ) × (Fin 3 → ℝ) :=
  ((sideA side).1 • kval fr.e1 + (sideA side).2 • kval fr.e2,
   (sideB side).1 • kval fr.e1 + (sideB side).2 • kval fr.e2)

theorem kval_sideVecs [ExactScalarVal K] (fr : Frame K) (side : ℕ) :
    (kval (sideVecs fr side).1, kval (sideVecs fr side).2) = rSideVecs fr side := by
  rcases side with _ | _ | _ | side
  · simp [sideVecs, rSideVecs, sideA, sideB]
  · simp [sideVecs, rSideVecs, sideA, sideB, kval_scale]
  · simp [sideVecs, rSideVecs, sideA, sideB]
  · simp [sideVecs, rSideVecs, sideA, sideB, kval_scale]

end KCap

end Noperts.Pipeline

end
