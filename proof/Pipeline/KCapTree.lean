module

public import Pipeline.KCapCheck
public import Pipeline.KCapCover

@[expose] public section

/-!
# Balanced cap certificates: trees, charts and claims

A certificate (`search/sc/sccapcert.cc --export`) lists the solid's vertices,
the frames, the parameters, and per chart a binary subdivision tree of the
chart's root box whose leaves are balanced witnesses (`Leaf.check`) or (F_e
charts) boxes inside the identity cone or the tie cone, which the cone charts
cover. `KTree.check_sound` turns the leaf tests into a statement about every
point of the root box.
-/

namespace Noperts.Pipeline

namespace KCap

open Noperts.Pipeline.KCap.PVec

variable {K : Type} [ExactScalarOps K]

inductive KTree where
  | split (axis : Fin 5) (l r : KTree)
  | leaf (w : Leaf)
  | cone
  | fail
deriving Inhabited

/-- The lower (upper = false) or upper half of the box in coordinate a. -/
def half (box : Box) (a : Fin 5) (upper : Bool) : Box := fun i =>
  if i = a then ((box i).1 + (if upper then (box i).2 / 2 else 0), (box i).2 / 2) else box i

theorem half_width_nonneg {box : Box} (hb : ∀ i, 0 ≤ (box i).2) (a : Fin 5) (upper : Bool) :
    ∀ i, 0 ≤ (half box a upper i).2 := by
  intro i
  by_cases hi : i = a
  · simp only [half, hi, ite_true]; exact div_nonneg (hb a) (by norm_num)
  · simp only [half, hi, ite_false]; exact hb i

theorem inBox_half {box : Box} {y : Fin 5 → ℝ} (hy : KPoly.InBox box y) (a : Fin 5) :
    KPoly.InBox (half box a false) y ∨ KPoly.InBox (half box a true) y := by
  by_cases hmid : y a ≤ (box a).1 + (box a).2 / 2
  · left
    intro i
    by_cases hi : i = a
    · subst hi
      simp only [half, ite_true, Bool.false_eq_true, ite_false, add_zero]
      push_cast
      exact ⟨(hy i).1, by linarith⟩
    · simp only [half, hi, ite_false]; exact hy i
  · right
    intro i
    by_cases hi : i = a
    · subst hi
      simp only [half, ite_true]
      push_cast
      exact ⟨by linarith, by linarith [(hy i).2]⟩
    · simp only [half, hi, ite_false]; exact hy i

/-- The tree check with the leaf tests as parameters. -/
def KTree.check (leafOk : Leaf → Box → Bool) (coneOk : Box → Bool) : KTree → Box → Bool
  | .split a l r, box => l.check leafOk coneOk (half box a false) && r.check leafOk coneOk (half box a true)
  | .leaf w, box => leafOk w box
  | .cone, box => coneOk box
  | .fail, _ => false

theorem KTree.check_sound (leafOk : Leaf → Box → Bool) (coneOk : Box → Bool)
    (Good : (Fin 5 → ℝ) → Prop)
    (hleaf : ∀ w box, (∀ i, 0 ≤ (box i).2) → leafOk w box = true → ∀ y, KPoly.InBox box y → Good y)
    (hcone : ∀ box, (∀ i, 0 ≤ (box i).2) → coneOk box = true → ∀ y, KPoly.InBox box y → Good y) :
    ∀ (t : KTree) (box : Box), (∀ i, 0 ≤ (box i).2) → t.check leafOk coneOk box = true →
      ∀ y, KPoly.InBox box y → Good y
  | .split a l r, box, hb, h, y, hy => by
    simp only [KTree.check, Bool.and_eq_true] at h
    rcases inBox_half hy a with h1 | h1
    · exact KTree.check_sound leafOk coneOk Good hleaf hcone l _ (half_width_nonneg hb a false) h.1 y h1
    · exact KTree.check_sound leafOk coneOk Good hleaf hcone r _ (half_width_nonneg hb a true) h.2 y h1
  | .leaf w, box, hb, h, y, hy => hleaf w box hb h y hy
  | .cone, box, hb, h, y, hy => hcone box hb h y hy
  | .fail, _, _, h, _, _ => by simp [KTree.check] at h

/-- A certificate. -/
structure KCert (K : Type) where
  V : Array (KVec K)
  fr : Frame K
  pr : Params
  mu0 : ℚ
  tieMu0 : ℚ
  charts : List (ChartId × KTree)

/-- The root box of a chart, as (lower end, width) per variable. -/
def rootBox (c : KCert K) (id : ChartId) : Box :=
  match id.kind with
  | .fe => ![(0, c.mu0), (-1, 2), (-c.pr.R, 2 * c.pr.R), (-c.pr.R, 2 * c.pr.R), (-c.pr.R, 2 * c.pr.R)]
  | .face => ![(0, c.mu0), (-1, 2), (0, 1), (-c.pr.R, 2 * c.pr.R), (-c.pr.R, 2 * c.pr.R)]
  | .cone => ![(0, c.mu0), (-1, 2), (0, c.pr.t0), (-1, 2), (-1, 2)]
  | .tcone => ![(0, c.tieMu0), (0, c.pr.tieT0), (-1, 2), (-1, 2), (-1, 2)]

/-- Every coordinate of the box within `rad` of `center`. -/
def withinB (box : Box) (v : Fin 5) (center rad : ℚ) : Bool :=
  decide (center - rad ≤ (box v).1 ∧ (box v).1 + (box v).2 ≤ center + rad)

/-- An F_e box inside the identity cone (|s|_∞ ≤ t₀ R / 2) or, on the tie's side, the tie
cone (|τ|, |s₀ − s₀*|, |s₁|, |s₂| ≤ t_tie). -/
def coneOk (c : KCert K) (id : ChartId) (box : Box) : Bool :=
  id.kind = .fe &&
    ((withinB box 2 0 (c.pr.t0 * c.pr.R / 2) && withinB box 3 0 (c.pr.t0 * c.pr.R / 2) &&
      withinB box 4 0 (c.pr.t0 * c.pr.R / 2)) ||
     (id.side = c.pr.tieSide && withinB box 1 0 c.pr.tieT0 && withinB box 2 c.pr.tieS0 c.pr.tieT0 &&
      withinB box 3 0 c.pr.tieT0 && withinB box 4 0 c.pr.tieT0))

def KCert.chartCheck (c : KCert K) (id : ChartId) (t : KTree) : Bool :=
  let cd := chartData c.fr c.pr id c.V
  t.check (fun l box => l.check c.V cd id box) (coneOk c id) (rootBox c id)

/-- The charts every certificate must contain. -/
def requiredCharts : List ChartId :=
  ((List.range 4).flatMap fun side =>
    ⟨.fe, side, 0, true⟩ :: (List.range 3).flatMap fun axis =>
      [true, false].flatMap fun sign => [⟨.face, side, axis, sign⟩, ⟨.cone, side, axis, sign⟩]) ++
  (List.range 4).flatMap fun axis => [true, false].map fun sign => ⟨.tcone, 1, axis, sign⟩

def KCert.hasChart (c : KCert K) (id : ChartId) : Bool :=
  c.charts.any fun e => decide (e.1 = id) && c.chartCheck e.1 e.2

/-! ### Chart points -/

section points

variable [ExactScalarVal K] (fr : Frame K) (pr : Params)

theorem fe_point (side axis : ℕ) (sign : Bool) (μ τ : ℝ) (s : Fin 3 → ℝ) :
    (chartU fr pr ⟨.fe, side, axis, sign⟩).eval ![μ, τ, s 0, s 1, s 2] =
        kval fr.x + μ • ((rSideVecs fr side).1 + τ • (rSideVecs fr side).2) ∧
      (chartW fr pr ⟨.fe, side, axis, sign⟩).eval ![μ, τ, s 0, s 1, s 2] =
        μ • (s 0 • kval fr.Z + (s 1 • kval fr.E1 + s 2 • kval fr.X)) := by
  constructor
  · rw [eval_chartU]
    simp [rE, rTau, chartParams, eval_pvar, eval_kOne]
  · rw [eval_chartW]
    simp [rS, chartParams, eval_pvar]

theorem fe_eval (side axis : ℕ) (sign : Bool) (y : Fin 5 → ℝ) :
    (chartU fr pr ⟨.fe, side, axis, sign⟩).eval y =
        kval fr.x + y 0 • ((rSideVecs fr side).1 + y 1 • (rSideVecs fr side).2) ∧
      (chartW fr pr ⟨.fe, side, axis, sign⟩).eval y = y 0 • (y 2 • kval fr.Z + (y 3 • kval fr.E1 + y 4 • kval fr.X)) := by
  constructor
  · rw [eval_chartU]
    simp [rE, rTau, chartParams, eval_pvar, eval_kOne]
  · rw [eval_chartW]
    simp [rS, chartParams, eval_pvar]

/-- The coordinates of a 3-vector other than `a`, in order. -/
def other3 (a : ℕ) (v : Fin 3 → ℝ) : ℝ × ℝ :=
  if a = 0 then (v 1, v 2) else if a = 1 then (v 0, v 2) else (v 0, v 1)

/-- The coordinates of a 4-vector other than `a`, in order. -/
def other4 (a : ℕ) (v : Fin 4 → ℝ) : ℝ × ℝ × ℝ :=
  if a = 0 then (v 1, v 2, v 3) else if a = 1 then (v 0, v 2, v 3) else if a = 2 then (v 0, v 1, v 3)
  else (v 0, v 1, v 2)

theorem face_point (side axis : ℕ) (sign : Bool) (ha : axis < 3) (μ τ e : ℝ) (s : Fin 3 → ℝ)
    (hs : s ⟨axis, ha⟩ = ((signQ sign * pr.R : ℚ) : ℝ)) :
    let y : Fin 5 → ℝ := ![μ, τ, e, (other3 axis s).1, (other3 axis s).2]
    (chartU fr pr ⟨.face, side, axis, sign⟩).eval y =
        kval fr.x + (μ * e) • ((rSideVecs fr side).1 + τ • (rSideVecs fr side).2) ∧
      (chartW fr pr ⟨.face, side, axis, sign⟩).eval y =
        μ • (s 0 • kval fr.Z + (s 1 • kval fr.E1 + s 2 • kval fr.X)) := by
  intro y
  constructor
  · rw [eval_chartU]
    simp [y, rE, rTau, chartParams, eval_pvar]
  · rw [eval_chartW]
    obtain rfl | rfl | rfl : axis = 0 ∨ axis = 1 ∨ axis = 2 := by omega
    all_goals
      simp only [rS, chartParams, eval_faceCoord]
      simp [y, other3, freeVar, hs.symm]

theorem cone_point (side axis : ℕ) (sign : Bool) (ha : axis < 3) (μ τ p0 : ℝ) (σ : Fin 3 → ℝ)
    (hσ : σ ⟨axis, ha⟩ = ((signQ sign : ℚ) : ℝ)) :
    let y : Fin 5 → ℝ := ![μ, τ, p0, (other3 axis σ).1, (other3 axis σ).2]
    (chartU fr pr ⟨.cone, side, axis, sign⟩).eval y =
        kval fr.x + μ • ((rSideVecs fr side).1 + τ • (rSideVecs fr side).2) ∧
      (chartW fr pr ⟨.cone, side, axis, sign⟩).eval y =
        μ • (((pr.R / 2 : ℚ) * p0 * σ 0) • kval fr.Z + (((pr.R / 2 : ℚ) * p0 * σ 1) • kval fr.E1 +
          ((pr.R / 2 : ℚ) * p0 * σ 2) • kval fr.X)) := by
  intro y
  constructor
  · rw [eval_chartU]
    simp [y, rE, rTau, chartParams, eval_pvar, eval_kOne]
  · rw [eval_chartW]
    obtain rfl | rfl | rfl : axis = 0 ∨ axis = 1 ∨ axis = 2 := by omega
    all_goals
      simp only [rS, chartParams, KPoly.eval_mul, eval_pconst, eval_faceCoord, eval_pvar]
      simp [y, other3, freeVar, ← hσ, mul_assoc]

theorem tcone_point (side axis : ℕ) (sign : Bool) (ha : axis < 4) (μ t : ℝ) (σ : Fin 4 → ℝ)
    (hσ : σ ⟨axis, ha⟩ = ((signQ sign : ℚ) : ℝ)) :
    let y : Fin 5 → ℝ := ![μ, t, (other4 axis σ).1, (other4 axis σ).2.1, (other4 axis σ).2.2]
    (chartU fr pr ⟨.tcone, side, axis, sign⟩).eval y =
        kval fr.x + μ • ((rSideVecs fr side).1 + (t * σ 0) • (rSideVecs fr side).2) ∧
      (chartW fr pr ⟨.tcone, side, axis, sign⟩).eval y =
        μ • (((pr.tieS0 : ℝ) + t * σ 1) • kval fr.Z + ((t * σ 2) • kval fr.E1 + (t * σ 3) • kval fr.X)) := by
  intro y
  obtain rfl | rfl | rfl | rfl : axis = 0 ∨ axis = 1 ∨ axis = 2 ∨ axis = 3 := by omega
  all_goals
    constructor
    · rw [eval_chartU]
      simp only [rE, rTau, chartParams, KPoly.eval_mul, eval_faceCoord, eval_pvar, eval_kOne]
      simp [y, other4, freeVar, ← hσ]
    · rw [eval_chartW]
      simp [rS, chartParams, KPoly.eval_mul, KPoly.eval_add, eval_pconst, eval_faceCoord, eval_pvar, y, other4,
        freeVar, ← hσ]

end points

/-! ### Covering -/

theorem signQ_cases (b : Bool) : ((signQ b : ℚ) : ℝ) = if b then 1 else -1 := by
  cases b <;> simp [signQ]

/-- A vector is t σ with t = max |v_i| and σ on a face of the cube. -/
theorem maxface {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ) :
    ∃ t : ℝ, 0 ≤ t ∧ (∀ i, |v i| ≤ t) ∧ (∃ i, |v i| = t) ∧ ∃ a : Fin n, ∃ sign : Bool, ∃ σ : Fin n → ℝ,
      σ a = ((signQ sign : ℚ) : ℝ) ∧ (∀ i, |σ i| ≤ 1) ∧ ∀ i, v i = t * σ i := by
  classical
  obtain ⟨a, -, ha⟩ := Finset.univ.exists_max_image (fun i => |v i|) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  set t := |v a|
  refine ⟨t, abs_nonneg _, fun i => ha i (Finset.mem_univ _), ⟨a, rfl⟩, a, ?_⟩
  rcases (abs_nonneg (v a)).lt_or_eq with ht | ht
  · have htne : t ≠ 0 := ne_of_gt ht
    refine ⟨decide (0 ≤ v a), fun i => v i / t, ?_, ?_, ?_⟩
    · rw [signQ_cases]
      by_cases h0 : 0 ≤ v a
      · have : t = v a := abs_of_nonneg h0
        simp only [h0, decide_true, ite_true]
        rw [← this, div_self htne]
      · push Not at h0
        have : t = -v a := abs_of_neg h0
        simp only [show ¬ (0 ≤ v a) from not_le.mpr h0, decide_false, Bool.false_eq_true, ite_false]
        rw [this, div_neg, div_self (ne_of_lt h0)]
    · intro i
      rw [abs_div, abs_of_pos ht, div_le_one ht]
      exact ha i (Finset.mem_univ _)
    · intro i; field_simp
  · refine ⟨true, fun i => if i = a then 1 else 0, by simp [signQ], ?_, ?_⟩
    · intro i; by_cases h : i = a <;> simp [h]
    · intro i
      have : |v i| ≤ 0 := by rw [ht]; exact ha i (Finset.mem_univ _)
      have hz : v i = 0 := abs_nonpos_iff.mp this
      have ht0 : t = 0 := ht.symm
      rw [hz, ht0, zero_mul]

/-! ### Certificates -/

def KCert.paramsOk (c : KCert K) : Bool :=
  decide (0 < c.pr.R) && decide (0 ≤ c.pr.t0) && decide (0 ≤ c.pr.tieT0) && decide (0 ≤ c.mu0) &&
    decide (c.mu0 ≤ c.tieMu0) && decide (c.pr.tieSide = 1)

def kdot (a b : KVec K) : K :=
  ExactScalarOps.add (ExactScalarOps.add (ExactScalarOps.mul (a 0) (b 0)) (ExactScalarOps.mul (a 1) (b 1)))
    (ExactScalarOps.mul (a 2) (b 2))

def orthoOk (a b : KVec K) : Bool := ExactScalarOps.isZero (kdot a b)

def posNormOk (a : KVec K) : Bool := decide (0 < ExactScalarOps.lo (kdot a a))

/-- Both frames are orthogonal with nonzero vectors. -/
def KCert.frameOk (c : KCert K) : Bool :=
  orthoOk c.fr.x c.fr.e1 && orthoOk c.fr.x c.fr.e2 && orthoOk c.fr.e1 c.fr.e2 &&
    orthoOk c.fr.Z c.fr.E1 && orthoOk c.fr.Z c.fr.X && orthoOk c.fr.E1 c.fr.X &&
    posNormOk c.fr.x && posNormOk c.fr.e1 && posNormOk c.fr.e2 &&
    posNormOk c.fr.Z && posNormOk c.fr.E1 && posNormOk c.fr.X

def KCert.check (c : KCert K) : Bool := c.paramsOk && c.frameOk && requiredCharts.all c.hasChart

section claims

variable [ExactScalarVal K]

/-- The solid: the hull of the certificate's vertices. -/
noncomputable def KCert.hull (c : KCert K) : Set ℝ³ :=
  convexHull ℝ {v | ∃ vj ∈ c.V.toList.map kval, v = Cap.toEuc vj}

/-- No pose over the chart point is Rupert. -/
def PointGood (c : KCert K) (id : ChartId) (y : Fin 5 → ℝ) : Prop :=
  ∀ (p : MatrixPose) (ξ : ℝ), p.view = ξ • (chartU c.fr c.pr id).eval y →
    p.relativeRotation = cayleyMatrix ((chartW c.fr c.pr id).eval y 0) ((chartW c.fr c.pr id).eval y 1)
      ((chartW c.fr c.pr id).eval y 2) → ¬ RupertPose p c.hull

theorem paramsOk_sound {c : KCert K} (h : c.paramsOk = true) :
    0 < c.pr.R ∧ 0 ≤ c.pr.t0 ∧ 0 ≤ c.pr.tieT0 ∧ 0 ≤ c.mu0 ∧ c.mu0 ≤ c.tieMu0 ∧ c.pr.tieSide = 1 := by
  simp only [KCert.paramsOk, Bool.and_eq_true, decide_eq_true_eq] at h
  tauto

theorem rootBox_width {c : KCert K} (h : c.paramsOk = true) (id : ChartId) : ∀ i, 0 ≤ (rootBox c id i).2 := by
  obtain ⟨hR, ht0, hT, hm, hmT, -⟩ := paramsOk_sound h
  intro i
  unfold rootBox
  cases hk : id.kind <;> fin_cases i <;> simp <;> linarith

theorem rootBox_lo (c : KCert K) (id : ChartId) (y : Fin 5 → ℝ) (hy : KPoly.InBox (rootBox c id) y) :
    0 ≤ y 0 ∧ (id.kind = .tcone → 0 ≤ y 1) ∧ (id.kind = .cone → 0 ≤ y 2) := by
  have h0 := (hy 0).1
  have h1 := (hy 1).1
  have h2 := (hy 2).1
  unfold rootBox at h0 h1 h2
  refine ⟨?_, fun hk => ?_, fun hk => ?_⟩
  · cases hk : id.kind <;> simp only [hk] at h0 <;> simpa using h0
  · simp only [hk] at h1; simpa using h1
  · simp only [hk] at h2; simpa using h2

theorem hasChart_sound {c : KCert K} {id : ChartId} (h : c.hasChart id = true) :
    ∃ t : KTree, c.chartCheck id t = true := by
  unfold KCert.hasChart at h
  obtain ⟨e, -, he⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at he
  obtain ⟨rfl, hc⟩ := he
  exact ⟨e.2, hc⟩

/-- The leaves of a checked chart tree make every point of its root box good, given the
points of the F_e boxes left to the cones. -/
theorem chart_good (c : KCert K) (hp : c.paramsOk = true) (id : ChartId) (t : KTree)
    (ht : c.chartCheck id t = true)
    (hcone : ∀ box, coneOk c id box = true → ∀ y, KPoly.InBox box y → KPoly.InBox (rootBox c id) y →
      PointGood c id y) :
    ∀ y, KPoly.InBox (rootBox c id) y → PointGood c id y := by
  intro y hy
  refine KTree.check_sound (fun l box => l.check c.V (chartData c.fr c.pr id c.V) id box) (coneOk c id)
    (fun y => KPoly.InBox (rootBox c id) y → PointGood c id y) ?_ ?_ t (rootBox c id) (rootBox_width hp id) ht y hy hy
  · intro l box hb hl y hyb hyr p ξ hview hR
    obtain ⟨h0, h1, h2⟩ := rootBox_lo c id y hyr
    exact Leaf.check_sound c.fr c.pr id c.V l box hl hb y hyb h0 h1 h2 c.hull rfl p ξ hview hR
  · intro box _ hc y hyb hyr
    exact hcone box hc y hyb hyr

theorem withinB_sound {box : Box} {v : Fin 5} {center rad : ℚ} (h : withinB box v center rad = true)
    {y : Fin 5 → ℝ} (hy : KPoly.InBox box y) : |y v - center| ≤ rad := by
  simp only [withinB, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  have := hy v
  have h1' : ((center - rad : ℚ) : ℝ) ≤ (box v).1 := by exact_mod_cast h1
  have h2' : (((box v).1 + (box v).2 : ℚ) : ℝ) ≤ center + rad := by exact_mod_cast h2
  push_cast at h1' h2'
  rw [abs_le]; constructor <;> linarith

theorem vec5_eta (y : Fin 5 → ℝ) : y = ![y 0, y 1, y 2, y 3, y 4] := by
  funext i; fin_cases i <;> rfl

theorem cone_mem_required (side axis : ℕ) (sign : Bool) (hs : side < 4) (ha : axis < 3) :
    (⟨.cone, side, axis, sign⟩ : ChartId) ∈ requiredCharts := by
  simp only [requiredCharts, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_map]
  left
  refine ⟨side, hs, ?_⟩
  right
  refine ⟨axis, ha, sign, by cases sign <;> simp, ?_⟩
  simp

theorem face_mem_required (side axis : ℕ) (sign : Bool) (hs : side < 4) (ha : axis < 3) :
    (⟨.face, side, axis, sign⟩ : ChartId) ∈ requiredCharts := by
  simp only [requiredCharts, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_map]
  left
  refine ⟨side, hs, ?_⟩
  right
  refine ⟨axis, ha, sign, by cases sign <;> simp, ?_⟩
  simp

theorem fe_mem_required (side : ℕ) (hs : side < 4) : (⟨.fe, side, 0, true⟩ : ChartId) ∈ requiredCharts := by
  simp only [requiredCharts, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
  left
  exact ⟨side, hs, Or.inl rfl⟩

theorem tcone_mem_required (axis : ℕ) (sign : Bool) (ha : axis < 4) :
    (⟨.tcone, 1, axis, sign⟩ : ChartId) ∈ requiredCharts := by
  simp only [requiredCharts, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map]
  right
  exact ⟨axis, ha, sign, by cases sign <;> simp, rfl⟩

theorem side_of_required {id : ChartId} (h : id ∈ requiredCharts) : id.side < 4 := by
  simp only [requiredCharts, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_map]
    at h
  rcases h with ⟨side, hs, h⟩ | ⟨axis, -, sign, -, rfl⟩
  · rcases h with rfl | ⟨axis, -, sign, -, h⟩
    · exact hs
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> exact hs
  · show 1 < 4; norm_num

theorem inBox_iff (box : Box) (y : Fin 5 → ℝ) :
    KPoly.InBox box y ↔ ∀ i, ((box i).1 : ℝ) ≤ y i ∧ y i ≤ (box i).1 + (box i).2 := Iff.rfl

theorem other3_bound (a : ℕ) (σ : Fin 3 → ℝ) (h : ∀ i, |σ i| ≤ 1) :
    |(other3 a σ).1| ≤ 1 ∧ |(other3 a σ).2| ≤ 1 := by
  unfold other3; split_ifs <;> exact ⟨h _, h _⟩

theorem other4_bound (a : ℕ) (σ : Fin 4 → ℝ) (h : ∀ i, |σ i| ≤ 1) :
    |(other4 a σ).1| ≤ 1 ∧ |(other4 a σ).2.1| ≤ 1 ∧ |(other4 a σ).2.2| ≤ 1 := by
  unfold other4; split_ifs <;> exact ⟨h _, h _, h _⟩

/-- An F_e point inside the identity cone is a point of a cone chart (same pose). -/
theorem fe_to_cone (c : KCert K) (hp : c.paramsOk = true) (side axis : ℕ) (sign : Bool) (hs : side < 4)
    (y : Fin 5 → ℝ) (hyr : KPoly.InBox (rootBox c ⟨.fe, side, axis, sign⟩) y)
    (hb : ∀ i : Fin 3, |y i.succ.succ| ≤ c.pr.t0 * c.pr.R / 2) :
    ∃ id' y', id' ∈ requiredCharts ∧ id'.kind ≠ .fe ∧ KPoly.InBox (rootBox c id') y' ∧
      (chartU c.fr c.pr id').eval y' = (chartU c.fr c.pr ⟨.fe, side, axis, sign⟩).eval y ∧
      (chartW c.fr c.pr id').eval y' = (chartW c.fr c.pr ⟨.fe, side, axis, sign⟩).eval y := by
  obtain ⟨hR, ht0, hT, hm, hmT, -⟩ := paramsOk_sound hp
  have hRpos : (0 : ℝ) < c.pr.R := by exact_mod_cast hR
  obtain ⟨tt, htt0, -, ⟨i0, hi0⟩, a, sgn, σ, hσa, hσ1, hv⟩ :=
    maxface (n := 3) (by norm_num) (fun i => (2 / (c.pr.R : ℝ)) * y i.succ.succ)
  have htt : tt ≤ c.pr.t0 := by
    rw [← hi0]
    simp only [abs_mul, abs_div, abs_two, abs_of_pos hRpos]
    have := hb i0
    rw [div_mul_eq_mul_div, div_le_iff₀ hRpos]
    linarith
  have hcp := cone_point c.fr c.pr side a sgn a.isLt (y 0) (y 1) tt σ hσa
  dsimp only at hcp
  refine ⟨⟨.cone, side, a, sgn⟩, ![y 0, y 1, tt, (other3 a σ).1, (other3 a σ).2],
    cone_mem_required side a sgn hs a.isLt, by simp, ?_, ?_, ?_⟩
  · have hy := hyr
    have hb3 := other3_bound a σ hσ1
    intro i
    fin_cases i
    · have := hy 0; simpa [rootBox] using this
    · have := hy 1; simpa [rootBox] using this
    · simp [rootBox]; exact ⟨htt0, htt⟩
    · simp [rootBox]; have := abs_le.mp hb3.1; constructor <;> linarith [this.1, this.2]
    · simp [rootBox]; have := abs_le.mp hb3.2; constructor <;> linarith [this.1, this.2]
  · rw [hcp.1, (fe_eval c.fr c.pr side axis sign y).1]
  · rw [hcp.2, (fe_eval c.fr c.pr side axis sign y).2]
    have e : ∀ i : Fin 3, ((c.pr.R / 2 : ℚ) : ℝ) * tt * σ i = y i.succ.succ := by
      intro i
      have := hv i
      push_cast
      rw [mul_assoc, ← this]
      field_simp
    rw [e 0, e 1, e 2]
    rfl

/-- An F_e point of the tie's side inside the tie cone is a point of a tie cone chart. -/
theorem fe_to_tcone (c : KCert K) (hp : c.paramsOk = true) (axis : ℕ) (sign : Bool)
    (y : Fin 5 → ℝ) (hyr : KPoly.InBox (rootBox c ⟨.fe, 1, axis, sign⟩) y)
    (h1 : |y 1| ≤ c.pr.tieT0) (h2 : |y 2 - c.pr.tieS0| ≤ c.pr.tieT0) (h3 : |y 3| ≤ c.pr.tieT0)
    (h4 : |y 4| ≤ c.pr.tieT0) :
    ∃ id' y', id' ∈ requiredCharts ∧ id'.kind ≠ .fe ∧ KPoly.InBox (rootBox c id') y' ∧
      (chartU c.fr c.pr id').eval y' = (chartU c.fr c.pr ⟨.fe, 1, axis, sign⟩).eval y ∧
      (chartW c.fr c.pr id').eval y' = (chartW c.fr c.pr ⟨.fe, 1, axis, sign⟩).eval y := by
  obtain ⟨hR, ht0, hT, hm, hmT, -⟩ := paramsOk_sound hp
  obtain ⟨tt, htt0, hle, ⟨i0, hi0⟩, a, sgn, σ, hσa, hσ1, hv⟩ :=
    maxface (n := 4) (by norm_num) ![y 1, y 2 - c.pr.tieS0, y 3, y 4]
  have htt : tt ≤ c.pr.tieT0 := by
    rw [← hi0]
    fin_cases i0 <;> simpa
  have hcp := tcone_point c.fr c.pr 1 a sgn a.isLt (y 0) tt σ hσa
  dsimp only at hcp
  refine ⟨⟨.tcone, 1, a, sgn⟩, ![y 0, tt, (other4 a σ).1, (other4 a σ).2.1, (other4 a σ).2.2],
    tcone_mem_required a sgn a.isLt, by simp, ?_, ?_, ?_⟩
  · have hb4 := other4_bound a σ hσ1
    have hmT' : (c.mu0 : ℝ) ≤ c.tieMu0 := by exact_mod_cast hmT
    intro i
    fin_cases i
    · have := hyr 0; simp [rootBox] at this ⊢; exact ⟨this.1, le_trans this.2 hmT'⟩
    · simp [rootBox]; exact ⟨htt0, htt⟩
    · simp [rootBox]; have := abs_le.mp hb4.1; constructor <;> linarith [this.1, this.2]
    · simp [rootBox]; have := abs_le.mp hb4.2.1; constructor <;> linarith [this.1, this.2]
    · simp [rootBox]; have := abs_le.mp hb4.2.2; constructor <;> linarith [this.1, this.2]
  · rw [hcp.1, (fe_eval c.fr c.pr 1 axis sign y).1]
    have := hv 0
    simp at this
    rw [← this]
  · rw [hcp.2, (fe_eval c.fr c.pr 1 axis sign y).2]
    have e1 := hv 1; have e2 := hv 2; have e3 := hv 3
    simp at e1 e2 e3
    rw [← e2, ← e3, show (c.pr.tieS0 : ℝ) + tt * σ 1 = y 2 by linarith]

/-- Every required chart is good on its root box. -/
theorem required_good (c : KCert K) (hc : c.check = true) :
    ∀ id ∈ requiredCharts, ∀ y, KPoly.InBox (rootBox c id) y → PointGood c id y := by
  simp only [KCert.check, Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨⟨hp, -⟩, hall⟩ := hc
  obtain ⟨hR, ht0, hT, hm, hmT, hside⟩ := paramsOk_sound hp
  -- Charts other than F_e: their trees have no cone leaves.
  have hnonfe : ∀ id ∈ requiredCharts, id.kind ≠ .fe → ∀ y, KPoly.InBox (rootBox c id) y → PointGood c id y := by
    intro id hid hk
    obtain ⟨t, ht⟩ := hasChart_sound (hall id hid)
    apply chart_good c hp id t ht
    intro box hco
    simp [coneOk, hk] at hco
  intro id hid
  by_cases hk : id.kind = .fe
  swap
  · exact hnonfe id hid hk
  obtain ⟨t, ht⟩ := hasChart_sound (hall id hid)
  have hs4 := side_of_required hid
  apply chart_good c hp id t ht
  intro box hco y hyb hyr p ξ hview hRot
  obtain ⟨kind, side, axis, sign⟩ := id
  simp only at hk
  subst hk
  simp only [coneOk, decide_true, Bool.true_and, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hco
  rcases hco with ⟨⟨h2, h3⟩, h4⟩ | ⟨⟨⟨⟨hsd, h1⟩, h2⟩, h3⟩, h4⟩
  · have b2 := withinB_sound h2 hyb; have b3 := withinB_sound h3 hyb; have b4 := withinB_sound h4 hyb
    push_cast at b2 b3 b4
    simp only [sub_zero] at b2 b3 b4
    obtain ⟨id', y', hid', hk', hy', hU, hW⟩ := fe_to_cone c hp side axis sign hs4 y hyr
      (fun i => by fin_cases i <;> simpa)
    rw [← hU] at hview
    rw [← hW] at hRot
    exact hnonfe id' hid' hk' y' hy' p ξ hview hRot
  · have b1 := withinB_sound h1 hyb; have b2 := withinB_sound h2 hyb
    have b3 := withinB_sound h3 hyb; have b4 := withinB_sound h4 hyb
    push_cast at b1 b2 b3 b4
    simp only [sub_zero] at b1 b3 b4
    rw [hside] at hsd
    subst hsd
    obtain ⟨id', y', hid', hk', hy', hU, hW⟩ := fe_to_tcone c hp axis sign y hyr b1 b2 b3 b4
    rw [← hU] at hview
    rw [← hW] at hRot
    exact hnonfe id' hid' hk' y' hy' p ξ hview hRot

theorem val_kdot (a b : KVec K) : ExactScalarVal.val (kdot a b) = rdot (kval a) (kval b) := by
  simp [kdot, rdot, kval, ExactScalarVal.val_add, ExactScalarVal.val_mul]

theorem orthoOk_sound {a b : KVec K} (h : orthoOk a b = true) : rdot (kval a) (kval b) = 0 := by
  rw [← val_kdot]; exact ExactScalarVal.val_of_isZero _ h

theorem posNormOk_sound {a : KVec K} (h : posNormOk a = true) : 0 < rdot (kval a) (kval a) := by
  rw [← val_kdot]
  have : (0 : ℚ) < ExactScalarOps.lo (kdot a a) := of_decide_eq_true h
  exact lt_of_lt_of_le (by exact_mod_cast this) (ExactScalarVal.lo_le_val _)

theorem frameOk_sound {c : KCert K} (h : c.frameOk = true) :
    rdot (kval c.fr.x) (kval c.fr.e1) = 0 ∧ rdot (kval c.fr.x) (kval c.fr.e2) = 0 ∧
    rdot (kval c.fr.e1) (kval c.fr.e2) = 0 ∧ rdot (kval c.fr.Z) (kval c.fr.E1) = 0 ∧
    rdot (kval c.fr.Z) (kval c.fr.X) = 0 ∧ rdot (kval c.fr.E1) (kval c.fr.X) = 0 ∧
    0 < rdot (kval c.fr.x) (kval c.fr.x) ∧ 0 < rdot (kval c.fr.e1) (kval c.fr.e1) ∧
    0 < rdot (kval c.fr.e2) (kval c.fr.e2) ∧ 0 < rdot (kval c.fr.Z) (kval c.fr.Z) ∧
    0 < rdot (kval c.fr.E1) (kval c.fr.E1) ∧ 0 < rdot (kval c.fr.X) (kval c.fr.X) := by
  simp only [KCert.frameOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  exact ⟨orthoOk_sound h1, orthoOk_sound h2, orthoOk_sound h3, orthoOk_sound h4, orthoOk_sound h5,
    orthoOk_sound h6, posNormOk_sound h7, posNormOk_sound h8, posNormOk_sound h9, posNormOk_sound h10,
    posNormOk_sound h11, posNormOk_sound h12⟩

/-- The cap's claim: no pose with view in the cap's cone and Cayley vector in its box is Rupert. -/
def BoxClaim (c : KCert K) : Prop :=
  ∀ (p : MatrixPose) (w : Fin 3 → ℝ), p.relativeRotation = cayleyMatrix (w 0) (w 1) (w 2) →
    InCapView (kval c.fr.x) (kval c.fr.e1) (kval c.fr.e2) c.mu0 p.view →
    InCapRot (kval c.fr.Z) (kval c.fr.E1) (kval c.fr.X) (c.pr.R * c.mu0) w → ¬ RupertPose p c.hull

theorem side_combo (fr : Frame K) (side : ℕ) (m τ t1 t2 : ℝ)
    (h1 : t1 = m * ((Cap.sideA side).1 + τ * (Cap.sideB side).1))
    (h2 : t2 = m * ((Cap.sideA side).2 + τ * (Cap.sideB side).2)) :
    t1 • kval fr.e1 + t2 • kval fr.e2 = m • ((rSideVecs fr side).1 + τ • (rSideVecs fr side).2) := by
  subst h1 h2
  funext i
  simp only [rSideVecs, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem KCert.boxClaim (c : KCert K) (hc : c.check = true) : BoxClaim c := by
  have hgood := required_good c hc
  simp only [KCert.check, Bool.and_eq_true] at hc
  obtain ⟨⟨hp, hf⟩, -⟩ := hc
  obtain ⟨hR, ht0, hT, hm, hmT, -⟩ := paramsOk_sound hp
  obtain ⟨hxe1, hxe2, he12, hZE, hZX, hEX, hxx, he1, he2, hZZ, hEE, hXX⟩ := frameOk_sound hf
  intro p w hRw hview hrot
  obtain ⟨a, t1, t2, ha, ht1, ht2, hu⟩ :=
    capView_decomp _ _ _ _ hxe1 hxe2 he12 hxx he1.ne' he2.ne' p.view hview
  obtain ⟨cw, hcw, hwdec⟩ := capRot_decomp _ _ _ _ hZE hZX hEX hZZ.ne' hEE.ne' hXX.ne' w hrot
  obtain ⟨side, hs4, m, τ, hmax, hτ, ht1', ht2'⟩ := Cap.view_side t1 t2
  have hRpos : (0 : ℝ) < c.pr.R := by exact_mod_cast hR
  have hm0 : 0 ≤ m := by rw [hmax]; exact le_max_of_le_left (abs_nonneg _)
  have hm1 : m ≤ c.mu0 := by rw [hmax]; exact max_le ht1 ht2
  obtain ⟨μ, e, s, hμ0, hμ1, he0, he1', hme, hs, hcase⟩ :=
    Cap.weighted_cube (fun _ => 1) (fun _ => Or.inl rfl) (fun _ => (c.pr.R : ℝ)) (fun _ => hRpos) c.mu0 m hm0 hm1 cw
      (fun i => by simpa using hcw i)
  simp only [pow_one] at hs
  have hview' : p.view = a • (kval c.fr.x + m • ((rSideVecs c.fr side).1 + τ • (rSideVecs c.fr side).2)) := by
    rw [← side_combo c.fr side m τ t1 t2 ht1' ht2', ← add_assoc, ← hu, smul_smul, mul_one_div_cancel ha.ne',
      one_smul]
  have hw' : w = μ • (s 0 • kval c.fr.Z + (s 1 • kval c.fr.E1 + s 2 • kval c.fr.X)) := by
    rw [hwdec, (hs 0).1, (hs 1).1, (hs 2).1]
    simp only [smul_add, smul_smul]
  have hτ' : -1 ≤ τ ∧ τ ≤ 1 := abs_le.mp hτ
  rcases hcase with rfl | ⟨k, hk⟩
  · -- The F_e chart.
    have hid := fe_mem_required side hs4
    have hy : KPoly.InBox (rootBox c ⟨.fe, side, 0, true⟩) ![μ, τ, s 0, s 1, s 2] := by
      intro i
      fin_cases i <;> simp [rootBox]
      · exact ⟨hμ0, hμ1⟩
      · exact ⟨hτ'.1, by linarith [hτ'.2]⟩
      all_goals exact abs_le.mp (hs _).2 |> fun h => ⟨by linarith [h.1], by linarith [h.2]⟩
    have hp' := hgood _ hid _ hy p a
    obtain ⟨hU, hW⟩ := fe_point c.fr c.pr side 0 true μ τ s
    rw [hU, hW] at hp'
    rw [mul_one] at hme
    apply hp'
    · rw [hview', hme]
    · rw [hRw, hw']
  · -- A face chart.
    set sgn := decide (0 ≤ s k)
    have hsk : s ⟨k, k.isLt⟩ = ((signQ sgn * c.pr.R : ℚ) : ℝ) := by
      push_cast
      rw [signQ_cases]
      by_cases h0 : 0 ≤ s k
      · simp only [sgn, h0, decide_true, ite_true, one_mul]; rw [← hk, abs_of_nonneg h0]
      · push Not at h0
        simp only [sgn, show ¬ (0 ≤ s k) from not_le.mpr h0, decide_false, Bool.false_eq_true, ite_false]
        rw [← hk, abs_of_neg h0]; ring
    have hid := face_mem_required side k sgn hs4 k.isLt
    have hb3 := other3_bound k (fun i => s i / c.pr.R) (fun i => by
      rw [abs_div, abs_of_pos hRpos, div_le_one hRpos]; exact (hs i).2)
    have hy : KPoly.InBox (rootBox c ⟨.face, side, k, sgn⟩) ![μ, τ, e, (other3 k s).1, (other3 k s).2] := by
      have hs' : ∀ i, -(c.pr.R : ℝ) ≤ s i ∧ s i ≤ c.pr.R := fun i => abs_le.mp (hs i).2
      intro i
      fin_cases i <;> simp [rootBox]
      · exact ⟨hμ0, hμ1⟩
      · exact ⟨hτ'.1, by linarith [hτ'.2]⟩
      · exact ⟨he0, he1'⟩
      all_goals (unfold other3; split_ifs <;> constructor <;> linarith [hs' 0, hs' 1, hs' 2])
    have hp' := hgood _ hid _ hy p a
    obtain ⟨hU, hW⟩ := face_point c.fr c.pr side k sgn k.isLt μ τ e s hsk
    rw [hU, hW] at hp'
    apply hp'
    · rw [hview', hme]
    · rw [hRw, hw']

/-- The tie tube: with a = u·x/|x|² and m = −u·e₁/|e₁|² (= a μ), 0 ≤ m ≤ μ_T a,
|u·e₂/|e₂|²| ≤ t m, and the Cayley vector's frame coordinates w_F within t m of
(s₀* m, 0, 0) after multiplying by a. -/
def InTube (c : KCert K) (u w : Fin 3 → ℝ) : Prop :=
  let x := kval c.fr.x; let e1 := kval c.fr.e1; let e2 := kval c.fr.e2
  let Z := kval c.fr.Z; let E1 := kval c.fr.E1; let X := kval c.fr.X
  let a := rdot u x / rdot x x
  let m := -(rdot u e1 / rdot e1 e1)
  0 < rdot u x ∧ 0 ≤ m ∧ m ≤ c.tieMu0 * a ∧ |rdot u e2 / rdot e2 e2| ≤ c.pr.tieT0 * m ∧
    |rdot w Z / rdot Z Z * a - c.pr.tieS0 * m| ≤ c.pr.tieT0 * m ∧
    |rdot w E1 / rdot E1 E1 * a| ≤ c.pr.tieT0 * m ∧ |rdot w X / rdot X X * a| ≤ c.pr.tieT0 * m

def TubeClaim (c : KCert K) : Prop :=
  ∀ (p : MatrixPose) (w : Fin 3 → ℝ), p.relativeRotation = cayleyMatrix (w 0) (w 1) (w 2) →
    InTube c p.view w → ¬ RupertPose p c.hull

theorem KCert.tubeClaim (c : KCert K) (hc : c.check = true) : TubeClaim c := by
  have hgood := required_good c hc
  simp only [KCert.check, Bool.and_eq_true] at hc
  obtain ⟨⟨hp, hf⟩, -⟩ := hc
  obtain ⟨hR, ht0, hT, hm, hmT, hside⟩ := paramsOk_sound hp
  obtain ⟨hxe1, hxe2, he12, hZE, hZX, hEX, hxx, he1, he2, hZZ, hEE, hXX⟩ := frameOk_sound hf
  intro p w hRw htube
  obtain ⟨hpos, hm0, hmT', hc2, hwZ, hwE, hwX⟩ := htube
  set x := kval c.fr.x; set e1 := kval c.fr.e1; set e2 := kval c.fr.e2
  set Z := kval c.fr.Z; set E1 := kval c.fr.E1; set X := kval c.fr.X
  set u := p.view
  set a := rdot u x / rdot x x with ha_def
  set m := -(rdot u e1 / rdot e1 e1) with hm_def
  set c2 := rdot u e2 / rdot e2 e2
  set wZ := rdot w Z / rdot Z Z; set wE := rdot w E1 / rdot E1 E1; set wX := rdot w X / rdot X X
  have ha : 0 < a := div_pos hpos hxx
  have hT' : (0 : ℝ) ≤ c.pr.tieT0 := by exact_mod_cast hT
  have hu : u = a • x + (-m) • e1 + c2 • e2 := by
    have := decomp3 x e1 e2 u hxe1 hxe2 he12 hxx.ne' he1.ne' he2.ne'
    rw [this]; simp [a, m, c2]
  have hw : w = wZ • Z + (wE • E1 + wX • X) := by
    have := decomp3 Z E1 X w hZE hZX hEX hZZ.ne' hEE.ne' hXX.ne'
    rw [this]; simp [wZ, wE, wX, add_assoc]
  rcases hm0.lt_or_eq with hmpos | hm00
  · -- μ = m / a > 0: a tie cone point.
    set μ := m / a
    have hμ : 0 < μ := div_pos hmpos ha
    set v : Fin 4 → ℝ := ![c2 / m, wZ / μ - c.pr.tieS0, wE / μ, wX / μ]
    have hvb : ∀ i, |v i| ≤ c.pr.tieT0 := by
      intro i
      have hμm : μ * a = m := by simp [μ]; field_simp
      fin_cases i
      · simp [v]; rw [abs_div, abs_of_pos hmpos, div_le_iff₀ hmpos]; exact hc2
      · simp [v]
        have : wZ / μ - c.pr.tieS0 = (wZ * a - c.pr.tieS0 * m) / m := by
          rw [← hμm]; field_simp
        rw [this, abs_div, abs_of_pos hmpos, div_le_iff₀ hmpos]; exact hwZ
      · simp [v]
        have : wE / μ = (wE * a) / m := by rw [← hμm]; field_simp
        rw [this, abs_div, abs_of_pos hmpos, div_le_iff₀ hmpos]; exact hwE
      · simp [v]
        have : wX / μ = (wX * a) / m := by rw [← hμm]; field_simp
        rw [this, abs_div, abs_of_pos hmpos, div_le_iff₀ hmpos]; exact hwX
    obtain ⟨tt, htt0, hle, ⟨i0, hi0⟩, k, sgn, σ, hσk, hσ1, hv⟩ := maxface (n := 4) (by norm_num) v
    have htt : tt ≤ c.pr.tieT0 := by rw [← hi0]; exact hvb i0
    have hid := tcone_mem_required k sgn k.isLt
    have hb4 := other4_bound k σ hσ1
    have hy : KPoly.InBox (rootBox c ⟨.tcone, 1, k, sgn⟩)
        ![μ, tt, (other4 k σ).1, (other4 k σ).2.1, (other4 k σ).2.2] := by
      intro i
      fin_cases i <;> simp [rootBox]
      · refine ⟨hμ.le, ?_⟩
        rw [div_le_iff₀ ha]; linarith
      · exact ⟨htt0, htt⟩
      · have := abs_le.mp hb4.1; constructor <;> linarith [this.1, this.2]
      · have := abs_le.mp hb4.2.1; constructor <;> linarith [this.1, this.2]
      · have := abs_le.mp hb4.2.2; constructor <;> linarith [this.1, this.2]
    have hp' := hgood _ hid _ hy p a
    have hcp := tcone_point c.fr c.pr 1 k sgn k.isLt μ tt σ hσk
    dsimp only at hcp
    rw [hcp.1, hcp.2] at hp'
    have e0 := hv 0; have e1' := hv 1; have e2' := hv 2; have e3 := hv 3
    simp only [v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons] at e0 e1' e2' e3
    apply hp'
    · rw [show p.view = u from rfl, hu]
      simp only [rSideVecs, Cap.sideA, Cap.sideB, ← e0]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hμm : μ * a = m := by simp [μ]; field_simp
      field_simp
      rw [← hμm]
      ring
    · have hvec : wZ • Z + (wE • E1 + wX • X) =
          μ • (((c.pr.tieS0 : ℝ) + tt * σ 1) • kval c.fr.Z + ((tt * σ 2) • kval c.fr.E1 + (tt * σ 3) • kval c.fr.X)) := by
        rw [← e1', ← e2', ← e3]
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Z, E1, X]
        field_simp
        ring
      rw [hRw, hw, hvec]
  · -- m = 0: the identity at view x.
    have hm0' : m = 0 := hm00.symm
    have hc20 : c2 = 0 := by
      have : |c2| ≤ 0 := by rw [hm0', mul_zero] at hc2; exact hc2
      exact abs_nonpos_iff.mp this
    have hz : ∀ q : ℝ, |q * a| ≤ c.pr.tieT0 * m → q = 0 := by
      intro q hq
      rw [hm0', mul_zero, abs_nonpos_iff, mul_eq_zero] at hq
      rcases hq with h | h
      · exact h
      · exact absurd h ha.ne'
    have hwZ0 : wZ = 0 := hz wZ (by rw [hm0', mul_zero] at hwZ ⊢; simpa [hm0'] using hwZ)
    have hwE0 : wE = 0 := hz wE hwE
    have hwX0 : wX = 0 := hz wX hwX
    have hid := tcone_mem_required 0 true (by norm_num)
    have hy : KPoly.InBox (rootBox c ⟨.tcone, 1, 0, true⟩) ![0, 0, 0, 0, 0] := by
      have hμT : (0 : ℝ) ≤ c.tieMu0 := by exact_mod_cast le_trans hm hmT
      intro i
      fin_cases i <;> simp [rootBox]
      · exact le_trans hm hmT
      · exact hT
    have hp' := hgood _ hid _ hy p a
    have hcp := tcone_point c.fr c.pr 1 0 true (by norm_num) 0 0 ![1, 0, 0, 0] (by simp [signQ])
    dsimp only at hcp
    have hy0 : (![0, 0, (other4 0 ![1, 0, 0, 0]).1, (other4 0 ![(1 : ℝ), 0, 0, 0]).2.1,
        (other4 0 ![(1 : ℝ), 0, 0, 0]).2.2] : Fin 5 → ℝ) = ![0, 0, 0, 0, 0] := by
      funext i; fin_cases i <;> simp [other4]
    rw [hy0] at hcp
    rw [hcp.1, hcp.2] at hp'
    apply hp'
    · rw [show p.view = u from rfl, hu, hm0', hc20]; simp; rfl
    · rw [hRw, hw, hwZ0, hwE0, hwX0]; simp

end claims

end KCap

end Noperts.Pipeline

end
