module

public import Pipeline.KCapDecode
public import Pipeline.RupertScale
public import Pipeline.CapCheck
public import Pipeline.IcoView
public import SnubCube.SolidModel

@[expose] public section

/-!
# The snub cube's caps

The cap at the zero-margin view u* = x/|x|, x = (1, 0, t²), and the tube
around the exact tie that continues from it (`nopert229/notes/SNUB-CUBE.md`,
`search/sc/sccapcert.cc`), over the field ℚ(t) (`TribQ`):

* `template`: the exact frames (x, e₁, e₂ = L₂ e_y with L₂ = (4 − 4t + 12t²)/7;
  Z = e_y, E₁ = e₁/4, X = x/4), the parameters (μ₀ = 1/8, R = 2, t₀ = 1/4, the
  tie on side 1 at s₀ = 1 with radius 1/4, the tube to μ = 1/3), and the
  vertices: the O-orbit of (t, 1, −t²) in the model's slot order.
* `CapsHold S`: no pose of the cap box (`BoxClaimS`) or the tie tube
  (`TubeClaimS`) is Rupert for `S`.
* `capsHold_of_cert`: a checked certificate with the template's data proves
  `CapsHold` for every positive multiple of its solid (`rupertPose_of_smul`).
-/

namespace SnubCube

open Noperts Noperts.Pipeline Noperts.Pipeline.KCap Noperts.Pipeline.KCap.PVec
open scoped Matrix Pointwise

def tq (a b c : ℚ) : TribQ := ⟨a, b, c⟩

/-- The cap's frames. -/
def scFrame : Frame TribQ where
  x := ![tq 1 0 0, tq 0 0 0, tq 0 0 1]
  e1 := ![tq 0 0 (-1), tq 0 0 0, tq 1 0 0]
  e2 := ![tq 0 0 0, tq (4 / 7) (-4 / 7) (12 / 7), tq 0 0 0]
  Z := ![tq 0 0 0, tq 1 0 0, tq 0 0 0]
  E1 := ![tq 0 0 (-1 / 4), tq 0 0 0, tq (1 / 4) 0 0]
  X := ![tq (1 / 4) 0 0, tq 0 0 0, tq 0 0 (1 / 4)]

/-- R = 2, t₀ = 1/4, the tie on side 1 at s₀ = 1 with radius 1/4. -/
def scParams : Params := ⟨2, 1 / 4, 1, 1, 1 / 4⟩

def scMu0 : ℚ := 1 / 8
def scTieMu0 : ℚ := 1 / 3

/-- (t, 1, −t²). -/
def seedT : KVec TribQ := ![tq 0 1 0, tq 1 0 0, tq 0 0 (-1)]

/-- Element g of O applied to an exact vector. -/
def octaApplyT (g : ℕ) (v : KVec TribQ) : KVec TribQ := fun r =>
  ExactScalarOps.add (ExactScalarOps.add (ExactScalarOps.scale (octaEntry g (3 * r.val) : ℚ) (v 0))
    (ExactScalarOps.scale (octaEntry g (3 * r.val + 1) : ℚ) (v 1)))
    (ExactScalarOps.scale (octaEntry g (3 * r.val + 2) : ℚ) (v 2))

/-- The exact vertices, in slot order: slot i is (slot i's element) · (t, 1, −t²). -/
def scVerts : Array (KVec TribQ) :=
  (List.range 24).toArray.map fun i => octaApplyT (slotElemData.getD i 0) seedT

/-- The template certificate (no charts): the data every certificate must have. -/
def template : KCert TribQ := ⟨scVerts, scFrame, scParams, scMu0, scTieMu0, []⟩

/-! ### The claims -/

/-- No pose with view in the cap's cone and Cayley vector in its box is Rupert for `S`. -/
def BoxClaimS (S : Set ℝ³) : Prop :=
  ∀ (p : MatrixPose) (w : Fin 3 → ℝ), p.relativeRotation = cayleyMatrix (w 0) (w 1) (w 2) →
    InCapView (kval scFrame.x) (kval scFrame.e1) (kval scFrame.e2) scMu0 p.view →
    InCapRot (kval scFrame.Z) (kval scFrame.E1) (kval scFrame.X) (scParams.R * scMu0) w → ¬ RupertPose p S

/-- No pose of the tie tube is Rupert for `S`. -/
def TubeClaimS (S : Set ℝ³) : Prop :=
  ∀ (p : MatrixPose) (w : Fin 3 → ℝ), p.relativeRotation = cayleyMatrix (w 0) (w 1) (w 2) →
    InTube template p.view w → ¬ RupertPose p S

def CapsHold (S : Set ℝ³) : Prop := BoxClaimS S ∧ TubeClaimS S

/-! ### From a certificate -/

def kvecEq (a b : KVec TribQ) : Bool := decide (a 0 = b 0) && decide (a 1 = b 1) && decide (a 2 = b 2)

theorem kvecEq_sound {a b : KVec TribQ} (h : kvecEq a b = true) : a = b := by
  simp only [kvecEq, Bool.and_eq_true, decide_eq_true_eq] at h
  funext i; fin_cases i
  · exact h.1.1
  · exact h.1.2
  · exact h.2

def frameEq (f g : Frame TribQ) : Bool :=
  kvecEq f.x g.x && kvecEq f.e1 g.e1 && kvecEq f.e2 g.e2 && kvecEq f.Z g.Z && kvecEq f.E1 g.E1 &&
    kvecEq f.X g.X

theorem frameEq_sound {f g : Frame TribQ} (h : frameEq f g = true) : f = g := by
  simp only [frameEq, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hx, h1⟩, h2⟩, hZ⟩, hE⟩, hX⟩ := h
  cases f; cases g
  simp only [Frame.mk.injEq]
  exact ⟨kvecEq_sound hx, kvecEq_sound h1, kvecEq_sound h2, kvecEq_sound hZ, kvecEq_sound hE, kvecEq_sound hX⟩

/-- A certificate with the template's data. -/
def certMatches (c : KCert TribQ) : Bool :=
  frameEq c.fr scFrame &&
    decide (c.pr.R = scParams.R ∧ c.pr.t0 = scParams.t0 ∧ c.pr.tieSide = scParams.tieSide ∧
      c.pr.tieS0 = scParams.tieS0 ∧ c.pr.tieT0 = scParams.tieT0) &&
    decide (c.mu0 = scMu0) && decide (c.tieMu0 = scTieMu0) &&
    decide (c.V.size = scVerts.size) &&
    (List.range scVerts.size).all fun i => kvecEq (c.V.getD i (fun _ => TribQ.zero)) (scVerts.getD i (fun _ => TribQ.zero))

theorem params_eq {p q : Params} (h : p.R = q.R ∧ p.t0 = q.t0 ∧ p.tieSide = q.tieSide ∧ p.tieS0 = q.tieS0 ∧
    p.tieT0 = q.tieT0) : p = q := by
  cases p; cases q
  simp only [Params.mk.injEq]
  exact h

theorem certMatches_sound {c : KCert TribQ} (h : certMatches c = true) :
    c.fr = scFrame ∧ c.pr = scParams ∧ c.mu0 = scMu0 ∧ c.tieMu0 = scTieMu0 ∧ c.V = scVerts := by
  simp only [certMatches, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨hfr, hpr⟩, hmu⟩, htm⟩, hsize⟩, hV⟩ := h
  refine ⟨frameEq_sound hfr, params_eq hpr, hmu, htm, ?_⟩
  apply Array.ext hsize
  intro i hi hi'
  have := kvecEq_sound (hV i hi')
  simpa [Array.getD, hi, hi'] using this

/-- **The caps hold** for every positive multiple of a checked certificate's solid
with the template's data. -/
theorem capsHold_of_cert (c : KCert TribQ) (hc : c.check = true) (hm : certMatches c = true)
    (s : ℝ) (hs : 0 < s) : CapsHold (s • c.hull) := by
  obtain ⟨hfr, hpr, hmu, htm, -⟩ := certMatches_sound hm
  have hbox := KCert.boxClaim c hc
  have htube := KCert.tubeClaim c hc
  constructor
  · intro p w hR hview hrot hr
    have := rupertPose_of_smul p c.hull s hs hr
    exact hbox { p with innerOffset := s⁻¹ • p.innerOffset } w hR (by rw [hfr, hmu]; exact hview)
      (by rw [hfr, hpr, hmu]; exact hrot) this
  · intro p w hR htb hr
    have := rupertPose_of_smul p c.hull s hs hr
    have htb' : InTube c p.view w := by
      have e : InTube c = InTube template := by
        unfold InTube; rw [hfr, hpr, htm]; rfl
      rw [e]; exact htb
    exact htube { p with innerOffset := s⁻¹ • p.innerOffset } w hR htb' this

/-! ### Cap leaves of the solution trees -/

/-- P · v for a rational point P and an exact vector. -/
def tdotQ (P : Fin 3 → ℚ) (v : KVec TribQ) : TribQ :=
  TribQ.add (TribQ.add (TribQ.scale (P 0) (v 0)) (TribQ.scale (P 1) (v 1))) (TribQ.scale (P 2) (v 2))

def tdot (a b : KVec TribQ) : TribQ :=
  TribQ.add (TribQ.add (TribQ.mul (a 0) (b 0)) (TribQ.mul (a 1) (b 1))) (TribQ.mul (a 2) (b 2))

/-- A rational lower bound of α + Σ_i β_i w_i over the box's Cayley coordinates (interval
products of the β_i enclosures with the coordinate ranges). -/
def lowerAff (iv : AtlasInterval ℚ) (α : TribQ) (β : KVec TribQ) : ℚ :=
  TribQ.lo α + (Cap.mulIvl (TribQ.lo (β 0), TribQ.hi (β 0)) (iv.min.x, iv.max.x)).1 +
    (Cap.mulIvl (TribQ.lo (β 1), TribQ.hi (β 1)) (iv.min.y, iv.max.y)).1 +
    (Cap.mulIvl (TribQ.lo (β 2), TribQ.hi (β 2)) (iv.min.z, iv.max.z)).1

def negV (v : KVec TribQ) : KVec TribQ := fun i => TribQ.neg (v i)
def scaleV (k : TribQ) (v : KVec TribQ) : KVec TribQ := fun i => TribQ.mul k (v i)

/-- The corner quantities, times |x|²|e₁|²|e₂|²: A = (P·x)|e₁|²|e₂|², C₁ = (P·e₁)|x|²|e₂|²,
C₂ = (P·e₂)|x|²|e₁|² (exact5d::TribCapLeafValid). -/
def cornerA (P : Fin 3 → ℚ) : TribQ :=
  TribQ.mul (tdotQ P scFrame.x) (TribQ.mul (tdot scFrame.e1 scFrame.e1) (tdot scFrame.e2 scFrame.e2))
def cornerC1 (P : Fin 3 → ℚ) : TribQ :=
  TribQ.mul (tdotQ P scFrame.e1) (TribQ.mul (tdot scFrame.x scFrame.x) (tdot scFrame.e2 scFrame.e2))
def cornerC2 (P : Fin 3 → ℚ) : TribQ :=
  TribQ.mul (tdotQ P scFrame.e2) (TribQ.mul (tdot scFrame.x scFrame.x) (tdot scFrame.e1 scFrame.e1))

def rotFrame : Fin 3 → KVec TribQ := ![scFrame.Z, scFrame.E1, scFrame.X]

/-- Kind 0, the cap box: every corner has A > 0 and |C_i| ≤ μ₀ A, and the box has
|w·F| ≤ R μ₀ |F|² for F = Z, E₁, X. -/
def boxLeafOk (iv : AtlasInterval ℚ) (T : AtlasProjectiveView.Triangle ℚ) : Bool :=
  (List.finRange 3).all (fun c =>
    let A := cornerA (T c)
    decide (0 < TribQ.lo A) &&
    [cornerC1 (T c), cornerC2 (T c)].all fun C =>
      decide (0 ≤ TribQ.lo (TribQ.sub (TribQ.scale scMu0 A) C)) &&
      decide (0 ≤ TribQ.lo (TribQ.add (TribQ.scale scMu0 A) C))) &&
  (List.finRange 3).all fun f =>
    let F := rotFrame f
    let bound := TribQ.scale (scParams.R * scMu0) (tdot F F)
    decide (0 ≤ lowerAff iv bound (negV F)) && decide (0 ≤ lowerAff iv bound F)

/-- Kind 1, the tie tube: per corner, with M = −C₁: A > 0, 0 ≤ M ≤ μ_T A, |C₂| ≤ t₀ M, and
over the box |(w·F) A − s_F |F|² M| ≤ t₀ |F|² M (s_Z = s₀*, s_E₁ = s_X = 0). -/
def tubeLeafOk (iv : AtlasInterval ℚ) (T : AtlasProjectiveView.Triangle ℚ) : Bool :=
  (List.finRange 3).all fun c =>
    let A := cornerA (T c)
    let M := TribQ.neg (cornerC1 (T c))
    let C2 := cornerC2 (T c)
    let t0 := scParams.tieT0
    decide (0 < TribQ.lo A) && decide (0 ≤ TribQ.lo M) &&
    decide (0 ≤ TribQ.lo (TribQ.sub (TribQ.scale scTieMu0 A) M)) &&
    decide (0 ≤ TribQ.lo (TribQ.sub (TribQ.scale t0 M) C2)) &&
    decide (0 ≤ TribQ.lo (TribQ.add (TribQ.scale t0 M) C2)) &&
    (List.finRange 3).all fun f =>
      let F := rotFrame f
      let sF : ℚ := if f = 0 then scParams.tieS0 else 0
      let base := TribQ.mul (tdot F F) M
      let β := scaleV A F
      decide (0 ≤ lowerAff iv (TribQ.add (TribQ.scale t0 base) (TribQ.scale sF base)) (negV β)) &&
      decide (0 ≤ lowerAff iv (TribQ.sub (TribQ.scale t0 base) (TribQ.scale sF base)) β)

/-- The cap-leaf check (cap 0: the box, cap 1: the tube; `search5d --trib_caps`). -/
def capLeafValidB (iv : AtlasInterval ℚ) (_root : Fin 8) (T : AtlasProjectiveView.Triangle ℚ) (cap : ℕ) :
    Bool :=
  match cap with
  | 0 => boxLeafOk iv T
  | 1 => tubeLeafOk iv T
  | _ => false

/-! ### Soundness of the cap leaves -/

theorem val_tdotQ (P : Fin 3 → ℚ) (v : KVec TribQ) :
    (tdotQ P v).val = rdot (fun i => (P i : ℝ)) (kval v) := by
  simp only [tdotQ, rdot, kval]
  rw [show TribQ.add = (· + ·) from rfl]
  simp only [TribQ.val_add, TribQ.val_scale]
  rfl

theorem val_tdot (a b : KVec TribQ) : (tdot a b).val = rdot (kval a) (kval b) := by
  simp only [tdot, rdot, kval]
  rw [show TribQ.add = (· + ·) from rfl, show TribQ.mul = (· * ·) from rfl]
  simp only [TribQ.val_add, TribQ.val_mul]
  rfl

theorem lo_le (x : TribQ) : (TribQ.lo x : ℝ) ≤ x.val := TribQ.lo_le_val x
theorem le_hi (x : TribQ) : x.val ≤ (TribQ.hi x : ℝ) := TribQ.val_le_hi x

theorem lowerAff_le (iv : AtlasInterval ℚ) (α : TribQ) (β : KVec TribQ) (p : AtlasPose ℝ) (hp : p ∈ iv.toReal) :
    (lowerAff iv α β : ℝ) ≤ α.val + (β 0).val * p.x + (β 1).val * p.y + (β 2).val * p.z := by
  have hm := AtlasInterval.mem_toReal_iff.mp hp
  have h2 := hm 2; have h3 := hm 3; have h4 := hm 4
  simp only [AtlasPose.get_two, AtlasPose.get_three, AtlasPose.get_four, Set.mem_Icc] at h2 h3 h4
  have m0 := (Cap.mem_mulIvl (a := (TribQ.lo (β 0), TribQ.hi (β 0))) (b := (iv.min.x, iv.max.x))
    ⟨lo_le (β 0), le_hi (β 0)⟩ ⟨h2.1, h2.2⟩).1
  have m1 := (Cap.mem_mulIvl (a := (TribQ.lo (β 1), TribQ.hi (β 1))) (b := (iv.min.y, iv.max.y))
    ⟨lo_le (β 1), le_hi (β 1)⟩ ⟨h3.1, h3.2⟩).1
  have m2 := (Cap.mem_mulIvl (a := (TribQ.lo (β 2), TribQ.hi (β 2))) (b := (iv.min.z, iv.max.z))
    ⟨lo_le (β 2), le_hi (β 2)⟩ ⟨h4.1, h4.2⟩).1
  have ha := lo_le α
  unfold lowerAff
  push_cast
  linarith

/-- An inequality linear in the view that holds at the corners holds over the cone. -/
theorem lin_nonneg {u : Fin 3 → ℝ} {κ : ℝ} (hκ : 0 < κ) {wc : Fin 3 → ℝ} (hw0 : ∀ c, 0 ≤ wc c)
    {P : Fin 3 → Fin 3 → ℝ} (hlin : ∀ v, rdot u v = κ * ∑ c, wc c * rdot (P c) v)
    (a b : ℝ) (v1 v2 : Fin 3 → ℝ) (hc : ∀ c, 0 ≤ a * rdot (P c) v1 + b * rdot (P c) v2) :
    0 ≤ a * rdot u v1 + b * rdot u v2 := by
  rw [hlin, hlin]
  have : a * (κ * ∑ c, wc c * rdot (P c) v1) + b * (κ * ∑ c, wc c * rdot (P c) v2) =
      κ * ∑ c, wc c * (a * rdot (P c) v1 + b * rdot (P c) v2) := by
    simp only [Fin.sum_univ_three]; ring
  rw [this]
  apply mul_nonneg hκ.le
  exact Finset.sum_nonneg fun c _ => mul_nonneg (hw0 c) (hc c)

theorem lin_pos {u : Fin 3 → ℝ} {κ : ℝ} (hκ : 0 < κ) {wc : Fin 3 → ℝ} (hw0 : ∀ c, 0 ≤ wc c)
    (hw1 : ∑ c, wc c = 1)
    {P : Fin 3 → Fin 3 → ℝ} (hlin : ∀ v, rdot u v = κ * ∑ c, wc c * rdot (P c) v)
    (a : ℝ) (v : Fin 3 → ℝ) (hc : ∀ c, 0 < a * rdot (P c) v) : 0 < a * rdot u v := by
  rw [hlin]
  have : a * (κ * ∑ c, wc c * rdot (P c) v) = κ * ∑ c, wc c * (a * rdot (P c) v) := by
    simp only [Fin.sum_univ_three]; ring
  rw [this]
  apply mul_pos hκ
  obtain ⟨c, hc'⟩ : ∃ c, 0 < wc c := by
    by_contra hneg
    push Not at hneg
    have : ∑ c, wc c ≤ 0 := Finset.sum_nonpos fun c _ => hneg c
    linarith
  calc 0 < wc c * (a * rdot (P c) v) := mul_pos hc' (hc c)
    _ ≤ ∑ c, wc c * (a * rdot (P c) v) :=
      Finset.single_le_sum (fun c _ => mul_nonneg (hw0 c) (hc c).le) (Finset.mem_univ c)

theorem template_frameOk : template.frameOk = true := by decide +kernel

/-- The real frame values (positive norms, from `template_frameOk`). -/
theorem frame_pos :
    0 < rdot (kval scFrame.x) (kval scFrame.x) ∧ 0 < rdot (kval scFrame.e1) (kval scFrame.e1) ∧
    0 < rdot (kval scFrame.e2) (kval scFrame.e2) ∧ 0 < rdot (kval scFrame.Z) (kval scFrame.Z) ∧
    0 < rdot (kval scFrame.E1) (kval scFrame.E1) ∧ 0 < rdot (kval scFrame.X) (kval scFrame.X) := by
  obtain ⟨-, -, -, -, -, -, h1, h2, h3, h4, h5, h6⟩ := frameOk_sound template_frameOk
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem val_sub' (a b : TribQ) : (TribQ.sub a b).val = a.val - b.val := TribQ.val_sub a b
theorem val_add' (a b : TribQ) : (TribQ.add a b).val = a.val + b.val := TribQ.val_add a b
theorem val_mul' (a b : TribQ) : (TribQ.mul a b).val = a.val * b.val := TribQ.val_mul a b
theorem val_neg' (a : TribQ) : (TribQ.neg a).val = -a.val := TribQ.val_neg a

theorem lo_nonneg {x : TribQ} (h : (0 : ℚ) ≤ TribQ.lo x) : 0 ≤ x.val :=
  le_trans (by exact_mod_cast h) (lo_le x)

theorem lo_pos {x : TribQ} (h : (0 : ℚ) < TribQ.lo x) : 0 < x.val :=
  lt_of_lt_of_le (by exact_mod_cast h) (lo_le x)

/-- The corner quantities' values. -/
theorem val_cornerA (P : Fin 3 → ℚ) : (cornerA P).val =
    rdot (fun i => (P i : ℝ)) (kval scFrame.x) *
      (rdot (kval scFrame.e1) (kval scFrame.e1) * rdot (kval scFrame.e2) (kval scFrame.e2)) := by
  simp only [cornerA, val_mul', val_tdotQ, val_tdot]

theorem val_cornerC1 (P : Fin 3 → ℚ) : (cornerC1 P).val =
    rdot (fun i => (P i : ℝ)) (kval scFrame.e1) *
      (rdot (kval scFrame.x) (kval scFrame.x) * rdot (kval scFrame.e2) (kval scFrame.e2)) := by
  simp only [cornerC1, val_mul', val_tdotQ, val_tdot]

theorem val_cornerC2 (P : Fin 3 → ℚ) : (cornerC2 P).val =
    rdot (fun i => (P i : ℝ)) (kval scFrame.e2) *
      (rdot (kval scFrame.x) (kval scFrame.x) * rdot (kval scFrame.e1) (kval scFrame.e1)) := by
  simp only [cornerC2, val_mul', val_tdotQ, val_tdot]

theorem rdot_w (F : KVec TribQ) (p : AtlasPose ℝ) :
    rdot (![p.x, p.y, p.z]) (kval F) = (F 0).val * p.x + (F 1).val * p.y + (F 2).val * p.z := by
  simp [rdot, kval, ExactScalarVal.val]; ring

/-- The view and the relative rotation of a chart-0 pose over a view triangle. -/
theorem leaf_view (root : Fin 8) (T : AtlasProjectiveView.Triangle ℚ) (p : AtlasPose ℝ)
    (hscale : 1 ≤ AtlasProjectiveView.viewScale root p)
    (htri : Noperts.Atlas.ProjectiveView.InTriangle (Noperts.Atlas.ProjectiveView.toReal T)
      (AtlasProjectiveView.normalizedView root p)) (offset : ℝ²) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ wc : Fin 3 → ℝ, (∀ c, 0 ≤ wc c) ∧ ∑ c, wc c = 1 ∧
      ∀ v, rdot (p.matrixPoseWithOffset 0 offset).view v = κ * ∑ c, wc c * rdot (fun i => (T c i : ℝ)) v := by
  obtain ⟨wc, hw0, hw1, hwT⟩ := htri
  set κ := AtlasProjectiveView.viewScale root p
  have hκ : 0 < κ := by linarith
  refine ⟨κ, hκ, wc, hw0, hw1, ?_⟩
  have hview : (p.matrixPoseWithOffset 0 offset).view = κ • (fun k => ∑ c, wc c * (T c k : ℝ)) := by
    funext k
    have hk := congrFun hwT k
    simp only [AtlasProjectiveView.normalizedView, Noperts.Atlas.ProjectiveView.affinePoint,
      Noperts.Atlas.ProjectiveView.toReal] at hk
    simp only [MatrixPose.view, AtlasPose.matrixPoseWithOffset_outerRot_val, rotRM_mat_row2, Pi.smul_apply,
      smul_eq_mul]
    have : eulerView p.θ p.φ k = AtlasEdgeCertificate.viewVector p k := by
      fin_cases k <;> simp [eulerView, AtlasEdgeCertificate.viewVector]
    rw [this, ← mul_div_cancel₀ (AtlasEdgeCertificate.viewVector p k) hκ.ne', hk]
  intro v
  rw [hview]
  simp only [rdot, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  ring

theorem leaf_rot (p : AtlasPose ℝ) (offset : ℝ²) :
    (p.matrixPoseWithOffset 0 offset).relativeRotation =
      cayleyMatrix ((![p.x, p.y, p.z] : Fin 3 → ℝ) 0) ((![p.x, p.y, p.z] : Fin 3 → ℝ) 1)
        ((![p.x, p.y, p.z] : Fin 3 → ℝ) 2) := by
  rw [AtlasPose.matrixPoseWithOffset_relativeRotation, CayleyAtlas.chartMatrix_zero, Matrix.one_mul]
  rfl

theorem rot_bound (iv : AtlasInterval ℚ) (p : AtlasPose ℝ) (hp : p ∈ iv.toReal) (F : KVec TribQ)
    (hpos : 0 < rdot (kval F) (kval F)) (k : ℚ)
    (h1 : 0 ≤ lowerAff iv (TribQ.scale k (tdot F F)) (negV F))
    (h2 : 0 ≤ lowerAff iv (TribQ.scale k (tdot F F)) F) :
    |rdot (![p.x, p.y, p.z]) (kval F) / rdot (kval F) (kval F)| ≤ k := by
  have h1' : (0 : ℝ) ≤ (lowerAff iv (TribQ.scale k (tdot F F)) (negV F) : ℝ) := by exact_mod_cast h1
  have h2' : (0 : ℝ) ≤ (lowerAff iv (TribQ.scale k (tdot F F)) F : ℝ) := by exact_mod_cast h2
  have a1 := le_trans h1' (lowerAff_le iv (TribQ.scale k (tdot F F)) (negV F) p hp)
  have a2 := le_trans h2' (lowerAff_le iv (TribQ.scale k (tdot F F)) F p hp)
  simp only [negV, val_neg', TribQ.val_scale, val_tdot] at a1 a2
  rw [rdot_w, abs_div, abs_of_pos hpos, div_le_iff₀ hpos, abs_le]
  constructor <;> nlinarith

theorem tube_abs {WF FF xx n1 n2 X Y t0 sF : ℝ} (hFF : 0 < FF) (hxx : 0 < xx) (hn1 : 0 < n1)
    (hn2 : 0 < n2)
    (hp : 0 ≤ -(n1 * n2 * WF) * X + -((t0 + sF) * FF * (xx * n2)) * Y)
    (hm : 0 ≤ n1 * n2 * WF * X + -((t0 - sF) * FF * (xx * n2)) * Y) :
    |WF / FF * (X / xx) - sF * -(Y / n1)| ≤ t0 * -(Y / n1) := by
  set a := X / xx
  set m := -(Y / n1)
  have hX : X = a * xx := by simp only [a]; field_simp
  have hY : Y = -m * n1 := by simp only [m]; field_simp
  have k : 0 < xx * n1 * n2 := by positivity
  have hp' : 0 ≤ -WF * a + (t0 + sF) * FF * m := by
    have e : -(n1 * n2 * WF) * X + -((t0 + sF) * FF * (xx * n2)) * Y =
        (xx * n1 * n2) * (-WF * a + (t0 + sF) * FF * m) := by rw [hX, hY]; ring
    rw [e] at hp
    exact (mul_nonneg_iff_of_pos_left k).mp hp
  have hm' : 0 ≤ WF * a + (t0 - sF) * FF * m := by
    have e : n1 * n2 * WF * X + -((t0 - sF) * FF * (xx * n2)) * Y =
        (xx * n1 * n2) * (WF * a + (t0 - sF) * FF * m) := by rw [hX, hY]; ring
    rw [e] at hm
    exact (mul_nonneg_iff_of_pos_left k).mp hm
  have hq : WF / FF * a - sF * m = (WF * a - sF * FF * m) / FF := by field_simp
  rw [hq, abs_div, abs_of_pos hFF, div_le_iff₀ hFF, abs_le]
  constructor <;> nlinarith

/-- **Cap leaves are sound**: given the claims, no pose of a valid cap leaf is Rupert. -/
theorem capLeaf_sound (S : Set ℝ³) (hcaps : CapsHold S) (iv : AtlasInterval ℚ) (root : Fin 8)
    (T : AtlasProjectiveView.Triangle ℚ) (cap : ℕ) (h : capLeafValidB iv root T cap = true)
    (p : AtlasPose ℝ) (hp : p ∈ iv.toReal) (hscale : 1 ≤ AtlasProjectiveView.viewScale root p)
    (htri : Noperts.Atlas.ProjectiveView.InTriangle (Noperts.Atlas.ProjectiveView.toReal T)
      (AtlasProjectiveView.normalizedView root p)) (offset : ℝ²) :
    ¬ RupertPose (p.matrixPoseWithOffset 0 offset) S := by
  set pose := p.matrixPoseWithOffset 0 offset
  set u := pose.view
  set w : Fin 3 → ℝ := ![p.x, p.y, p.z]
  obtain ⟨κ, hκ, wc, hw0, hw1, hlin⟩ := leaf_view root T p hscale htri offset
  have hRw := leaf_rot p offset
  obtain ⟨hxx, hn1, hn2, hZZ, hEE, hXX⟩ := frame_pos
  set x0 := kval scFrame.x; set e1 := kval scFrame.e1; set e2 := kval scFrame.e2
  set xx := rdot x0 x0; set n1 := rdot e1 e1; set n2 := rdot e2 e2
  set P : Fin 3 → Fin 3 → ℝ := fun c i => (T c i : ℝ)
  have hK : 0 < xx * n1 * n2 := by positivity
  have hux : 0 < rdot u x0 := by
    have := lin_pos hκ hw0 hw1 hlin (n1 * n2) x0 (fun c => by
      have hc : (0 : ℚ) < TribQ.lo (cornerA (T c)) := by
        match cap, h with
        | 0, h =>
          simp only [capLeafValidB, boxLeafOk, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
            true_implies, decide_eq_true_eq] at h
          exact (h.1 c).1
        | 1, h =>
          simp only [capLeafValidB, tubeLeafOk, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
            true_implies, decide_eq_true_eq] at h
          exact (h c).1.1.1.1.1
      have := lo_pos hc
      rw [val_cornerA] at this
      linarith [this])
    exact pos_of_mul_pos_right this (by positivity)
  match cap, h with
  | 0, h =>
    simp only [capLeafValidB, boxLeafOk, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
      true_implies, decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at h
    obtain ⟨hcorner, hrot⟩ := h
    -- The view cone: |C_i(u)| ≤ μ₀ A(u), divided by |x|²|e₁|²|e₂|².
    have hcone : ∀ (e : Fin 3 → ℝ) (k : ℝ), 0 < k →
        (∀ c, 0 ≤ (scMu0 : ℝ) * (n1 * n2) * rdot (P c) x0 - k * rdot (P c) e) →
        (∀ c, 0 ≤ (scMu0 : ℝ) * (n1 * n2) * rdot (P c) x0 + k * rdot (P c) e) →
        |rdot u e| * k ≤ (scMu0 : ℝ) * (n1 * n2) * rdot u x0 := by
      intro e k hk h1 h2
      have a := lin_nonneg hκ hw0 hlin ((scMu0 : ℝ) * (n1 * n2)) (-k) x0 e (fun c => by linarith [h1 c])
      have b := lin_nonneg hκ hw0 hlin ((scMu0 : ℝ) * (n1 * n2)) k x0 e (fun c => by linarith [h2 c])
      rcases abs_cases (rdot u e) with ⟨he, -⟩ | ⟨he, -⟩ <;> rw [he] <;> linarith
    have hvA : ∀ c, (cornerA (T c)).val = (n1 * n2) * rdot (P c) x0 := fun c => by rw [val_cornerA]; ring
    have hvC1 : ∀ c, (cornerC1 (T c)).val = (xx * n2) * rdot (P c) e1 := fun c => by rw [val_cornerC1]; ring
    have hvC2 : ∀ c, (cornerC2 (T c)).val = (xx * n1) * rdot (P c) e2 := fun c => by rw [val_cornerC2]; ring
    have hc1 := hcone e1 (xx * n2) (by positivity)
      (fun c => by
        have := lo_nonneg (hcorner c).2.1.1
        rw [val_sub', TribQ.val_scale, hvA, hvC1] at this; linarith)
      (fun c => by
        have := lo_nonneg (hcorner c).2.1.2
        rw [val_add', TribQ.val_scale, hvA, hvC1] at this; linarith)
    have hc2 := hcone e2 (xx * n1) (by positivity)
      (fun c => by
        have := lo_nonneg (hcorner c).2.2.1
        rw [val_sub', TribQ.val_scale, hvA, hvC2] at this; linarith)
      (fun c => by
        have := lo_nonneg (hcorner c).2.2.2
        rw [val_add', TribQ.val_scale, hvA, hvC2] at this; linarith)
    apply hcaps.1 pose w hRw
    · refine ⟨hux, ?_, ?_⟩
      · rw [abs_div, abs_of_pos hn1, div_le_iff₀ hn1]
        have : (scMu0 : ℝ) * (rdot u x0 / xx) * n1 = (scMu0 * (n1 * n2) * rdot u x0) / (xx * n2) := by
          field_simp
        rw [this, le_div_iff₀ (by positivity)]
        exact hc1
      · rw [abs_div, abs_of_pos hn2, div_le_iff₀ hn2]
        have : (scMu0 : ℝ) * (rdot u x0 / xx) * n2 = (scMu0 * (n1 * n2) * rdot u x0) / (xx * n1) := by
          field_simp
        rw [this, le_div_iff₀ (by positivity)]
        exact hc2
    · have hr := fun f => hrot f
      have r0 := rot_bound iv p hp scFrame.Z hZZ _ (hr 0).1 (hr 0).2
      have r1 := rot_bound iv p hp scFrame.E1 hEE _ (hr 1).1 (hr 1).2
      have r2 := rot_bound iv p hp scFrame.X hXX _ (hr 2).1 (hr 2).2
      push_cast at r0 r1 r2
      exact ⟨r0, r1, r2⟩
  | 1, h =>
    simp only [capLeafValidB, tubeLeafOk, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
      true_implies, decide_eq_true_eq] at h
    have hvA : ∀ c, (cornerA (T c)).val = (n1 * n2) * rdot (P c) x0 := fun c => by rw [val_cornerA]; ring
    have hvM : ∀ c, (TribQ.neg (cornerC1 (T c))).val = -(xx * n2) * rdot (P c) e1 := fun c => by
      rw [val_neg', val_cornerC1]; ring
    have hvC2 : ∀ c, (cornerC2 (T c)).val = (xx * n1) * rdot (P c) e2 := fun c => by rw [val_cornerC2]; ring
    -- 0 ≤ m.
    have hY : 0 ≤ -(xx * n2) * rdot u e1 := by
      have := lin_nonneg hκ hw0 hlin 0 (-(xx * n2)) x0 e1 (fun c => by
        have := lo_nonneg (h c).1.1.1.1.2
        rw [hvM] at this; linarith)
      linarith
    have hm0 : 0 ≤ -(rdot u e1 / n1) := by
      have : rdot u e1 ≤ 0 := by nlinarith [mul_pos hxx hn2]
      have : rdot u e1 / n1 ≤ 0 := div_nonpos_of_nonpos_of_nonneg this hn1.le
      linarith
    -- m ≤ μ_T a.
    have hmT : 0 ≤ (scTieMu0 : ℝ) * (n1 * n2) * rdot u x0 + (xx * n2) * rdot u e1 :=
      lin_nonneg hκ hw0 hlin _ _ x0 e1 (fun c => by
        have := lo_nonneg (h c).1.1.1.2
        rw [val_sub', TribQ.val_scale, hvA, hvM] at this; linarith)
    -- |c₂| ≤ t₀ m.
    have hc2a : 0 ≤ -((scParams.tieT0 : ℝ) * (xx * n2)) * rdot u e1 + -(xx * n1) * rdot u e2 :=
      lin_nonneg hκ hw0 hlin _ _ e1 e2 (fun c => by
        have := lo_nonneg (h c).1.1.2
        rw [val_sub', TribQ.val_scale, hvM, hvC2] at this; linarith)
    have hc2b : 0 ≤ -((scParams.tieT0 : ℝ) * (xx * n2)) * rdot u e1 + (xx * n1) * rdot u e2 :=
      lin_nonneg hκ hw0 hlin _ _ e1 e2 (fun c => by
        have := lo_nonneg (h c).1.2
        rw [val_add', TribQ.val_scale, hvM, hvC2] at this; linarith)
    -- The rotation: per frame vector F, from both interval bounds at every corner.
    have hrotF : ∀ f : Fin 3, let F := rotFrame f; let sF : ℚ := if f = 0 then scParams.tieS0 else 0;
        |rdot w (kval F) / rdot (kval F) (kval F) * (rdot u x0 / xx) - (sF : ℝ) * -(rdot u e1 / n1)| ≤
          (scParams.tieT0 : ℝ) * -(rdot u e1 / n1) := by
      intro f F sF
      have hFF : 0 < rdot (kval F) (kval F) := by
        fin_cases f
        · exact hZZ
        · exact hEE
        · exact hXX
      set WF := rdot w (kval F)
      set FF := rdot (kval F) (kval F)
      have hb := fun c => (h c).2 f
      have hwF : WF = (F 0).val * p.x + (F 1).val * p.y + (F 2).val * p.z := rdot_w F p
      have hp' := lin_nonneg hκ hw0 hlin (-(n1 * n2 * WF)) (-(((scParams.tieT0 : ℝ) + sF) * FF * (xx * n2))) x0 e1
        (fun c => by
          have l1 := le_trans (show (0 : ℝ) ≤ (lowerAff iv _ _ : ℝ) by exact_mod_cast (hb c).1)
            (lowerAff_le iv _ _ p hp)
          simp only [negV, scaleV, val_neg', val_mul', val_add', TribQ.val_scale, val_tdot, hvA, hvM] at l1
          have e : -(n1 * n2 * WF) * rdot (P c) x0 + -(((scParams.tieT0 : ℝ) + sF) * FF * (xx * n2)) * rdot (P c) e1 =
              ↑scParams.tieT0 * (FF * (-(xx * n2) * rdot (P c) e1)) + ↑sF * (FF * (-(xx * n2) * rdot (P c) e1)) +
                -(n1 * n2 * rdot (P c) x0 * (F 0).val) * p.x + -(n1 * n2 * rdot (P c) x0 * (F 1).val) * p.y +
                -(n1 * n2 * rdot (P c) x0 * (F 2).val) * p.z := by rw [hwF]; ring
          rw [e]; exact l1)
      have hm' := lin_nonneg hκ hw0 hlin (n1 * n2 * WF) (-(((scParams.tieT0 : ℝ) - sF) * FF * (xx * n2))) x0 e1
        (fun c => by
          have l1 := le_trans (show (0 : ℝ) ≤ (lowerAff iv _ _ : ℝ) by exact_mod_cast (hb c).2)
            (lowerAff_le iv _ _ p hp)
          simp only [scaleV, val_mul', val_sub', TribQ.val_scale, val_tdot, hvA, hvM] at l1
          have e : n1 * n2 * WF * rdot (P c) x0 + -(((scParams.tieT0 : ℝ) - sF) * FF * (xx * n2)) * rdot (P c) e1 =
              ↑scParams.tieT0 * (FF * (-(xx * n2) * rdot (P c) e1)) - ↑sF * (FF * (-(xx * n2) * rdot (P c) e1)) +
                n1 * n2 * rdot (P c) x0 * (F 0).val * p.x + n1 * n2 * rdot (P c) x0 * (F 1).val * p.y +
                n1 * n2 * rdot (P c) x0 * (F 2).val * p.z := by rw [hwF]; ring
          rw [e]; exact l1)
      exact tube_abs hFF hxx hn1 hn2 hp' hm'
    apply hcaps.2 pose w hRw
    show 0 < rdot u x0 ∧ 0 ≤ -(rdot u e1 / n1) ∧ -(rdot u e1 / n1) ≤ (scTieMu0 : ℝ) * (rdot u x0 / xx) ∧
      |rdot u e2 / n2| ≤ (scParams.tieT0 : ℝ) * -(rdot u e1 / n1) ∧
      |rdot w (kval scFrame.Z) / rdot (kval scFrame.Z) (kval scFrame.Z) * (rdot u x0 / xx) -
          (scParams.tieS0 : ℝ) * -(rdot u e1 / n1)| ≤ (scParams.tieT0 : ℝ) * -(rdot u e1 / n1) ∧
      |rdot w (kval scFrame.E1) / rdot (kval scFrame.E1) (kval scFrame.E1) * (rdot u x0 / xx)| ≤
          (scParams.tieT0 : ℝ) * -(rdot u e1 / n1) ∧
      |rdot w (kval scFrame.X) / rdot (kval scFrame.X) (kval scFrame.X) * (rdot u x0 / xx)| ≤
          (scParams.tieT0 : ℝ) * -(rdot u e1 / n1)
    have hK1 : 0 < xx * n1 * n2 := by positivity
    refine ⟨hux, hm0, ?_, ?_, ?_, ?_, ?_⟩
    · have e : (scTieMu0 : ℝ) * (rdot u x0 / xx) - -(rdot u e1 / n1) =
          ((scTieMu0 : ℝ) * (n1 * n2) * rdot u x0 + (xx * n2) * rdot u e1) / (xx * n1 * n2) := by
        first | (field_simp; ring) | field_simp
      have : 0 ≤ (scTieMu0 : ℝ) * (rdot u x0 / xx) - -(rdot u e1 / n1) := by rw [e]; positivity
      linarith
    · rw [abs_le]
      have ea : (scParams.tieT0 : ℝ) * -(rdot u e1 / n1) - rdot u e2 / n2 =
          (-((scParams.tieT0 : ℝ) * (xx * n2)) * rdot u e1 + -(xx * n1) * rdot u e2) / (xx * n1 * n2) := by
        first | (field_simp; ring) | field_simp
      have eb : (scParams.tieT0 : ℝ) * -(rdot u e1 / n1) + rdot u e2 / n2 =
          (-((scParams.tieT0 : ℝ) * (xx * n2)) * rdot u e1 + (xx * n1) * rdot u e2) / (xx * n1 * n2) := by
        first | (field_simp; ring) | field_simp
      have ha : 0 ≤ (scParams.tieT0 : ℝ) * -(rdot u e1 / n1) - rdot u e2 / n2 := by rw [ea]; positivity
      have hb : 0 ≤ (scParams.tieT0 : ℝ) * -(rdot u e1 / n1) + rdot u e2 / n2 := by rw [eb]; positivity
      constructor <;> linarith
    · have := hrotF 0
      simpa [rotFrame] using this
    · have := hrotF 1
      simpa [rotFrame] using this
    · have := hrotF 2
      simpa [rotFrame] using this

/-- The snub cube's caps for the octahedral solution trees (a scoped instance). -/
scoped instance octaCaps : OctaCaps where
  capLeafValidB := capLeafValidB
  CapsHold := CapsHold
  capLeaf_sound := fun S hS iv root T cap h p hp hscale htri offset =>
    capLeaf_sound S hS iv root T cap h p hp hscale htri offset

end SnubCube

end
