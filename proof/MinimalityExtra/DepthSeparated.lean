module

public import Mathlib
public import MinimalityExtra
public import Minimality.DepthSeparated
public import Minimality.SplitRows

/-!
# Depth-separated views are free, frame-free and with an explicit motion

`depthSeparatedViewIsFree` proves `MinimalityExtra.DepthSeparatedViewIsFree`.
`SplitRows` is its row form, a product of two linear forms in the view per rim row, and
`freeAt_of_splitRows` needs no antipodality. `freeAt_of_pivot` is a sufficient condition at rims
that are not split: rotation about a line through a corner that keeps both of its edges.

The proofs live in `Minimality.SplitRows` (namespace `Minimality.Split`), so that the minimality
proof can use them without importing `MinimalityExtra`; this file restates them under their old
names. The `Minimality.Split` definitions repeat the bodies of the `MinimalityExtra` ones, so the
restatements are proved by the moved lemmas up to unfolding (`freeAt_iff_split` and friends).
-/

@[expose] public section

namespace MinimalityExtra
open scoped RealInnerProductSpace
open Finset

theorem inner3 (a b : ℝ³) : ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 :=
  Minimality.Split.inner3 a b

@[simp] theorem cross_0 (a b : ℝ³) : cross a b 0 = a 1 * b 2 - a 2 * b 1 :=
  Minimality.Split.cross_0 a b
@[simp] theorem cross_1 (a b : ℝ³) : cross a b 1 = a 2 * b 0 - a 0 * b 2 :=
  Minimality.Split.cross_1 a b
@[simp] theorem cross_2 (a b : ℝ³) : cross a b 2 = a 0 * b 1 - a 1 * b 0 :=
  Minimality.Split.cross_2 a b

/-! ### The `MinimalityExtra` notions agree with the `Minimality.Split` ones -/

theorem det3_eq_split (a b c : ℝ³) : det3 a b c = Minimality.Split.det3 a b c := rfl

theorem cross_eq_minimality (a b : ℝ³) : cross a b = Minimality.cross a b := rfl

theorem tiltCert_iff_split (V : Finset ℝ³) (w ω τ y : ℝ³) :
    TiltCert V w ω τ y ↔ Minimality.Split.TiltCert V w ω τ y := Iff.rfl

theorem freeAt_iff_split (V : Finset ℝ³) (w : ℝ³) : FreeAt V w ↔ Minimality.Split.FreeAt V w :=
  Iff.rfl

theorem strictRimN_iff_split {n k : ℕ} [NeZero k] (x : Fin n → ℝ³) (u : ℝ³) (lab : ZMod k → Fin n) :
    StrictRimN x u lab ↔ Minimality.Split.StrictRimN x u lab := Iff.rfl

theorem hiddenInTriangles_iff_split {n k : ℕ} (x : Fin n → ℝ³) (w : ℝ³) (lab : ZMod k → Fin n) :
    HiddenInTriangles x w lab ↔ Minimality.Split.HiddenInTriangles x w lab := Iff.rfl

theorem levelPoint_eq_split {k : ℕ} (X : ZMod k → ℝ³) (w : ℝ³) (a c : ZMod k) :
    levelPoint X w a c = Minimality.Split.levelPoint X w a c := rfl

theorem isDepthSeparatedAt_iff_split {k : ℕ} (X : ZMod k → ℝ³) (w : ℝ³) (a c : ZMod k) :
    IsDepthSeparatedAt X w a c ↔ Minimality.Split.IsDepthSeparatedAt X w a c := Iff.rfl

/-- Row form of a split antipodal level pair `(edge a, corner c)` of the cycle `X` at the view
`w`, with orientation `σ`.  For every rim edge `i` other than `a` and every end `j ≠ c` of it,
the depth `⟪X j - X c, w⟫` and the rise `det3 (X (i+1) - X i) d w` of the height
`det3 d w ·` (`d` the edge `a`) along edge `i` have the sign product `σ`. -/
def SplitRows {k : ℕ} (X : ZMod k → ℝ³) (w : ℝ³) (a c : ZMod k) (σ : ℝ) : Prop :=
  Minimality.Split.SplitRows X w a c σ

/-- Motion 1: turning about the horizontal axis through `X c` normal to the support planes. -/
theorem col_turn (E d w y C : ℝ³) :
    det3 E (cross (cross w d) y + (-⟪C, w⟫) • d) w = ⟪y - C, w⟫ * det3 E d w :=
  Minimality.Split.col_turn E d w y C

/-- Motion 2 in general: constant `T` at `C`, spin `θ`, normal shear `β`. -/
theorem col_fix (E d w y C T : ℝ³) (θ β : ℝ) :
    det3 E (cross (θ • w + β • cross w (cross d w)) y +
        (T - θ • cross w C - (β * ⟪C, w⟫) • cross d w)) w =
      det3 E T w + θ * det3 E (cross w (y - C)) w + β * ⟪y - C, w⟫ * det3 E (cross d w) w :=
  Minimality.Split.col_fix E d w y C T θ β

theorem det3_sum_motion (E w y ω₁ τ₁ ω₂ τ₂ : ℝ³) (L : ℝ) :
    det3 E (cross (L • ω₁ + ω₂) y + (L • τ₁ + τ₂)) w =
      L * det3 E (cross ω₁ y + τ₁) w + det3 E (cross ω₂ y + τ₂) w :=
  Minimality.Split.det3_sum_motion E w y ω₁ τ₁ ω₂ τ₂ L

/-- Motion 2 on the edge line: the value is constant. -/
theorem col_edge (d w u T : ℝ³) (D ρ s : ℝ) (hD : D ≠ 0) (hDw : ⟪d, w⟫ = D)
    (hρ : ⟪u, d⟫ - s * ⟪d, d⟫ = ρ) (hs : ⟪u, w⟫ = s * D) (θ : ℝ) :
    det3 d T w + θ * det3 d (cross w u) w + (θ / D) * ⟪u, w⟫ * det3 d (cross d w) w =
      det3 d T w + θ * (⟪w, w⟫ * ρ) :=
  Minimality.Split.col_edge d w u T D ρ s hD hDw hρ hs θ

/-- Large multiples win. -/
theorem exists_large {ι : Type*} [Finite ι] (p q : ι → ℝ)
    (h : ∀ t, 0 < p t ∨ (p t = 0 ∧ 0 < q t)) : ∃ L : ℝ, ∀ t, 0 < L * p t + q t :=
  Minimality.Split.exists_large p q h

theorem zmod_pred_ne_succ {k : ℕ} [NeZero k] (hk : 3 ≤ k) (i : ZMod k) : i - 1 ≠ i + 1 :=
  Minimality.Split.zmod_pred_ne_succ hk i

/-- **Propeller Lemma, row form, with an explicit motion on the rim.** -/
theorem exists_motion_of_splitRows {n k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : Fin n → ℝ³) (w : ℝ³)
    (lab : ZMod k → Fin n) (hinj : Function.Injective lab) (hrim : StrictRimN x w lab)
    (a c : ZMod k) (σ : ℝ)
    (hrows : SplitRows (fun i => x (lab i)) w a c σ)
    (hD : ⟪x (lab (a + 1)) - x (lab a), w⟫ ≠ 0)
    (hnd : ⟪levelPoint (fun i => x (lab i)) w a c - x (lab c),
      x (lab (a + 1)) - x (lab a)⟫ ≠ 0) :
    ∃ ω τ : ℝ³, ∀ i : ZMod k,
      0 < det3 (x (lab (i + 1)) - x (lab i)) (cross ω (x (lab i)) + τ) w ∧
      0 < det3 (x (lab (i + 1)) - x (lab i)) (cross ω (x (lab (i + 1))) + τ) w :=
  Minimality.Split.exists_motion_of_splitRows hk x w lab hinj hrim a c σ hrows hD hnd

/-- A motion strictly inward at both ends of every rim edge gives `FreeAt`. -/
theorem freeAt_of_rimMotion {n k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : Fin n → ℝ³) (w : ℝ³)
    (lab : ZMod k → Fin n) (hinj : Function.Injective lab) (hrim : StrictRimN x w lab)
    (hhid : HiddenInTriangles x w lab)
    (hm : ∃ ω τ : ℝ³, ∀ i : ZMod k,
      0 < det3 (x (lab (i + 1)) - x (lab i)) (cross ω (x (lab i)) + τ) w ∧
      0 < det3 (x (lab (i + 1)) - x (lab i)) (cross ω (x (lab (i + 1))) + τ) w) :
    FreeAt (univ.image x) w :=
  Minimality.Split.freeAt_of_rimMotion hk x w lab hinj hrim hhid hm

/-- **Propeller Lemma, row form.** -/
theorem freeAt_of_splitRows {n k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : Fin n → ℝ³) (w : ℝ³)
    (lab : ZMod k → Fin n) (hinj : Function.Injective lab) (hrim : StrictRimN x w lab)
    (hhid : HiddenInTriangles x w lab) (a c : ZMod k) (σ : ℝ)
    (hrows : SplitRows (fun i => x (lab i)) w a c σ)
    (hD : ⟪x (lab (a + 1)) - x (lab a), w⟫ ≠ 0)
    (hnd : ⟪levelPoint (fun i => x (lab i)) w a c - x (lab c),
      x (lab (a + 1)) - x (lab a)⟫ ≠ 0) :
    FreeAt (univ.image x) w :=
  Minimality.Split.freeAt_of_splitRows hk x w lab hinj hrim hhid a c σ hrows hD hnd


/-- The planar projection used for the monotonicity facts. -/
noncomputable def projP (N w : ℝ³) (e : ℝ³) : ℝ² :=
  Minimality.Split.projP N w e

theorem projP_sub (N w e f : ℝ³) : projP N w e - projP N w f = projP N w (e - f) :=
  Minimality.Split.projP_sub N w e f

theorem cross2_projP (d w e f : ℝ³) :
    Minimality.cross2 (projP (cross d w) w e) (projP (cross d w) w f) =
      ⟪cross d w, cross d w⟫ * det3 e f w :=
  Minimality.Split.cross2_projP d w e f

theorem det3_eq_inner (d w x : ℝ³) : det3 d w x = ⟪cross d w, x⟫ :=
  Minimality.Split.det3_eq_inner d w x

theorem det3_rot (D d w : ℝ³) : det3 D d w = det3 d w D :=
  Minimality.Split.det3_rot D d w

theorem val_succ_sub {k : ℕ} [NeZero k] (hk : 3 ≤ k) (i c : ZMod k) (h : i + 1 ≠ c) :
    (i + 1 - c).val = (i - c).val + 1 ∧ (i - c).val + 1 < k :=
  Minimality.Split.val_succ_sub hk i c h

/-- Arcs give rows. -/
theorem splitRows_of_isDepthSeparatedAt {n k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : Fin n → ℝ³) (w : ℝ³)
    (lab : ZMod k → Fin n) (hinj : Function.Injective lab) (hrim : StrictRimN x w lab)
    (a c : ZMod k) (hs : IsDepthSeparatedAt (fun i => x (lab i)) w a c) :
    (∃ σ : ℝ, SplitRows (fun i => x (lab i)) w a c σ) ∧
      ⟪x (lab (a + 1)) - x (lab a), w⟫ ≠ 0 :=
  Minimality.Split.splitRows_of_isDepthSeparatedAt hk x w lab hinj hrim a c hs

theorem depthSeparatedViewIsFree : DepthSeparatedViewIsFree := by
  intro n k _ x w lab a c hk hinj hrim hhid hs hnd
  obtain ⟨⟨σ, hrows⟩, hD⟩ := splitRows_of_isDepthSeparatedAt hk x w lab hinj hrim a c hs
  exact freeAt_of_splitRows hk x w lab hinj hrim hhid a c σ hrows hD hnd

/-! ## Secondary: the pivot lemma (for rims that are not split) -/

/-- The covector of the condition "the line of the edge `D` stays in its silhouette plane". -/
noncomputable def edgeRow (D w : ℝ³) : ℝ³ :=
  Minimality.Split.edgeRow D w

/-- The axis direction of the pivot at the corner `c`: rotating about the line through `X c` with
this direction keeps the screen lines of both edges at `c`. -/
noncomputable def pivotAxis {k : ℕ} (X : ZMod k → ℝ³) (w : ℝ³) (c : ZMod k) : ℝ³ :=
  Minimality.Split.pivotAxis X w c

theorem det3_pivot_self (D w ν : ℝ³) (h : ⟪ν, edgeRow D w⟫ = 0) : det3 D (cross ν D) w = 0 :=
  Minimality.Split.det3_pivot_self D w ν h

theorem inner_cross_left (A B : ℝ³) : ⟪cross A B, A⟫ = 0 :=
  Minimality.Split.inner_cross_left A B

theorem inner_cross_right (A B : ℝ³) : ⟪cross A B, B⟫ = 0 :=
  Minimality.Split.inner_cross_right A B

theorem cross_sub_right (ν y C : ℝ³) : cross ν (y - C) = cross ν y + -cross ν C :=
  Minimality.Split.cross_sub_right ν y C

/-- **Pivot Lemma.**  If rotating about the pivot axis at `c` (with sign `σ`) moves both ends of
every rim edge not at `c` strictly inward, the view is free.  On a two-peaked 4-corner rim, with
`c` the sharp corner, the four numbers are the torques of the two level tripods at the ends of
their private edges. -/
theorem freeAt_of_pivot {n k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : Fin n → ℝ³) (w : ℝ³)
    (lab : ZMod k → Fin n) (hinj : Function.Injective lab) (hrim : StrictRimN x w lab)
    (hhid : HiddenInTriangles x w lab) (c : ZMod k) (σ : ℝ)
    (hrows : ∀ i j : ZMod k, i ≠ c → i + 1 ≠ c → (j = i ∨ j = i + 1) →
      0 < σ * det3 (x (lab (i + 1)) - x (lab i))
        (cross (pivotAxis (fun i => x (lab i)) w c) (x (lab j) - x (lab c))) w) :
    FreeAt (univ.image x) w :=
  Minimality.Split.freeAt_of_pivot hk x w lab hinj hrim hhid c σ hrows

#print axioms depthSeparatedViewIsFree
#print axioms freeAt_of_pivot

end MinimalityExtra

#print axioms MinimalityExtra.freeAt_of_splitRows
#print axioms MinimalityExtra.freeAt_of_pivot
#print axioms MinimalityExtra.depthSeparatedViewIsFree
