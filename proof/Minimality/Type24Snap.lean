module

public import Minimality.SameView

@[expose] public section

/-!
# The snap form: a test good at the exact corner certifies a neighbourhood (17.1, 17.1′)

The depth difference at an oblique view `d` is exactly linear in the three cosines `h_ij` of the
axes at `1` (`depth_sub_viewOf`); at the exact corner (`h = 0`) it is the snap depth
`snapDepth`.  On the obtuse octant with `|h_ij| ≤ δ L_i L_j` the pair radius `SnapAbove`
keeps the order of the snap (`depth_lt_of_snapAbove`).  A certified rim (`RimTestR`, depths left
open) whose failure patterns are all broken at the snap is Rupert for the whole neighbourhood:
for a quad (`isRupert_type24_snap4`) and a triangle (`isRupert_type24_snap3`).
-/

namespace Minimality
open Finset
open scoped RealInnerProductSpace

namespace Type24

/-- **The snap depth** at the oblique view `d`, relative to the cap: the depth at the exact corner
with the same oblique coordinates and axis lengths. -/
noncomputable def snapDepth (x : Fin 7 → ℝ³) (d : Fin 3 → ℝ) (v : Fin 7) : ℝ :=
  d 0 * ‖x 0 - x 1‖ ^ 2 * oblX0 x v + d 1 * ‖x 2 - x 1‖ ^ 2 * oblX2 x v +
    d 2 * ‖x 6 - x 1‖ ^ 2 * oblX6 x v

/-- The coefficient of `h_ab = ⟪e_a, e_b⟫` in `z_v − z_w` at the view `d` (17.1). -/
noncomputable def cosCoefAB (x : Fin 7 → ℝ³) (d : Fin 3 → ℝ) (v w : Fin 7) : ℝ :=
  d 0 * (oblX2 x v - oblX2 x w) + d 1 * (oblX0 x v - oblX0 x w)

/-- The coefficient of `h_ac`. -/
noncomputable def cosCoefAC (x : Fin 7 → ℝ³) (d : Fin 3 → ℝ) (v w : Fin 7) : ℝ :=
  d 0 * (oblX6 x v - oblX6 x w) + d 2 * (oblX0 x v - oblX0 x w)

/-- The coefficient of `h_bc`. -/
noncomputable def cosCoefBC (x : Fin 7 → ℝ³) (d : Fin 3 → ℝ) (v w : Fin 7) : ℝ :=
  d 1 * (oblX6 x v - oblX6 x w) + d 2 * (oblX2 x v - oblX2 x w)

/-- **The obtuse octant at `1` within cosine `δ`**: `h_ij ≤ 0` and `−h_ij ≤ δ L_i L_j`. -/
def ObtuseNear (x : Fin 7 → ℝ³) (δ : ℝ) : Prop :=
  ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0 ∧ ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0 ∧ ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0 ∧
    -⟪x 0 - x 1, x 2 - x 1⟫ ≤ δ * (‖x 0 - x 1‖ * ‖x 2 - x 1‖) ∧
    -⟪x 0 - x 1, x 6 - x 1⟫ ≤ δ * (‖x 0 - x 1‖ * ‖x 6 - x 1‖) ∧
    -⟪x 2 - x 1, x 6 - x 1⟫ ≤ δ * (‖x 2 - x 1‖ * ‖x 6 - x 1‖)

/-- **`v` is above `w` at the snap, with octant margin `δ`** (17.1′ for the form `z_v − z_w`). -/
def SnapAbove (x : Fin 7 → ℝ³) (d : Fin 3 → ℝ) (δ : ℝ) (v w : Fin 7) : Prop :=
  δ * (max 0 (cosCoefAB x d v w) * (‖x 0 - x 1‖ * ‖x 2 - x 1‖) +
      max 0 (cosCoefAC x d v w) * (‖x 0 - x 1‖ * ‖x 6 - x 1‖) +
      max 0 (cosCoefBC x d v w) * (‖x 2 - x 1‖ * ‖x 6 - x 1‖)) <
    snapDepth x d v - snapDepth x d w

variable {x : Fin 7 → ℝ³} (T : Type24 x)
include T

/-- **Lemma 17.1 at a general oblique view.** -/
theorem depth_sub_viewOf (d : Fin 3 → ℝ) (v w : Fin 7) :
    ⟪x v, viewOf x d⟫ - ⟪x w, viewOf x d⟫ =
      (snapDepth x d v - snapDepth x d w) + cosCoefAB x d v w * ⟪x 0 - x 1, x 2 - x 1⟫ +
        cosCoefAC x d v w * ⟪x 0 - x 1, x 6 - x 1⟫ +
        cosCoefBC x d v w * ⟪x 2 - x 1, x 6 - x 1⟫ := by
  rw [← inner_sub_left, T.diff_frame v w]
  simp only [viewOf]
  rw [inner_frame_diff, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]
  simp only [snapDepth, cosCoefAB, cosCoefAC, cosCoefBC]
  ring

/-- **Corollary 17.1′ for one pair, obtuse octant.** -/
theorem depth_lt_of_snapAbove {d : Fin 3 → ℝ} {δ : ℝ} {v w : Fin 7} (hn : ObtuseNear x δ)
    (h : SnapAbove x d δ v w) : ⟪x w, viewOf x d⟫ < ⟪x v, viewOf x d⟫ := by
  obtain ⟨n1, n2, n3, h1, h2, h3⟩ := hn
  have := radius_pos_octant n1 n2 n3 h1 h2 h3 h
  linarith [T.depth_sub_viewOf d v w]

omit T in
/-- **A certified rim at a view**, depth pattern left open (Theorem 7.3 with Lemma 16.27′, any
`k`): `isRupert_of_edgeView_uniform_robust`'s hypotheses without the depths. -/
def RimTestR (V : Finset ℝ³) (u : ℝ³) {k : ℕ} (p : ZMod k → ℝ³) : Prop :=
  ∃ M D W : Finset ℝ³, u ≠ 0 ∧ 3 ≤ k ∧ (∀ i, p i ∈ V) ∧ (∀ i, p i ∉ M) ∧
    (∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (p (i + 1) - p i) (p j - p i) u) ∧
    (∀ y ∈ V, y ∉ M → y ∉ D → (∀ j, y ≠ p j) → ∀ i, 0 < det3 (p (i + 1) - p i) (y - p i) u) ∧
    NoHDNAt W u ∧ (∀ i, p i ∈ W) ∧
    (∀ m ∈ M, ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = p i + s • (p (i + 1) - p i) + δ • u) ∧
    (∀ y ∈ D, ∃ i : ZMod k, ∃ h : ℝ, h ≠ 0 ∧ y = p i - h • u)

omit T in
theorem RimTestR.isRupert {V : Finset ℝ³} {u : ℝ³} {k : ℕ} [NeZero k] {p : ZMod k → ℝ³}
    (h : RimTestR V u p) (hz : IsRobustUnimodal fun i => ⟪p i, u⟫) : IsRupert V := by
  obtain ⟨M, D, W, hu, hk, hV, hM0, hc, hr, hnd, hW, hMm, hD⟩ := h
  exact isRupert_of_edgeView_uniform_robust V M D W u hu hk p hV hM0 hc hr hz hnd hW hMm hD

/-- **The same for a triangle rim**: one pair separated at the snap suffices. -/
theorem isRupert_type24_snap3 (d : Fin 3 → ℝ) {r : ZMod 3 → Fin 7}
    (hR : RimTestR (univ.image x) (viewOf x d) fun i => x (r i)) {δ : ℝ}
    (hn : ObtuseNear x δ) {i j : ZMod 3} (hij : SnapAbove x d δ (r i) (r j)) :
    IsRupert (univ.image x) := by
  refine hR.isRupert (isRobustUnimodal_three ?_)
  rintro ⟨h01, h12⟩
  have hall : ∀ y : ZMod 3, ⟪x (r y), viewOf x d⟫ = ⟪x (r 0), viewOf x d⟫ := by
    intro y
    have : y = 0 ∨ y = 1 ∨ y = 2 := by revert y; decide
    rcases this with rfl | rfl | rfl
    · rfl
    · exact h01.symm
    · rw [← h12, h01]
  have := T.depth_lt_of_snapAbove hn hij
  rw [hall i, hall j] at this
  exact lt_irrefl _ this

/-- **The same for a 4-corner rim, through `QuadTestR'`**: the two diagonals `{y, c}`, `{a, b}`
of the rim `(y, a, c, b)`. -/
theorem isRupert_type24_snap4 (d : Fin 3 → ℝ) {y a c b : Fin 7}
    (hQ : QuadTestR' (univ.image x) (viewOf x d) (x y) (x a) (x c) (x b)) {δ : ℝ}
    (hn : ObtuseNear x δ)
    (h1 : SnapAbove x d δ a y ∨ SnapAbove x d δ a c ∨ SnapAbove x d δ b y ∨
      SnapAbove x d δ b c)
    (h2 : SnapAbove x d δ y a ∨ SnapAbove x d δ y b ∨ SnapAbove x d δ c a ∨
      SnapAbove x d δ c b) :
    IsRupert (univ.image x) := by
  refine hQ.isRupert ?_
  unfold Fails4
  rintro (h | h)
  · rw [max_le_iff, le_min_iff, le_min_iff] at h
    obtain ⟨⟨h1', h2'⟩, h3', h4'⟩ := h
    rcases h2 with k | k | k | k
    · linarith [T.depth_lt_of_snapAbove hn k]
    · linarith [T.depth_lt_of_snapAbove hn k]
    · linarith [T.depth_lt_of_snapAbove hn k]
    · linarith [T.depth_lt_of_snapAbove hn k]
  · rw [max_le_iff, le_min_iff, le_min_iff] at h
    obtain ⟨⟨h1', h2'⟩, h3', h4'⟩ := h
    rcases h1 with k | k | k | k
    · linarith [T.depth_lt_of_snapAbove hn k]
    · linarith [T.depth_lt_of_snapAbove hn k]
    · linarith [T.depth_lt_of_snapAbove hn k]
    · linarith [T.depth_lt_of_snapAbove hn k]

end Type24

end Minimality
