module

public import M12.ArcLeaf
public import M12.AxisCap

@[expose] public section

/-!
# Axis cap and P cap leaves for M12's solution tree

As `M12.ArcLeaf`, for the other two caps that M12's tubes and 5D search leave to special caps
(`search/h12/arc-cap.txt`, each with Cayley rotation radius 1/46 in chart 0):

* cap 2, the axis region `InAxis` (`M12.axis_not_rupert`, claim `AxisHolds`);
* cap 3, the P strip around (2, 1, 0): the convex cone `InP` of five half-spaces (the `piece` line
  of cap 3), whose claim `PCapClaim` is a hypothesis (no certificate yet).

A leaf is a chart-0 box in the ball of radius 1/46 and a view triangle with all corners in the
region. The regions here are convex cones, given by a first strict and further non-strict
half-spaces; `axisLeafOk` tests the (weaker, hence implied by the piece of `arc-cap.txt`) cone
`axisCone` that implies `InAxis`.
-/

namespace M12
open Noperts

open Noperts.Pipeline
open Noperts.Pipeline.ArcCap
open Noperts.Pipeline.KCap (rdot)

/-- A rational half-space normal applied to a rational point. -/
def dotQ (n P : Fin 3 → ℚ) : ℚ := n 0 * P 0 + n 1 * P 1 + n 2 * P 2

/-- A rational half-space normal applied to a real point. -/
def dotR (n : Fin 3 → ℚ) (v : Fin 3 → ℝ) : ℝ := (n 0 : ℝ) * v 0 + (n 1 : ℝ) * v 1 + (n 2 : ℝ) * v 2

/-- The cone n₀·v > 0, nᵢ·v ≥ 0. -/
def Cone (n0 : Fin 3 → ℚ) (ns : List (Fin 3 → ℚ)) (v : Fin 3 → ℝ) : Prop :=
  0 < dotR n0 v ∧ ∀ n ∈ ns, 0 ≤ dotR n v

/-- A rational point lies in the cone. -/
def coneB (n0 : Fin 3 → ℚ) (ns : List (Fin 3 → ℚ)) (P : Fin 3 → ℚ) : Bool :=
  decide (0 < dotQ n0 P) && ns.all fun n => decide (0 ≤ dotQ n P)

theorem dotR_comb (n : Fin 3 → ℚ) (κ : ℝ) (wt : Fin 3 → ℝ) (T : AtlasProjectiveView.Triangle ℚ) :
    dotR n (fun k => κ * ∑ c, wt c * (T c k : ℝ)) = κ * ∑ c, wt c * (dotQ n (T c) : ℝ) := by
  simp only [dotR, dotQ, Fin.sum_univ_three]; push_cast; ring

/-- A positive combination of corners, all in a cone, lies in the cone. -/
theorem cone_comb (n0 : Fin 3 → ℚ) (ns : List (Fin 3 → ℚ)) (κ : ℝ) (hκ : 0 < κ) (wt : Fin 3 → ℝ)
    (hw0 : ∀ c, 0 ≤ wt c) (hw1 : ∑ c, wt c = 1) (T : AtlasProjectiveView.Triangle ℚ)
    (h : ∀ c, coneB n0 ns (T c) = true) :
    Cone n0 ns (fun k => κ * ∑ c, wt c * (T c k : ℝ)) := by
  have hh : ∀ c, 0 < dotQ n0 (T c) ∧ ∀ n ∈ ns, 0 ≤ dotQ n (T c) := by
    intro c
    have := h c
    simp only [coneB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at this
    exact this
  refine ⟨?_, ?_⟩
  · rw [dotR_comb]
    exact comb_pos κ hκ wt hw0 hw1 _ (fun c => by exact_mod_cast (hh c).1)
  · intro n hn
    rw [dotR_comb]
    apply mul_nonneg hκ.le
    exact Finset.sum_nonneg fun c _ => mul_nonneg (hw0 c) (by exact_mod_cast (hh c).2 n hn)

/-- **Leaves over a region are sound**: given a claim for a region `R` of views that holds at all
positive combinations of the corners of the triangle `T`, no pose of a chart-0 box in the ball of
radius 1/46 whose view lies over `T` is Rupert, whatever the offset. -/
theorem region_leaf_sound {R : (Fin 3 → ℝ) → Prop}
    (hclaim : ∀ (p : MatrixPose), R p.view → ∀ w : Fin 3 → ℝ,
      p.relativeRotation = cayleyMatrix (w 0) (w 1) (w 2) → rdot w w ≤ (1 / 46) ^ 2 → ¬ RupertPose p solid)
    (iv : AtlasInterval ℚ) (root : Fin 8) (T : AtlasProjectiveView.Triangle ℚ)
    (hbox : arcBoxOk iv = true)
    (hR : ∀ (κ : ℝ), 0 < κ → ∀ (wt : Fin 3 → ℝ), (∀ c, 0 ≤ wt c) → ∑ c, wt c = 1 →
      R (fun k => κ * ∑ c, wt c * (T c k : ℝ)))
    (p : AtlasPose ℝ) (hp : p ∈ iv.toReal)
    (hscale : 0 < AtlasProjectiveView.viewScale root p)
    (htri : Noperts.Atlas.ProjectiveView.InTriangle (Noperts.Atlas.ProjectiveView.toReal T)
      (AtlasProjectiveView.normalizedView root p)) (offset : ℝ²) :
    ¬ RupertPose (p.matrixPoseWithOffset 0 offset) solid := by
  set pose := p.matrixPoseWithOffset 0 offset
  obtain ⟨wt, hw0, hw1, hwT⟩ := htri
  set κ := AtlasProjectiveView.viewScale root p
  have hview : pose.view = fun k => κ * ∑ c, wt c * (T c k : ℝ) := by
    funext k
    have hk := congrFun hwT k
    simp only [AtlasProjectiveView.normalizedView, Noperts.Atlas.ProjectiveView.affinePoint,
      Noperts.Atlas.ProjectiveView.toReal] at hk
    simp only [pose, MatrixPose.view, AtlasPose.matrixPoseWithOffset_outerRot_val]
    have hv : rotRM_mat p.θ p.φ 0 2 k = AtlasEdgeCertificate.viewVector p k := by
      obtain ⟨e0, e1, e2⟩ := rotRM_mat_row2_zero p.θ p.φ
      fin_cases k <;> simp [AtlasEdgeCertificate.viewVector, e0, e1, e2]
    rw [hv, ← mul_div_cancel₀ (AtlasEdgeCertificate.viewVector p k) hscale.ne', hk]
  have hRot : pose.relativeRotation = cayleyMatrix p.x p.y p.z := by
    rw [AtlasPose.matrixPoseWithOffset_relativeRotation, CayleyAtlas.chartMatrix_zero, Matrix.one_mul]
  refine hclaim pose ?_ ![p.x, p.y, p.z] ?_ (arcBoxOk_sound hbox hp)
  · rw [hview]
    exact hR κ hscale wt hw0 hw1
  · rw [hRot]; rfl

/-! ### Cap 2: the axis region -/

/-- A cone inside `InAxis`: S > 0, S ± 24 (v₀ − v₁) ≥ 0, S ± 16 (v₀ + v₁ − 2 v₂) ≥ 0, S = v₀+v₁+v₂. -/
def axisN0 : Fin 3 → ℚ := ![1, 1, 1]
def axisNs : List (Fin 3 → ℚ) :=
  [![-23, 25, 1], ![25, -23, 1], ![-15, -15, 33], ![17, 17, -31]]

theorem inAxis_of_cone {v : Fin 3 → ℝ} (h : Cone axisN0 axisNs v) : InAxis v := by
  obtain ⟨h0, h1⟩ := h
  have c := h1 (![-15, -15, 33]) (by simp [axisNs])
  have d := h1 (![17, 17, -31]) (by simp [axisNs])
  have a := h1 (![-23, 25, 1]) (by simp [axisNs])
  have b := h1 (![25, -23, 1]) (by simp [axisNs])
  simp only [dotR, axisN0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Rat.cast_one,
    Rat.cast_neg, Rat.cast_ofNat] at h0 a b c d
  refine ⟨by linarith, ?_, ?_⟩
  · rw [← abs_of_pos (show (0 : ℝ) < 24 by norm_num), ← abs_mul]
    rw [abs_le]; constructor <;> linarith
  · rw [← abs_of_pos (show (0 : ℝ) < 16 by norm_num), ← abs_mul]
    rw [abs_le]; constructor <;> linarith

def axisLeafOk (iv : AtlasInterval ℚ) (T : AtlasProjectiveView.Triangle ℚ) : Bool :=
  arcBoxOk iv && (List.finRange 3).all (fun c => coneB axisN0 axisNs (T c))

theorem axisLeaf_sound (haxis : AxisHolds) (iv : AtlasInterval ℚ) (root : Fin 8)
    (T : AtlasProjectiveView.Triangle ℚ) (h : axisLeafOk iv T = true) (p : AtlasPose ℝ)
    (hp : p ∈ iv.toReal) (hscale : 0 < AtlasProjectiveView.viewScale root p)
    (htri : Noperts.Atlas.ProjectiveView.InTriangle (Noperts.Atlas.ProjectiveView.toReal T)
      (AtlasProjectiveView.normalizedView root p)) (offset : ℝ²) :
    ¬ RupertPose (p.matrixPoseWithOffset 0 offset) solid := by
  simp only [axisLeafOk, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at h
  obtain ⟨hbox, hcorners⟩ := h
  exact region_leaf_sound haxis iv root T hbox
    (fun κ hκ wt hw0 hw1 => inAxis_of_cone (cone_comb _ _ κ hκ wt hw0 hw1 T hcorners)) p hp hscale
    htri offset

/-! ### Cap 3: the P strip -/

/-- The piece of cap 3 in `search/h12/arc-cap.txt`: the strip around (2, 1, 0). -/
def pN0 : Fin 3 → ℚ := ![2, 1, 0]
def pNs : List (Fin 3 → ℚ) :=
  [![-15 / 16, 65 / 32, -1], ![17 / 16, -63 / 32, 1], ![-9 / 10, 41 / 20, 5], ![7 / 4, -13 / 8, -5]]

/-- The views of cap 3. -/
abbrev InP (v : Fin 3 → ℝ) : Prop := Cone pN0 pNs v

/-- **The claim of cap 3** (not yet certified): no Rupert pose, whatever the offset, has a view in
the strip `InP` around (2, 1, 0) and a relative rotation the Cayley rotation of a vector of length
at most 1/46. -/
def PCapClaim : Prop :=
  ∀ (p : MatrixPose), InP p.view → ∀ w : Fin 3 → ℝ,
    p.relativeRotation = cayleyMatrix (w 0) (w 1) (w 2) → rdot w w ≤ (1 / 46) ^ 2 → ¬ RupertPose p solid

def pLeafOk (iv : AtlasInterval ℚ) (T : AtlasProjectiveView.Triangle ℚ) : Bool :=
  arcBoxOk iv && (List.finRange 3).all (fun c => coneB pN0 pNs (T c))

theorem pLeaf_sound (hp3 : PCapClaim) (iv : AtlasInterval ℚ) (root : Fin 8)
    (T : AtlasProjectiveView.Triangle ℚ) (h : pLeafOk iv T = true) (p : AtlasPose ℝ)
    (hp : p ∈ iv.toReal) (hscale : 0 < AtlasProjectiveView.viewScale root p)
    (htri : Noperts.Atlas.ProjectiveView.InTriangle (Noperts.Atlas.ProjectiveView.toReal T)
      (AtlasProjectiveView.normalizedView root p)) (offset : ℝ²) :
    ¬ RupertPose (p.matrixPoseWithOffset 0 offset) solid := by
  simp only [pLeafOk, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at h
  obtain ⟨hbox, hcorners⟩ := h
  exact region_leaf_sound hp3 iv root T hbox
    (fun κ hκ wt hw0 hw1 => cone_comb _ _ κ hκ wt hw0 hw1 T hcorners) p hp hscale htri offset

end M12

end
