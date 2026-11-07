module

public import SeptopertM18.ArcCap
public import SeptopertM18.CapLeaf

@[expose] public section

/-!
# Arc cap leaves for the 7-vertex solid's solution tree

As `SeptopertM18.CapLeaf` for the cap at the mirror normal. An arc cap leaf is a chart-0 box of
atlas poses and a projective view triangle: `arcLeafOk` checks, exactly over ℚ, that all corners
lie in one of the two *convex* pieces of the view polygon (`inHalf`, `inWedge`; their union is not
convex, so corners in the union do not suffice) and that the Cayley box lies in the ball of
radius 1/46. `arcLeaf_sound`: given `ArcHolds`, no pose of the box whose view lies over the
triangle is Rupert, whatever the offset. No cell hypothesis is needed.
-/

namespace SeptopertM18
open Noperts

open Noperts.Pipeline
open Noperts.Pipeline.ArcCap
open Noperts.Pipeline.KCap (rdot)

/-- The apex dots (v·E₁, v·E₂, v·X) of a rational view. -/
def dotE1 (P : Fin 3 → ℚ) : ℚ := -P 0 + 2 * P 1 + 2 * P 2
def dotE2 (P : Fin 3 → ℚ) : ℚ := 2 * P 0 - P 1 + 2 * P 2
def dotX (P : Fin 3 → ℚ) : ℚ := 2 * P 0 + 2 * P 1 - P 2

/-- A corner lies in the half square. -/
def inHalf (P : Fin 3 → ℚ) : Bool :=
  decide (0 < dotX P) && decide (|dotE1 P| ≤ dotX P / 8) && decide (|dotE2 P| ≤ dotX P / 8) &&
    decide (dotE1 P ≤ dotE2 P)

/-- A corner lies in the wedge. -/
def inWedge (P : Fin 3 → ℚ) : Bool :=
  decide (0 < dotX P) && decide (|dotE2 P| ≤ -dotE1 P / 8) && decide (-dotE1 P ≤ 13 / 32 * dotX P)

/-- The Cayley box lies in the ball of radius 1/46. -/
def arcBoxOk (iv : AtlasInterval ℚ) : Bool :=
  decide ((max |iv.min.x| |iv.max.x|) ^ 2 + (max |iv.min.y| |iv.max.y|) ^ 2 +
    (max |iv.min.z| |iv.max.z|) ^ 2 ≤ (1 / 46) ^ 2)

def arcLeafOk (iv : AtlasInterval ℚ) (T : AtlasProjectiveView.Triangle ℚ) : Bool :=
  arcBoxOk iv && ((List.finRange 3).all (fun c => inHalf (T c)) || (List.finRange 3).all (fun c => inWedge (T c)))

theorem arcBoxOk_sound {iv : AtlasInterval ℚ} (h : arcBoxOk iv = true) {p : AtlasPose ℝ} (hp : p ∈ iv.toReal) :
    rdot ![p.x, p.y, p.z] ![p.x, p.y, p.z] ≤ (1 / 46) ^ 2 := by
  simp only [arcBoxOk, decide_eq_true_eq] at h
  have hm := AtlasInterval.mem_toReal_iff.mp hp
  have hx := hm 2; have hy := hm 3; have hz := hm 4
  simp only [AtlasPose.get_two, AtlasPose.get_three, AtlasPose.get_four, Set.mem_Icc] at hx hy hz
  have h' := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at h'
  have sq : ∀ {lo hi t : ℝ}, lo ≤ t → t ≤ hi → t ^ 2 ≤ (max |lo| |hi|) ^ 2 := by
    intro lo hi t h1 h2
    rw [← sq_abs t]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_le_max_of_mem h1 h2) 2
  have a := sq hx.1 hx.2
  have b := sq hy.1 hy.2
  have c := sq hz.1 hz.2
  simp only [rdot, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  nlinarith

/-- A combination with weights wt of a function of the corners. -/
theorem comb_pos (κ : ℝ) (hκ : 0 < κ) (wt : Fin 3 → ℝ) (hw0 : ∀ c, 0 ≤ wt c) (hw1 : ∑ c, wt c = 1)
    (L : Fin 3 → ℝ) (hL : ∀ c, 0 < L c) : 0 < κ * ∑ c, wt c * L c := by
  apply mul_pos hκ
  have hmin : ∑ c, wt c * min (L 0) (min (L 1) (L 2)) ≤ ∑ c, wt c * L c := by
    apply Finset.sum_le_sum; intro c _
    apply mul_le_mul_of_nonneg_left _ (hw0 c)
    fin_cases c
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (min_le_left _ _)
    · exact le_trans (min_le_right _ _) (min_le_right _ _)
  rw [← Finset.sum_mul, hw1, one_mul] at hmin
  have : 0 < min (L 0) (min (L 1) (L 2)) := lt_min (hL 0) (lt_min (hL 1) (hL 2))
  linarith

theorem comb_le (κ : ℝ) (hκ : 0 < κ) (wt : Fin 3 → ℝ) (hw0 : ∀ c, 0 ≤ wt c) (f g : Fin 3 → ℝ)
    (h : ∀ c, f c ≤ g c) : κ * ∑ c, wt c * f c ≤ κ * ∑ c, wt c * g c := by
  apply mul_le_mul_of_nonneg_left _ hκ.le
  exact Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (h c) (hw0 c)

theorem comb_abs (κ : ℝ) (hκ : 0 < κ) (wt : Fin 3 → ℝ) (hw0 : ∀ c, 0 ≤ wt c) (f g : Fin 3 → ℝ)
    (h : ∀ c, |f c| ≤ g c) : |κ * ∑ c, wt c * f c| ≤ κ * ∑ c, wt c * g c := by
  rw [abs_le]
  constructor
  · have := comb_le κ hκ wt hw0 (fun c => -g c) f (fun c => by have := abs_le.mp (h c); linarith [this.1])
    simp only [mul_neg, Finset.sum_neg_distrib] at this
    linarith
  · exact comb_le κ hκ wt hw0 f g (fun c => le_trans (le_abs_self _) (h c))

theorem kval_E1 : KCap.PVec.kval apexFrame.E1 = ![-1, 2, 2] := by
  funext i; fin_cases i <;> simp [kval_q, apexFrame]

theorem kval_E2 : KCap.PVec.kval apexFrame.E2 = ![2, -1, 2] := by
  funext i; fin_cases i <;> simp [kval_q, apexFrame]

theorem kval_X : KCap.PVec.kval apexFrame.X = ![2, 2, -1] := by
  funext i; fin_cases i <;> simp [kval_q, apexFrame]

/-- A positive combination of corners, all in the half square or all in the wedge, lies in the
polygon. -/
theorem inArc_comb (κ : ℝ) (hκ : 0 < κ) (wt : Fin 3 → ℝ) (hw0 : ∀ c, 0 ≤ wt c) (hw1 : ∑ c, wt c = 1)
    (T : AtlasProjectiveView.Triangle ℚ)
    (h : (∀ c, inHalf (T c) = true) ∨ (∀ c, inWedge (T c) = true)) :
    InArc (fun k => κ * ∑ c, wt c * (T c k : ℝ)) := by
  set v : Fin 3 → ℝ := fun k => κ * ∑ c, wt c * (T c k : ℝ) with hv
  have e1 : rdot v (KCap.PVec.kval apexFrame.E1) = κ * ∑ c, wt c * (dotE1 (T c) : ℝ) := by
    rw [kval_E1]
    simp only [rdot, hv, dotE1, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    push_cast; ring
  have e2 : rdot v (KCap.PVec.kval apexFrame.E2) = κ * ∑ c, wt c * (dotE2 (T c) : ℝ) := by
    rw [kval_E2]
    simp only [rdot, hv, dotE2, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    push_cast; ring
  have ex : rdot v (KCap.PVec.kval apexFrame.X) = κ * ∑ c, wt c * (dotX (T c) : ℝ) := by
    rw [kval_X]
    simp only [rdot, hv, dotX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    push_cast; ring
  have ediv : ∀ (r : ℝ) (f : Fin 3 → ℝ), κ * ∑ c, wt c * (r * f c) = r * (κ * ∑ c, wt c * f c) := by
    intro r f
    simp only [Fin.sum_univ_three]; ring
  unfold InArc InPolygon
  rw [e1, e2, ex]
  rcases h with h | h
  · have hh : ∀ c, 0 < (dotX (T c) : ℝ) ∧ |(dotE1 (T c) : ℝ)| ≤ (dotX (T c) : ℝ) / 8 ∧
        |(dotE2 (T c) : ℝ)| ≤ (dotX (T c) : ℝ) / 8 ∧ (dotE1 (T c) : ℝ) ≤ (dotE2 (T c) : ℝ) := by
      intro c
      have := h c
      simp only [inHalf, Bool.and_eq_true, decide_eq_true_eq] at this
      obtain ⟨⟨⟨a, b⟩, d⟩, e⟩ := this
      refine ⟨by exact_mod_cast a, ?_, ?_, by exact_mod_cast e⟩
      · have := (Rat.cast_le (K := ℝ)).mpr b; push_cast at this; exact this
      · have := (Rat.cast_le (K := ℝ)).mpr d; push_cast at this; exact this
    refine ⟨comb_pos κ hκ wt hw0 hw1 _ (fun c => (hh c).1), Or.inl ⟨?_, ?_, ?_⟩⟩
    · have := comb_abs κ hκ wt hw0 (fun c => (dotE1 (T c) : ℝ)) (fun c => 1 / 8 * (dotX (T c) : ℝ))
        (fun c => by have := (hh c).2.1; linarith)
      rw [ediv] at this; linarith
    · have := comb_abs κ hκ wt hw0 (fun c => (dotE2 (T c) : ℝ)) (fun c => 1 / 8 * (dotX (T c) : ℝ))
        (fun c => by have := (hh c).2.2.1; linarith)
      rw [ediv] at this; linarith
    · exact comb_le κ hκ wt hw0 _ _ (fun c => (hh c).2.2.2)
  · have hh : ∀ c, 0 < (dotX (T c) : ℝ) ∧ |(dotE2 (T c) : ℝ)| ≤ -(dotE1 (T c) : ℝ) / 8 ∧
        -(dotE1 (T c) : ℝ) ≤ 13 / 32 * (dotX (T c) : ℝ) := by
      intro c
      have := h c
      simp only [inWedge, Bool.and_eq_true, decide_eq_true_eq] at this
      obtain ⟨⟨a, b⟩, d⟩ := this
      refine ⟨by exact_mod_cast a, ?_, ?_⟩
      · have := (Rat.cast_le (K := ℝ)).mpr b; push_cast at this; exact this
      · have := (Rat.cast_le (K := ℝ)).mpr d; push_cast at this; exact this
    refine ⟨comb_pos κ hκ wt hw0 hw1 _ (fun c => (hh c).1), Or.inr ⟨?_, ?_⟩⟩
    · have := comb_abs κ hκ wt hw0 (fun c => (dotE2 (T c) : ℝ)) (fun c => -1 / 8 * (dotE1 (T c) : ℝ))
        (fun c => by have := (hh c).2.1; linarith)
      rw [ediv] at this; linarith
    · have := comb_le κ hκ wt hw0 (fun c => -1 * (dotE1 (T c) : ℝ)) (fun c => 13 / 32 * (dotX (T c) : ℝ))
        (fun c => by have := (hh c).2.2; linarith)
      rw [ediv, ediv] at this; linarith

/-- **Arc cap leaves are sound**: given the arc cap, no pose of a chart-0 box in the ball of radius
1/46 whose view lies over a triangle inside a piece of the polygon (at a positive view scale) is
Rupert, whatever the offset. -/
theorem arcLeaf_sound (harc : ArcHolds) (iv : AtlasInterval ℚ) (root : Fin 8)
    (T : AtlasProjectiveView.Triangle ℚ) (h : arcLeafOk iv T = true) (p : AtlasPose ℝ) (hp : p ∈ iv.toReal)
    (hscale : 0 < AtlasProjectiveView.viewScale root p)
    (htri : Noperts.Atlas.ProjectiveView.InTriangle (Noperts.Atlas.ProjectiveView.toReal T)
      (AtlasProjectiveView.normalizedView root p)) (offset : ℝ²) :
    ¬ RupertPose (p.matrixPoseWithOffset 0 offset) solid := by
  simp only [arcLeafOk, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, List.mem_finRange,
    true_implies] at h
  obtain ⟨hbox, hcorners⟩ := h
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
  have hR : pose.relativeRotation = cayleyMatrix p.x p.y p.z := by
    rw [AtlasPose.matrixPoseWithOffset_relativeRotation, CayleyAtlas.chartMatrix_zero, Matrix.one_mul]
  refine harc pose ?_ ![p.x, p.y, p.z] ?_ (arcBoxOk_sound hbox hp)
  · rw [hview]
    exact inArc_comb κ hscale wt hw0 hw1 T hcorners
  · rw [hR]; rfl

end SeptopertM18

end
