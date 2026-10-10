module

public import Noperthedron.Nopert7.Caps
public import Noperthedron.Nopert7.Reduce
public import Noperthedron.PentagonalHexecontahedron.AtlasProjectiveView

@[expose] public section

/-!
# Cap leaves for the 7-vertex solid's solution tree

A cap leaf (after DH's `CapRow.capLeaf_sound`) is a chart-0 box of atlas poses
and a projective view triangle: `capLeafOk` checks, exactly over ℚ, that every
corner of the triangle lies in the cap's view cone (`InCapView`) and that the
Cayley box lies in the cap's weighted box (`InCapCayley`). `capLeaf_sound`:
given a checked cap certificate, no pose of the box whose view lies over the
triangle and whose relative rotation lies in the C3v cell is Rupert, whatever
the offset.
-/

namespace Noperthedron.Nopert7

open Noperthedron.PentagonalHexecontahedron
open Noperthedron.PentagonalHexecontahedron.Cap
open Noperthedron.PentagonalHexecontahedron.PVec
open scoped Matrix

/-- A triangle corner lies in the cap's view cone. -/
def cornerOk (P : Fin 3 → ℚ) : Bool :=
  decide (0 < P 0 - P 2) && decide (2 * |P 1| ≤ capMu0 * (P 0 - P 2)) &&
    decide (|P 0 + P 2| ≤ capMu0 * (P 0 - P 2))

/-- The Cayley box lies in the cap's weighted box. -/
def boxOk (iv : AtlasInterval ℚ) : Bool :=
  decide (max |iv.min.y| |iv.max.y| ≤ 2 * capMu0) &&
    decide (max |iv.min.x + iv.min.z| |iv.max.x + iv.max.z| ≤ 4 * capMu0) &&
    decide (max |iv.min.x - iv.max.z| |iv.max.x - iv.min.z| ≤ 4 * capMu0 ^ 2)

def capLeafOk (iv : AtlasInterval ℚ) (T : AtlasProjectiveView.Triangle ℚ) : Bool :=
  boxOk iv && (List.finRange 3).all fun c => cornerOk (T c)

theorem abs_le_max_of_mem {lo hi t : ℝ} (h1 : lo ≤ t) (h2 : t ≤ hi) : |t| ≤ max |lo| |hi| := by
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h]; exact le_trans (le_trans h2 (le_abs_self hi)) (le_max_right _ _)
  · rw [abs_of_nonpos h]; exact le_trans (le_trans (by linarith) (neg_le_abs lo)) (le_max_left _ _)

theorem boxOk_sound {iv : AtlasInterval ℚ} (h : boxOk iv = true) {p : AtlasPose ℝ} (hp : p ∈ iv.toReal) :
    InCapCayley ![p.x, p.y, p.z] := by
  simp only [boxOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hy, hxz⟩, hxz'⟩ := h
  have hm := AtlasInterval.mem_toReal_iff.mp hp
  have hx := hm 2; have hy' := hm 3; have hz := hm 4
  simp only [AtlasPose.get_two, AtlasPose.get_three, AtlasPose.get_four, Set.mem_Icc] at hx hy' hz
  have cast : ∀ {a b c : ℚ}, max |a| |b| ≤ c → max |(a : ℝ)| |(b : ℝ)| ≤ (c : ℝ) := by
    intro a b c h
    have : ((max |a| |b| : ℚ) : ℝ) ≤ c := by exact_mod_cast h
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    have := cast hy
    push_cast at this
    exact le_trans (abs_le_max_of_mem hy'.1 hy'.2) this
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    have := cast hxz
    push_cast at this
    exact le_trans (abs_le_max_of_mem (by linarith) (by linarith)) this
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    have := cast hxz'
    push_cast at this
    exact le_trans (abs_le_max_of_mem (by linarith) (by linarith)) this

theorem cornerOk_sound {P : Fin 3 → ℚ} (h : cornerOk P = true) :
    InCapView (fun i => (P i : ℝ)) := by
  simp only [cornerOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · show (0 : ℝ) < (P 0 : ℝ) - P 2
    exact_mod_cast h0
  · have : ((2 * |P 1| : ℚ) : ℝ) ≤ ((capMu0 * (P 0 - P 2) : ℚ) : ℝ) := by exact_mod_cast h1
    push_cast at this; exact this
  · have : ((|P 0 + P 2| : ℚ) : ℝ) ≤ ((capMu0 * (P 0 - P 2) : ℚ) : ℝ) := by exact_mod_cast h2
    push_cast at this; exact this

/-- The cap's view cone is a convex cone: positive combinations of its points stay in it. -/
theorem inCapView_comb (κ : ℝ) (hκ : 0 < κ) (wt : Fin 3 → ℝ) (hw0 : ∀ c, 0 ≤ wt c) (hw1 : ∑ c, wt c = 1)
    (P : Fin 3 → Fin 3 → ℝ) (hP : ∀ c, InCapView (P c)) :
    InCapView (fun k => κ * ∑ c, wt c * P c k) := by
  have hμ : (0 : ℝ) ≤ capMu0 := by norm_num [capMu0]
  set L : Fin 3 → ℝ := fun c => P c 0 - P c 2
  have hL : ∀ c, 0 < L c := fun c => (hP c).1
  have hsum : (fun k => κ * ∑ c, wt c * P c k) 0 - (fun k => κ * ∑ c, wt c * P c k) 2 = κ * ∑ c, wt c * L c := by
    simp only [L, Fin.sum_univ_three]; ring
  -- Σ wt L > 0.
  have hpos : 0 < ∑ c, wt c * L c := by
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
  have hcone : ∀ (f : Fin 3 → ℝ) (a : ℝ), 0 ≤ a → (∀ c, a * |f c| ≤ capMu0 * L c) →
      a * |κ * ∑ c, wt c * f c| ≤ capMu0 * (κ * ∑ c, wt c * L c) := by
    intro f a ha hf
    rw [abs_mul, abs_of_pos hκ]
    have h1 : |∑ c, wt c * f c| ≤ ∑ c, wt c * |f c| := by
      calc |∑ c, wt c * f c| ≤ ∑ c, |wt c * f c| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ c, wt c * |f c| := by
            apply Finset.sum_congr rfl; intro c _; rw [abs_mul, abs_of_nonneg (hw0 c)]
    have h2 : a * ∑ c, wt c * |f c| ≤ capMu0 * ∑ c, wt c * L c := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_le_sum; intro c _
      have := mul_le_mul_of_nonneg_left (hf c) (hw0 c)
      nlinarith
    have h3 : a * |∑ c, wt c * f c| ≤ capMu0 * ∑ c, wt c * L c :=
      le_trans (mul_le_mul_of_nonneg_left h1 ha) h2
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hsum]; exact mul_pos hκ hpos
  · rw [hsum]
    have := hcone (fun c => P c 1) 2 (by norm_num) (fun c => (hP c).2.1)
    simpa only [mul_comm] using this
  · rw [hsum]
    have := hcone (fun c => P c 0 + P c 2) 1 (by norm_num) (fun c => by simpa using (hP c).2.2)
    simp only [one_mul] at this
    have e : (fun k => κ * ∑ c, wt c * P c k) 0 + (fun k => κ * ∑ c, wt c * P c k) 2 =
        κ * ∑ c, wt c * (P c 0 + P c 2) := by
      simp only [Fin.sum_univ_three]; ring
    rw [e]; exact this

/-- **Cap leaves are sound**: with a checked cap certificate, no pose of a chart-0 box in the cap's
Cayley box whose view lies over a triangle inside the cap cone (at a positive view scale) and whose
relative rotation lies in the C3v cell is Rupert, whatever the offset. -/
theorem capLeaf_sound (c : CapCert) (hc : certOk c = true) (iv : AtlasInterval ℚ) (root : Fin 8)
    (T : AtlasProjectiveView.Triangle ℚ) (h : capLeafOk iv T = true) (p : AtlasPose ℝ) (hp : p ∈ iv.toReal)
    (hcell : InC3vCell (fun k => rotRM_mat p.θ p.φ 0 2 k) (CayleyAtlas.chartMatrix 0 * cayleyMatrix p.x p.y p.z))
    (hscale : 0 < AtlasProjectiveView.viewScale root p)
    (htri : Noperthedron.Atlas.ProjectiveView.InTriangle (Noperthedron.Atlas.ProjectiveView.toReal T)
      (AtlasProjectiveView.normalizedView root p)) (offset : ℝ²) :
    ¬ RupertPose (p.matrixPoseWithOffset 0 offset) solid := by
  simp only [capLeafOk, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at h
  obtain ⟨hbox, hcorners⟩ := h
  set pose := p.matrixPoseWithOffset 0 offset
  obtain ⟨wt, hw0, hw1, hwT⟩ := htri
  set κ := AtlasProjectiveView.viewScale root p
  have hview : pose.view = fun k => κ * ∑ c, wt c * (T c k : ℝ) := by
    funext k
    have hk := congrFun hwT k
    simp only [AtlasProjectiveView.normalizedView, Noperthedron.Atlas.ProjectiveView.affinePoint,
      Noperthedron.Atlas.ProjectiveView.toReal] at hk
    simp only [pose, MatrixPose.view, AtlasPose.matrixPoseWithOffset_outerRot_val]
    have hv : rotRM_mat p.θ p.φ 0 2 k = AtlasEdgeCertificate.viewVector p k := by
      obtain ⟨e0, e1, e2⟩ := rotRM_mat_row2_zero p.θ p.φ
      fin_cases k <;> simp [AtlasEdgeCertificate.viewVector, e0, e1, e2]
    rw [hv, ← mul_div_cancel₀ (AtlasEdgeCertificate.viewVector p k) hscale.ne', hk]
  have hR : pose.relativeRotation = cayleyMatrix p.x p.y p.z := by
    rw [AtlasPose.matrixPoseWithOffset_relativeRotation, CayleyAtlas.chartMatrix_zero, Matrix.one_mul]
  refine cap_not_rupert_of_cell c hc pose ?_ ![p.x, p.y, p.z] ?_ (boxOk_sound hbox hp) ?_
  · rw [hview]
    exact inCapView_comb κ hscale wt hw0 hw1 (fun c k => (T c k : ℝ)) (fun c => cornerOk_sound (hcorners c))
  · rw [hR]; rfl
  · rw [hR]
    have hv : pose.view = fun k => rotRM_mat p.θ p.φ 0 2 k := rfl
    rw [hv, show cayleyMatrix p.x p.y p.z = CayleyAtlas.chartMatrix 0 * cayleyMatrix p.x p.y p.z by
      rw [CayleyAtlas.chartMatrix_zero, Matrix.one_mul]]
    exact hcell

end Noperthedron.Nopert7
