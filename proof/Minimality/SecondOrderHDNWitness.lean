module

public import Minimality.SecondOrderHDNView

@[expose] public section

/-!
# Non-vacuity of Theorem H2 (plan specpos A2/A3b)

An 11-point rational shape `hdnV` (8 rim corners and 3 hidden points; `h2check.cc` mode 0) with a level double
normal between `(1, 0, 0)` and `(-1, 0, 0)` and tilt axis `w = (1, 3/10)`.  `levelHDN_witness` checks every
hypothesis of `isRupert_of_levelHDN` except `hpoly`; `levelHDN_witness_isRupert` proves `IsRupert hdnV` outright
through `isRupert_of_levelHDN_rim`.
-/
/-! Non-vacuity witness for `isRupert_of_levelHDN`: the 8-corner rim of `h2check.cc` (mode 0), all coordinates
rational, w = (1, 3/10).  Every hypothesis except `hpoly` is verified. -/
noncomputable section
namespace Minimality
open scoped RealInnerProductSpace

def hdnX : Fin 11 → ℝ := ![1, 7/10, 0, -7/10, -1, -7/10, 0, 7/10, 0, 1/5, -3/10]
def hdnY : Fin 11 → ℝ := ![0, 7/10, 1, 7/10, 0, -7/10, -1, -7/10, 0, 1/10, 1/5]
def hdnZ : Fin 11 → ℝ := ![0, 3/10, 4/5, 2/5, 0, -1/2, -1/5, -3/5, 3/10, -2/5, 0]
noncomputable def hdnPt (i : Fin 11) : ℝ³ := !₂[hdnX i, hdnY i, hdnZ i]
noncomputable def hdnV : Finset ℝ³ := Finset.image hdnPt Finset.univ
def hdnNx : Fin 8 → ℝ := ![7/10, 3/10, -3/10, -7/10, -7/10, -3/10, 3/10, 7/10]
def hdnNy : Fin 8 → ℝ := ![3/10, 7/10, 7/10, 3/10, -3/10, -7/10, -7/10, -3/10]
noncomputable def hdnN (e : Fin 8) : ℝ² := !₂[hdnNx e, hdnNy e]
noncomputable def hdnW : ℝ² := !₂[1, 3/10]

theorem levelHDN_witness :
    (∀ v ∈ hdnV, ∀ e, ⟪hdnN e, proj_xy v⟫ ≤ 7/10) ∧ hdnPt 0 ∈ hdnV ∧ hdnPt 4 ∈ hdnV ∧
    (hdnPt 0) 2 = (hdnPt 4) 2 ∧
    cross2 (proj_xy (hdnPt 0) - proj_xy (hdnPt 4)) hdnW ≠ 0 ∧
    (∀ e, ⟪hdnN e, proj_xy (hdnPt 0)⟫ = 7/10 → ⟪hdnN e, proj_xy (hdnPt 4)⟫ < 7/10) ∧
    (∀ e, ⟪hdnN e, proj_xy (hdnPt 4)⟫ = 7/10 → ⟪hdnN e, proj_xy (hdnPt 0)⟫ < 7/10) ∧
    (∀ v ∈ hdnV, v ≠ hdnPt 0 → v ≠ hdnPt 4 → ∀ e, ⟪hdnN e, proj_xy v⟫ = 7/10 →
      (v 2 - (hdnPt 0) 2) * cross2 (hdnN e) hdnW < 0) := by
  have ev : ∀ i e, ⟪hdnN e, proj_xy (hdnPt i)⟫ = hdnNx e * hdnX i + hdnNy e * hdnY i := by
    intro i e
    simp [hdnN, hdnPt, proj_xy, PiLp.inner_apply, Fin.sum_univ_two]; ring
  have cr : ∀ e, cross2 (hdnN e) hdnW = hdnNx e * (3/10) - hdnNy e := by
    intro e; simp [hdnN, hdnW, cross2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv e
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
    rw [ev]; fin_cases i <;> fin_cases e <;> norm_num [hdnNx, hdnNy, hdnX, hdnY]
  · exact Finset.mem_image.2 ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.2 ⟨4, Finset.mem_univ _, rfl⟩
  · simp [hdnPt, hdnZ]
  · simp [hdnPt, hdnW, proj_xy, cross2, hdnX, hdnY]
  · intro e; rw [ev, ev]; fin_cases e <;> norm_num [hdnNx, hdnNy, hdnX, hdnY]
  · intro e; rw [ev, ev]; fin_cases e <;> norm_num [hdnNx, hdnNy, hdnX, hdnY]
  · intro v hv a b e he
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
    rw [ev] at he
    have hz : (hdnPt i) 2 = hdnZ i := by simp [hdnPt]
    have hz0 : (hdnPt 0) 2 = 0 := by simp [hdnPt, hdnZ]
    rw [hz, hz0, cr]
    fin_cases i <;> fin_cases e <;> first
      | (exfalso; apply a; rfl)
      | (exfalso; apply b; rfl)
      | (exfalso; norm_num [hdnNx, hdnNy, hdnX, hdnY] at he; done)
      | norm_num [hdnNx, hdnNy, hdnZ]

/-- All hypotheses of `isRupert_of_levelHDN` hold (except possibly `hpoly`), so the theorem is not vacuous. -/
theorem levelHDN_witness_rupert (hpoly : {y : ℝ² | ∀ e, ⟪hdnN e, y⟫ < 7/10} ⊆
    proj_xy '' convexHull ℝ (hdnV : Set ℝ³)) : IsRupert hdnV := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := levelHDN_witness
  exact isRupert_of_levelHDN hdnV hdnN (fun _ => 7/10) hpoly h1 _ _ h2 h3 h4 hdnW h5 h6 h7 h8
end Minimality
end

noncomputable section
namespace Minimality
open scoped RealInnerProductSpace

/-- The 8 rim corners of the witness, indexed by `ZMod 8`. -/
def levelHDNv_x (t : ZMod 8) : ℝ³ := hdnPt (Fin.castLE (by norm_num) (show Fin 8 from t))

def levelHDNv_X (n : ℕ) : ℝ := [(1:ℝ), 7/10, 0, -7/10, -1, -7/10, 0, 7/10].getD n 0
def levelHDNv_Y (n : ℕ) : ℝ := [(0:ℝ), 7/10, 1, 7/10, 0, -7/10, -1, -7/10].getD n 0
def levelHDNv_Z (n : ℕ) : ℝ := [(0:ℝ), 3/10, 4/5, 2/5, 0, -1/2, -1/5, -3/5].getD n 0

lemma levelHDNv_x_eq (t : ZMod 8) :
    levelHDNv_x t = !₂[levelHDNv_X t.val, levelHDNv_Y t.val, levelHDNv_Z t.val] := by
  fin_cases t <;> ext a <;> fin_cases a <;>
    simp [levelHDNv_x, hdnPt, hdnX, hdnY, hdnZ, levelHDNv_X, levelHDNv_Y, levelHDNv_Z, ZMod.val, Fin.castLE]

lemma levelHDNv_px (t : ZMod 8) :
    proj_xy (levelHDNv_x t) = !₂[levelHDNv_X t.val, levelHDNv_Y t.val] := by
  rw [levelHDNv_x_eq]; ext a; fin_cases a <;> simp [proj_xy]

lemma levelHDNv_val_succ (i : ZMod 8) : (i + 1).val = (i.val + 1) % 8 := by
  fin_cases i <;> rfl

lemma levelHDNv_ccw : ∀ i j : ZMod 8, j ≠ i → j ≠ i + 1 →
      0 < cross2 (proj_xy (levelHDNv_x (i + 1)) - proj_xy (levelHDNv_x i)) (proj_xy (levelHDNv_x j) - proj_xy (levelHDNv_x i)) := by
  intro i j h1 h2
  rw [levelHDNv_px, levelHDNv_px, levelHDNv_px, levelHDNv_val_succ]
  fin_cases i <;> fin_cases j <;> first | (exfalso; apply h1; rfl) | (exfalso; apply h2; rfl) | skip
  all_goals
    simp [cross2, levelHDNv_X, levelHDNv_Y, ZMod.val]
    try norm_num

/-- Inner product with the rim edge normal, in coordinates. -/
lemma levelHDNv_pc0 (t : ZMod 8) : (proj_xy (levelHDNv_x t)) 0 = levelHDNv_X t.val := by
  rw [levelHDNv_px]; simp
lemma levelHDNv_pc1 (t : ZMod 8) : (proj_xy (levelHDNv_x t)) 1 = levelHDNv_Y t.val := by
  rw [levelHDNv_px]; simp
lemma levelHDNv_v0 : (0 : ZMod 8).val = 0 := rfl
lemma levelHDNv_v4 : (4 : ZMod 8).val = 4 := rfl

lemma levelHDNv_inner (e : ZMod 8) (y : ℝ²) :
    ⟪levelHDNv_n (fun t => proj_xy (levelHDNv_x t)) e, y⟫ =
      (levelHDNv_Y ((e.val + 1) % 8) - levelHDNv_Y e.val) * y 0 -
        (levelHDNv_X ((e.val + 1) % 8) - levelHDNv_X e.val) * y 1 := by
  simp [levelHDNv_n, rot90, PiLp.inner_apply, Fin.sum_univ_two, levelHDNv_px, levelHDNv_val_succ]
  ring

lemma levelHDNv_hh (e : ZMod 8) :
    levelHDNv_h (fun t => proj_xy (levelHDNv_x t)) e =
      (levelHDNv_Y ((e.val + 1) % 8) - levelHDNv_Y e.val) * levelHDNv_X e.val -
        (levelHDNv_X ((e.val + 1) % 8) - levelHDNv_X e.val) * levelHDNv_Y e.val := by
  rw [levelHDNv_h, levelHDNv_inner]; simp [levelHDNv_px]

lemma levelHDNv_pt (m : Fin 11) : proj_xy (hdnPt m) = !₂[hdnX m, hdnY m] := by
  ext a; fin_cases a <;> simp [hdnPt, proj_xy]

lemma levelHDNv_corner (m : Fin 11) (hm : m.val < 8) :
    proj_xy (hdnPt m) ∈ Set.range (fun t => proj_xy (levelHDNv_x t)) :=
  ⟨((⟨m.val, hm⟩ : Fin 8) : ZMod 8), by
    simp only [levelHDNv_x]; congr 2⟩

theorem levelHDN_witness_isRupert : IsRupert hdnV := by
  have hxV : ∀ t, levelHDNv_x t ∈ hdnV := fun t =>
    Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩
  have hhull : ∀ v ∈ hdnV, proj_xy v ∈ convexHull ℝ (Set.range fun t => proj_xy (levelHDNv_x t)) := by
    intro v hv
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 hv
    by_cases hm : m.val < 8
    · exact subset_convexHull ℝ _ (levelHDNv_corner m hm)
    · refine (halfPlanes_of_ccwPolygon (fun t => proj_xy (levelHDNv_x t)) (by norm_num)
        levelHDNv_ccw).1 ?_
      intro e
      show ⟪levelHDNv_n (fun t => proj_xy (levelHDNv_x t)) e, proj_xy (hdnPt m)⟫ < levelHDNv_h (fun t => proj_xy (levelHDNv_x t)) e
      rw [levelHDNv_inner, levelHDNv_hh, levelHDNv_pt]
      have : m = 8 ∨ m = 9 ∨ m = 10 := by fin_cases m <;> simp at hm ⊢
      rcases this with rfl | rfl | rfl <;>
        (fin_cases e <;> simp [hdnX, hdnY, levelHDNv_X, levelHDNv_Y, ZMod.val] <;> norm_num)
  have hn0 : ∀ e : ZMod 8, levelHDNv_n (fun t => proj_xy (levelHDNv_x t)) e 0 =
      levelHDNv_Y ((e.val + 1) % 8) - levelHDNv_Y e.val := by
    intro e; simp [levelHDNv_n, rot90, levelHDNv_pc1, levelHDNv_val_succ]
  have hn1 : ∀ e : ZMod 8, levelHDNv_n (fun t => proj_xy (levelHDNv_x t)) e 1 =
      -(levelHDNv_X ((e.val + 1) % 8) - levelHDNv_X e.val) := by
    intro e; simp [levelHDNv_n, rot90, levelHDNv_pc0, levelHDNv_val_succ]
  have hx0 : levelHDNv_x 0 = hdnPt 0 := rfl
  have hx4 : levelHDNv_x 4 = hdnPt 4 := rfl
  refine isRupert_of_levelHDN_rim hdnV (k := 8) (by norm_num) levelHDNv_x hxV levelHDNv_ccw hhull 0 4
    ?_ hdnW ?_ ?_ ?_ ?_
  · rw [hx0, hx4]; simp [hdnPt, hdnZ]
  · rw [levelHDNv_px, levelHDNv_px]
    simp [hdnW, cross2, levelHDNv_X, levelHDNv_Y, levelHDNv_v0, levelHDNv_v4]
  · intro e
    rw [levelHDNv_inner, levelHDNv_hh, levelHDNv_inner, levelHDNv_px, levelHDNv_px]
    simp only [levelHDNv_v0, levelHDNv_v4]
    fin_cases e <;> simp [levelHDNv_X, levelHDNv_Y, ZMod.val, levelHDNv_v0, levelHDNv_v4] <;> norm_num
  · intro e
    rw [levelHDNv_inner, levelHDNv_hh, levelHDNv_inner, levelHDNv_px, levelHDNv_px]
    simp only [levelHDNv_v0, levelHDNv_v4]
    fin_cases e <;> simp [levelHDNv_X, levelHDNv_Y, ZMod.val, levelHDNv_v0, levelHDNv_v4] <;> norm_num
  · intro v hv a b e he
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 hv
    rw [levelHDNv_inner, levelHDNv_hh, levelHDNv_pt] at he
    have hcr : cross2 (levelHDNv_n (fun t => proj_xy (levelHDNv_x t)) e) hdnW =
        (levelHDNv_Y ((e.val + 1) % 8) - levelHDNv_Y e.val) * (3/10) +
          (levelHDNv_X ((e.val + 1) % 8) - levelHDNv_X e.val) := by
      simp [cross2, hn0, hn1, hdnW]; ring
    rw [hcr, hx0]
    have hz : (hdnPt m) 2 = hdnZ m := by simp [hdnPt]
    have hz0 : (hdnPt 0) 2 = 0 := by simp [hdnPt, hdnZ]
    rw [hz, hz0]
    rw [hx0] at a
    rw [hx4] at b
    fin_cases m <;> fin_cases e <;> first
      | (exfalso; apply a; rfl)
      | (exfalso; apply b; rfl)
      | (exfalso; norm_num [hdnX, hdnY, levelHDNv_X, levelHDNv_Y, ZMod.val] at he; done)
      | norm_num [hdnZ, levelHDNv_X, levelHDNv_Y, ZMod.val]

end Minimality
end
