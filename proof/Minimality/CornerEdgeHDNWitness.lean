module

public import Minimality.CornerEdgeHDN

@[expose] public section

/-!
# Non-vacuity of Theorem CE′ (plan specpos A5)

An 11-point rational shape (8 rim corners, 3 interior points; `h2check.cc` mode 2, reflected so the corner is
`vp = (-1, 0, 0)` and the edge `e0` is the vertical right edge from `a = (1, -3/10, -3/10)` to
`b = (1, 3/10, 3/10)`).  The chord to `y = (a+b)/2 = (1, 0, 0)` is level and `⟂ e0`.  The motion `σ = 1`, `β = 1/4`
is weakly inward at every tight pair, `ceW_isRupert : IsRupert ceV` is proved outright through
`isRupert_of_cornerEdgeHDN_rim`.
-/
noncomputable section
namespace Minimality
open scoped RealInnerProductSpace

def ceX : Fin 11 → ℝ := ![1, 7/10, 0, -7/10, -1, -7/10, 0, 1, 0, 1/5, -3/10]
def ceY : Fin 11 → ℝ := ![3/10, 7/10, 1, 7/10, 0, -7/10, -1, -3/10, 0, 1/10, 1/5]
def ceZ : Fin 11 → ℝ := ![3/10, 1/2, 4/5, 2/5, 0, -1/2, -1/5, -3/10, 3/10, -2/5, 0]
noncomputable def cePt (i : Fin 11) : ℝ³ := !₂[ceX i, ceY i, ceZ i]
noncomputable def ceV : Finset ℝ³ := Finset.image cePt Finset.univ

/-- The 8 rim corners, indexed by `ZMod 8`. -/
def ceW_x (t : ZMod 8) : ℝ³ := cePt (Fin.castLE (by norm_num) (show Fin 8 from t))

def ceW_X (n : ℕ) : ℝ := [(1:ℝ), 7/10, 0, -7/10, -1, -7/10, 0, 1].getD n 0
def ceW_Y (n : ℕ) : ℝ := [(3/10:ℝ), 7/10, 1, 7/10, 0, -7/10, -1, -3/10].getD n 0
def ceW_Z (n : ℕ) : ℝ := [(3/10:ℝ), 1/2, 4/5, 2/5, 0, -1/2, -1/5, -3/10].getD n 0

lemma ceW_x_eq (t : ZMod 8) : ceW_x t = !₂[ceW_X t.val, ceW_Y t.val, ceW_Z t.val] := by
  fin_cases t <;> ext a <;> fin_cases a <;>
    simp [ceW_x, cePt, ceX, ceY, ceZ, ceW_X, ceW_Y, ceW_Z, ZMod.val, Fin.castLE]

lemma ceW_px (t : ZMod 8) : proj_xy (ceW_x t) = !₂[ceW_X t.val, ceW_Y t.val] := by
  rw [ceW_x_eq]; ext a; fin_cases a <;> simp [proj_xy]

lemma ceW_val_succ (i : ZMod 8) : (i + 1).val = (i.val + 1) % 8 := by
  fin_cases i <;> rfl

lemma ceW_ccw : ∀ i j : ZMod 8, j ≠ i → j ≠ i + 1 →
      0 < cross2 (proj_xy (ceW_x (i + 1)) - proj_xy (ceW_x i)) (proj_xy (ceW_x j) - proj_xy (ceW_x i)) := by
  intro i j h1 h2
  rw [ceW_px, ceW_px, ceW_px, ceW_val_succ]
  fin_cases i <;> fin_cases j <;> first | (exfalso; apply h1; rfl) | (exfalso; apply h2; rfl) | skip
  all_goals
    simp [cross2, ceW_X, ceW_Y, ZMod.val]
    try norm_num

lemma ceW_v7 : (7 : ZMod 8).val = 7 := rfl
lemma ceW_v4 : (4 : ZMod 8).val = 4 := rfl
lemma ceW_v0 : (0 : ZMod 8).val = 0 := rfl
lemma ceW_e8 : (7 + 1 : ZMod 8) = 0 := by decide

lemma ceW_pc0 (t : ZMod 8) : (proj_xy (ceW_x t)) 0 = ceW_X t.val := by
  rw [ceW_px]; simp
lemma ceW_pc1 (t : ZMod 8) : (proj_xy (ceW_x t)) 1 = ceW_Y t.val := by
  rw [ceW_px]; simp

lemma ceW_inner (e : ZMod 8) (y : ℝ²) :
    ⟪levelHDNv_n (fun t => proj_xy (ceW_x t)) e, y⟫ =
      (ceW_Y ((e.val + 1) % 8) - ceW_Y e.val) * y 0 - (ceW_X ((e.val + 1) % 8) - ceW_X e.val) * y 1 := by
  simp [levelHDNv_n, rot90, PiLp.inner_apply, Fin.sum_univ_two, ceW_px, ceW_val_succ]
  ring

lemma ceW_hh (e : ZMod 8) :
    levelHDNv_h (fun t => proj_xy (ceW_x t)) e =
      (ceW_Y ((e.val + 1) % 8) - ceW_Y e.val) * ceW_X e.val -
        (ceW_X ((e.val + 1) % 8) - ceW_X e.val) * ceW_Y e.val := by
  rw [levelHDNv_h, ceW_inner]; simp [ceW_px]

lemma ceW_pt (m : Fin 11) : proj_xy (cePt m) = !₂[ceX m, ceY m] := by
  ext a; fin_cases a <;> simp [cePt, proj_xy]

lemma ceW_corner (m : Fin 11) (hm : m.val < 8) :
    proj_xy (cePt m) ∈ Set.range (fun t => proj_xy (ceW_x t)) :=
  ⟨((⟨m.val, hm⟩ : Fin 8) : ZMod 8), by simp only [ceW_x]; congr 2⟩

theorem ceW_isRupert : IsRupert ceV := by
  have hxV : ∀ t, ceW_x t ∈ ceV := fun t => Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩
  have hhull : ∀ v ∈ ceV, proj_xy v ∈ convexHull ℝ (Set.range fun t => proj_xy (ceW_x t)) := by
    intro v hv
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 hv
    by_cases hm : m.val < 8
    · exact subset_convexHull ℝ _ (ceW_corner m hm)
    · refine (halfPlanes_of_ccwPolygon (fun t => proj_xy (ceW_x t)) (by norm_num) ceW_ccw).1 ?_
      intro e
      show ⟪levelHDNv_n (fun t => proj_xy (ceW_x t)) e, proj_xy (cePt m)⟫ <
        levelHDNv_h (fun t => proj_xy (ceW_x t)) e
      rw [ceW_inner, ceW_hh, ceW_pt]
      have : m = 8 ∨ m = 9 ∨ m = 10 := by fin_cases m <;> simp at hm ⊢
      rcases this with rfl | rfl | rfl <;>
        (fin_cases e <;> simp [ceX, ceY, ceW_X, ceW_Y, ZMod.val] <;> norm_num)
  have hn0 : ∀ e : ZMod 8, levelHDNv_n (fun t => proj_xy (ceW_x t)) e 0 =
      ceW_Y ((e.val + 1) % 8) - ceW_Y e.val := by
    intro e; simp [levelHDNv_n, rot90, ceW_pc1, ceW_val_succ]
  have hn1 : ∀ e : ZMod 8, levelHDNv_n (fun t => proj_xy (ceW_x t)) e 1 =
      -(ceW_X ((e.val + 1) % 8) - ceW_X e.val) := by
    intro e; simp [levelHDNv_n, rot90, ceW_pc0, ceW_val_succ]
  have hx : ∀ m : ZMod 8, ceW_x m = cePt (Fin.castLE (by norm_num) (show Fin 8 from m)) := fun _ => rfl
  have hD : (!₂[2, 0] : ℝ²) = proj_xy ((1 - 1/2 : ℝ) • ceW_x 7 + (1/2 : ℝ) • ceW_x 0) - proj_xy (ceW_x 4) := by
    rw [ceW_x_eq, ceW_x_eq, ceW_x_eq]
    ext a; fin_cases a <;> norm_num [proj_xy, ceW_X, ceW_Y, ceW_v7, ceW_v4, ceW_v0]
  have hgen : ∀ (v : ℝ³) (e : ZMod 8), cornerEdge_c (levelHDNv_n (fun s => proj_xy (ceW_x s)) e) !₂[2, 0]
      (ceW_x 0 - ceW_x 7) (ceW_x 4) v 1 (1/4) =
      v 2 * ((ceW_Y ((e.val + 1) % 8) - ceW_Y e.val) * 0 + (ceW_X ((e.val + 1) % 8) - ceW_X e.val) * 2) +
      1/4 * (-(ceW_X ((e.val + 1) % 8) - ceW_X e.val) * (3/5) * (v 0 + 1) -
        (ceW_Y ((e.val + 1) % 8) - ceW_Y e.val) * (3/5) * v 1 +
        ((ceW_Y ((e.val + 1) % 8) - ceW_Y e.val) * (3/5)) * v 2) := by
    intro v e
    simp only [cornerEdge_c, PiLp.sub_apply, cross2]
    rw [hn0, hn1]
    simp [ceW_x_eq, cross2, ceW_X, ceW_Y, ceW_Z, ceW_v0, ceW_v4, ceW_v7]
    ring
  refine isRupert_of_cornerEdgeHDN_rim ceV (k := 8) (by norm_num) ceW_x hxV ceW_ccw hhull 0 ?_ 4 7 (1/2)
    !₂[2, 0] hD ?_ ?_ ?_ 1 (1/4) (by norm_num) ?_
  all_goals try simp only [ceW_e8]
  · intro e
    rw [ceW_inner, ceW_hh]
    simp [ceW_X, ceW_Y, ZMod.val]
    fin_cases e <;> simp [ceW_X, ceW_Y, ZMod.val] <;> norm_num
  · rw [ceW_x_eq, ceW_x_eq, ceW_x_eq]
    norm_num [ceW_Z, ceW_v7, ceW_v4, ceW_v0]
  · simp [cross2, hn1, hn0, ceW_X, ceW_Y, ceW_v7]
  · rw [ceW_x_eq, ceW_x_eq]
    norm_num [ceW_Z, ceW_v7, ceW_v0]
  · intro v hv e he
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 hv
    rw [ceW_inner, ceW_hh, ceW_pt] at he
    have hg := hgen (cePt m) e
    fin_cases m <;> fin_cases e <;> first
      | (exfalso; norm_num [ceX, ceY, ceW_X, ceW_Y, ZMod.val] at he; done)
      | (left; rfl)
      | (right; left; exact ⟨rfl, Or.inl rfl⟩)
      | (right; left; exact ⟨rfl, Or.inr rfl⟩)
      | (right; right
         rw [hg]
         norm_num [cePt, ceX, ceY, ceZ, ceW_X, ceW_Y, ZMod.val])

end Minimality
end
