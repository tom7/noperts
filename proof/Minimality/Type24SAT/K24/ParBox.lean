module

public import Minimality.Type24SAT.K24.ParStratum
public import Minimality.Type24SAT.K24.ParBoxCoord

@[expose] public section

/-!
# Type 24 box corner `R₄'`

`isRupert_parBox`: on `D` a parallelogram with `E ∥ G`, the box corner `ParBox` (`D` a rectangle, `E, G, C, I` all
perpendicular to it, `X 2 = 0`, `X 6 = |e|²`) is Rupert.  The facet structure gives box coordinates
(`isRupert_box_of_facets`: frame `e/|e|`, `-N_D/|N_D|`, `g/|g|`; vertex `1` between the planes `026` and `H`), and
`box_rupert` (`ParBoxCoord`) closes it by one fixed lexicographic motion per case.
-/


set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.Par
open Minimality Minimality.H21 Minimality.T24.SAT

variable {x : Fin 7 → ℝ³}

/-- The box corner from the facet structure: `D` a rectangle, `E, G, C, I` perpendicular to it, `X 2 = 0`,
`X 6 = |e|²`, in the frame `e/|e|`, `-N_D/|N_D|`, `g/|g|` (either orientation). -/
theorem isRupert_box_of_facets (F : S0xFac 9 s0x_S24 x) (hP : x 3 = x 4 + x 5 - x 0)
    (hE : ⟪F.N 4, x 2 - x 3⟫ = 0) (hw : ⟪x 5 - x 0, x 2 - x 3⟫ = 0) (hs : ⟪x 5 - x 0, x 6 - x 0⟫ = 0)
    (h2 : ⟪x 2 - x 0, x 4 - x 0⟫ = 0) (h6 : ⟪x 6 - x 0, x 4 - x 0⟫ = ⟪x 4 - x 0, x 4 - x 0⟫) :
    IsRupert (univ.image x) := by
  obtain ⟨heg, hen, hng, -, -⟩ := rect_frame F hP hE hw hs
  have IS := F.inner_sub
  have hx := Minimality.H24.SAT.inj_of_fac F
  have he : x 4 - x 0 ≠ 0 := fun h => absurd (hx (sub_eq_zero.1 h)) (by decide)
  have hg : x 5 - x 0 ≠ 0 := fun h => absurd (hx (sub_eq_zero.1 h)) (by decide)
  have hn : -F.N 3 ≠ 0 := by
    intro h
    have := nn24 F 3
    rw [neg_eq_zero] at h; rw [h, inner_zero_left] at this; exact lt_irrefl 0 this
  set e := x 4 - x 0 with he_def
  set g := x 5 - x 0 with hg_def
  set n := -F.N 3 with hn_def
  have hee : 0 < ⟪e, e⟫ := real_inner_self_pos.2 he
  have hgg : 0 < ⟪g, g⟫ := real_inner_self_pos.2 hg
  have hnn : 0 < ⟪n, n⟫ := real_inner_self_pos.2 hn
  have hen' : ⟪e, n⟫ = 0 := by rw [hn_def, inner_neg_right, hen, neg_zero]
  have hng' : ⟪n, g⟫ = 0 := by rw [hn_def, inner_neg_left, hng, neg_zero]
  have hgn' : ⟪g, n⟫ = 0 := by rw [real_inner_comm]; exact hng'
  have hne' : ⟪n, e⟫ = 0 := by rw [real_inner_comm]; exact hen'
  have hge : ⟪g, e⟫ = 0 := by rw [real_inner_comm]; exact heg
  obtain ⟨L, hL, hLL⟩ : ∃ L : ℝ, 0 < L ∧ L * L = ⟪e, e⟫ := ⟨Real.sqrt ⟪e, e⟫, Real.sqrt_pos.2 hee, Real.mul_self_sqrt hee.le⟩
  obtain ⟨c, hc, hcc⟩ : ∃ c : ℝ, 0 < c ∧ c * c = ⟪g, g⟫ := ⟨Real.sqrt ⟪g, g⟫, Real.sqrt_pos.2 hgg, Real.mul_self_sqrt hgg.le⟩
  obtain ⟨ν, hν, hνν⟩ : ∃ ν : ℝ, 0 < ν ∧ ν * ν = ⟪n, n⟫ := ⟨Real.sqrt ⟪n, n⟫, Real.sqrt_pos.2 hnn, Real.mul_self_sqrt hnn.le⟩
  set f1 := L⁻¹ • e with hf1
  set f2 := ν⁻¹ • n with hf2
  set f3 := c⁻¹ • g with hf3
  have o11 : ⟪f1, f1⟫ = 1 := by
    rw [hf1, real_inner_smul_left, real_inner_smul_right, ← hLL]; field_simp
  have o22 : ⟪f2, f2⟫ = 1 := by
    rw [hf2, real_inner_smul_left, real_inner_smul_right, ← hνν]; field_simp
  have o33 : ⟪f3, f3⟫ = 1 := by
    rw [hf3, real_inner_smul_left, real_inner_smul_right, ← hcc]; field_simp
  have o12 : ⟪f1, f2⟫ = 0 := by rw [hf1, hf2, real_inner_smul_left, real_inner_smul_right, hen']; simp
  have o13 : ⟪f1, f3⟫ = 0 := by rw [hf1, hf3, real_inner_smul_left, real_inner_smul_right, heg]; simp
  have o23 : ⟪f2, f3⟫ = 0 := by rw [hf2, hf3, real_inner_smul_left, real_inner_smul_right, hng']; simp
  -- coordinates
  have c1 : ∀ v : ℝ³, ⟪f1, v⟫ = L⁻¹ * ⟪e, v⟫ := fun v => by rw [hf1, real_inner_smul_left]
  have c2 : ∀ v : ℝ³, ⟪f2, v⟫ = ν⁻¹ * ⟪n, v⟫ := fun v => by rw [hf2, real_inner_smul_left]
  have c3 : ∀ v : ℝ³, ⟪f3, v⟫ = c⁻¹ * ⟪g, v⟫ := fun v => by rw [hf3, real_inner_smul_left]
  -- coordinates of the vertices
  have z0 : x 0 - x 0 = 0 := sub_self _
  have e3 : x 3 - x 0 = e + g := by rw [hP, he_def, hg_def]; abel
  have e2g : ⟪g, x 2 - x 0⟫ = ⟪g, g⟫ := by
    have : x 2 - x 3 = (x 2 - x 0) - e - g := by rw [hP, he_def, hg_def]; abel
    rw [this, inner_sub_right, inner_sub_right, hge] at hw
    rw [hg_def] at hw ⊢; linarith
  have e6g : ⟪g, x 6 - x 0⟫ = 0 := hs
  have Xe : ⟪f1, e⟫ = L := by rw [c1, ← hLL]; field_simp
  have Ye : ⟪f2, e⟫ = 0 := by rw [c2, hne']; simp
  have Ze : ⟪f3, e⟫ = 0 := by rw [c3, hge]; simp
  have Xg : ⟪f1, g⟫ = 0 := by rw [c1, heg]; simp
  have Yg : ⟪f2, g⟫ = 0 := by rw [c2, hng']; simp
  have Zg : ⟪f3, g⟫ = c := by rw [c3, ← hcc]; field_simp
  have X4 : ⟪f1, x 4 - x 0⟫ = L := Xe
  have Y4 : ⟪f2, x 4 - x 0⟫ = 0 := Ye
  have Z4 : ⟪f3, x 4 - x 0⟫ = 0 := Ze
  have X5 : ⟪f1, x 5 - x 0⟫ = 0 := Xg
  have Y5 : ⟪f2, x 5 - x 0⟫ = 0 := Yg
  have Z5 : ⟪f3, x 5 - x 0⟫ = c := Zg
  have X3 : ⟪f1, x 3 - x 0⟫ = L := by rw [e3, inner_add_right, Xe, Xg]; ring
  have Y3 : ⟪f2, x 3 - x 0⟫ = 0 := by rw [e3, inner_add_right, Ye, Yg]; ring
  have Z3 : ⟪f3, x 3 - x 0⟫ = c := by rw [e3, inner_add_right, Ze, Zg]; ring
  have X2 : ⟪f1, x 2 - x 0⟫ = 0 := by rw [c1, real_inner_comm, h2]; simp
  have Z2 : ⟪f3, x 2 - x 0⟫ = c := by rw [c3, e2g, ← hcc]; field_simp
  have X6 : ⟪f1, x 6 - x 0⟫ = L := by rw [c1, real_inner_comm, h6, ← hLL]; field_simp
  have Z6 : ⟪f3, x 6 - x 0⟫ = 0 := by rw [c3, e6g]; simp
  have X0 : ⟪f1, x 0 - x 0⟫ = 0 := by rw [z0]; simp
  have Y0 : ⟪f2, x 0 - x 0⟫ = 0 := by rw [z0]; simp
  have Z0 : ⟪f3, x 0 - x 0⟫ = 0 := by rw [z0]; simp
  -- the frame coordinates of the normals
  have fcoord : ∀ (t : Fin 9) (i : Fin 7), F.f t (x i) - F.f t (x 0) =
      ⟪f1, F.N t⟫ * ⟪f1, x i - x 0⟫ + ⟪f2, F.N t⟫ * ⟪f2, x i - x 0⟫ + ⟪f3, F.N t⟫ * ⟪f3, x i - x 0⟫ := by
    intro t i
    rw [← IS t i 0, frame_inner o11 o22 o33 o12 o13 o23 (F.N t) (x i - x 0)]
  -- orientation: the other vertices have positive `Y`
  have posY : ∀ i : Fin 7, i ∉ s0x_S24 3 → 0 < ⟪f2, x i - x 0⟫ := by
    intro i hi
    have h := F.neg 3 i hi
    have h0 := F.zero 3 0 (by decide)
    have := IS 3 i 0
    rw [h0, sub_zero] at this
    rw [c2]
    refine mul_pos (inv_pos.2 hν) ?_
    rw [hn_def, inner_neg_left]; linarith
  have z := fun t i (hi : i ∈ s0x_S24 t) => F.zero t i hi
  have ng := fun t i (hi : i ∉ s0x_S24 t) => F.neg t i hi
  have hy2 : 0 < ⟪f2, x 2 - x 0⟫ := posY 2 (by decide)
  have hy6 : 0 < ⟪f2, x 6 - x 0⟫ := posY 6 (by decide)
  obtain ⟨y2, hy2d⟩ : ∃ y, y = ⟪f2, x 2 - x 0⟫ := ⟨_, rfl⟩
  obtain ⟨y6, hy6d⟩ : ∃ y, y = ⟪f2, x 6 - x 0⟫ := ⟨_, rfl⟩
  obtain ⟨xi, hX1⟩ : ∃ y, ⟪f1, x 1 - x 0⟫ = y * L := ⟨⟪f1, x 1 - x 0⟫ / L, by field_simp⟩
  obtain ⟨ze, hZ1⟩ : ∃ y, ⟪f3, x 1 - x 0⟫ = y * c := ⟨⟪f3, x 1 - x 0⟫ / c, by field_simp⟩
  obtain ⟨Y1, hY1⟩ : ∃ y, y = ⟪f2, x 1 - x 0⟫ := ⟨_, rfl⟩
  rw [← hy2d] at hy2; rw [← hy6d] at hy6
  have xiP : 0 < xi := by
    have a5 := fcoord 2 5; have a2 := fcoord 2 2; have a4 := fcoord 2 4; have a1 := fcoord 2 1
    rw [z 2 5 (by decide), z 2 0 (by decide), X5, Y5, Z5] at a5
    rw [z 2 2 (by decide), z 2 0 (by decide), X2, ← hy2d, Z2] at a2
    rw [z 2 0 (by decide), X4, Y4, Z4] at a4
    rw [z 2 0 (by decide), hX1, ← hY1, hZ1] at a1
    exact facC_xi (b := Y1) (ze := ze) (p := ⟪f1, F.N 2⟫) (q := ⟪f2, F.N 2⟫) (r := ⟪f3, F.N 2⟫) (f4 := F.f 2 (x 4)) (f1v := F.f 2 (x 1)) hL hc hy2 (by linarith) (by linarith) (by linarith) (by linarith)
      (ng 2 4 (by decide)) (ng 2 1 (by decide))
  have zeP : 0 < ze := by
    have a4 := fcoord 4 4; have a6 := fcoord 4 6; have a5 := fcoord 4 5; have a1 := fcoord 4 1
    rw [z 4 4 (by decide), z 4 0 (by decide), X4, Y4, Z4] at a4
    rw [z 4 6 (by decide), z 4 0 (by decide), X6, ← hy6d, Z6] at a6
    rw [z 4 0 (by decide), X5, Y5, Z5] at a5
    rw [z 4 0 (by decide), hX1, ← hY1, hZ1] at a1
    exact facE_ze (b := Y1) (xi := xi) (p := ⟪f1, F.N 4⟫) (q := ⟪f2, F.N 4⟫) (r := ⟪f3, F.N 4⟫) (f5 := F.f 4 (x 5)) (f1v := F.f 4 (x 1)) hL hc hy6 (by linarith) (by linarith) (by linarith) (by linarith)
      (ng 4 5 (by decide)) (ng 4 1 (by decide))
  have hlo : y6 * xi + y2 * ze < Y1 := by
    have a2 := fcoord 0 2; have a1 := fcoord 0 1; have a4 := fcoord 0 4; have a5 := fcoord 0 5
    have a6 := fcoord 0 6
    rw [z 0 2 (by decide), z 0 0 (by decide), X2, ← hy2d, Z2] at a2
    rw [z 0 1 (by decide), z 0 0 (by decide), hX1, ← hY1, hZ1] at a1
    rw [z 0 0 (by decide), X4, Y4, Z4] at a4
    rw [z 0 0 (by decide), X5, Y5, Z5] at a5
    rw [z 0 0 (by decide), X6, ← hy6d, Z6] at a6
    exact facA_lo (b := Y1) (p := ⟪f1, F.N 0⟫) (q := ⟪f2, F.N 0⟫) (r := ⟪f3, F.N 0⟫) (f4 := F.f 0 (x 4)) (f5 := F.f 0 (x 5)) (f6 := F.f 0 (x 6)) hL hc hy2 xiP (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith) (ng 0 4 (by decide)) (ng 0 5 (by decide)) (ng 0 6 (by decide))
  have hhi : Y1 < y2 * (1 - xi) + y6 * (1 - ze) := by
    have a2 := fcoord 7 2; have a3 := fcoord 7 3; have a6 := fcoord 7 6; have a1 := fcoord 7 1
    rw [z 7 2 (by decide), X2, ← hy2d, Z2] at a2
    rw [z 7 3 (by decide), X3, Y3, Z3] at a3
    rw [z 7 6 (by decide), X6, ← hy6d, Z6] at a6
    rw [hX1, ← hY1, hZ1] at a1
    exact facH_hi (b := Y1) (p := ⟪f1, F.N 7⟫) (q := ⟪f2, F.N 7⟫) (r := ⟪f3, F.N 7⟫) (f0 := F.f 7 (x 0)) (f1v := F.f 7 (x 1)) hy2 hy6 hL hc (by linarith) (by linarith) (by linarith) (by linarith)
      (ng 7 0 (by decide)) (ng 7 1 (by decide))
  have hbox := box_rupert hL hc hy2 hy6 xiP zeP hlo hhi
  refine rupert_of_frame x f1 f2 f3 (x 0) o11 o22 o33 o12 o13 o23 ?_
  convert hbox using 2
  funext i
  fin_cases i
  · ext j; fin_cases j <;> simp [boxCfg, X0, Y0, Z0]
  · ext j; fin_cases j <;> simp [boxCfg, hX1, hZ1, ← hY1]
  · ext j; fin_cases j <;> simp [boxCfg, X2, Z2, ← hy2d]
  · ext j; fin_cases j <;> simp [boxCfg, X3, Y3, Z3]
  · ext j; fin_cases j <;> simp [boxCfg, X4, Y4, Z4]
  · ext j; fin_cases j <;> simp [boxCfg, X5, Y5, Z5]
  · ext j; fin_cases j <;> simp [boxCfg, X6, Z6, ← hy6d]
end Minimality.T24.Par

namespace Minimality.T24.Par
open Minimality Minimality.H21 Minimality.T24.SAT

/-- **The box corner `R₄'`** of the parallel-pair stratum: `05 ⊥ 23`, `05 ⊥ 06`, `h = ⟪x 6 - x 0, x 2 - x 3⟫ ≥ 0`,
`X 2 = 0`, `X 6 = |e|²` and `T ≤ 0` (`e = x 4 - x 0`, `X i = ⟪x i - x 0, e⟫`, `T = ⟪x 3 - x 6, x 2 - x 0⟫`).
(`h ≥ 0` and `T ≤ 0` are not used by `isRupert_parBox`.) -/
def ParBox (x : Fin 7 → ℝ³) : Prop :=
  ⟪x 5 - x 0, x 2 - x 3⟫ = 0 ∧ ⟪x 5 - x 0, x 6 - x 0⟫ = 0 ∧ 0 ≤ ⟪x 6 - x 0, x 2 - x 3⟫ ∧
    ⟪x 2 - x 0, x 4 - x 0⟫ = 0 ∧ ⟪x 6 - x 0, x 4 - x 0⟫ = ⟪x 4 - x 0, x 4 - x 0⟫ ∧
    ⟪x 3 - x 6, x 2 - x 0⟫ ≤ 0

/-- **The box corner `R₄'` is Rupert** (the last piece of the parallel-pair stratum): `D` a parallelogram with
`E ∥ G` (`⟪N_E, x 2 - x 3⟫ = 0`) inside `ParBox`.  Recipes I, IV, III, L at the edge view along `e`. -/
theorem isRupert_parBox {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hP : x 3 = x 4 + x 5 - x 0)
    (hE : ⟪F.N 4, x 2 - x 3⟫ = 0) (hB : ParBox x) : IsRupert (Finset.univ.image x) := by
  obtain ⟨hw, hs, -, h2, h6, -⟩ := hB
  exact isRupert_box_of_facets F hP hE hw hs h2 h6

end Minimality.T24.Par
