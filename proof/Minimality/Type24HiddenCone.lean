module

public import Minimality.M4Type24
public import Minimality.HiddenCapFree
public import Minimality.Type24SAT.K24.CornerOB1

/-!
# Type 24: the hidden-cap cone at vertex `1`

For `F : S0xFac 9 s0x_S24 x` the corner frame at vertex `1` is `e_a = x 0 - x 1`, `e_b = x 2 - x 1`,
`e_c = x 6 - x 1`.  At a view `u = ca e_a + cb e_b + cc e_c` (`ca, cb, cc > 0`) vertex `1` is hidden
by the other six (`hiddenAt24_of_cone`), freedom of the six gives freedom of all seven
(`freeAt24_of_cone`), every positive covector `(ζ0, ζ1, ζ2) = (⟪e_a,u⟫, ⟪e_b,u⟫, ⟪e_c,u⟫)` is
realised by such a `u` under `OB1` (`cone24_of_zeta`), the depths are then metric free
(`depth24_metric_free`), and the three facets through `1` face back (`back24_of_cone`, converse
`cone24_of_back`).  Instances of `hiddenAt_of_cone`, `freeAt_insert_of_cone`, `pos_of_gram_solve`.
-/

@[expose] public section

set_option autoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT

namespace Minimality.T24.HC

/-- The cone view `ca e_a + cb e_b + cc e_c` at vertex `1`. -/
noncomputable def capView (x : Fin 7 → ℝ³) (ca cb cc : ℝ) : ℝ³ :=
  ca • (x 0 - x 1) + cb • (x 2 - x 1) + cc • (x 6 - x 1)

theorem det3_e026_ne {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) ≠ 0 := by
  have hne := (Minimality.T24.M4.type24OfFac F).det_ne
  have heq : det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) = det24 x := by
    simp only [det24, vol3, det3_expand]; ring
  rwa [heq]

theorem li_of_det3 (a b c : ℝ³) (h : det3 a b c ≠ 0) : LinearIndependent ℝ ![a, b, c] := by
  have h1 : Matrix.det (Matrix.of ![a, b, c]) ≠ 0 := by
    rw [Matrix.det_fin_three]
    intro h0; apply h
    simp only [det3_expand]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h0
    linarith
  have h2 := (Matrix.linearIndependent_row_iff_isUnit (A := Matrix.of ![a, b, c])).2
    ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h1))
  have e := (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap
  have h3 := h2.map' (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap
    (LinearMap.ker_eq_bot.2 (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.injective)
  convert h3 using 1
  ext i : 1
  fin_cases i <;> rfl

theorem li24 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    LinearIndependent ℝ ![x 0 - x 1, x 2 - x 1, x 6 - x 1] :=
  li_of_det3 _ _ _ (det3_e026_ne F)

theorem mem_cap {x : Fin 7 → ℝ³} (i : Fin 7) (hi : i ≠ 1) : x i ∈ (univ.erase 1).image x :=
  mem_image_of_mem x (Finset.mem_erase.2 ⟨hi, mem_univ _⟩)

theorem insert_erase_image (x : Fin 7 → ℝ³) :
    insert (x 1) ((univ.erase 1).image x) = univ.image x := by
  rw [← Finset.image_insert, Finset.insert_erase (mem_univ _)]

/-- **1.** Vertex `1` is hidden by the other six at every cone view. -/
theorem hiddenAt24_of_cone {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (ca cb cc : ℝ)
    (hca : 0 < ca) (hcb : 0 < cb) (hcc : 0 < cc) :
    HiddenAt ((univ.erase 1).image x) (capView x ca cb cc) (x 1) :=
  hiddenAt_of_cone _ (x 1) (x 0) (x 2) (x 6) (mem_cap 0 (by decide)) (mem_cap 2 (by decide))
    (mem_cap 6 (by decide)) (li24 F) ca cb cc hca hcb hcc

/-- **2.** Freedom of the six points gives freedom of all seven at a cone view. -/
theorem freeAt24_of_cone {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (ca cb cc : ℝ)
    (hca : 0 < ca) (hcb : 0 < cb) (hcc : 0 < cc)
    (h : Minimality.Split.FreeAt ((univ.erase 1).image x) (capView x ca cb cc)) :
    Minimality.Split.FreeAt (univ.image x) (capView x ca cb cc) := by
  rw [← insert_erase_image x]
  have hD : Minimality.Split.det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) ≠ 0 := by
    have := det3_e026_ne F
    intro h0; apply this
    simp only [Minimality.Split.det3] at h0
    simp only [det3_expand]; linarith
  exact Minimality.Split.freeAt_insert_of_cone _ (x 1) (x 0) (x 2) (x 6)
    (mem_cap 0 (by decide)) (mem_cap 2 (by decide)) (mem_cap 6 (by decide)) hD ca cb cc
    (Or.inl ⟨hca, hcb, hcc⟩) h


theorem inner_cross_right (b c d : ℝ³) : ⟪d, cross b c⟫ = det3 b c d := by
  rw [real_inner_comm]; rfl

theorem det3_cyc (a b c : ℝ³) : det3 b c a = det3 a b c := by
  simp only [det3_expand]; ring

theorem gram_pos (a b c : ℝ³) (h : LinearIndependent ℝ ![a, b, c]) (x y z : ℝ)
    (hxyz : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) :
    0 < ⟪a, a⟫ * x ^ 2 + ⟪b, b⟫ * y ^ 2 + ⟪c, c⟫ * z ^ 2 +
      2 * (⟪a, b⟫ * x * y + ⟪a, c⟫ * x * z + ⟪b, c⟫ * y * z) := by
  have hw : x • a + y • b + z • c ≠ 0 := by
    intro h0
    have := Fintype.linearIndependent_iff.1 h ![x, y, z]
      (by simpa [Fin.sum_univ_three] using h0)
    rcases hxyz with h1 | h1 | h1
    · exact h1 (by simpa using this 0)
    · exact h1 (by simpa using this 1)
    · exact h1 (by simpa using this 2)
  have := real_inner_self_pos.2 hw
  have e : ⟪x • a + y • b + z • c, x • a + y • b + z • c⟫ =
      ⟪a, a⟫ * x ^ 2 + ⟪b, b⟫ * y ^ 2 + ⟪c, c⟫ * z ^ 2 +
      2 * (⟪a, b⟫ * x * y + ⟪a, c⟫ * x * z + ⟪b, c⟫ * y * z) := by
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm a b, real_inner_comm a c, real_inner_comm b c]
    ring
  linarith

/-- **3.** Under `OB1`, every positive covector `(ζ0, ζ1, ζ2)` is `(⟪e_a,u⟫, ⟪e_b,u⟫, ⟪e_c,u⟫)`
for a cone view `u = ca e_a + cb e_b + cc e_c` with `ca, cb, cc > 0`. -/
theorem cone24_of_zeta {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hob : H24K.SAT.OB1 x)
    (ζ0 ζ1 ζ2 : ℝ) (h0 : 0 < ζ0) (h1 : 0 < ζ1) (h2 : 0 < ζ2) :
    ∃ ca cb cc : ℝ, 0 < ca ∧ 0 < cb ∧ 0 < cc ∧
      ⟪x 0 - x 1, capView x ca cb cc⟫ = ζ0 ∧ ⟪x 2 - x 1, capView x ca cb cc⟫ = ζ1 ∧
      ⟪x 6 - x 1, capView x ca cb cc⟫ = ζ2 := by
  obtain ⟨o01, o06, o26⟩ := hob
  have hD := det3_e026_ne F
  have hli := li24 F
  set a := x 0 - x 1 with ha
  set b := x 2 - x 1 with hb
  set c := x 6 - x 1 with hc
  set D := det3 a b c with hDdef
  set u : ℝ³ := D⁻¹ • (ζ0 • cross b c + ζ1 • cross c a + ζ2 • cross a b) with hu
  have iu : ∀ d : ℝ³, ⟪d, u⟫ = D⁻¹ * (ζ0 * det3 b c d + ζ1 * det3 c a d + ζ2 * det3 a b d) := by
    intro d
    simp only [hu, real_inner_smul_right, inner_add_right]
    rw [inner_cross_right, inner_cross_right, inner_cross_right]
  have d1 : det3 b c a = D := by simp only [hDdef, det3_expand]; ring
  have d2 : det3 c a b = D := by simp only [hDdef, det3_expand]; ring
  have d3 : det3 a b c = D := rfl
  have z1 : det3 c a a = 0 := by simp only [det3_expand]; ring
  have z2 : det3 a b a = 0 := by simp only [det3_expand]; ring
  have z3 : det3 b c b = 0 := by simp only [det3_expand]; ring
  have z4 : det3 a b b = 0 := by simp only [det3_expand]; ring
  have z5 : det3 b c c = 0 := by simp only [det3_expand]; ring
  have z6 : det3 c a c = 0 := by simp only [det3_expand]; ring
  have ia : ⟪a, u⟫ = ζ0 := by rw [iu, d1, z1, z2]; field_simp; ring
  have ib : ⟪b, u⟫ = ζ1 := by rw [iu, z3, d2, z4]; field_simp; ring
  have ic : ⟪c, u⟫ = ζ2 := by rw [iu, z5, z6, d3]; field_simp; ring
  obtain ⟨ca, cb, cc, hcu⟩ := span_of_indep3 hli u
  have e1 : ⟪a, a⟫ * ca + ⟪a, b⟫ * cb + ⟪a, c⟫ * cc = ζ0 := by
    rw [← ia, hcu]
    simp only [inner_add_right, real_inner_smul_right]; ring
  have e2 : ⟪a, b⟫ * ca + ⟪b, b⟫ * cb + ⟪b, c⟫ * cc = ζ1 := by
    rw [← ib, hcu]
    simp only [inner_add_right, real_inner_smul_right]
    rw [real_inner_comm a b]; ring
  have e3 : ⟪a, c⟫ * ca + ⟪b, c⟫ * cb + ⟪c, c⟫ * cc = ζ2 := by
    rw [← ic, hcu]
    simp only [inner_add_right, real_inner_smul_right]
    rw [real_inner_comm a c, real_inner_comm b c]; ring
  obtain ⟨p1, p2, p3⟩ := pos_of_gram_solve _ _ _ _ _ _ ca cb cc ζ0 ζ1 ζ2 o01 o06 o26
    (fun X Y Z h => gram_pos a b c hli X Y Z h) h0 h1 h2 e1 e2 e3
  refine ⟨ca, cb, cc, p1, p2, p3, ?_, ?_, ?_⟩
  · rw [← ia]; exact congrArg (fun w => ⟪_, w⟫) hcu.symm
  · rw [← ib]; exact congrArg (fun w => ⟪_, w⟫) hcu.symm
  · rw [← ic]; exact congrArg (fun w => ⟪_, w⟫) hcu.symm


/-- **4.** Metric-free depths: if `u` has the covector `(ζ0, ζ1, ζ2)` on the corner frame, then
`⟪x v - x 1, u⟫ = X0(v) ζ0 + X2(v) ζ1 + X6(v) ζ2` for every vertex `v`. -/
theorem depth24_metric_free {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (u : ℝ³) (ζ0 ζ1 ζ2 : ℝ)
    (h0 : ⟪x 0 - x 1, u⟫ = ζ0) (h1 : ⟪x 2 - x 1, u⟫ = ζ1) (h2 : ⟪x 6 - x 1, u⟫ = ζ2)
    (v : Fin 7) :
    ⟪x v - x 1, u⟫ = oblX0 x v * ζ0 + oblX2 x v * ζ1 + oblX6 x v * ζ2 := by
  have hv : x v - x 1 = oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) +
      oblX6 x v • (x 6 - x 1) := by
    have := (Minimality.T24.M4.type24OfFac F).rep v
    rw [sub_eq_iff_eq_add]; rw [this]; abel
  rw [hv, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_smul_left, h0, h1, h2]

/-- The inner products of the three facets through vertex `1` with the frame edges
(`012` contains `a, b`; `016` contains `a, c`; `126` contains `b, c`). -/
theorem facet_back_vals {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    (⟪F.N 0, x 0 - x 1⟫ = 0 ∧ ⟪F.N 0, x 2 - x 1⟫ = 0 ∧ ⟪F.N 0, x 6 - x 1⟫ < 0) ∧
    (⟪F.N 1, x 0 - x 1⟫ = 0 ∧ ⟪F.N 1, x 6 - x 1⟫ = 0 ∧ ⟪F.N 1, x 2 - x 1⟫ < 0) ∧
    (⟪F.N 5, x 2 - x 1⟫ = 0 ∧ ⟪F.N 5, x 6 - x 1⟫ = 0 ∧ ⟪F.N 5, x 0 - x 1⟫ < 0) := by
  have z : ∀ (t : Fin 9) (i : Fin 7), i ∈ s0x_S24 t → F.f t (x i) = 0 := fun t i h => F.zero t i h
  have n : ∀ (t : Fin 9) (i : Fin 7), i ∉ s0x_S24 t → F.f t (x i) < 0 := fun t i h => F.neg t i h
  simp only [F.inner_sub]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · rw [z 0 0 (by decide), z 0 1 (by decide)]; simp
  · rw [z 0 2 (by decide), z 0 1 (by decide)]; simp
  · rw [z 0 1 (by decide)]; simpa using n 0 6 (by decide)
  · rw [z 1 0 (by decide), z 1 1 (by decide)]; simp
  · rw [z 1 6 (by decide), z 1 1 (by decide)]; simp
  · rw [z 1 1 (by decide)]; simpa using n 1 2 (by decide)
  · rw [z 5 2 (by decide), z 5 1 (by decide)]; simp
  · rw [z 5 6 (by decide), z 5 1 (by decide)]; simp
  · rw [z 5 1 (by decide)]; simpa using n 5 0 (by decide)

/-- **5.** At a cone view the three facets through vertex `1` (`012`, `016`, `126`, i.e. `t = 0, 1, 5`)
face back: `⟪F.N t, u⟫ < 0` (`N` is the outward normal, `f ≤ 0` on `K`). -/
theorem back24_of_cone {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (ca cb cc : ℝ)
    (hca : 0 < ca) (hcb : 0 < cb) (hcc : 0 < cc) :
    ⟪F.N 0, capView x ca cb cc⟫ < 0 ∧ ⟪F.N 1, capView x ca cb cc⟫ < 0 ∧
      ⟪F.N 5, capView x ca cb cc⟫ < 0 := by
  obtain ⟨⟨a0, b0, c0⟩, ⟨a1, c1, b1⟩, ⟨b5, c5, a5⟩⟩ := facet_back_vals F
  simp only [capView, inner_add_right, real_inner_smul_right]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

/-- **5'.** Converse: if the three facets through vertex `1` face back at `u`, then `u` is a cone
view with positive coefficients. -/
theorem cone24_of_back {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (u : ℝ³)
    (h0 : ⟪F.N 0, u⟫ < 0) (h1 : ⟪F.N 1, u⟫ < 0) (h5 : ⟪F.N 5, u⟫ < 0) :
    ∃ ca cb cc : ℝ, 0 < ca ∧ 0 < cb ∧ 0 < cc ∧ u = capView x ca cb cc := by
  obtain ⟨⟨a0, b0, c0⟩, ⟨a1, c1, b1⟩, ⟨b5, c5, a5⟩⟩ := facet_back_vals F
  obtain ⟨ca, cb, cc, hu⟩ := span_of_indep3 (li24 F) u
  have e0 : ⟪F.N 0, u⟫ = cc * ⟪F.N 0, x 6 - x 1⟫ := by
    rw [hu]; simp only [inner_add_right, real_inner_smul_right, a0, b0]; ring
  have e1 : ⟪F.N 1, u⟫ = cb * ⟪F.N 1, x 2 - x 1⟫ := by
    rw [hu]; simp only [inner_add_right, real_inner_smul_right, a1, c1]; ring
  have e5 : ⟪F.N 5, u⟫ = ca * ⟪F.N 5, x 0 - x 1⟫ := by
    rw [hu]; simp only [inner_add_right, real_inner_smul_right, b5, c5]; ring
  refine ⟨ca, cb, cc, ?_, ?_, ?_, hu⟩
  · by_contra h; push Not at h; nlinarith
  · by_contra h; push Not at h; nlinarith
  · by_contra h; push Not at h; nlinarith

end Minimality.T24.HC
