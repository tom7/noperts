module

public import Pipeline.CapBridge

@[expose] public section

/-!
# The cap theorem (given per-chart goodness)

`cap_pose_not_rupert`: if every point of every chart of a cap is *good*
(`ChartGood`: an F_e point in the cone region, a point outside the half-turn
cell for the element G, or a width witness (v_k, v_k', c) with u × c ≠ 0
whose witness values are ≥ 0 for every pair of vertices), then no pose with
view in the cap's cone (frame coordinates |uᵢ| ≤ μ₀ u_x), relative rotation
cayley(w) with w in the weighted box of frame coordinates, and (when the cap
uses the half-turn prune) relative rotation in the half-turn cell, is Rupert
for the solid, whatever the offset. The frame (e₁, e₂, x) is orthogonal, not
necessarily normalized, and the solid need not be centrally symmetric. The certificate check (`CapCert`) establishes
`ChartGood` for every chart point.
-/

namespace Noperts.Pipeline.Cap

open NPoly PVec
open scoped Matrix RealInnerProductSpace

/-- The real witness value of vertex v_j: N(w) v_k · d − D(w) (v_j · d), d = u × c. -/
noncomputable def witnessValue (u w vk c vj : Fin 3 → ℝ) : ℝ :=
  rdot (rcayleyNum w vk) (rcross u c) - (1 + rdot w w) * rdot vj (rcross u c)

/-- A chart point is good: an F_e point in the cone region, a point outside the half-turn cell
for G, or a width witness (v_k, v_k', c) with u × c ≠ 0 whose values at every pair of vertices
(v_j, v_j') are ≥ 0 (the witness values of v_k − v_k' against v_j − v_j'). -/
def ChartGood (st : Setup) (pr : Params) (V : List (Fin 3 → ℝ)) (usePrune : Bool)
    (G : Matrix (Fin 3) (Fin 3) ℝ) (id : ChartId) (y : Fin 5 → ℝ) : Prop :=
  (id.kind = .fe ∧ InConeRegion st pr (rES st id (st.frameAB id.side).1 (st.frameAB id.side).2 y).2) ∨
  (usePrune = true ∧ Matrix.trace (cayleyMatrix (rChartW st id y 0) (rChartW st id y 1) (rChartW st id y 2)) <
    Matrix.trace (halfTurnMat (rChartU st id y) *
      cayleyMatrix (rChartW st id y 0) (rChartW st id y 1) (rChartW st id y 2) * G)) ∨
  ∃ vk ∈ V, ∃ vk' ∈ V, ∃ c : Fin 3 → ℝ, rcross (rChartU st id y) c ≠ 0 ∧
    ∀ vj ∈ V, ∀ vj' ∈ V, 0 ≤ witnessValue (rChartU st id y) (rChartW st id y) (vk - vk') c (vj - vj')

/-- The Cayley rotation times its denominator is the numerator N(w). -/
theorem cayley_mulVec (w v : Fin 3 → ℝ) :
    (1 + rdot w w) • (cayleyMatrix (w 0) (w 1) (w 2)).mulVec v = rcayleyNum w v := by
  have hD : (1 + rdot w w) = cayleyDenom (w 0) (w 1) (w 2) := by
    simp [rdot, cayleyDenom]; ring
  have hne := cayleyDenom_ne (w 0) (w 1) (w 2)
  rw [cayleyMatrix_eq_div_numerator, hD]
  funext k
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Fin.sum_univ_three, rcayleyNum, rdot, rcross,
    Pi.add_apply, smul_eq_mul]
  fin_cases k <;> simp [cayleyNumeratorMatrix] <;> field_simp <;> ring

/-- A linear bound on a set bounds its convex hull. -/
theorem inner_le_of_mem_convexHull {T : Set ℝ³} (d : ℝ³) (M : ℝ) (hT : ∀ v ∈ T, ⟪d, v⟫ ≤ M) :
    ∀ v ∈ convexHull ℝ T, ⟪d, v⟫ ≤ M := by
  have hconv : Convex ℝ {v : ℝ³ | ⟪d, v⟫ ≤ M} := by
    have : {v : ℝ³ | ⟪d, v⟫ ≤ M} = {v : ℝ³ | (innerₛₗ ℝ d) v ≤ M} := rfl
    rw [this]
    exact convex_halfSpace_le (innerₛₗ ℝ d).isLinear M
  exact fun v hv => convexHull_min hT hconv hv

def toEuc (v : Fin 3 → ℝ) : ℝ³ := WithLp.toLp 2 v

theorem inner_toEuc (a b : Fin 3 → ℝ) : ⟪toEuc a, toEuc b⟫ = rdot a b := by
  rw [inner_euc3]; simp [toEuc, rdot]

theorem rdot_rcross_self (u c : Fin 3 → ℝ) : rdot u (rcross u c) = 0 := by
  simp [rdot, rcross]; ring

/-- The frame vectors e₁, e₂, x. -/
noncomputable def frameVec (st : Setup) : Fin 3 → Fin 3 → ℝ := ![kv st.e1, kv st.e2, kv st.x]

/-- Coordinate i of v in the orthogonal frame (e₁, e₂, x): v·fᵢ/|fᵢ|². -/
noncomputable def frameCoord (st : Setup) (v : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  rdot v (frameVec st i) / rdot (frameVec st i) (frameVec st i)

theorem decomp_frame (st : Setup) (hF : FrameOK st) (v : Fin 3 → ℝ) :
    v = frameCoord st v 0 • kv st.e1 + frameCoord st v 1 • kv st.e2 + frameCoord st v 2 • kv st.x :=
  decomp_orthogonal hF.2 v

theorem rcayleyNum_sub (w a b : Fin 3 → ℝ) : rcayleyNum w (a - b) = rcayleyNum w a - rcayleyNum w b := by
  funext k; simp only [rcayleyNum, rdot, rcross, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  fin_cases k <;> simp <;> ring

/-- **The cap theorem**, given that every chart point is good: no pose is Rupert whose view u
has frame coordinates (u₁, u₂, u_x) with u_x > 0, |uᵢ| ≤ μ₀ u_x, whose relative rotation is
cayley(w) with frame coordinates |w₁|, |w₂| ≤ R μ₀ and |w_x| ≤ S μ₀², and (with the prune)
which lies in the half-turn cell tr(H_u R G) ≤ tr R. -/
theorem cap_pose_not_rupert (st : Setup) (pr : Params) (zOf : Kind × ℕ × ℕ × Bool → ℕ) (hz : ∀ b, 0 < zOf b)
    (htie : TieOK st pr zOf) (hF : FrameOK st) (hS : 2 ≤ st.strongScale) (hmcm : 1 ≤ st.mcm)
    (V : List (Fin 3 → ℝ)) (usePrune : Bool) (G : Matrix (Fin 3) (Fin 3) ℝ)
    (hgood : ∀ id ∈ chartList st pr zOf, ∀ y, InBoxR (rootBox st pr id) y → ChartGood st pr V usePrune G id y)
    (S : Set ℝ³) (hSdef : S = convexHull ℝ {v | ∃ vj ∈ V, v = toEuc vj}) (p : MatrixPose)
    (hx : 0 < frameCoord st p.view 2)
    (he1 : |frameCoord st p.view 0| ≤ pr.mu0 * frameCoord st p.view 2)
    (he2 : |frameCoord st p.view 1| ≤ pr.mu0 * frameCoord st p.view 2)
    (w : Fin 3 → ℝ) (hR : p.relativeRotation = cayleyMatrix (w 0) (w 1) (w 2))
    (hw : ∀ i, |frameCoord st w i| ≤ (st.range i : ℝ) * (pr.mu0 : ℝ) ^ isoWt i)
    (hcell : usePrune = true →
      Matrix.trace (halfTurnMat p.view * p.relativeRotation * G) ≤ Matrix.trace p.relativeRotation) :
    ¬ RupertPose p S := by
  set u₀ := p.view
  set ξ := frameCoord st u₀ 2
  have hξ : ξ ≠ 0 := hx.ne'
  set t₁ := frameCoord st u₀ 0 / ξ
  set t₂ := frameCoord st u₀ 1 / ξ
  have ht₁ : |t₁| ≤ pr.mu0 := by
    simp only [t₁]; rw [abs_div, abs_of_pos hx, div_le_iff₀ hx]; exact he1
  have ht₂ : |t₂| ≤ pr.mu0 := by
    simp only [t₂]; rw [abs_div, abs_of_pos hx, div_le_iff₀ hx]; exact he2
  have hu : kv st.x + t₁ • kv st.e1 + t₂ • kv st.e2 = (1 / ξ) • u₀ := by
    have hd := decomp_frame st hF u₀
    conv_rhs => rw [hd]
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, t₁, t₂]
    field_simp
    ring
  obtain ⟨id, hid, y, hy, hU, hW, hFe⟩ :=
    cap_cover st pr zOf hz htie hF.1 hS hmcm t₁ t₂ ht₁ ht₂ (frameCoord st w) hw
  rw [hu] at hU
  rw [← decomp_frame st hF w] at hW
  rcases hgood id hid y hy with ⟨hfe, hcone⟩ | ⟨hp, htr⟩ | ⟨vk, hvk, vk', hvk', c, hd, hwit⟩
  · exact absurd hcone (hFe hfe)
  · rw [hU, hW, halfTurnMat_smul (1 / ξ) (by positivity) u₀] at htr
    have : cayleyMatrix (w 0) (w 1) (w 2) = p.relativeRotation := hR.symm
    rw [this] at htr
    exact absurd (hcell hp) (not_le.mpr htr)
  · rw [hU] at hd
    rw [hU, hW] at hwit
    set u := (1 / ξ) • u₀
    set d := rcross u c
    set Rm := cayleyMatrix (w 0) (w 1) (w 2)
    have hD : 0 < 1 + rdot w w := by linarith [rdot_self_nonneg w]
    -- (R (v_k − v_k'))·d ≥ (v_j − v_j')·d for every pair of vertices.
    have hRvk : ∀ vj ∈ V, ∀ vj' ∈ V, rdot vj d - rdot vj' d ≤
        rdot (Rm.mulVec vk) d - rdot (Rm.mulVec vk') d := by
      intro vj hvj vj' hvj'
      have h := hwit vj hvj vj' hvj'
      unfold witnessValue at h
      rw [← cayley_mulVec] at h
      have e1 : rdot ((1 + rdot w w) • Rm.mulVec (vk - vk')) d =
          (1 + rdot w w) * (rdot (Rm.mulVec vk) d - rdot (Rm.mulVec vk') d) := by
        rw [Matrix.mulVec_sub]
        simp only [rdot, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
      have e2 : rdot (vj - vj') d = rdot vj d - rdot vj' d := by
        simp only [rdot, Pi.sub_apply]; ring
      rw [e1, e2] at h
      nlinarith
    -- The largest value of ⟪d, ·⟫ on the vertices.
    classical
    obtain ⟨vm, hvm, hmax⟩ := Finset.exists_max_image V.toFinset (fun v => rdot v d)
      ⟨vk, List.mem_toFinset.mpr hvk⟩
    have hvm' := List.mem_toFinset.mp hvm
    set Δ := rdot (Rm.mulVec vk) d - rdot (Rm.mulVec vk') d
    have hmulE : ∀ v : Fin 3 → ℝ, Rm.toEuclideanLin (toEuc v) = toEuc (Rm.mulVec v) := by
      intro v; simp [Matrix.toLpLin_apply, toEuc]
    apply not_rupert_of_width_support p S (toEuc d) ?_ ?_ (rdot vm d) (Δ - rdot vm d) ?_ ?_
      (toEuc vk) (toEuc vk') ?_ ?_ ?_
    · intro h0
      apply hd
      have := congrArg (WithLp.ofLp) h0
      simpa [toEuc] using this
    · -- (O d)_z = u₀ · d = ξ (u · d) = 0.
      have h2 : (p.outerRot.val.toEuclideanLin (toEuc d)) 2 = rdot u₀ d := by
        simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, toEuc, rdot, u₀,
          MatrixPose.view]
      rw [h2]
      have hud : rdot u d = 0 := rdot_rcross_self u c
      have : rdot u₀ d = ξ * rdot u d := by
        simp only [u, rdot, Pi.smul_apply, smul_eq_mul]; field_simp
      rw [this, hud, mul_zero]
    · rw [hSdef]
      apply inner_le_of_mem_convexHull
      rintro v ⟨vj, hvj, rfl⟩
      rw [inner_toEuc, rdot_comm]
      exact hmax vj (List.mem_toFinset.mpr hvj)
    · rw [hSdef]
      have := inner_le_of_mem_convexHull (-(toEuc d)) (Δ - rdot vm d) (T := {v | ∃ vj ∈ V, v = toEuc vj})
        (by
          rintro v ⟨vj, hvj, rfl⟩
          rw [inner_neg_left, inner_toEuc, rdot_comm]
          have := hRvk vm hvm' vj hvj
          linarith)
      intro v hv
      have h := this v hv
      rwa [inner_neg_left] at h
    · rw [hSdef]; exact subset_convexHull ℝ _ ⟨vk, hvk, rfl⟩
    · rw [hSdef]; exact subset_convexHull ℝ _ ⟨vk', hvk', rfl⟩
    · rw [hR, hmulE, hmulE, inner_toEuc, inner_toEuc, rdot_comm d, rdot_comm d]
      simp only [Δ]
      linarith

end Noperts.Pipeline.Cap
