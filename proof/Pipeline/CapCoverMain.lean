module

public import Pipeline.CapRealize

@[expose] public section

/-!
# The cap domain is covered by the charts

`cap_cover`: for an isotropic (u0) cap with frame (x, e₁, e₂), every pose
with view u = x + t₁ e₁ + t₂ e₂ (|tᵢ| ≤ μ₀) and Cayley vector
w = ω₀ e₁ + ω₁ e₂ + ω₂ x with |ω₀|, |ω₁| ≤ 2 μ₀, |ω₂| ≤ S μ₀² is the image
(rChartU, rChartW) of a point of the root box of a chart in `chartList`; an
F_e chart is used only outside the cone region (which the cone charts
cover). The frame need not be normalized (nor, here, orthogonal): the chart
maps are written in it. (The anisotropic ux charts of the deltoidal
hexecontahedron are not covered here; `DeltoidalHexecontahedron/CapCoverMain.lean`
covers them.)
-/

namespace Noperts.Pipeline.Cap

open NPoly PVec

theorem rdot_sq_le (w v : Fin 3 → ℝ) : rdot w v ^ 2 ≤ rdot w w * rdot v v := by
  simp only [rdot]
  nlinarith [sq_nonneg (w 0 * v 1 - w 1 * v 0), sq_nonneg (w 0 * v 2 - w 2 * v 0),
    sq_nonneg (w 1 * v 2 - w 2 * v 1)]

theorem rdot_self_nonneg (w : Fin 3 → ℝ) : 0 ≤ rdot w w := by
  simp only [rdot]; nlinarith [mul_self_nonneg (w 0), mul_self_nonneg (w 1), mul_self_nonneg (w 2)]

/-- The F_e chart's cone region (identity cone; tie cone at (1, 0, 0) for ux). -/
def InConeRegion (st : Setup) (pr : Params) (s : Fin 3 → ℝ) : Prop :=
  (∀ i : Fin 3, |s i| ≤ pr.t0 * st.coneScale .cone i) ∨
    (st.aniso = true ∧ pr.tieCones = true ∧ |s 0 - 1| ≤ pr.t0m * st.coneScale .mcone 0 ∧
      |s 1| ≤ pr.t0m * st.coneScale .mcone 1 ∧ |s 2| ≤ pr.t0m * st.coneScale .mcone 2)

/-- The frame of a cap: an isotropic (u0) cap whose real frame (e₁, e₂, x) is orthogonal
(not necessarily normalized: the rational frames). -/
def FrameOK (st : Setup) : Prop := st.aniso = false ∧ Orthogonal3 (kv st.e1) (kv st.e2) (kv st.x)

/-- The side's (A, B) as real vectors in terms of (e₁, e₂). -/
theorem frameAB_val (st : Setup) (side : ℕ) (hside : side < 4) :
    kv (st.frameAB side).1 = (sideA side).1 • kv st.e1 + (sideA side).2 • kv st.e2 ∧
      kv (st.frameAB side).2 = (sideB side).1 • kv st.e1 + (sideB side).2 • kv st.e2 := by
  interval_cases side <;> simp [Setup.frameAB, sideA, sideB, kval_kneg] <;> funext i <;> simp

theorem mem_chartList (st : Setup) (pr : Params) (zOf : Kind × ℕ × ℕ × Bool → ℕ)
    {b : Kind × ℕ × ℕ × Bool} (hb : b ∈ baseCharts pr) {id : ChartId} (hid : id ∈ expandChart st pr zOf b) :
    id ∈ chartList st pr zOf :=
  List.mem_flatMap.mpr ⟨b, hb, hid⟩

theorem fe_mem_base (pr : Params) {side : ℕ} (h : side < 4) : (Kind.fe, side, 0, true) ∈ baseCharts pr := by
  simp only [baseCharts, List.mem_flatMap, List.mem_range]
  exact ⟨side, h, List.mem_cons_self⟩

theorem face_mem_base (pr : Params) {side axis : ℕ} (h : side < 4) (ha : axis < 3) (sg : Bool) :
    (Kind.face, side, axis, sg) ∈ baseCharts pr := by
  simp only [baseCharts, List.mem_flatMap, List.mem_range]
  refine ⟨side, h, List.mem_cons_of_mem _ ?_⟩
  rw [List.mem_flatMap]
  refine ⟨axis, List.mem_range.mpr ha, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨sg, by cases sg <;> simp, ?_⟩
  simp

theorem cone_mem_base (pr : Params) {side axis : ℕ} (h : side < 4) (ha : axis < 3) (sg : Bool) :
    (Kind.cone, side, axis, sg) ∈ baseCharts pr := by
  simp only [baseCharts, List.mem_flatMap, List.mem_range]
  refine ⟨side, h, List.mem_cons_of_mem _ ?_⟩
  rw [List.mem_flatMap]
  refine ⟨axis, List.mem_range.mpr ha, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨sg, by cases sg <;> simp, ?_⟩
  simp

theorem mcone_mem_base (pr : Params) (ht : pr.tieCones = true) {side axis : ℕ} (h : side < 4) (ha : axis < 3)
    (sg : Bool) : (Kind.mcone, side, axis, sg) ∈ baseCharts pr := by
  simp only [baseCharts, List.mem_flatMap, List.mem_range]
  refine ⟨side, h, List.mem_cons_of_mem _ ?_⟩
  rw [List.mem_flatMap]
  refine ⟨axis, List.mem_range.mpr ha, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨sg, by cases sg <;> simp, ?_⟩
  simp [ht]

/-- The chart's view in terms of its (e, μ, τ). -/
theorem rChartU_eq (st : Setup) (id : ChartId) (y : Fin 5 → ℝ) :
    rChartU st id y = kv st.x + (y 0 * (rES st id (st.frameAB id.side).1 (st.frameAB id.side).2 y).1) •
      (kv (st.frameAB id.side).1 + y 1 • kv (st.frameAB id.side).2) := rfl

theorem rChartW_eq (st : Setup) (id : ChartId) (y : Fin 5 → ℝ) :
    rChartW st id y =
      let s := (rES st id (st.frameAB id.side).1 (st.frameAB id.side).2 y).2
      let a := kv (st.frameAB id.side).1 + y 1 • kv (st.frameAB id.side).2
      if st.aniso then (y 0 * s 0) • rcross (kv st.x) a + ((y 0 * y 0) * s 1) • a + ((y 0 * y 0) * s 2) • kv st.x
      else (y 0 * s 0) • kv st.e1 + (y 0 * s 1) • kv st.e2 + ((y 0 * y 0) * s 2) • kv st.x := rfl

theorem range_pos (st : Setup) (hS : 2 ≤ st.strongScale) (i : ℕ) : (2 : ℝ) ≤ st.range i := by
  unfold Setup.range; split_ifs <;> [exact_mod_cast hS; norm_num]

theorem coneScale_pos (st : Setup) (hS : 2 ≤ st.strongScale) (hm : 1 ≤ st.mcm) (k : Kind) (i : ℕ) :
    (1 : ℝ) ≤ st.coneScale k i := by
  unfold Setup.coneScale
  have h : (2 : ℤ) ≤ (st.range i : ℤ) := by exact_mod_cast (show 2 ≤ st.range i by
    unfold Setup.range; split_ifs <;> omega)
  have h1 : (1 : ℤ) ≤ (st.range i : ℤ) / 2 := by omega
  have h2 : (1 : ℤ) ≤ (if k = .mcone ∧ st.strong i = true then (st.mcm : ℤ) else 1) := by
    split_ifs <;> omega
  have : (1 : ℤ) ≤ (st.range i : ℤ) / 2 * (if k = .mcone ∧ st.strong i = true then (st.mcm : ℤ) else 1) := by
    nlinarith
  exact_mod_cast this

/-- The tie scheme's parameters are admissible (faces with a strong axis ≠ 0, K ≥ Z + Z₂, K' > K). -/
def TieOK (st : Setup) (pr : Params) (zOf : Kind × ℕ × ℕ × Bool → ℕ) : Prop :=
  ∀ b p, st.tieOf b = some p → b.1 = .face →
    b.2.2.1 ≠ 0 ∧ zOf b + p.1 ≤ p.2.1 ∧ p.2.1 < p.2.2 ∧ pr.ratioOn = true ∧ st.strong b.2.2.1 = true

/-- The weight of frame coordinate i of an isotropic chart (2 for the strong coordinate x). -/
def isoWt (i : Fin 3) : ℕ := if (i : ℕ) = 2 then 2 else 1

/-- **The covering of the cap domain by the charts** (isotropic caps): every view
x + t₁ e₁ + t₂ e₂ (|tᵢ| ≤ μ₀) and every Cayley vector ω₀ e₁ + ω₁ e₂ + ω₂ x with
|ωᵢ| ≤ Rᵢ μ₀^{wᵢ} (weights 1, 1, 2) is the chart image of a point of the root box of a
chart in `chartList`; an F_e chart is used only outside the cone region. -/
theorem cap_cover (st : Setup) (pr : Params) (zOf : Kind × ℕ × ℕ × Bool → ℕ) (hz : ∀ b, 0 < zOf b)
    (htie : TieOK st pr zOf) (haniso : st.aniso = false) (hS : 2 ≤ st.strongScale) (hmcm : 1 ≤ st.mcm)
    (t₁ t₂ : ℝ) (ht₁ : |t₁| ≤ pr.mu0) (ht₂ : |t₂| ≤ pr.mu0) (ω : Fin 3 → ℝ)
    (hω : ∀ i, |ω i| ≤ (st.range i : ℝ) * (pr.mu0 : ℝ) ^ isoWt i) :
    ∃ id ∈ chartList st pr zOf, ∃ y, InBoxR (rootBox st pr id) y ∧
      rChartU st id y = kv st.x + t₁ • kv st.e1 + t₂ • kv st.e2 ∧
      rChartW st id y = ω 0 • kv st.e1 + ω 1 • kv st.e2 + ω 2 • kv st.x ∧
      (id.kind = .fe → ¬ InConeRegion st pr (rES st id (st.frameAB id.side).1 (st.frameAB id.side).2 y).2) := by
  obtain ⟨side, hside, m, τ, hm, hτ, ht1', ht2'⟩ := view_side t₁ t₂
  set A := (st.frameAB side).1
  set B := (st.frameAB side).2
  set a := kv A + τ • kv B
  have hm0 : 0 ≤ m := by rw [hm]; exact le_trans (abs_nonneg _) (le_max_left _ _)
  have hm1 : m ≤ pr.mu0 := by rw [hm]; exact max_le ht₁ ht₂
  -- The view.
  have hview : ∀ μ e : ℝ, μ * e = m → kv st.x + (μ * e) • a = kv st.x + t₁ • kv st.e1 + t₂ • kv st.e2 := by
    intro μ e hme
    obtain ⟨hA, hB⟩ := frameAB_val st side hside
    rw [hme]
    funext k
    simp only [a, A, B, hA, hB, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [ht1', ht2']; ring
  have hwt : ∀ i, isoWt i = 1 ∨ isoWt i = 2 := by intro i; simp only [isoWt]; split_ifs <;> simp
  have hR : ∀ i : Fin 3, (0 : ℝ) < (st.range i : ℝ) := fun i => by linarith [range_pos st hS i]
  obtain ⟨μ, e, sv, hμ0, hμ1, he0, he1, hme, hωs, hcase⟩ :=
    weighted_cube isoWt hwt (fun i => (st.range i : ℝ)) hR pr.mu0 m hm0 hm1 ω hω
  -- Closing the view and the Cayley vector for any chart point with these coordinates.
  have hU : ∀ (id : ChartId) (y : Fin 5 → ℝ), id.side = side → y 0 = μ → y 1 = τ →
      (rES st id (st.frameAB id.side).1 (st.frameAB id.side).2 y).1 = e →
      rChartU st id y = kv st.x + t₁ • kv st.e1 + t₂ • kv st.e2 := by
    intro id y hs h0 h1 he
    rw [rChartU_eq, he, h0, h1, hs]
    exact hview μ e hme.symm
  have hωv : ∀ i, ω i = μ ^ isoWt i * sv i := fun i => (hωs i).1
  have hW : ∀ (id : ChartId) (y : Fin 5 → ℝ), id.side = side → y 0 = μ → y 1 = τ →
      (rES st id (st.frameAB id.side).1 (st.frameAB id.side).2 y).2 = sv →
      rChartW st id y = ω 0 • kv st.e1 + ω 1 • kv st.e2 + ω 2 • kv st.x := by
    intro id y hs h0 h1 hsv
    rw [rChartW_eq]
    simp only []
    rw [hsv, h0, ite_eq_right (by rw [haniso]; decide)]
    rw [hωv 0, hωv 1, hωv 2, show isoWt 0 = 1 from rfl, show isoWt 1 = 1 from rfl, show isoWt 2 = 2 from rfl]
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hsb : ∀ i : Fin 3, |sv i| ≤ st.range i := fun i => (hωs i).2
  have hhalf : ∀ i : Fin 3, (0 : ℝ) < 2 * (st.coneScale .cone i : ℝ) := fun i => by
    linarith [coneScale_pos st hS hmcm .cone i]
  -- Sign of a unit coordinate.
  have hsgn : ∀ (x : ℝ), |x| = 1 → x = (if decide (0 ≤ x) then 1 else -1) := by
    intro x hx
    by_cases h : 0 ≤ x
    · simp only [h, decide_true, ite_true]; rw [abs_of_nonneg h] at hx; exact hx
    · simp only [h, decide_false, Bool.false_eq_true, ite_false]; rw [abs_of_neg (lt_of_not_ge h)] at hx; linarith
  have hμ1' : μ ≤ (pr.mu0 : ℝ) := hμ1
  rcases hcase with he | ⟨k, hk⟩
  · -- The F_e face (e = 1).
    by_cases hc1 : ∀ i : Fin 3, |sv i| ≤ pr.t0 * st.coneScale .cone i
    · obtain ⟨t, σ, k, htn, htt, hσk, hσ, hseq⟩ := cone_decomp (fun i => 2 * (st.coneScale .cone i : ℝ)) hhalf pr.t0 0 sv
        (by intro i; have := hc1 i; simp only [Pi.zero_apply, sub_zero]; linarith)
      obtain ⟨id, hid, hk', hsd, y, hy, hy0, hy1, hres⟩ := realize_cone st pr zOf .cone (Or.inl rfl) side k k.isLt
        (decide (0 ≤ σ k)) (hz _) μ τ t hμ0 hμ1' hτ htn (by simpa [Params.coneT] using htt) σ hσ
        (fun i hi => by rw [show i = k from Fin.ext hi]; exact hsgn _ hσk) A B
      refine ⟨id, mem_chartList st pr zOf (cone_mem_base pr hside k.isLt _) hid, y, hy, ?_, ?_, ?_⟩
      · exact hU id y hsd hy0 hy1 (by rw [hsd, hres, he])
      · apply hW id y hsd hy0 hy1
        rw [hsd, hres]
        funext i
        rw [hseq i]
        simp [rCenter]
      · intro hfe; rw [hk'] at hfe; exact absurd hfe (by decide)
    · obtain ⟨id, hid, hk', hsd, y, hy, hy0, hy1, hres⟩ :=
        realize_fe st pr zOf side (hz _) μ τ hμ0 hμ1' hτ sv hsb A B
      refine ⟨id, mem_chartList st pr zOf (fe_mem_base pr hside) hid, y, hy, ?_, ?_, ?_⟩
      · exact hU id y hsd hy0 hy1 (by rw [hsd, hres, he])
      · exact hW id y hsd hy0 hy1 (by rw [hsd, hres])
      · intro _ hcone
        rw [hsd, hres] at hcone
        rcases hcone with h | h
        · exact hc1 h
        · rw [haniso] at h; exact absurd h.1 (by decide)
  · -- A coordinate face: |s_k| = R_k.
    have hsk : sv k = (if decide (0 ≤ sv k) then 1 else -1) * (st.range k : ℝ) := by
      by_cases h : 0 ≤ sv k
      · simp only [h, decide_true, ite_true, one_mul]; rw [abs_of_nonneg h] at hk; exact hk
      · simp only [h, decide_false, Bool.false_eq_true, ite_false]; rw [abs_of_neg (lt_of_not_ge h)] at hk; linarith
    obtain ⟨id, hid, hk', hsd, y, hy, hy0, hy1, hres⟩ :
        ∃ id ∈ expandChart st pr zOf (.face, side, k, decide (0 ≤ sv k)), id.kind = .face ∧ id.side = side ∧
          ∃ y, InBoxR (rootBox st pr id) y ∧ y 0 = μ ∧ y 1 = τ ∧ rES st id A B y = (e, sv) := by
      by_cases htb : IsTie st (.face, side, k, decide (0 ≤ sv k))
      · obtain ⟨-, hsome⟩ := htb
        obtain ⟨⟨z2, kk, kp⟩, hp⟩ := Option.isSome_iff_exists.mp hsome
        obtain ⟨hax0, hK, hKp, hro, hstr⟩ := htie _ _ hp rfl
        exact realize_tie st pr zOf side k k.isLt hax0 (decide (0 ≤ sv k)) z2 kk kp hp hK hKp hro hstr
          μ τ e hμ0 hμ1' hτ he0 he1 sv hsb (fun i hi => by rw [show i = k from Fin.ext hi]; exact hsk) A B
      · exact realize_face st pr zOf side k k.isLt (decide (0 ≤ sv k)) (hz _) htb μ τ e hμ0 hμ1' hτ he0 he1 sv hsb
          (fun i hi => by rw [show i = k from Fin.ext hi]; exact hsk) A B
    refine ⟨id, mem_chartList st pr zOf (face_mem_base pr hside k.isLt _) hid, y, hy, ?_, ?_, ?_⟩
    · exact hU id y hsd hy0 hy1 (by rw [hsd, hres])
    · exact hW id y hsd hy0 hy1 (by rw [hsd, hres])
    · intro hfe; rw [hk'] at hfe; exact absurd hfe (by decide)

end Noperts.Pipeline.Cap
