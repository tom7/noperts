module

public import Minimality.CaseC18Fo
public import Minimality.CaseC18M
public import Minimality.CaseC09Frame
public import Minimality.TripleTieObtuse
public import Minimality.ParDichotomy
public import Minimality.SevenTypes

@[expose] public section

/-! # sp02 Lean, group F: the normal-form frame of type 02's case (c) 

Template: `frame09` (CaseC09Frame.lean), `Frame18`/`Frame18.toFrame7` (CaseC18Frame/Bridge).
Type 02 is type 09 with the relabelling `0->2, 3->3, 5->4, 1->0, 4->5, 2->1, 6->6` and the two triangles
`123`, `235` merged into the quadrilateral `0134` (so the cap relations are the *planarity* equalities
`hp/(1-tp) = kp/(1-sp)`, `hm/(1-tm) = km/(1-sm)` instead of type 09's roof inequality).  Frame (paper sp02 §1):
vertex `v = x 2`, far ends `x 3 = v + u1`, `x 4 = v + u2`, `L = R e`;
`x 0 = v + tp u1 + hp e`, `x 5 = v + tm u1 - hm e` (face `0235`), `x 1 = v + sp u2 + kp e`, `x 6 = v + sm u2 - km e`
(face `1246`); caps `0134` (up) and `3456` (down). -/

namespace Minimality.CaseC18

open Finset Filter Minimality.CaseC09
open scoped RealInnerProductSpace Topology

/-- The parameters of a type-02 shape in case (c).  PROVISIONAL field list: whoever proves `frame02`
may add fields that the realization gives for free and the sector tests need (e.g. the chord
condition `2 ∉ conv{0,1,5,6}` in real form). -/
structure Shape02 where
  tp : ℝ
  tm : ℝ
  sp : ℝ
  sm : ℝ
  hp : ℝ
  hm : ℝ
  kp : ℝ
  km : ℝ
  tp_pos : 0 < tp
  tp_lt : tp < 1
  tm_pos : 0 < tm
  tm_lt : tm < 1
  sp_pos : 0 < sp
  sp_lt : sp < 1
  sm_pos : 0 < sm
  sm_lt : sm < 1
  hp_pos : 0 < hp
  hm_pos : 0 < hm
  kp_pos : 0 < kp
  km_pos : 0 < km
  /-- `0134` is planar (`h1 = κ+ (1 - t1)`, `k1 = κ+ (1 - s1)`) -/
  plane_up : hp / (1 - tp) = kp / (1 - sp)
  /-- `3456` is planar -/
  plane_dn : hm / (1 - tm) = km / (1 - sm)

/-- **The frame of case (c) at `0235`, `1246` (vertex `2`)** (cf. `Frame18`, `Frame09`):
`A12 > 0` is the acute angle at `v`, `A12 ≤ A11`, `A12 ≤ A22` the non-obtuse far angles
(a right far angle is allowed: it is the paper's Theorem 02.R). -/
structure Frame02 (x : Fin 7 → ℝ³) where
  e : ℝ³
  S : Shape02
  e_ne : e ≠ 0
  indep : LinearIndependent ℝ ![x 3 - x 2, x 4 - x 2, e]
  x0_eq : x 0 = x 2 + S.tp • (x 3 - x 2) + S.hp • e
  x5_eq : x 5 = x 2 + S.tm • (x 3 - x 2) - S.hm • e
  x1_eq : x 1 = x 2 + S.sp • (x 4 - x 2) + S.kp • e
  x6_eq : x 6 = x 2 + S.sm • (x 4 - x 2) - S.km • e
  inner_u1_e : ⟪x 3 - x 2, e⟫ = 0
  inner_u2_e : ⟪x 4 - x 2, e⟫ = 0
  A12_pos : 0 < ⟪x 3 - x 2, x 4 - x 2⟫
  A12_le_A11 : ⟪x 3 - x 2, x 4 - x 2⟫ ≤ ⟪x 3 - x 2, x 3 - x 2⟫
  A12_le_A22 : ⟪x 3 - x 2, x 4 - x 2⟫ ≤ ⟪x 4 - x 2, x 4 - x 2⟫

/-- α = (0 5)(1 6). -/
def permAlpha : Equiv.Perm (Fin 7) := Equiv.swap 0 5 * Equiv.swap 1 6
/-- β = (0 1)(3 4)(5 6). -/
def permBeta : Equiv.Perm (Fin 7) := Equiv.swap 0 1 * Equiv.swap 3 4 * Equiv.swap 5 6

namespace Frame02
variable {x : Fin 7 → ℝ³} (F : Frame02 x)

/-- Frame coordinates (relative to `x 2`) of the seven points, labels `0..6`. -/
noncomputable def pt (S : Shape02) : Fin 7 → C3 := ![⟨S.tp, 0, S.hp⟩, ⟨0, S.sp, S.kp⟩,
  ⟨0, 0, 0⟩, ⟨1, 0, 0⟩, ⟨0, 1, 0⟩, ⟨S.tm, 0, -S.hm⟩, ⟨0, S.sm, -S.km⟩]

/-- The `Frame7` of a type-02 frame (as `Frame18.toFrame7`). -/
noncomputable def toFrame7 : Frame7 x where
  base := x 2
  u1 := x 3 - x 2
  u2 := x 4 - x 2
  e := F.e
  indep := F.indep
  inner_u1_e := F.inner_u1_e
  inner_u2_e := F.inner_u2_e
  ptC := pt F.S
  x_eq := by
    intro j
    fin_cases j
    · show x 0 = x 2 + F.S.tp • (x 3 - x 2) + 0 • (x 4 - x 2) + F.S.hp • F.e
      rw [F.x0_eq]; simp
    · show x 1 = x 2 + 0 • (x 3 - x 2) + F.S.sp • (x 4 - x 2) + F.S.kp • F.e
      rw [F.x1_eq]; simp
    · show x 2 = x 2 + 0 • (x 3 - x 2) + 0 • (x 4 - x 2) + 0 • F.e
      simp
    · show x 3 = x 2 + (1:ℝ) • (x 3 - x 2) + 0 • (x 4 - x 2) + 0 • F.e
      simp
    · show x 4 = x 2 + 0 • (x 3 - x 2) + (1:ℝ) • (x 4 - x 2) + 0 • F.e
      simp
    · show x 5 = x 2 + F.S.tm • (x 3 - x 2) + 0 • (x 4 - x 2) + (-F.S.hm) • F.e
      rw [F.x5_eq]; simp [sub_eq_add_neg]
    · show x 6 = x 2 + 0 • (x 3 - x 2) + F.S.sm • (x 4 - x 2) + (-F.S.km) • F.e
      rw [F.x6_eq]; simp [sub_eq_add_neg]

end Frame02

/-- `A11 = |x3 - x2|²`, `A12 = ⟪x3 - x2, x4 - x2⟫`, `A22 = |x4 - x2|²`. -/
noncomputable def gA11 (x : Fin 7 → ℝ³) : ℝ := ⟪x 3 - x 2, x 3 - x 2⟫
noncomputable def gA12 (x : Fin 7 → ℝ³) : ℝ := ⟪x 3 - x 2, x 4 - x 2⟫
noncomputable def gA22 (x : Fin 7 → ℝ³) : ℝ := ⟪x 4 - x 2, x 4 - x 2⟫

/-- `F1 = 0235` is a rectangle with diagonal `[x2, x3]` (parallelogram + right angle at `x2`). -/
def F1Rect (x : Fin 7 → ℝ³) : Prop :=
  x 3 - x 2 = (x 0 - x 2) + (x 5 - x 2) ∧ ⟪x 0 - x 2, x 5 - x 2⟫ = 0

/-- Right angles of `F1` at `x0` and `x5`, and the angle at `x2` at least a right angle (the set X2). -/
def X2Set (x : Fin 7 → ℝ³) : Prop :=
  ⟪x 2 - x 0, x 3 - x 0⟫ = 0 ∧ ⟪x 2 - x 5, x 3 - x 5⟫ = 0 ∧ ⟪x 0 - x 2, x 5 - x 2⟫ ≤ 0

namespace Frame02
variable {x : Fin 7 → ℝ³}

theorem pA0 : permAlpha 0 = 5 := by decide
theorem pA1 : permAlpha 1 = 6 := by decide
theorem pA2 : permAlpha 2 = 2 := by decide
theorem pA3 : permAlpha 3 = 3 := by decide
theorem pA4 : permAlpha 4 = 4 := by decide
theorem pA5 : permAlpha 5 = 0 := by decide
theorem pA6 : permAlpha 6 = 1 := by decide
theorem pB0 : permBeta 0 = 1 := by decide
theorem pB1 : permBeta 1 = 0 := by decide
theorem pB2 : permBeta 2 = 2 := by decide
theorem pB3 : permBeta 3 = 4 := by decide
theorem pB4 : permBeta 4 = 3 := by decide
theorem pB5 : permBeta 5 = 6 := by decide
theorem pB6 : permBeta 6 = 5 := by decide

/-- α = (0 5)(1 6): the frame of `x ∘ α`, with swapped parameters and the same Gram entries.
Proof: `e ↦ -e`, field by field (`x0_eq` of the new frame is `x5_eq` of the old one). -/
theorem alpha_spec (F : Frame02 x) : ∃ G : Frame02 (x ∘ permAlpha),
    G.S.tp = F.S.tm ∧ G.S.tm = F.S.tp ∧ G.S.sp = F.S.sm ∧ G.S.sm = F.S.sp ∧
    gA11 (x ∘ permAlpha) = gA11 x ∧ gA12 (x ∘ permAlpha) = gA12 x ∧
    gA22 (x ∘ permAlpha) = gA22 x := by
  have h2 : (x ∘ permAlpha) 2 = x 2 := by simp [Function.comp, pA2]
  have h3 : (x ∘ permAlpha) 3 = x 3 := by simp [Function.comp, pA3]
  have h4 : (x ∘ permAlpha) 4 = x 4 := by simp [Function.comp, pA4]
  have h0 : (x ∘ permAlpha) 0 = x 5 := by simp [Function.comp, pA0]
  have h1 : (x ∘ permAlpha) 1 = x 6 := by simp [Function.comp, pA1]
  have h5 : (x ∘ permAlpha) 5 = x 0 := by simp [Function.comp, pA5]
  have h6 : (x ∘ permAlpha) 6 = x 1 := by simp [Function.comp, pA6]
  let S' : Shape02 :=
    { tp := F.S.tm, tm := F.S.tp, sp := F.S.sm, sm := F.S.sp,
      hp := F.S.hm, hm := F.S.hp, kp := F.S.km, km := F.S.kp,
      tp_pos := F.S.tm_pos, tp_lt := F.S.tm_lt, tm_pos := F.S.tp_pos, tm_lt := F.S.tp_lt,
      sp_pos := F.S.sm_pos, sp_lt := F.S.sm_lt, sm_pos := F.S.sp_pos, sm_lt := F.S.sp_lt,
      hp_pos := F.S.hm_pos, hm_pos := F.S.hp_pos, kp_pos := F.S.km_pos, km_pos := F.S.kp_pos,
      plane_up := F.S.plane_dn, plane_dn := F.S.plane_up }
  refine ⟨⟨-F.e, S', neg_ne_zero.mpr F.e_ne, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · rw [h2, h3, h4]
    have := F.indep.units_smul ![1, 1, -1]
    convert this using 1
    ext i; fin_cases i <;> simp
  · simp only [h0, h2, h3]; show _ = _ + F.S.tm • _ + F.S.hm • -F.e
    rw [F.x5_eq]; simp [sub_eq_add_neg]
  · simp only [h5, h2, h3]; show _ = _ + F.S.tp • _ - F.S.hp • -F.e
    rw [F.x0_eq]; simp
  · simp only [h1, h2, h4]; show _ = _ + F.S.sm • _ + F.S.km • -F.e
    rw [F.x6_eq]; simp [sub_eq_add_neg]
  · simp only [h6, h2, h4]; show _ = _ + F.S.sp • _ - F.S.kp • -F.e
    rw [F.x1_eq]; simp
  · rw [h2, h3]; simp [F.inner_u1_e]
  · rw [h2, h4]; simp [F.inner_u2_e]
  · rw [h2, h3, h4]; exact F.A12_pos
  · rw [h2, h3, h4]; exact F.A12_le_A11
  · rw [h2, h3, h4]; exact F.A12_le_A22
  · simp [gA11, Function.comp, pA2, pA3]
  · simp [gA12, Function.comp, pA2, pA3, pA4]
  · simp [gA22, Function.comp, pA2, pA4]

/-- β = (0 1)(3 4)(5 6): `u1 ↔ u2`, so `A11 ↔ A22`, `tp ↔ sp`, `tm ↔ sm`.  (`hp ↔ kp`, `hm ↔ km`;
planarity equalities are symmetric.) -/
theorem beta_spec (F : Frame02 x) : ∃ G : Frame02 (x ∘ permBeta),
    G.S.tp = F.S.sp ∧ G.S.sp = F.S.tp ∧ G.S.tm = F.S.sm ∧ G.S.sm = F.S.tm ∧
    gA11 (x ∘ permBeta) = gA22 x ∧ gA22 (x ∘ permBeta) = gA11 x ∧
    gA12 (x ∘ permBeta) = gA12 x := by
  have h2 : (x ∘ permBeta) 2 = x 2 := by simp [Function.comp, pB2]
  have h3 : (x ∘ permBeta) 3 = x 4 := by simp [Function.comp, pB3]
  have h4 : (x ∘ permBeta) 4 = x 3 := by simp [Function.comp, pB4]
  have h0 : (x ∘ permBeta) 0 = x 1 := by simp [Function.comp, pB0]
  have h1 : (x ∘ permBeta) 1 = x 0 := by simp [Function.comp, pB1]
  have h5 : (x ∘ permBeta) 5 = x 6 := by simp [Function.comp, pB5]
  have h6 : (x ∘ permBeta) 6 = x 5 := by simp [Function.comp, pB6]
  let S' : Shape02 :=
    { tp := F.S.sp, tm := F.S.sm, sp := F.S.tp, sm := F.S.tm,
      hp := F.S.kp, hm := F.S.km, kp := F.S.hp, km := F.S.hm,
      tp_pos := F.S.sp_pos, tp_lt := F.S.sp_lt, tm_pos := F.S.sm_pos, tm_lt := F.S.sm_lt,
      sp_pos := F.S.tp_pos, sp_lt := F.S.tp_lt, sm_pos := F.S.tm_pos, sm_lt := F.S.tm_lt,
      hp_pos := F.S.kp_pos, hm_pos := F.S.km_pos, kp_pos := F.S.hp_pos, km_pos := F.S.hm_pos,
      plane_up := F.S.plane_up.symm, plane_dn := F.S.plane_dn.symm }
  refine ⟨⟨F.e, S', F.e_ne, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · rw [h2, h3, h4]
    have hI := Fintype.linearIndependent_iff.mp F.indep
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    simp [Fin.sum_univ_three] at hg
    have := hI ![g 1, g 0, g 2] (by
      simp [Fin.sum_univ_three]; rw [← hg]; abel)
    fin_cases i
    · simpa using this 1
    · simpa using this 0
    · simpa using this 2
  · simp only [h0, h1, h2, h3, h4, h5, h6]; show _ = _ + F.S.sp • _ + F.S.kp • F.e
    rw [F.x1_eq]
  · simp only [h0, h1, h2, h3, h4, h5, h6]; show _ = _ + F.S.sm • _ - F.S.km • F.e
    rw [F.x6_eq]
  · simp only [h0, h1, h2, h3, h4, h5, h6]; show _ = _ + F.S.tp • _ + F.S.hp • F.e
    rw [F.x0_eq]
  · simp only [h0, h1, h2, h3, h4, h5, h6]; show _ = _ + F.S.tm • _ - F.S.hm • F.e
    rw [F.x5_eq]
  · rw [h2, h3]; exact F.inner_u2_e
  · rw [h2, h4]; exact F.inner_u1_e
  · rw [h2, h3, h4, real_inner_comm]; exact F.A12_pos
  · rw [h2, h3, h4, real_inner_comm]; exact F.A12_le_A22
  · rw [h2, h3, h4, real_inner_comm]; exact F.A12_le_A11
  · simp [gA11, gA22, Function.comp, pB2, pB3, pB4]
  · simp [gA11, gA22, Function.comp, pB2, pB3, pB4]
  · simp [gA12, Function.comp, pB2, pB3, pB4, real_inner_comm]

/-- `F1Rect`, `X2Set` are invariant under α (the swap `0 ↔ 5` exchanges the two clauses). -/
theorem F1Rect_alpha (x : Fin 7 → ℝ³) : F1Rect (x ∘ permAlpha) ↔ F1Rect x := by
  have h2 : (x ∘ permAlpha) 2 = x 2 := by simp [Function.comp, pA2]
  have h3 : (x ∘ permAlpha) 3 = x 3 := by simp [Function.comp, pA3]
  have h0 : (x ∘ permAlpha) 0 = x 5 := by simp [Function.comp, pA0]
  have h5 : (x ∘ permAlpha) 5 = x 0 := by simp [Function.comp, pA5]
  simp only [F1Rect, h0, h2, h3, h5]
  rw [add_comm (x 5 - x 2), real_inner_comm (x 0 - x 2)]

theorem X2Set_alpha (x : Fin 7 → ℝ³) : X2Set (x ∘ permAlpha) ↔ X2Set x := by
  have h2 : (x ∘ permAlpha) 2 = x 2 := by simp [Function.comp, pA2]
  have h3 : (x ∘ permAlpha) 3 = x 3 := by simp [Function.comp, pA3]
  have h0 : (x ∘ permAlpha) 0 = x 5 := by simp [Function.comp, pA0]
  have h5 : (x ∘ permAlpha) 5 = x 0 := by simp [Function.comp, pA5]
  simp only [X2Set, h0, h2, h3, h5]
  rw [real_inner_comm (x 0 - x 2)]; tauto

end Frame02


namespace Frame02
variable {x : Fin 7 → ℝ³}

/-- `f1Rect_of_X2` (statement identical to `Type02Assemble.lean`): three right angles of the planar
quadrilateral `2, 0, 3, 5` make it a rectangle. -/
theorem f1Rect_of_X2_pf (F : Frame02 x) (hX : X2Set x) (h0 : ⟪x 0 - x 2, x 5 - x 2⟫ = 0) :
    F1Rect x := by
  obtain ⟨hA, hB, -⟩ := hX
  have hu : x 3 - x 2 ≠ 0 := F.indep.ne_zero 0
  have ha : 0 < ⟪x 3 - x 2, x 3 - x 2⟫ := real_inner_self_pos.mpr hu
  have hg : 0 < ⟪F.e, F.e⟫ := real_inner_self_pos.mpr F.e_ne
  have hue := F.inner_u1_e
  have heu : ⟪F.e, x 3 - x 2⟫ = 0 := by rw [real_inner_comm]; exact hue
  set u := x 3 - x 2 with hu_def
  set a := ⟪u, u⟫ with ha_def
  set g := ⟪F.e, F.e⟫ with hg_def
  have e0 : x 0 - x 2 = F.S.tp • u + F.S.hp • F.e := by rw [F.x0_eq]; abel
  have e5 : x 5 - x 2 = F.S.tm • u - F.S.hm • F.e := by rw [F.x5_eq]; abel
  have e30 : x 3 - x 0 = (1 - F.S.tp) • u - F.S.hp • F.e := by
    have : x 3 - x 0 = (x 3 - x 2) - (x 0 - x 2) := by abel
    rw [this, e0, ← hu_def]; module
  have e35 : x 3 - x 5 = (1 - F.S.tm) • u + F.S.hm • F.e := by
    have : x 3 - x 5 = (x 3 - x 2) - (x 5 - x 2) := by abel
    rw [this, e5, ← hu_def]; module
  have e20 : x 2 - x 0 = -(F.S.tp • u + F.S.hp • F.e) := by rw [← e0]; abel
  have e25 : x 2 - x 5 = -(F.S.tm • u - F.S.hm • F.e) := by rw [← e5]; abel
  rw [e20, e30] at hA
  rw [e25, e35] at hB
  rw [e0, e5] at h0
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, inner_neg_left,
    inner_smul_left, inner_smul_right, hue, heu, RCLike.conj_to_real, ← ha_def, ← hg_def] at hA hB h0
  have tp0 := F.S.tp_pos; have tp1 := F.S.tp_lt; have tm0 := F.S.tm_pos; have tm1 := F.S.tm_lt
  have hp0 := F.S.hp_pos; have hm0 := F.S.hm_pos
  have key : (F.S.tp * F.S.tm - (1 - F.S.tp) * (1 - F.S.tm)) * (F.S.tp * F.S.tm * a ^ 2) = 0 := by
    have P : F.S.hp ^ 2 * g = F.S.tp * (1 - F.S.tp) * a := by linarith
    have Q : F.S.hm ^ 2 * g = F.S.tm * (1 - F.S.tm) * a := by linarith
    have R : F.S.tp * F.S.tm * a = F.S.hp * F.S.hm * g := by linarith
    have R2 : (F.S.tp * F.S.tm * a) ^ 2 = (F.S.hp ^ 2 * g) * (F.S.hm ^ 2 * g) := by
      rw [R]; ring
    rw [P, Q] at R2
    linear_combination R2
  have hsum : F.S.tp + F.S.tm = 1 := by
    have hne : F.S.tp * F.S.tm * a ^ 2 ≠ 0 := by positivity
    have := (mul_eq_zero.mp key).resolve_right hne
    linarith
  have hh : F.S.hp = F.S.hm := by
    have htm : F.S.tm = 1 - F.S.tp := by linarith
    have : (F.S.hp - F.S.hm) * (F.S.hp + F.S.hm) * g = 0 := by
      rw [htm] at hB; nlinarith [hA, hB]
    have h1 := (mul_eq_zero.mp this).resolve_right hg.ne'
    have h2 := (mul_eq_zero.mp h1).resolve_right (by linarith : 0 < F.S.hp + F.S.hm).ne'
    linarith
  refine ⟨?_, ?_⟩
  · rw [e0, e5, ← hu_def]
    have : F.S.tm = 1 - F.S.tp := by linarith
    rw [← hh, this]; module
  · rw [e0, e5]
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      inner_smul_left, inner_smul_right, hue, heu, RCLike.conj_to_real, ← ha_def, ← hg_def]
    linarith

end Frame02

/-- The image point set only depends on `x` up to relabelling: so `IsRupert` transfers along
α and β. -/
theorem isRupert_image_comp_perm (x : Fin 7 → ℝ³) (π : Equiv.Perm (Fin 7)) :
    Finset.univ.image (x ∘ π) = Finset.univ.image x := by
  ext p; simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp]
  exact ⟨fun ⟨i, h⟩ => ⟨π i, h⟩, fun ⟨i, h⟩ => ⟨π.symm i, by simpa using h⟩⟩

set_option maxHeartbeats 1000000 in
/-- **The frame from the triple-tie data at vertex `2`** (core of `frame02`, after the far ends are
identified as `x 3`, `x 4` and `e` is oriented so that `x 0` is above the plane of `x 2, x 3, x 4`).
Relabelling of `frame09_core`; facets `012`, `0134` (planar, gives `plane_up`), `3456` (gives
`plane_dn`).  `z4_neg`, `z6_rel`, `z2_pos` of CaseC09 are reused verbatim. -/
theorem frame02_core (x : Fin 7 → ℝ³) (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ)
    (hf1 : ∀ i : Fin 7, (i ∈ ({0, 2, 3, 5} : Finset (Fin 7)) → f1 (x i) = 0) ∧
      (i ∉ ({0, 2, 3, 5} : Finset (Fin 7)) → f1 (x i) < 0))
    (hf2 : ∀ i : Fin 7, (i ∈ ({1, 2, 4, 6} : Finset (Fin 7)) → f2 (x i) = 0) ∧
      (i ∉ ({1, 2, 4, 6} : Finset (Fin 7)) → f2 (x i) < 0))
    (m2 : f2 (x 3) ≤ f2 (x 0) ∧ f2 (x 3) ≤ f2 (x 5))
    (m1 : f1 (x 4) ≤ f1 (x 1) ∧ f1 (x 4) ≤ f1 (x 6))
    (e : ℝ³) (he : e ≠ 0) (h1e : f1 (x 2 + e) = 0) (h2e : f2 (x 2 + e) = 0)
    (hu1e : ⟪x 3 - x 2, e⟫ = 0) (hu2e : ⟪x 4 - x 2, e⟫ = 0)
    (par0 : ∀ c : ℝ, x 0 - x 3 ≠ c • e) (par5 : ∀ c : ℝ, x 5 - x 3 ≠ c • e)
    (par1 : ∀ c : ℝ, x 1 - x 4 ≠ c • e) (par6 : ∀ c : ℝ, x 6 - x 4 ≠ c • e)
    (a12 : 0 < ⟪x 3 - x 2, x 4 - x 2⟫) (a11 : ⟪x 4 - x 3, x 3 - x 2⟫ ≤ 0)
    (a22 : ⟪x 3 - x 4, x 4 - x 2⟫ ≤ 0) (hz : 0 < ⟪x 0 - x 2, e⟫)
    (φ012 φ0134 φ3456 : ℝ³ →ᵃ[ℝ] ℝ)
    (h012 : ∀ i : Fin 7, (i ∈ ({0, 1, 2} : Finset (Fin 7)) → φ012 (x i) = 0) ∧
      (i ∉ ({0, 1, 2} : Finset (Fin 7)) → φ012 (x i) < 0))
    (h0134 : ∀ i : Fin 7, (i ∈ ({0, 1, 3, 4} : Finset (Fin 7)) → φ0134 (x i) = 0) ∧
      (i ∉ ({0, 1, 3, 4} : Finset (Fin 7)) → φ0134 (x i) < 0))
    (h3456 : ∀ i : Fin 7, (i ∈ ({3, 4, 5, 6} : Finset (Fin 7)) → φ3456 (x i) = 0) ∧
      (i ∉ ({3, 4, 5, 6} : Finset (Fin 7)) → φ3456 (x i) < 0)) :
    Nonempty (Frame02 x) := by
  have h1v : f1 (x 2) = 0 := (hf1 2).1 (by decide)
  have h1_0 : f1 (x 0) = 0 := (hf1 0).1 (by decide)
  have h1_3 : f1 (x 3) = 0 := (hf1 3).1 (by decide)
  have h1_5 : f1 (x 5) = 0 := (hf1 5).1 (by decide)
  have n1_1 : f1 (x 1) < 0 := (hf1 1).2 (by decide)
  have n1_4 : f1 (x 4) < 0 := (hf1 4).2 (by decide)
  have n1_6 : f1 (x 6) < 0 := (hf1 6).2 (by decide)
  have h2v : f2 (x 2) = 0 := (hf2 2).1 (by decide)
  have h2_1 : f2 (x 1) = 0 := (hf2 1).1 (by decide)
  have h2_4 : f2 (x 4) = 0 := (hf2 4).1 (by decide)
  have h2_6 : f2 (x 6) = 0 := (hf2 6).1 (by decide)
  have n2_0 : f2 (x 0) < 0 := (hf2 0).2 (by decide)
  have n2_3 : f2 (x 3) < 0 := (hf2 3).2 (by decide)
  have n2_5 : f2 (x 5) < 0 := (hf2 5).2 (by decide)
  have hee : 0 < ⟪e, e⟫ := real_inner_self_pos.mpr he
  have hli := frame_indep he h1v h2v h1_3 h2_4 h1e h2e n2_3.ne n1_4.ne hu1e hu2e
  have dec := fun i => frame_decomp he h1v h2v h1_3 h2_4 h1e h2e n2_3.ne n1_4.ne hu1e hu2e (x i)
  obtain ⟨tp, htp⟩ : ∃ r : ℝ, r = f2 (x 0) / f2 (x 3) := ⟨_, rfl⟩
  obtain ⟨tm, htm⟩ : ∃ r : ℝ, r = f2 (x 5) / f2 (x 3) := ⟨_, rfl⟩
  obtain ⟨sp, hsp⟩ : ∃ r : ℝ, r = f1 (x 1) / f1 (x 4) := ⟨_, rfl⟩
  obtain ⟨sm, hsm⟩ : ∃ r : ℝ, r = f1 (x 6) / f1 (x 4) := ⟨_, rfl⟩
  obtain ⟨hp, hhp⟩ : ∃ r : ℝ, r = ⟪x 0 - x 2, e⟫ / ⟪e, e⟫ := ⟨_, rfl⟩
  obtain ⟨z5, hz5⟩ : ∃ r : ℝ, r = ⟪x 5 - x 2, e⟫ / ⟪e, e⟫ := ⟨_, rfl⟩
  obtain ⟨kp, hkp⟩ : ∃ r : ℝ, r = ⟪x 1 - x 2, e⟫ / ⟪e, e⟫ := ⟨_, rfl⟩
  obtain ⟨z6, hz6⟩ : ∃ r : ℝ, r = ⟪x 6 - x 2, e⟫ / ⟪e, e⟫ := ⟨_, rfl⟩
  have d0 : x 0 - x 2 = tp • (x 3 - x 2) + hp • e := by
    have := dec 0
    rw [h1_0, zero_div, zero_smul, add_zero, ← htp, ← hhp] at this
    exact this
  have d5 : x 5 - x 2 = tm • (x 3 - x 2) + z5 • e := by
    have := dec 5
    rw [h1_5, zero_div, zero_smul, add_zero, ← htm, ← hz5] at this
    exact this
  have d1 : x 1 - x 2 = sp • (x 4 - x 2) + kp • e := by
    have := dec 1
    rw [h2_1, zero_div, zero_smul, zero_add, ← hsp, ← hkp] at this
    exact this
  have d6 : x 6 - x 2 = sm • (x 4 - x 2) + z6 • e := by
    have := dec 6
    rw [h2_6, zero_div, zero_smul, zero_add, ← hsm, ← hz6] at this
    exact this
  have tp_pos : 0 < tp := by rw [htp]; exact div_pos_of_neg_of_neg n2_0 n2_3
  have tm_pos : 0 < tm := by rw [htm]; exact div_pos_of_neg_of_neg n2_5 n2_3
  have sp_pos : 0 < sp := by rw [hsp]; exact div_pos_of_neg_of_neg n1_1 n1_4
  have sm_pos : 0 < sm := by rw [hsm]; exact div_pos_of_neg_of_neg n1_6 n1_4
  have tp_lt : tp < 1 := by
    refine lt_of_le_of_ne ((div_le_one_of_neg n2_3).mpr m2.1 |> fun h => htp ▸ h) fun h => ?_
    apply par0 hp
    rw [h, one_smul] at d0
    rw [show x 0 - x 3 = (x 0 - x 2) - (x 3 - x 2) by abel, d0]
    abel
  have tm_lt : tm < 1 := by
    refine lt_of_le_of_ne ((div_le_one_of_neg n2_3).mpr m2.2 |> fun h => htm ▸ h) fun h => ?_
    apply par5 z5
    rw [h, one_smul] at d5
    rw [show x 5 - x 3 = (x 5 - x 2) - (x 3 - x 2) by abel, d5]
    abel
  have sp_lt : sp < 1 := by
    refine lt_of_le_of_ne ((div_le_one_of_neg n1_4).mpr m1.1 |> fun h => hsp ▸ h) fun h => ?_
    apply par1 kp
    rw [h, one_smul] at d1
    rw [show x 1 - x 4 = (x 1 - x 2) - (x 4 - x 2) by abel, d1]
    abel
  have sm_lt : sm < 1 := by
    refine lt_of_le_of_ne ((div_le_one_of_neg n1_4).mpr m1.2 |> fun h => hsm ▸ h) fun h => ?_
    apply par6 z6
    rw [h, one_smul] at d6
    rw [show x 6 - x 4 = (x 6 - x 2) - (x 4 - x 2) by abel, d6]
    abel
  have hp_pos : 0 < hp := by rw [hhp]; exact div_pos hz hee
  have ev0 : ∀ φ : ℝ³ →ᵃ[ℝ] ℝ,
      φ (x 0) = φ (x 2) + tp * (φ (x 3) - φ (x 2)) + hp * φ.linear e := by
    intro φ
    have := eval_dec φ (dec 0)
    rw [h1_0, zero_div, zero_mul, add_zero, ← htp, ← hhp] at this
    exact this
  have ev5 : ∀ φ : ℝ³ →ᵃ[ℝ] ℝ,
      φ (x 5) = φ (x 2) + tm * (φ (x 3) - φ (x 2)) + z5 * φ.linear e := by
    intro φ
    have := eval_dec φ (dec 5)
    rw [h1_5, zero_div, zero_mul, add_zero, ← htm, ← hz5] at this
    exact this
  have ev1 : ∀ φ : ℝ³ →ᵃ[ℝ] ℝ,
      φ (x 1) = φ (x 2) + sp * (φ (x 4) - φ (x 2)) + kp * φ.linear e := by
    intro φ
    have := eval_dec φ (dec 1)
    rw [h2_1, zero_div, zero_mul, add_zero, ← hsp, ← hkp] at this
    exact this
  have ev6 : ∀ φ : ℝ³ →ᵃ[ℝ] ℝ,
      φ (x 6) = φ (x 2) + sm * (φ (x 4) - φ (x 2)) + z6 * φ.linear e := by
    intro φ
    have := eval_dec φ (dec 6)
    rw [h2_6, zero_div, zero_mul, add_zero, ← hsm, ← hz6] at this
    exact this
  -- facet 012
  have A0 : φ012 (x 0) = 0 := (h012 0).1 (by decide)
  have A1 : φ012 (x 1) = 0 := (h012 1).1 (by decide)
  have A2 : φ012 (x 2) = 0 := (h012 2).1 (by decide)
  have A3 : φ012 (x 3) < 0 := (h012 3).2 (by decide)
  have A4 : φ012 (x 4) < 0 := (h012 4).2 (by decide)
  have kp_pos : 0 < kp :=
    z2_pos (a := φ012 (x 3) - φ012 (x 2)) (b := φ012 (x 4) - φ012 (x 2)) (c := φ012.linear e)
      tp_pos sp_pos hp_pos (by have := ev0 φ012; linarith) (by have := ev1 φ012; linarith)
      (by linarith) (by linarith)
  -- facets 3456, 0134
  have B2 : φ3456 (x 2) < 0 := (h3456 2).2 (by decide)
  have B3 : φ3456 (x 3) = 0 := (h3456 3).1 (by decide)
  have B4 : φ3456 (x 4) = 0 := (h3456 4).1 (by decide)
  have B5 : φ3456 (x 5) = 0 := (h3456 5).1 (by decide)
  have B6 : φ3456 (x 6) = 0 := (h3456 6).1 (by decide)
  have B0 : φ3456 (x 0) < 0 := (h3456 0).2 (by decide)
  have C0 : φ0134 (x 0) = 0 := (h0134 0).1 (by decide)
  have C1 : φ0134 (x 1) = 0 := (h0134 1).1 (by decide)
  have C2 : φ0134 (x 2) < 0 := (h0134 2).2 (by decide)
  have C3 : φ0134 (x 3) = 0 := (h0134 3).1 (by decide)
  have C4 : φ0134 (x 4) = 0 := (h0134 4).1 (by decide)
  have C5 : φ0134 (x 5) < 0 := (h0134 5).2 (by decide)
  have z5_neg' : z5 < 0 :=
    z4_neg (z4 := z5) (φ0 := φ3456 (x 2)) (a := φ3456 (x 3) - φ3456 (x 2)) (c := φ3456.linear e)
      (ψ0 := φ0134 (x 2)) (a' := φ0134 (x 3) - φ0134 (x 2)) (c' := φ0134.linear e)
      (t := tp) tm_lt hp_pos B2 C2 (by linarith) (by have := ev5 φ3456; linarith)
      (by have := ev0 φ3456; linarith) (by linarith) (by have := ev0 φ0134; rw [C0] at this; linarith)
      (by have := ev5 φ0134; linarith)
  obtain ⟨z6_neg, z6_rel'⟩ :=
    z6_rel (z6 := z6) (z4 := z5) (φ0 := φ3456 (x 2)) (a := φ3456 (x 3) - φ3456 (x 2))
      (b := φ3456 (x 4) - φ3456 (x 2)) (c := φ3456.linear e) tm_lt sm_lt B2 z5_neg'
      (by linarith) (by linarith) (by have := ev5 φ3456; linarith)
      (by have := ev6 φ3456; linarith)
  -- planarity of 0134
  have plane_up' : hp / (1 - tp) = kp / (1 - sp) := by
    have hN : 0 < -φ0134 (x 2) := neg_pos.2 C2
    have q0 : φ0134.linear e * hp = (-φ0134 (x 2)) * (1 - tp) := by
      have := ev0 φ0134; rw [C0, C3] at this; linarith
    have q1 : φ0134.linear e * kp = (-φ0134 (x 2)) * (1 - sp) := by
      have := ev1 φ0134; rw [C1, C4] at this; linarith
    have hc : φ0134.linear e ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at q0
      have : 0 < (-φ0134 (x 2)) * (1 - tp) := mul_pos hN (by linarith)
      linarith
    rw [div_eq_div_iff (by linarith) (by linarith)]
    apply mul_left_cancel₀ hc
    linear_combination (1 - sp) * q0 - (1 - tp) * q1
  have plane_dn' : (-z5) / (1 - tm) = (-z6) / (1 - sm) := by
    rw [div_eq_div_iff (by linarith) (by linarith)]
    linarith
  let S : Shape02 :=
    { tp := tp, tm := tm, sp := sp, sm := sm, hp := hp, hm := -z5, kp := kp, km := -z6
      tp_pos := tp_pos, tp_lt := tp_lt, tm_pos := tm_pos, tm_lt := tm_lt
      sp_pos := sp_pos, sp_lt := sp_lt, sm_pos := sm_pos, sm_lt := sm_lt
      hp_pos := hp_pos, hm_pos := neg_pos.2 z5_neg', kp_pos := kp_pos,
      km_pos := neg_pos.2 z6_neg, plane_up := plane_up', plane_dn := plane_dn' }
  refine ⟨{ e := e
            S := S
            e_ne := he
            indep := hli
            x0_eq := ?_
            x5_eq := ?_
            x1_eq := ?_
            x6_eq := ?_
            inner_u1_e := hu1e
            inner_u2_e := hu2e
            A12_pos := a12
            A12_le_A11 := ?_
            A12_le_A22 := ?_ }⟩
  · show x 0 = x 2 + tp • (x 3 - x 2) + hp • e
    rw [add_assoc, ← d0]; abel
  · show x 5 = x 2 + tm • (x 3 - x 2) - (-z5) • e
    rw [neg_smul, sub_neg_eq_add, add_assoc, ← d5]; abel
  · show x 1 = x 2 + sp • (x 4 - x 2) + kp • e
    rw [add_assoc, ← d1]; abel
  · show x 6 = x 2 + sm • (x 4 - x 2) - (-z6) • e
    rw [neg_smul, sub_neg_eq_add, add_assoc, ← d6]; abel
  · have : ⟪x 4 - x 3, x 3 - x 2⟫ = ⟪x 4 - x 2, x 3 - x 2⟫ - ⟪x 3 - x 2, x 3 - x 2⟫ := by
      rw [← inner_sub_left]; congr 1; abel
    have c : ⟪x 4 - x 2, x 3 - x 2⟫ = ⟪x 3 - x 2, x 4 - x 2⟫ := real_inner_comm _ _
    linarith
  · have : ⟪x 3 - x 4, x 4 - x 2⟫ = ⟪x 3 - x 2, x 4 - x 2⟫ - ⟪x 4 - x 2, x 4 - x 2⟫ := by
      rw [← inner_sub_left]; congr 1; abel
    linarith

/-- **`frame02`** (as `frame09`, CaseC09Frame.lean:649): `TriGenPar` and `¬TriGenTieO` for the faces
`0235`, `1246` at the vertex `2` of a type-02 realization give the frame `Frame02 x`.  Proof template:
`not_tieO_data`, `q1_side_contra`/`q2_side_contra` (far ends are `3` and `4`), `frame02_core`. -/
theorem frame02 {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (hgen : NoThreeCollinear (Finset.univ.image x))
    (hR : RealizesFaces x (sevenTypeFaces 1))
    (hP : TriGenPar (Finset.univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
      (({1, 2, 4, 6} : Finset (Fin 7)).image x) (x 2))
    (hT : ¬ TriGenTieO (Finset.univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
      (({1, 2, 4, 6} : Finset (Fin 7)).image x) (x 2)) : Nonempty (Frame02 x) := by
  classical
  obtain ⟨f1, f2, z1, n1, z2, n2, e, he, e1, e2, hpar, p, hp, q, hq, hpq, hmin1, hmin2, htie,
    hvp, hacute, ha1, ha2, hos1, hos2⟩ := not_tieO_data hP hT
  obtain ⟨φ012, h012⟩ := hR {0, 1, 2} (by decide)
  obtain ⟨φ256, h256⟩ := hR {2, 5, 6} (by decide)
  obtain ⟨φ0134, h0134⟩ := hR {0, 1, 3, 4} (by decide)
  obtain ⟨φ3456, h3456⟩ := hR {3, 4, 5, 6} (by decide)
  have hf1 : ∀ i : Fin 7, (i ∈ ({0, 2, 3, 5} : Finset (Fin 7)) → f1 (x i) = 0) ∧
      (i ∉ ({0, 2, 3, 5} : Finset (Fin 7)) → f1 (x i) < 0) := fun i =>
    ⟨fun hi => z1 _ (Finset.mem_image_of_mem x hi), fun hi =>
      n1 _ (Finset.mem_image_of_mem x (Finset.mem_univ i))
        (fun h => hi (hx.mem_finset_image.mp h))⟩
  have hf2 : ∀ i : Fin 7, (i ∈ ({1, 2, 4, 6} : Finset (Fin 7)) → f2 (x i) = 0) ∧
      (i ∉ ({1, 2, 4, 6} : Finset (Fin 7)) → f2 (x i) < 0) := fun i =>
    ⟨fun hi => z2 _ (Finset.mem_image_of_mem x hi), fun hi =>
      n2 _ (Finset.mem_image_of_mem x (Finset.mem_univ i))
        (fun h => hi (hx.mem_finset_image.mp h))⟩
  have h1v : f1 (x 2) = 0 := (hf1 2).1 (by decide)
  have h2v : f2 (x 2) = 0 := (hf2 2).1 (by decide)
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
  have hiS : i = 0 ∨ i = 3 ∨ i = 5 := by
    have h0 : i ≠ 2 := by
      rintro rfl
      have := hmin1 (x 0) (Finset.mem_image_of_mem x (by decide))
      have := (hf2 0).2 (by decide)
      linarith
    exact (by decide : ∀ i : Fin 7, i ∈ ({0, 2, 3, 5} : Finset (Fin 7)) → i ≠ 2 →
      (i = 0 ∨ i = 3 ∨ i = 5)) i hi h0
  have hjS : j = 1 ∨ j = 4 ∨ j = 6 := by
    have h0 : j ≠ 2 := by
      rintro rfl
      have := hmin2 (x 1) (Finset.mem_image_of_mem x (by decide))
      have := (hf1 1).2 (by decide)
      linarith
    exact (by decide : ∀ j : Fin 7, j ∈ ({1, 2, 4, 6} : Finset (Fin 7)) → j ≠ 2 →
      (j = 1 ∨ j = 4 ∨ j = 6)) j hj h0
  have h2p : f2 (x i) < 0 := (hf2 i).2 (by rcases hiS with rfl | rfl | rfl <;> decide)
  have h1q : f1 (x j) < 0 := (hf1 j).2 (by rcases hjS with rfl | rfl | rfl <;> decide)
  have h1p : f1 (x i) = 0 := (hf1 i).1 hi
  have h2q : f2 (x j) = 0 := (hf2 j).1 hj
  have hpe : ⟪x i - x 2, e⟫ = 0 := by rw [inner_sub_left]; linarith
  have hqe : ⟪x j - x 2, e⟫ = 0 := by rw [inner_sub_left]; linarith
  have hQ1 : ∀ (a b c d : Fin 7), ({0, 2, 3, 5} : Finset (Fin 7)) = {a, b, c, d} →
      ∀ y ∈ (({0, 2, 3, 5} : Finset (Fin 7)).image x), y = x a ∨ y = x b ∨ y = x c ∨ y = x d := by
    intro a b c d h y hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
    rw [h] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> simp
  have hQ2 : ∀ (a b c d : Fin 7), ({1, 2, 4, 6} : Finset (Fin 7)) = {a, b, c, d} →
      ∀ y ∈ (({1, 2, 4, 6} : Finset (Fin 7)).image x), y = x a ∨ y = x b ∨ y = x c ∨ y = x d := by
    intro a b c d h y hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
    rw [h] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> simp
  have hi3 : i = 3 := by
    rcases hiS with rfl | h | rfl
    · exact (q1_side_contra (m := x 3) (m' := x 5) he h1v h2v h1p h2q e1 e2 h2p.ne h1q.ne hpe hqe
        ((hf1 3).1 (by decide)) ((hf1 5).1 (by decide)) φ012 ((h012 2).1 (by decide))
        ((h012 0).1 (by decide)) ((h012 3).2 (by decide)) ((h012 5).2 (by decide))
        (hQ1 2 0 3 5 (by decide)) hos1).elim
    · exact h
    · exact (q1_side_contra (m := x 0) (m' := x 3) he h1v h2v h1p h2q e1 e2 h2p.ne h1q.ne hpe hqe
        ((hf1 0).1 (by decide)) ((hf1 3).1 (by decide)) φ256 ((h256 2).1 (by decide))
        ((h256 5).1 (by decide)) ((h256 0).2 (by decide)) ((h256 3).2 (by decide))
        (hQ1 2 5 0 3 (by decide)) hos1).elim
  subst hi3
  have hj4 : j = 4 := by
    rcases hjS with rfl | h | rfl
    · exact (q2_side_contra (m := x 4) (m' := x 6) he h1v h2v h1p h2q e1 e2 h2p.ne h1q.ne hpe hqe
        ((hf2 4).1 (by decide)) ((hf2 6).1 (by decide)) φ012 ((h012 2).1 (by decide))
        ((h012 1).1 (by decide)) ((h012 4).2 (by decide)) ((h012 6).2 (by decide))
        (hQ2 2 1 4 6 (by decide)) hos2).elim
    · exact h
    · exact (q2_side_contra (m := x 1) (m' := x 4) he h1v h2v h1p h2q e1 e2 h2p.ne h1q.ne hpe hqe
        ((hf2 1).1 (by decide)) ((hf2 4).1 (by decide)) φ256 ((h256 2).1 (by decide))
        ((h256 6).1 (by decide)) ((h256 1).2 (by decide)) ((h256 4).2 (by decide))
        (hQ2 2 6 1 4 (by decide)) hos2).elim
  subst hj4
  have fm1 : ∀ y : Fin 7, y ∈ ({0, 5} : Finset (Fin 7)) → ∀ c : ℝ, x y - x 3 ≠ c • e := by
    intro y hy c hc
    have hne : x 3 ≠ x y := hx.ne
      ((by decide : ∀ y : Fin 7, y ∈ ({0, 5} : Finset (Fin 7)) → 3 ≠ y) y hy)
    exact not_midPair_far1 (Finset.mem_image_of_mem x (by decide))
      (fun h => absurd (hx.mem_finset_image.mp h) (by decide)) hmin1
      (hpar (x 3) (Finset.mem_image_of_mem x (Finset.mem_univ _)) (x y)
        (Finset.mem_image_of_mem x (Finset.mem_univ _)) hne c hc)
  have fm2 : ∀ y : Fin 7, y ∈ ({1, 6} : Finset (Fin 7)) → ∀ c : ℝ, x y - x 4 ≠ c • e := by
    intro y hy c hc
    have hne : x 4 ≠ x y := hx.ne
      ((by decide : ∀ y : Fin 7, y ∈ ({1, 6} : Finset (Fin 7)) → 4 ≠ y) y hy)
    exact not_midPair_far2 (Finset.mem_image_of_mem x (by decide))
      (fun h => absurd (hx.mem_finset_image.mp h) (by decide)) hmin2
      (hpar (x 4) (Finset.mem_image_of_mem x (Finset.mem_univ _)) (x y)
        (Finset.mem_image_of_mem x (Finset.mem_univ _)) hne c hc)
  have m2 : f2 (x 3) ≤ f2 (x 0) ∧ f2 (x 3) ≤ f2 (x 5) :=
    ⟨hmin1 _ (Finset.mem_image_of_mem x (by decide)), hmin1 _ (Finset.mem_image_of_mem x (by decide))⟩
  have m1 : f1 (x 4) ≤ f1 (x 1) ∧ f1 (x 4) ≤ f1 (x 6) :=
    ⟨hmin2 _ (Finset.mem_image_of_mem x (by decide)), hmin2 _ (Finset.mem_image_of_mem x (by decide))⟩
  have hzne : ⟪x 0 - x 2, e⟫ ≠ 0 := by
    intro h0
    have d := frame_decomp he h1v h2v h1p h2q e1 e2 h2p.ne h1q.ne hpe hqe (x 0)
    rw [(hf1 0).1 (by decide), zero_div, zero_smul, add_zero, h0, zero_div, zero_smul,
      add_zero] at d
    exact hgen (x 2) (Finset.mem_image_of_mem x (Finset.mem_univ _)) (x 3)
      (Finset.mem_image_of_mem x (Finset.mem_univ _)) (x 0)
      (Finset.mem_image_of_mem x (Finset.mem_univ _)) (hx.ne (by decide)) (hx.ne (by decide))
      (hx.ne (by decide)) _ d
  have a11 : ⟪x 4 - x 3, x 3 - x 2⟫ ≤ 0 := ha1
  have a22 : ⟪x 3 - x 4, x 4 - x 2⟫ ≤ 0 := ha2
  have key : ∀ e' : ℝ³, e' ≠ 0 → f1 (x 2 + e') = 0 → f2 (x 2 + e') = 0 →
      ⟪x 3 - x 2, e'⟫ = 0 → ⟪x 4 - x 2, e'⟫ = 0 →
      (∀ c : ℝ, x 0 - x 3 ≠ c • e') → (∀ c : ℝ, x 5 - x 3 ≠ c • e') →
      (∀ c : ℝ, x 1 - x 4 ≠ c • e') → (∀ c : ℝ, x 6 - x 4 ≠ c • e') →
      0 < ⟪x 0 - x 2, e'⟫ → Nonempty (Frame02 x) :=
    fun e' he' a b c d p0 p5 p1 p6 hz' =>
      frame02_core x f1 f2 hf1 hf2 m2 m1 e' he' a b c d p0 p5 p1 p6 hacute a11 a22 hz'
        φ012 φ0134 φ3456 h012 h0134 h3456
  rcases lt_or_gt_of_ne hzne with hneg | hpos
  · have hl1 : f1 (x 2 + -e) = 0 := by
      have := aff_add f1 (x 2) (-e); have := aff_add f1 (x 2) e
      rw [map_neg] at *; linarith
    have hl2 : f2 (x 2 + -e) = 0 := by
      have := aff_add f2 (x 2) (-e); have := aff_add f2 (x 2) e
      rw [map_neg] at *; linarith
    refine key (-e) (neg_ne_zero.mpr he) hl1 hl2 (by rw [inner_neg_right, hpe, neg_zero])
      (by rw [inner_neg_right, hqe, neg_zero])
      (fun c h => fm1 0 (by decide) (-c) (by rw [h, smul_neg, neg_smul]))
      (fun c h => fm1 5 (by decide) (-c) (by rw [h, smul_neg, neg_smul]))
      (fun c h => fm2 1 (by decide) (-c) (by rw [h, smul_neg, neg_smul]))
      (fun c h => fm2 6 (by decide) (-c) (by rw [h, smul_neg, neg_smul])) ?_
    rw [inner_neg_right]; linarith
  · exact key e he e1 e2 hpe hqe (fm1 0 (by decide)) (fm1 5 (by decide)) (fm2 1 (by decide))
      (fm2 6 (by decide)) hpos

end Minimality.CaseC18
