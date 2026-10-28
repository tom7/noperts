module

public import Minimality.Type08S.Defs08

@[expose] public section

set_option autoImplicit true

/-!
# Group G4' / G5a (Q half): case Q as form U (Statement A(U) of consolidation.md section 1.1)

Frame `d; a, c, b` of case Q (`b' = d + α(a-d) + β(c-d)`, `c' = d + α₁(a-d) + β₁(b-d)`,
`a' = d + α₂(b-d) + β₂(c-d)`, far ends `α₁ < 1`, `β₂ < 1`).  At the view `u₀ = b - d` the rim is the
planar face `Q_ac = (d, a, b', c)`; `c'`, `a'` lie over its sides `da`, `cd`, and `b` over the corner
`d`.  The tilt `v = (d - a) + (d - c)` hides all three at first order (the closing is realized on both
circles, Prop. 22.2).  The depths at `u₀ + ε v` are an affine function on a convex planar quadrilateral,
which has no weak saddle unless it is constant, and it is not constant at `u₀ + εv` for small `ε > 0`:
this covers the level face (29.4: the depths at `u₀` are all equal, the tilt breaks the tie) and the
non-level face with ANY horizontal double normal (no `NoBadNormal`, no `hlev`): `levelQ` and `slideQ`
are not needed in case Q.
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality

theorem q_tilt_dets {a a' b b' c c' d : ℝ³} {α β α₁ β₁ α₂ β₂ : ℝ}
    (hb' : b' = d + α • (a - d) + β • (c - d)) (hc' : c' = d + α₁ • (a - d) + β₁ • (b - d))
    (ha' : a' = d + α₂ • (b - d) + β₂ • (c - d)) :
    det3 (d - c) (a' - c) ((d - a) + (d - c)) = α₂ * det3 (a - d) (c - d) (b - d) ∧
    det3 (a - d) (c' - d) ((d - a) + (d - c)) = β₁ * det3 (a - d) (c - d) (b - d) ∧
    det3 (a - d) (b - d) ((d - a) + (d - c)) = det3 (a - d) (c - d) (b - d) ∧
    det3 (d - c) (b - c) ((d - a) + (d - c)) = det3 (a - d) (c - d) (b - d) ∧
    det3 (a - d) (b - d) (b - d) = 0 ∧
    det3 (d - c) (b - c) (b - d) = 0 ∧
    det3 (b' - a) (b - a) (b - d) = β * det3 (a - d) (c - d) (b - d) ∧
    det3 (c - b') (b - b') (b - d) = α * det3 (a - d) (c - d) (b - d) := by
  subst hb' hc' ha'
  simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

theorem TiltSignS.strict {σ E P : ℝ} {X Y u v : ℝ³} (hσ : 0 < σ * E)
    (h : det3 X Y u = P * E) (hP : 0 < P) : TiltSignS σ X Y u v := by
  left; rw [h, show σ * (P * E) = P * (σ * E) by ring]; exact mul_pos hP hσ

theorem TiltSignS.zero {σ E P : ℝ} {X Y u v : ℝ³} (hσ : 0 < σ * E)
    (h0 : det3 X Y u = 0) (h : det3 X Y v = P * E) (hP : 0 < P) : TiltSignS σ X Y u v := by
  right; refine ⟨h0, ?_⟩
  rw [h, show σ * (P * E) = P * (σ * E) by ring]; exact mul_pos hP hσ

theorem eventually_planar_not_level {x y u v : ℝ³} (hxy : x + y ≠ 0) (hv : v = -(x + y)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪x, u + ε • v⟫ ≠ 0 ∨ ⟪y, u + ε • v⟫ ≠ 0 := by
  have hc : ∀ w : ℝ³, Continuous fun ε : ℝ => ⟪w, u + ε • v⟫ := fun w => by fun_prop
  by_cases h1 : ⟪x, u⟫ = 0
  · by_cases h2 : ⟪y, u⟫ = 0
    · have h3 : ⟪x, v⟫ ≠ 0 ∨ ⟪y, v⟫ ≠ 0 := by
        by_contra hcon
        push Not at hcon
        apply hxy
        have : ⟪x + y, x + y⟫ = 0 := by
          have e : ⟪x + y, v⟫ = 0 := by rw [inner_add_left, hcon.1, hcon.2, add_zero]
          rw [hv, inner_neg_right] at e
          linarith
        exact inner_self_eq_zero.mp this
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0 : ℝ) < ε := hε
      simp only [inner_add_right, real_inner_smul_right, h1, h2, zero_add]
      rcases h3 with h | h
      · left; exact mul_ne_zero hε'.ne' h
      · right; exact mul_ne_zero hε'.ne' h
    · have := ((hc y).continuousAt (x := 0)).eventually_ne (by simpa using h2)
      filter_upwards [this.filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))] with ε hε
      exact Or.inr hε
  · have := ((hc x).continuousAt (x := 0)).eventually_ne (by simpa using h1)
    filter_upwards [this.filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))] with ε hε
    exact Or.inl hε

/-- **Case Q as form U** (`levelQ` and `slideQ` are not needed). -/
theorem isRupert_q_formU {a a' b b' c c' d : ℝ³} {α β α₁ β₁ α₂ β₂ : ℝ}
    (hb' : b' = d + α • (a - d) + β • (c - d)) (hc' : c' = d + α₁ • (a - d) + β₁ • (b - d))
    (ha' : a' = d + α₂ • (b - d) + β₂ • (c - d))
    (hnd : [d, a, a', b, b', c, c'].Nodup) (hE : det3 (a - d) (c - d) (b - d) ≠ 0)
    (hα : 0 < α) (hβ : 0 < β) (hαβ : 1 < α + β) (hα₁ : 0 < α₁) (hα₁1 : α₁ < 1) (hβ₁ : 0 < β₁)
    (hα₂ : 0 < α₂) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  classical
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hda, hda', hdb, hdb', hdc, hdc'⟩, ⟨haa', hab, hab', hac, hac'⟩,
    ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩, ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have pαβ : 0 < α + β - 1 := by linarith
  have pQ9 : 0 < α * β₂ + β - β₂ := by
    rcases le_or_gt 1 α with h1 | h1
    · rw [show α * β₂ + β - β₂ = β + β₂ * (α - 1) by ring]
      exact add_pos_of_pos_of_nonneg hβ (mul_nonneg hβ₂.le (by linarith))
    · rw [show α * β₂ + β - β₂ = (α + β - 1) + (1 - α) * (1 - β₂) by ring]
      exact add_pos pαβ (mul_pos (by linarith) (by linarith))
  have pQ10 : 0 < -α * β₂ + α := by
    rw [show -α * β₂ + α = α * (1 - β₂) by ring]; exact mul_pos hα (by linarith)
  have pQ15 : 0 < -β * α₁ + β := by
    rw [show -β * α₁ + β = β * (1 - α₁) by ring]; exact mul_pos hβ (by linarith)
  have pQ16 : 0 < α + β * α₁ - α₁ := by
    rcases le_or_gt 1 β with h1 | h1
    · rw [show α + β * α₁ - α₁ = α + α₁ * (β - 1) by ring]
      exact add_pos_of_pos_of_nonneg hα (mul_nonneg hα₁.le (by linarith))
    · rw [show α + β * α₁ - α₁ = (α + β - 1) + (1 - α₁) * (1 - β) by ring]
      exact add_pos pαβ (mul_pos (by linarith) (by linarith))
  obtain ⟨Q0, Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11, Q12, Q13, Q14, Q15, Q16, Q17⟩ :=
    q_slide_dets hb' hc' ha'
  obtain ⟨T0, T1, T2, T3, T4, T5, T6, T7⟩ := q_tilt_dets hb' hc' ha'
  set E := det3 (a - d) (c - d) (b - d) with hEdef
  -- the orientation
  obtain ⟨σ, hσ, hσE⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ 0 < σ * E := by
    rcases lt_or_gt_of_ne hE with h | h
    · exact ⟨-1, Or.inr rfl, by linarith⟩
    · exact ⟨1, Or.inl rfl, by linarith⟩
  set V : Finset ℝ³ := insert d {a, a', b, b', c, c'} with hV
  have hmemV : ∀ z ∈ V, z = d ∨ z = a ∨ z = a' ∨ z = b ∨ z = b' ∨ z = c ∨ z = c' := by
    intro z hz; simpa [V] using hz
  have hu : b - d ≠ 0 := sub_ne_zero.mpr (Ne.symm hdb)
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  set v : ℝ³ := (d - a) + (d - c) with hv
  have hxy : (a - d) + (c - d) ≠ 0 := by
    intro h
    apply hE
    have : c - d = -(a - d) := eq_neg_of_add_eq_zero_right h
    rw [hEdef, this]
    simp only [det3_expand, PiLp.neg_apply]; ring
  have hxV : ∀ i, quad d a b' c i ∈ V := by
    intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp [V, quad_0, quad_1, quad_2, quad_3]
  refine isRupert_of_tilted_unimodal_σ V (b - d) v hu (by norm_num) (quad d a b' c) hxV σ hσ
    ?_ ?_ NWS4 isOpen_NWS4 (fun z c hc hz => hz.mul hc.ne') ?_
    (fun z hz hQ => isCyclicUnimodal_of_NWS4 hz hQ)
  · intro i j hi hj
    rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
    exacts [TiltSignS.strict hσE Q0 hβ, TiltSignS.strict hσE Q1 one_pos,
      TiltSignS.strict hσE Q2 pαβ, TiltSignS.strict hσE Q3 hβ, TiltSignS.strict hσE Q4 hα,
      TiltSignS.strict hσE Q5 pαβ, TiltSignS.strict hσE Q6 one_pos, TiltSignS.strict hσE Q7 hα]
  · intro z hz hzx i
    have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2; have h3 := hzx 3
    simp only [quad_0, quad_1, quad_2, quad_3] at h0 h1 h2 h3
    rcases hmemV z hz with h | h | h | h | h | h | h
    · exact absurd h h0
    · exact absurd h h1
    · -- a'
      rw [h]
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
      · exact TiltSignS.strict hσE Q8 hβ₂
      · exact TiltSignS.strict hσE Q9 pQ9
      · exact TiltSignS.strict hσE Q10 pQ10
      · exact TiltSignS.zero hσE Q11 T0 hα₂
    · -- b
      rw [h]
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
      · exact TiltSignS.zero hσE T4 (by rw [T2, one_mul]) one_pos
      · exact TiltSignS.strict hσE T6 hβ
      · exact TiltSignS.strict hσE T7 hα
      · exact TiltSignS.zero hσE T5 (by rw [T3, one_mul]) one_pos
    · exact absurd h h2
    · exact absurd h h3
    · -- c'
      rw [h]
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
      · exact TiltSignS.zero hσE Q13 T1 hβ₁
      · exact TiltSignS.strict hσE Q15 pQ15
      · exact TiltSignS.strict hσE Q16 pQ16
      · exact TiltSignS.strict hσE Q17 hα₁
  · -- the depths at `u₀ + ε v` have no weak saddle
    filter_upwards [eventually_planar_not_level (u := b - d) hxy (v := v) (by rw [hv]; abel)] with ε hε
    have hnws := nws4_of_planar_quad' (P₀ := d) (P₁ := a) (P₂ := b') (P₃ := c) (u := b - d + ε • v)
      hα hβ hαβ hb' (by
        rcases hε with h | h
        · left; intro h'; apply h; rw [inner_sub_left, h', sub_self]
        · right; intro h'; apply h; rw [inner_sub_left, h', sub_self])
    convert hnws using 1
    funext i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp [quad_0, quad_1, quad_2, quad_3]


/-! ### The octahedron form (case Q of `isRupert_type08_slide_core`) -/

namespace Type08Sp

/-- **G4' / G5a (Q half).**  In case Q (far ends `a`, `c` along `d b`: `F.abc'.f c < F.abc'.f a'`,
`F.a'bc.f a < F.a'bc.f c'`) the shape is Rupert with NO hypothesis on `levelQ`, `slideQ`, the tie fields
or horizontal double normals.  Hence `close_levelQ` and `close_slideQ` hold in case Q, and the case-Q
branch of `isRupert_type08_slide_core` needs neither field. -/
theorem close_caseQ {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c') (hd : IsCap F d)
    (hfc : F.abc'.f c < F.abc'.f a') (hfa : F.a'bc.f a < F.a'bc.f c') :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  classical
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd'
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := hd.ne
  have hnd7 : [d, a, a', b, b', c, c'].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    exact ⟨⟨hda, hda', hdb, hdb', hdc, hdc'⟩, ⟨haa', hab, hab', hac, hac'⟩,
      ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩, ⟨hb'c, hb'c'⟩, hcc', not_false⟩
  have hFc := F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc'
  have hFa := F.a'bc.neg a (by simp) haa' hab hac
  obtain ⟨hα, hβ, hαβ, hb'⟩ := hd.Qac_coords'
  obtain ⟨hα₁, hβ₁, -, hc'⟩ : 0 < F.a'bc.f c' / F.a'bc.f a ∧ 0 < F.ab'c.f c' / F.ab'c.f b ∧
      1 < F.a'bc.f c' / F.a'bc.f a + F.ab'c.f c' / F.ab'c.f b ∧
      c' = d + (F.a'bc.f c' / F.a'bc.f a) • (a - d) + (F.ab'c.f c' / F.ab'c.f b) • (b - d) :=
    hd.perm₂₃.Qac_coords'
  obtain ⟨hα₂, hβ₂, hαβ₂, ha'⟩ : 0 < F.ab'c.f a' / F.ab'c.f b ∧ 0 < F.abc'.f a' / F.abc'.f c ∧
      1 < F.ab'c.f a' / F.ab'c.f b + F.abc'.f a' / F.abc'.f c ∧
      a' = d + (F.ab'c.f a' / F.ab'c.f b) • (b - d) + (F.abc'.f a' / F.abc'.f c) • (c - d) :=
    hd.perm₁₂.Qac_coords'
  have hβ₂1 : F.abc'.f a' / F.abc'.f c < 1 := (div_lt_one_of_neg hFc).mpr hfc
  have hα₁1 : F.a'bc.f c' / F.a'bc.f a < 1 := (div_lt_one_of_neg hFa).mpr hfa
  exact isRupert_q_formU hb' hc' ha' hnd7 hd.det_Qac_ne hα hβ hαβ hα₁ hα₁1 hβ₁ hα₂ hβ₂ hβ₂1

end Type08Sp


/-- `Type08Gen` without the fields `levelQ`, `slideQ` (not needed, `Type08Sp.close_caseQ`). -/
structure Type08GenNoQ (a a' b b' c c' d : ℝ³) : Prop where
  tieTT' : ¬ ((∃ r : ℝ, c - a' = r • (b - d)) ∧ ∃ r : ℝ, c' - a = r • (b - d))
  routeT : (∃ r : ℝ, c - a' = r • (b - d)) → RouteT a a' b b' c c' d
  routeT' : (∃ r : ℝ, c' - a = r • (b - d)) → RouteT' a a' b b' c c' d
  touchN2 : (⟪b, c - a'⟫ = ⟪c', c - a'⟫ ∧ ⟪b', c - a'⟫ = ⟪c', c - a'⟫) →
    Touch30N2 a a' b b' c c' d
  touchT4 : (⟪c, b - d⟫ = ⟪b', b - d⟫ ∧ ⟪c', b - d⟫ = ⟪b', b - d⟫) →
    Touch30T4 a a' b b' c c' d
  touchTie : (⟪c, b - d⟫ = ⟪b', b - d⟫ ∧ ⟪c', b - d⟫ = ⟪b', b - d⟫) →
    ¬ ((∃ r : ℝ, c - a' = r • (b - d)) ∨ ∃ r : ℝ, c' - a = r • (b - d))
  slideN2c : NoBadNormal (quad c b c' b') (c - a') (b - c) ∨
    (UniOrSep (quint c d b c' b') (c - a') ∧
      NoBadNormal (quint c d b c' b') (c - a') (b' - c)) ∨
    RdCond c d b c' b' a'
  slideN2a' : NoBadNormal (quad a' b c' b') (c - a') (b - a') ∨
    NoBadNormal (quad a' b c' b') (c - a') (b' - a')
  slideT4b : NoBadNormal (quad b c' b' c) (b - d) (c - d) ∨
    (UniOrSep (quint b c' b' c a') (b - d) ∧
      NoBadNormal (quint b c' b' c a') (b - d) (a - d)) ∨
    RdCond b a' c b' c' d
  slideT4d : NoBadNormal (quad d c' b' c) (b - d) (a - d) ∨
    ((UniOrSep (quint d a c' b' c) (b - d) ∨
        (det3 (d - b) (c' - d) (b' - c) = 0 ∧
          ¬ NWS4 (quad ⟪b, b - d⟫ ⟪c', b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫) ∧
          ∀ i, ⟪quint d a c' b' c i, b - d⟫ ≠ ⟪quint d a c' b' c (i + 1), b - d⟫)) ∧
      NoBadNormal (quint d a c' b' c) (b - d) (c - d))
  flatN2 : det3 (c - b) (b' - b) (c' - b) = 0 →
      ¬ (⟪b, c - a'⟫ = ⟪b', c - a'⟫ ∧ ⟪c, c - a'⟫ = ⟪c', c - a'⟫)
  flatT4 : det3 (c - b) (b' - b) (c' - b) = 0 →
      ¬ (⟪b, b - d⟫ = ⟪b', b - d⟫ ∧ ⟪c, b - d⟫ = ⟪c', b - d⟫)

set_option maxHeartbeats 1000000 in
/-- `isRupert_type08_slide_core` (Type08Codim.lean) verbatim, with the case-Q branch replaced by
`Type08Sp.close_caseQ` (form U) and `hgen` without `levelQ`, `slideQ`. -/
theorem isRupert_type08_core_noQ {a a' b b' c c' d : ℝ³}
    (F : OctFacets a a' b b' c c') (hd : IsCap F d)
    (hN2 : F.abc'.f a' < F.abc'.f c → F.ab'c'.f a' < F.ab'c'.f c ∧
      ¬ max ⟪c, c - a'⟫ ⟪c', c - a'⟫ ≤ min ⟪b, c - a'⟫ ⟪b', c - a'⟫)
    (hT4 : F.abc'.f c < F.abc'.f a' → F.a'bc.f c' < F.a'bc.f a →
      ¬ max ⟪b, b - d⟫ ⟪b', b - d⟫ ≤ min ⟪c, b - d⟫ ⟪c', b - d⟫)
    (hT_far : F.abc'.f a' = F.abc'.f c → F.a'bc.f c' < F.a'bc.f a)
    (hT'_far : F.a'bc.f c' = F.a'bc.f a → F.abc'.f a' ≠ F.abc'.f c → F.abc'.f c < F.abc'.f a')
    (hTgood : F.abc'.f a' = F.abc'.f c ∨ F.a'bc.f c' = F.a'bc.f a →
      ¬ max ⟪b, b - d⟫ ⟪b', b - d⟫ ≤ min ⟪c, b - d⟫ ⟪c', b - d⟫)
    (hsideN2 : 0 ≤ det3 (b - c) (c' - c) (b' - c) * det3 (b - c) (c' - c) (a' - c))
    (hsideT4 : det3 (c - b) (b' - b) (a' - b) * det3 (c - b) (b' - b) (c' - b) ≤ 0)
    (hgen : Type08GenNoQ a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  classical
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd'
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := hd.ne
  have hnd7 : [d, a, a', b, b', c, c'].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    exact ⟨⟨hda, hda', hdb, hdb', hdc, hdc'⟩, ⟨haa', hab, hab', hac, hac'⟩,
      ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩, ⟨hb'c, hb'c'⟩, hcc', not_false⟩
  have hFc := F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc'
  have hFa := F.a'bc.neg a (by simp) haa' hab hac
  -- the coordinates in the frame `d; a, c, b`
  obtain ⟨hα, hβ, hαβ, hb'⟩ := hd.Qac_coords'
  obtain ⟨hα₁, hβ₁, -, hc'⟩ : 0 < F.a'bc.f c' / F.a'bc.f a ∧ 0 < F.ab'c.f c' / F.ab'c.f b ∧
      1 < F.a'bc.f c' / F.a'bc.f a + F.ab'c.f c' / F.ab'c.f b ∧
      c' = d + (F.a'bc.f c' / F.a'bc.f a) • (a - d) + (F.ab'c.f c' / F.ab'c.f b) • (b - d) :=
    hd.perm₂₃.Qac_coords'
  obtain ⟨hα₂, hβ₂, hαβ₂, ha'⟩ : 0 < F.ab'c.f a' / F.ab'c.f b ∧ 0 < F.abc'.f a' / F.abc'.f c ∧
      1 < F.ab'c.f a' / F.ab'c.f b + F.abc'.f a' / F.abc'.f c ∧
      a' = d + (F.ab'c.f a' / F.ab'c.f b) • (b - d) + (F.abc'.f a' / F.abc'.f c) • (c - d) :=
    hd.perm₁₂.Qac_coords'
  have hE := hd.det_Qac_ne
  by_cases htie₁ : F.abc'.f a' = F.abc'.f c
  · -- the tie `T` (Lemma X): `β₂ = 1`, and the far end of `Q_ab` is `c'`
    have hfc' := hT_far htie₁
    have hα₁1 : 1 < F.a'bc.f c' / F.a'bc.f a := (one_lt_div_of_neg hFa).mpr hfc'
    have hβ₂eq : F.abc'.f a' / F.abc'.f c = 1 := by rw [htie₁, div_self hFc.ne]
    have ha'1 := ha'
    rw [hβ₂eq, one_smul] at ha'1
    have hκ := t4_kappa_pos hd hb' hc' ha' hα hβ₁ hα₂ hβ₂eq.le
    exact isRupert_routeT hb' hc' ha'1 hnd7 hE hα hβ hαβ hα₁1 hβ₁ hα₂ hκ (hTgood (Or.inl htie₁))
      (fun ht => hgen.touchTie ht (Or.inl (hd.tieT_geom htie₁)))
      (hgen.routeT (hd.tieT_geom htie₁))
  by_cases htie₂ : F.a'bc.f c' = F.a'bc.f a
  · -- the tie `T'` (Lemma X): `α₁ = 1`, and the far end of `Q_bc` is `c`
    have hfc := hT'_far htie₂ htie₁
    have hβ₂1 : F.abc'.f a' / F.abc'.f c < 1 := (div_lt_one_of_neg hFc).mpr hfc
    have hα₁eq : F.a'bc.f c' / F.a'bc.f a = 1 := by rw [htie₂, div_self hFa.ne]
    have hc'1 := hc'
    rw [hα₁eq, one_smul] at hc'1
    exact isRupert_routeT' hb' hc'1 ha' hnd7 hE hα hβ hαβ hβ₁ hα₂ hβ₂ hβ₂1 hαβ₂
      (hTgood (Or.inr htie₂)) (fun ht => hgen.touchTie ht (Or.inr (hd.tieT'_geom htie₂)))
      (hgen.routeT' (hd.tieT'_geom htie₂))
  rcases lt_or_gt_of_ne htie₁ with hfar | hfc
  · -- case N2: the quad edge `a' → c` of `O`, with the cap `d` a middle of `Q_bc`
    obtain ⟨hq₂, hgood⟩ := hN2 hfar
    by_cases ht : (⟪b, c - a'⟫ = ⟪c', c - a'⟫ ∧ ⟪b', c - a'⟫ = ⟪c', c - a'⟫)
    · -- the far triple tie (Propositions 29.3, 30.4)
      exact isRupert_touchN2 F hd hfar hq₂ hgood ht (hgen.touchN2 ht)
    obtain ⟨s, δ, hs0, hs1, hδ, hdmid⟩ := hd.middle_Qbc hfar
    have e : (insert d ({a', a, c, c', b, b'} : Finset ℝ³)) = insert d {a, a', b, b', c, c'} :=
      (type08_set_perm a a' b b' c c' d).1
    rw [← e]
    rcases hgen.slideN2c with hs | hs | hR
    · exact isRupert_quad_edge_middle_slide (m := d) F.swap₁.perm₂₃ hfar hq₂ hgood
        ⟨s, δ, hs0, hs1, hδ, hdmid⟩ ⟨hda', hda, hdc, hdc', hdb, hdb'⟩ ht (Or.inl hs)
        hgen.slideN2a'
    · exact isRupert_quad_edge_middle_slide (m := d) F.swap₁.perm₂₃ hfar hq₂ hgood
        ⟨s, δ, hs0, hs1, hδ, hdmid⟩ ⟨hda', hda, hdc, hdc', hdb, hdb'⟩ ht (Or.inr hs)
        hgen.slideN2a'
    · -- `R_d` (A.10): if `K_{a'}` has no weak saddle, slide it; otherwise Lemma R0 and the
      -- two-peaked five-corner rim along `a'b'c`
      by_cases hNx : NWS4 (quad ⟪a', c - a'⟫ ⟪b, c - a'⟫ ⟪c', c - a'⟫ ⟪b', c - a'⟫)
      · exact isRupert_quad_edge_middle_sel (m := d) F.swap₁.perm₂₃ hfar hq₂
          ⟨s, δ, hs0, hs1, hδ, hdmid⟩ ⟨hda', hda, hdc, hdc', hdb, hdb'⟩
          (Or.inr ⟨hNx, hgen.slideN2a'⟩)
      have hNy : NWS4 (quad ⟪c, c - a'⟫ ⟪b, c - a'⟫ ⟪c', c - a'⟫ ⟪b', c - a'⟫) := by
        by_contra hN
        exact hNx (nws4_closing_oct F.swap₁.perm₂₃ hfar hq₂ hN hgood ht)
      exact isRupert_quad_edge_middle_rdCond F.swap₁.perm₂₃ hfar hq₂ ⟨s, δ, hs0, hs1, hδ, hdmid⟩
        ⟨F.abc'.f, F.abc'.N, F.abc'.hN, hd.abc', F.abc'.hQ, F.abc'.hR,
          F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc',
          F.abc'.neg b' (by simp) (Ne.symm hab') (Ne.symm hbb') hb'c'⟩
        hsideN2 hNy hNx hR
  · have hβ₂1 : F.abc'.f a' / F.abc'.f c < 1 := (div_lt_one_of_neg hFc).mpr hfc
    by_cases hfa : F.a'bc.f a < F.a'bc.f c'
    · -- case Q: the far ends are `a` and `c`
      have hα₁1 : F.a'bc.f c' / F.a'bc.f a < 1 := (div_lt_one_of_neg hFa).mpr hfa
      exact Type08Sp.close_caseQ F hd hfc hfa
    · -- case T4: the far ends are `c'` and `c`
      have hfc' : F.a'bc.f c' < F.a'bc.f a := lt_of_le_of_ne (not_lt.mp hfa) htie₂
      have hα₁1 : 1 < F.a'bc.f c' / F.a'bc.f a := (one_lt_div_of_neg hFa).mpr hfc'
      have hκ := t4_kappa_pos hd hb' hc' ha' hα hβ₁ hα₂ hβ₂1.le
      have hgood := hT4 hfc hfc'
      by_cases ht : (⟪c, b - d⟫ = ⟪b', b - d⟫ ∧ ⟪c', b - d⟫ = ⟪b', b - d⟫)
      · -- the far triple tie (Propositions 29.3, 30.4)
        exact isRupert_touchT4 F hd hfc hfc' hgood ht (hgen.touchT4 ht)
      have hsd := t4d_slide_of_par hb' hc' hdb hd.det_Qac_ne hα hα₁1 hβ₁ hgood hgen.slideT4d
      rcases hgen.slideT4b with hs | hs | hR
      · exact isRupert_t4_slide hb' hc' ha' hnd7 hd.det_Qac_ne hα hβ hαβ hα₁1 hβ₁ hα₂ hβ₂ hβ₂1
          hαβ₂ hκ hgood ht (Or.inl hs) hsd
      · exact isRupert_t4_slide hb' hc' ha' hnd7 hd.det_Qac_ne hα hβ hαβ hα₁1 hβ₁ hα₂ hβ₂ hβ₂1
          hαβ₂ hκ hgood ht (Or.inr hs) hsd
      · -- `R_d` (A.10): if `K_d` has no weak saddle, slide it; otherwise Lemma R0 and the
        -- two-peaked five-corner rim along `Q_ab`
        by_cases hNd : NWS4 (quad ⟪d, b - d⟫ ⟪c', b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫)
        · rcases hsd with hs | ⟨hu5, hs5⟩
          · exact isRupert_t4_sel hb' hc' ha' hnd7 hd.det_Qac_ne hα hβ hαβ hα₁1 hβ₁ hα₂ hβ₂
              hβ₂1 hαβ₂ hκ (Or.inr ⟨hNd, hs⟩)
          · exact isRupert_t4d_five hb' hc' ha' hnd7 hd.det_Qac_ne hα hβ hαβ hα₁1 hβ₁ hα₂ hβ₂
              hβ₂1 hκ hu5 hs5
        have hNb : NWS4 (quad ⟪b, b - d⟫ ⟪c', b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫) := by
          by_contra hN
          exact hNd (t4_closing hb' hc' ha' hdb hd.det_Qac_ne hα hβ (by linarith) hβ₁ hκ hgood
            ht hN)
        exact isRupert_t4b_rdCond hb' hc' ha' hdb hd.det_Qac_ne hα hβ hα₁1 hβ₁ hβ₂ hβ₂1 hαβ₂ hκ
          ⟨F.a'b'c.f, F.a'b'c.N, F.a'b'c.hN, F.a'b'c.hP, F.a'b'c.hR, F.a'b'c.hQ,
            F.a'b'c.neg b (by simp) (Ne.symm ha'b) hbb' hbc,
            F.a'b'c.neg c' (by simp) (Ne.symm ha'c') (Ne.symm hb'c') (Ne.symm hcc')⟩
          hsideT4 hNb hNd hR


theorem isRupert_type08_noQ_normalized {a a' b b' c c' d : ℝ³} (h : IsOctahedron a a' b b' c c')
    (F : OctFacets a a' b b' c c') (hd : IsCap F d) (G : GaleData a a' b b' c c')
    (hκa : 0 < galeD G.l G.m a a') (hκb : 0 < galeD G.l G.m b b')
    (hκc : galeD G.l G.m c c' ≠ 0) (hU : galeD G.l G.m b c < 0)
    (hgen : Type08GenNoQ a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨-, -, -, -, -, -, -, ha'b, ha'b', -, -, -, -, hac, hac'⟩ :=
    type08_signs F G hκa hκb hκc hU
  have hsides := type08_rd_sides h G hκa ha'b ha'b' hac hac'
  exact isRupert_type08_core_noQ F hd (fun hfar => type08_lemma7 F G hκa hκb hκc hU hfar)
    (fun _ _ => type08_t4_not_bad h F hd G hκa hκb hκc hU hd.t4_opp)
    (type08_T_far F G hκb hκc hU) (type08_T'_far F G hκb hκc hU)
    (fun _ => type08_t4_not_bad h F hd G hκa hκb hκc hU hd.t4_opp) hsides.1.le hsides.2.le hgen

namespace Type08Sp

theorem noQ_of_FP {a a' b b' c c' d : ℝ³}
    (h : ∀ f, f ≠ .levelQ → f ≠ .slideQ → FP a a' b b' c c' d f) :
    Type08GenNoQ a a' b b' c c' d :=
  ⟨h .tieTT (by simp) (by simp), h .routeT (by simp) (by simp), h .routeT' (by simp) (by simp),
   h .touchN2 (by simp) (by simp), h .touchT4 (by simp) (by simp), h .touchTie (by simp) (by simp),
   h .slideN2c (by simp) (by simp), h .slideN2a' (by simp) (by simp),
   h .slideT4b (by simp) (by simp), h .slideT4d (by simp) (by simp),
   h .flatN2 (by simp) (by simp), h .flatT4 (by simp) (by simp)⟩

/-- **G4'**: the level face (29.4) and, with `close_slideQ`, the whole case Q, by form U: the
hypotheses `hT`, `hT'`, `hfail` are not used, and neither is the field `slideQ`. -/
theorem close_levelQ {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (hT : ¬ IsT a' b c d) (hT' : ¬ IsT' a b c' d)
    (hfail : ¬ FP a a' b b' c c' d .levelQ)
    (hothers : ∀ f, f ≠ .levelQ → FP a a' b b' c c' d f) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) :=
  isRupert_type08_noQ_normalized N.F.isOctahedron N.F N.hd N.G N.hκa N.hκb N.hκc N.hU
    (noQ_of_FP fun f h1 _ => hothers f h1)

end Type08Sp

end Minimality
