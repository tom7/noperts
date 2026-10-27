module

public import Minimality.CaseC18Final
public import Minimality.SlideRim

@[expose] public section

/-!
# Type 18: `V`'s rim slid along `F1`'s circle 
(`FEWER-FACES-PROOFS.md` Theorem 27.41, Steps 1-3; stage M5 of `lean2741/PLAN.md`)

Plan.  `CaseC18Special` excludes "`V` (resp. `V^Z`) has a horizontal double normal at its view
`uV`".  Instead of excluding that, slide the view of `V` along the circle of `F1`
(`uV + η e1`, `e1 = m1- - m1+`, `η → 0⁺`).  At `uV` all the strict tests of `vN4_rupert` /
`vNt_rupert` hold, so they hold at the slid views, and the rim stays robustly unimodal
(`Q4_ev_strict`, `robust_quad_of_nws`; for the triangle, unless the three depths are equal).
What remains is the horizontal double normals of the rim at the slid views: by
`eventually_noHDNRim_slide` (M3, `SlideRim.lean`) there are none for small `η` as soon as no
double normal of the rim in space is perpendicular to `uV` and `e1` (`NoPersistHDN`).  Lemma 27.38
(a) with Lemma 27.36, 27.40 classifies those persistent pairs: they are the class `H_F1`, the
perpendicular from `xb` to the line of `F1`'s side (foot in the open chord), and that happens
exactly on one hyperplane of the metric,
`A12 (h+ + h-) = A11 (t+ h- + t- h+)` (`Frame18.ClassH`).
-/

namespace Minimality.CaseC18

open Finset Filter Minimality.CaseC09 Minimality.CaseC20
open scoped RealInnerProductSpace Topology

namespace Shape18
variable (S : Shape18)

/-- The slide direction `m1- - m1+` of `F1`'s circle, in frame coordinates (`y = 0`).  The sign
is irrelevant for `NoPersistHDN` (it only uses `⟪·, e⟫ = 0`). -/
def eF1 : C3 := ⟨S.tm - S.tp, 0, -S.hm - S.hp⟩

end Shape18

namespace Frame18
variable {x : Fin 7 → ℝ³} (F : Frame18 x)

/-- **Class `H_F1` (Proposition 27.38 (a), corner `xb`)**: the hyperplane
`Φ(m1+, m1-; xb) = 0`, i.e. `A12 (h+ + h-) = A11 (t+ h- + t- h+)`: the `G`-perpendicular from `xb`
to the line `m1+ m1-` is horizontal at the views of `F1`'s circle. -/
def ClassH : Prop :=
  F.a12 * (F.S.hp + F.S.hm) = F.a11 * (F.S.tp * F.S.hm + F.S.tm * F.S.hp)

/-- `V` and `V^Z` give the same hyperplane (Proposition 27.39, type 18): the Z-image of a frame
has the same `x 3 - x 5`, `x 4 - x 5`, and `t±, h±` exchanged. -/
theorem classH_zFrame_iff : F.zFrame.ClassH ↔ F.ClassH := by
  have e12 : F.zFrame.a12 = F.a12 := rfl
  have e11 : F.zFrame.a11 = F.a11 := rfl
  unfold ClassH
  rw [e12, e11]
  show F.a12 * (F.S.hm + F.S.hp) = F.a11 * (F.S.tm * F.S.hp + F.S.tp * F.S.hm) ↔ _
  constructor <;> intro h <;> linarith

/-! ### (i) The persistent-pair classification -/

/-- The `y`-coordinate (frame) of the rim corners `m1+, m1-, m2-, xb`. -/
noncomputable def yv (v : Fin 7) : ℝ := if v = 2 then F.S.sm else if v = 4 then 1 else 0

theorem yv_facts (v : Fin 7) (hv : v = 0 ∨ v = 6 ∨ v = 2 ∨ v = 4) :
    0 ≤ F.yv v ∧ F.yv v ≤ 1 ∧ (F.yv v = 1 → v = 4) ∧ (F.yv v = 0 → v = 0 ∨ v = 6) := by
  have h1 := F.S.sm_pos; have h2 := F.S.sm_lt
  have e0 : F.yv 0 = 0 := by simp [yv]
  have e6 : F.yv 6 = 0 := by simp [yv]
  have e2 : F.yv 2 = F.S.sm := by simp [yv]
  have e4 : F.yv 4 = 1 := by simp [yv]
  rcases hv with rfl | rfl | rfl | rfl
  · rw [e0]; exact ⟨le_rfl, zero_le_one, fun h => by norm_num at h, fun _ => Or.inl rfl⟩
  · rw [e6]; exact ⟨le_rfl, zero_le_one, fun h => by norm_num at h, fun _ => Or.inr rfl⟩
  · rw [e2]; exact ⟨h1.le, h2.le, fun h => absurd h h2.ne, fun h => absurd h h1.ne'⟩
  · rw [e4]; exact ⟨zero_le_one, le_rfl, fun _ => rfl, fun h => by norm_num at h⟩

/-- A vector perpendicular to the view `uV` and to the slide direction is perpendicular to
`u1 = xa - v` and to `e` (the determinant is `Vp + k+ t+ > 0`, i.e. (G1)). -/
theorem persist_perp (hV : 0 < F.S.Vp) (w : ℝ³) (h1 : ⟪w, F.toFrame7.fvC F.S.uV⟫ = 0)
    (h2 : ⟪w, F.toFrame7.fvC F.S.eF1⟫ = 0) : ⟪w, x 3 - x 5⟫ = 0 ∧ ⟪w, F.e⟫ = 0 := by
  have hu : F.toFrame7.fvC F.S.uV = (-F.S.sp * F.S.tp + F.S.tp) • (x 3 - x 5) +
      (0 : ℝ) • (x 4 - x 5) + (-F.S.hp * F.S.sp + F.S.hp - F.S.kp) • F.e := rfl
  have he : F.toFrame7.fvC F.S.eF1 = (F.S.tm - F.S.tp) • (x 3 - x 5) +
      (0 : ℝ) • (x 4 - x 5) + (-F.S.hm - F.S.hp) • F.e := rfl
  rw [hu, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
    inner_smul_right] at h1
  rw [he, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
    inner_smul_right] at h2
  have hpos : 0 < F.S.Vp + F.S.kp * F.S.tp := by
    have := mul_pos F.S.kp_pos F.S.tp_pos; linarith
  have hd : F.S.Vp + F.S.kp * F.S.tp ≠ 0 := hpos.ne'
  unfold Shape18.Vp at hd
  constructor
  · apply mul_left_cancel₀ hd
    linear_combination (-(-F.S.hm - F.S.hp)) * h1 + (-F.S.hp * F.S.sp + F.S.hp - F.S.kp) * h2
  · apply mul_left_cancel₀ hd
    linear_combination (-(-F.S.sp * F.S.tp + F.S.tp)) * h2 + (F.S.tm - F.S.tp) * h1

theorem persist_nu_ne (w : ℝ³) (hw : w ≠ 0) (hA : ⟪w, x 3 - x 5⟫ = 0) (hB : ⟪w, F.e⟫ = 0) :
    ⟪w, x 4 - x 5⟫ ≠ 0 := by
  intro h0
  obtain ⟨p, hp⟩ := F.toFrame7.decomp w
  apply hw
  have h : ⟪w, F.toFrame7.fvC p⟫ = 0 := by
    show ⟪w, p.x • (x 3 - x 5) + p.y • (x 4 - x 5) + p.z • F.e⟫ = 0
    rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
      inner_smul_right, hA, h0, hB]; ring
  rw [← hp] at h
  exact inner_self_eq_zero.mp h

theorem persist_vals (w : ℝ³) (hA : ⟪w, x 3 - x 5⟫ = 0) (hB : ⟪w, F.e⟫ = 0) (v : Fin 7)
    (hv : v = 0 ∨ v = 6 ∨ v = 2 ∨ v = 4) :
    ⟪w, x v - x 5⟫ = F.yv v * ⟪w, x 4 - x 5⟫ := by
  rcases hv with rfl | rfl | rfl | rfl
  · have : x 0 - x 5 = F.S.tp • (x 3 - x 5) + F.S.hp • F.e := by rw [F.x0_eq]; abel
    rw [this, inner_add_right, inner_smul_right, inner_smul_right, hA, hB]; simp [yv]
  · have : x 6 - x 5 = F.S.tm • (x 3 - x 5) - F.S.hm • F.e := by rw [F.x6_eq]; abel
    rw [this, inner_sub_right, inner_smul_right, inner_smul_right, hA, hB]; simp [yv]
  · have : x 2 - x 5 = F.S.sm • (x 4 - x 5) - F.S.km • F.e := by rw [F.x2_eq]; abel
    rw [this, inner_sub_right, inner_smul_right, inner_smul_right, hB]; simp [yv]
  · simp [yv]

/-- The core of the classification, for a positive `ν = ⟪Y' - Y, u2⟫`: the double normal runs from
the chord `[m1+, m1-]` to `xb`, and its perpendicularity to `e` is `ClassH`. -/
theorem persist_core {k : ℕ} [NeZero k] (c : ZMod k → Fin 7)
    (hcr : ∀ i, c i = 0 ∨ c i = 6 ∨ c i = 2 ∨ c i = 4)
    (h0 : ∃ m, c m = 0) (h4 : ∃ m, c m = 4) (hV : 0 < F.S.Vp)
    (i j : ZMod k) (Y Y' : ℝ³) (hY : Y ∈ segment ℝ (x (c i)) (x (c (i + 1))))
    (hY' : Y' ∈ segment ℝ (x (c j)) (x (c (j + 1)))) (hne : Y' ≠ Y)
    (hu : ⟪Y' - Y, F.toFrame7.fvC F.S.uV⟫ = 0) (he : ⟪Y' - Y, F.toFrame7.fvC F.S.eF1⟫ = 0)
    (hext : ∀ m, ⟪Y' - Y, x (c m) - Y'⟫ ≤ 0 ∧ ⟪Y - Y', x (c m) - Y⟫ ≤ 0)
    (hν : 0 < ⟪Y' - Y, x 4 - x 5⟫) : F.ClassH := by
  obtain ⟨hA, hB⟩ := F.persist_perp hV (Y' - Y) hu he
  set w := Y' - Y with hw
  set ν := ⟪w, x 4 - x 5⟫ with hνdef
  have vals := F.persist_vals w hA hB
  have conv : ∀ a b : ℝ, ∀ P Q : ℝ³, a + b = 1 →
      ⟪w, a • P + b • Q - x 5⟫ = a * ⟪w, P - x 5⟫ + b * ⟪w, Q - x 5⟫ := by
    intro a b P Q h
    have hb : b = 1 - a := by linarith
    subst hb
    have : a • P + (1 - a) • Q - x 5 = a • (P - x 5) + (1 - a) • (Q - x 5) := by module
    rw [this, inner_add_right, inner_smul_right, inner_smul_right]
  have sub_in : ∀ P Q : ℝ³, ⟪w, P - Q⟫ = ⟪w, P - x 5⟫ - ⟪w, Q - x 5⟫ := by
    intro P Q; rw [← inner_sub_right]; congr 1; abel
  -- the double normal ends at `xb`
  obtain ⟨α', β', hα', hβ', hαβ', hY'eq⟩ := hY'
  obtain ⟨m4, hm4⟩ := h4
  obtain ⟨m0, hm0⟩ := h0
  have hT' : ⟪w, Y' - x 5⟫ = α' * (F.yv (c j) * ν) + β' * (F.yv (c (j + 1)) * ν) := by
    rw [← hY'eq, conv α' β' _ _ hαβ', vals _ (hcr j), vals _ (hcr (j + 1))]
  have hext4 := (hext m4).1
  rw [sub_in, vals _ (hcr m4), hm4] at hext4
  have hy4 : F.yv 4 = 1 := by simp [yv]
  rw [hy4] at hext4
  obtain ⟨a0, a1, a2, a3⟩ := F.yv_facts (c j) (hcr j)
  obtain ⟨b0, b1, b2, b3⟩ := F.yv_facts (c (j + 1)) (hcr (j + 1))
  have hq : α' * (1 - F.yv (c j)) + β' * (1 - F.yv (c (j + 1))) ≤ 0 := by
    by_contra hh
    push Not at hh
    nlinarith [mul_pos hν hh]
  have hq1 : α' * (1 - F.yv (c j)) = 0 := by
    nlinarith [mul_nonneg hα' (sub_nonneg.2 a1), mul_nonneg hβ' (sub_nonneg.2 b1)]
  have hq2 : β' * (1 - F.yv (c (j + 1))) = 0 := by
    nlinarith [mul_nonneg hα' (sub_nonneg.2 a1), mul_nonneg hβ' (sub_nonneg.2 b1)]
  have hY'4 : Y' = x 4 := by
    rw [← hY'eq]
    have e1 : α' • x (c j) = α' • x 4 := by
      rcases mul_eq_zero.mp hq1 with h | h
      · rw [h, zero_smul, zero_smul]
      · rw [a2 (by linarith)]
    have e2 : β' • x (c (j + 1)) = β' • x 4 := by
      rcases mul_eq_zero.mp hq2 with h | h
      · rw [h, zero_smul, zero_smul]
      · rw [b2 (by linarith)]
    rw [e1, e2, ← add_smul, hαβ', one_smul]
  -- the double normal starts on the chord
  obtain ⟨α, β, hα, hβ, hαβ, hYeq⟩ := hY
  have hT : ⟪w, Y - x 5⟫ = α * (F.yv (c i) * ν) + β * (F.yv (c (i + 1)) * ν) := by
    rw [← hYeq, conv α β _ _ hαβ, vals _ (hcr i), vals _ (hcr (i + 1))]
  have hext0 := (hext m0).2
  have hneg : Y - Y' = -w := by rw [hw]; abel
  rw [hneg, inner_neg_left, sub_in, vals _ (hcr m0), hm0] at hext0
  have hy0 : F.yv 0 = 0 := by simp [yv]
  rw [hy0] at hext0
  obtain ⟨c0, c1, c2, c3⟩ := F.yv_facts (c i) (hcr i)
  obtain ⟨d0, d1, d2, d3⟩ := F.yv_facts (c (i + 1)) (hcr (i + 1))
  have hsum : ν * (α * F.yv (c i) + β * F.yv (c (i + 1))) ≤ 0 := by
    nlinarith [hext0, hT]
  have hsum' : α * F.yv (c i) + β * F.yv (c (i + 1)) ≤ 0 := by
    by_contra hh
    push Not at hh
    nlinarith [mul_pos hν hh]
  have hz1 : α * F.yv (c i) = 0 := by
    linarith [mul_nonneg hα c0, mul_nonneg hβ d0]
  have hz2 : β * F.yv (c (i + 1)) = 0 := by
    linarith [mul_nonneg hα c0, mul_nonneg hβ d0]
  have split0 : ∀ (a : ℝ) (v : Fin 7), 0 ≤ a → (v = 0 ∨ v = 6 ∨ v = 2 ∨ v = 4) →
      a * F.yv v = 0 → ∃ p q : ℝ, 0 ≤ p ∧ 0 ≤ q ∧ p + q = a ∧ a • x v = p • x 0 + q • x 6 := by
    intro a v ha hv hz
    rcases mul_eq_zero.mp hz with h | h
    · exact ⟨0, 0, le_rfl, le_rfl, by linarith, by rw [h]; simp⟩
    · rcases (F.yv_facts v hv).2.2.2 h with rfl | rfl
      · exact ⟨a, 0, ha, le_rfl, by ring, by simp⟩
      · exact ⟨0, a, le_rfl, ha, by ring, by simp⟩
  obtain ⟨p1, q1, hp1, hq1', hpq1, hv1⟩ := split0 α (c i) hα (hcr i) hz1
  obtain ⟨p2, q2, hp2, hq2', hpq2, hv2⟩ := split0 β (c (i + 1)) hβ (hcr (i + 1)) hz2
  obtain ⟨a, ha⟩ : ∃ a, a = p1 + p2 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = q1 + q2 := ⟨_, rfl⟩
  have hab : a + b = 1 := by rw [ha, hb]; linarith
  have hYab : Y = a • x 0 + b • x 6 := by
    calc Y = α • x (c i) + β • x (c (i + 1)) := hYeq.symm
      _ = (p1 • x 0 + q1 • x 6) + (p2 • x 0 + q2 • x 6) := by rw [hv1, hv2]
      _ = a • x 0 + b • x 6 := by rw [ha, hb]; module
  have hb' : b = 1 - a := by linarith
  subst hb'
  have hwexp : w = (x 4 - x 5) - a • (F.S.tp • (x 3 - x 5) + F.S.hp • F.e) -
      (1 - a) • (F.S.tm • (x 3 - x 5) - F.S.hm • F.e) := by
    rw [hw, hY'4, hYab, F.x0_eq, F.x6_eq]; module
  have i1 : ⟪F.e, x 3 - x 5⟫ = 0 := by rw [real_inner_comm]; exact F.inner_u1_e
  have i2 : ⟪x 4 - x 5, x 3 - x 5⟫ = F.a12 := real_inner_comm (x 3 - x 5) (x 4 - x 5)
  have i3 : ⟪x 3 - x 5, x 3 - x 5⟫ = F.a11 := rfl
  have i4 : ⟪F.e, F.e⟫ = F.gg := rfl
  have hgg := F.g_pos
  have hB' := hB
  have hA' := hA
  rw [hwexp] at hB' hA'
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left, F.inner_u1_e,
    F.inner_u2_e, i1, i2, i3, i4] at hB' hA'
  have E2 : a * F.S.hp = (1 - a) * F.S.hm := by
    have : F.gg * ((1 - a) * F.S.hm - a * F.S.hp) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hgg.ne'
    · linarith
  unfold ClassH
  linear_combination (F.S.hp + F.S.hm) * hA' + F.a11 * (F.S.tp - F.S.tm) * E2

/-- The classification for a rim whose corners are among `m1+, m1-, m2-, xb`, containing `m1+`
and `xb`. -/
theorem persist_gen {k : ℕ} [NeZero k] (c : ZMod k → Fin 7)
    (hcr : ∀ i, c i = 0 ∨ c i = 6 ∨ c i = 2 ∨ c i = 4)
    (h0 : ∃ m, c m = 0) (h4 : ∃ m, c m = 4) (hV : 0 < F.S.Vp) :
    NoPersistHDN (fun i => x (c i)) (F.toFrame7.fvC F.S.uV) (F.toFrame7.fvC F.S.eF1) ∨
      F.ClassH := by
  by_cases hH : F.ClassH
  · exact Or.inr hH
  left
  intro i j Y hY Y' hY' hne hu he hext
  obtain ⟨hA, hB⟩ := F.persist_perp hV (Y' - Y) hu he
  have hν := F.persist_nu_ne (Y' - Y) (sub_ne_zero.2 hne) hA hB
  rcases lt_or_gt_of_ne hν with hneg | hpos
  · refine hH (F.persist_core c hcr h0 h4 hV j i Y' Y hY' hY hne.symm ?_ ?_ ?_ ?_)
    · rw [← neg_sub, inner_neg_left, hu, neg_zero]
    · rw [← neg_sub, inner_neg_left, he, neg_zero]
    · intro m; exact (hext m).symm
    · rw [← neg_sub, inner_neg_left]; linarith
  · exact hH (F.persist_core c hcr h0 h4 hV i j Y Y' hY hY' hne hu he hext hpos)

/-- **Persistent double normals of `V`'s 4-cycle rim** `(m1+, m1-, m2-, xb) = (0, 6, 2, 4)` along
`F1`'s circle (Steps 2-3 of 27.41, rim `N4`): none, or the hyperplane `ClassH`.  The hypotheses are
those of `vN4_rupert` (non-realizable `V`, rim a 4-cycle: `D2 < 0`); they give `c_u = Vp + k+ t+ > 0`
(the view is not along `F1`'s chord, (G1)), `u_y = 0`, and the 4-cycle's ccw tests. -/
theorem noPersistHDN_or_classH_N4 (hx : Function.Injective x) (hD2 : F.S.D2p < 0)
    (hV : 0 < F.S.Vp) (hA1z : 0 < F.S.hm * F.S.tp - F.S.hp * (1 - F.S.tm))
    (hA1 : 0 < F.S.hp * F.S.tm - F.S.hm * (1 - F.S.tp)) :
    NoPersistHDN (fun i : ZMod 4 => x (quad 0 6 2 4 i)) (F.toFrame7.fvC F.S.uV)
        (F.toFrame7.fvC F.S.eF1) ∨ F.ClassH := by
  refine F.persist_gen (quad 0 6 2 4) (fun i => ?_) ⟨0, by simp [quad_0]⟩ ⟨3, by simp [quad_3]⟩ hV
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp [quad_0, quad_1, quad_2, quad_3]

/-- **Persistent double normals of `V`'s triangle rim** `(m1+, m1-, xb) = (0, 6, 4)` along `F1`'s
circle (rim `Nt`, `D2 > 0`): none, or the hyperplane `ClassH`.  The corner pairs
`m1± - xb`, `m1+ - m1-` have different `z`, so there is no tie to discuss. -/
theorem noPersistHDN_or_classH_Nt (hx : Function.Injective x) (hD2 : 0 < F.S.D2p)
    (hV : 0 < F.S.Vp) (hA1z : 0 < F.S.hm * F.S.tp - F.S.hp * (1 - F.S.tm))
    (hA1 : 0 < F.S.hp * F.S.tm - F.S.hm * (1 - F.S.tp)) :
    NoPersistHDN (fun i : ZMod 3 => x (tri 0 6 4 i)) (F.toFrame7.fvC F.S.uV)
        (F.toFrame7.fvC F.S.eF1) ∨ F.ClassH := by
  refine F.persist_gen (tri 0 6 4) (fun i => ?_) ⟨0, by simp [tri_0]⟩ ⟨2, by simp [tri_2]⟩ hV
  rcases zmod3_cases i with rfl | rfl | rfl <;> simp [tri_0, tri_1, tri_2]

end Frame18

/-! ### Slide tests -/

theorem Frame7.GG_slide {x : Fin 7 → ℝ³} (F : Frame7 x) (P u e : C3) (η : ℝ) :
    F.GG P (C3.slide u e η) = F.GG P u + η * F.GG P e := by
  simp only [Frame7.GG, Gf, C3.slide]; ring


theorem mid_slide_gen (px pz qx qz mx mz ux uz ex ez : ℝ)
    (hD : (qx - px) * uz - (qz - pz) * ux ≠ 0)
    (h : ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧ mx = px + s * (qx - px) + δ * ux ∧
      mz = pz + s * (qz - pz) + δ * uz) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      mx = px + s * (qx - px) + δ * (ux + η * ex) ∧ mz = pz + s * (qz - pz) + δ * (uz + η * ez) := by
  obtain ⟨s0, δ0, hs0, hs1, hδ0, hx, hz⟩ := h
  set D : ℝ → ℝ := fun η => (qx - px) * (uz + η * ez) - (qz - pz) * (ux + η * ex) with hDdef
  set Sn : ℝ → ℝ := fun η => (mx - px) * (uz + η * ez) - (mz - pz) * (ux + η * ex) with hSdef
  set Dn : ℝ := (qx - px) * (mz - pz) - (qz - pz) * (mx - px) with hDn
  have hcD : Continuous D := by simp only [hDdef]; fun_prop
  have hcS : Continuous Sn := by simp only [hSdef]; fun_prop
  have hD0 : D 0 ≠ 0 := by simpa [hDdef] using hD
  have hS0 : Sn 0 / D 0 = s0 := by
    rw [div_eq_iff hD0]
    simp only [hSdef, hDdef, zero_mul, add_zero]
    rw [hx, hz]; ring
  have hδ0' : Dn / D 0 = δ0 := by
    rw [div_eq_iff hD0]
    simp only [hDdef, hDn, zero_mul, add_zero]
    rw [hx, hz]; ring
  have c1 : ContinuousAt (fun η => Sn η / D η) 0 := hcS.continuousAt.div hcD.continuousAt hD0
  have c2 : ContinuousAt (fun η => Dn / D η) 0 := continuousAt_const.div hcD.continuousAt hD0
  have e1 := c1.eventually_mem (Ioo_mem_nhds (a := (0:ℝ)) (b := 1) (by rw [hS0]; exact hs0)
    (by rw [hS0]; exact hs1))
  have e2 := c2.eventually_ne (by rw [hδ0']; exact hδ0)
  have e3 := hcD.continuousAt.eventually_ne hD0
  filter_upwards [(e1.and (e2.and e3)).filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))]
    with η ⟨hη1, hη2, hη3⟩
  refine ⟨Sn η / D η, Dn / D η, hη1.1, hη1.2, hη2, ?_, ?_⟩
  · field_simp
    simp only [hSdef, hDdef, hDn]; ring
  · field_simp
    simp only [hSdef, hDdef, hDn]; ring

theorem PCyc4_of_all {σ : ℝ} {u P0 P1 P2 P3 : C3}
    (h : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      PS σ u ((quad P0 P1 P2 P3 (i + 1)).sub (quad P0 P1 P2 P3 i))
        ((quad P0 P1 P2 P3 j).sub (quad P0 P1 P2 P3 i))) : Minimality.CaseC20.PCyc4 σ u P0 P1 P2 P3 := by
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  have k := fun i j hi hj => h i j hi hj
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3] using k 0 2 (by decide) (by decide)
  · simpa only [b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3] using k 0 3 (by decide) (by decide)
  · simpa only [b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3] using k 1 3 (by decide) (by decide)
  · simpa only [b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3] using k 1 0 (by decide) (by decide)
  · simpa only [b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3] using k 2 0 (by decide) (by decide)
  · simpa only [b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3] using k 2 1 (by decide) (by decide)
  · simpa only [b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3] using k 3 1 (by decide) (by decide)
  · simpa only [b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3] using k 3 2 (by decide) (by decide)

namespace Shape18
variable (S : Shape18)

/-- `m2+ = sp xb + (1 - sp) m1+ - uV` (it lies in the plane of the face `014`, edge-on at `uV`). -/
theorem Dc_m2p (a P : C3) :
    Dc a ((⟨0, S.sp, S.kp⟩ : C3).sub P) S.uV =
      S.sp * Dc a ((⟨0, 1, 0⟩ : C3).sub P) S.uV +
        (1 - S.sp) * Dc a ((⟨S.tp, 0, S.hp⟩ : C3).sub P) S.uV := by
  simp only [Dc, C3.sub, uV]; ring

theorem m2p_pos (a P : C3) (h1 : 0 ≤ Dc a ((⟨0, 1, 0⟩ : C3).sub P) S.uV)
    (h2 : 0 ≤ Dc a ((⟨S.tp, 0, S.hp⟩ : C3).sub P) S.uV)
    (h : 0 < Dc a ((⟨0, 1, 0⟩ : C3).sub P) S.uV ∨ 0 < Dc a ((⟨S.tp, 0, S.hp⟩ : C3).sub P) S.uV) :
    0 < Dc a ((⟨0, S.sp, S.kp⟩ : C3).sub P) S.uV := by
  rw [Dc_m2p]
  have hsp := S.sp_pos; have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  rcases h with h | h
  · nlinarith [mul_pos hsp h, mul_nonneg hsp1.le h2]
  · nlinarith [mul_pos hsp1 h, mul_nonneg hsp.le h1]

theorem Dc_self (a w : C3) : Dc a a w = 0 := by simp only [Dc]; ring
theorem Dc_zero_right (a w : C3) (P : C3) : Dc a (P.sub P) w = 0 := by
  simp only [Dc, C3.sub]; ring

/-- The tangent test of `m2+` along the slide: it is exactly `η (Vp + k+ t+)`. -/
theorem tang_slide (η : ℝ) :
    PS 1 (C3.slide S.uV S.eF1 η) ((⟨S.tp, 0, S.hp⟩ : C3).sub ⟨0, 1, 0⟩)
        ((⟨0, S.sp, S.kp⟩ : C3).sub ⟨0, 1, 0⟩) ↔ 0 < η * (S.Vp + S.kp * S.tp) := by
  have : Dc ((⟨S.tp, 0, S.hp⟩ : C3).sub ⟨0, 1, 0⟩) ((⟨0, S.sp, S.kp⟩ : C3).sub ⟨0, 1, 0⟩)
      (C3.slide S.uV S.eF1 η) = η * (S.Vp + S.kp * S.tp) := by
    simp only [Dc, C3.sub, C3.slide, uV, eF1, Vp]; ring
  unfold PS
  rw [this, one_mul]

theorem tang_ev (hV : 0 < S.Vp) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), PS 1 (C3.slide S.uV S.eF1 η)
      ((⟨S.tp, 0, S.hp⟩ : C3).sub ⟨0, 1, 0⟩) ((⟨0, S.sp, S.kp⟩ : C3).sub ⟨0, 1, 0⟩) := by
  filter_upwards [self_mem_nhdsWithin] with η hη
  rw [tang_slide]
  exact mul_pos hη (by have := mul_pos S.kp_pos S.tp_pos; linarith)

theorem uD_ne (hV : 0 < S.Vp) :
    (S.tm - S.tp) * S.uV.z - (-S.hm - S.hp) * S.uV.x ≠ 0 := by
  have : (S.tm - S.tp) * S.uV.z - (-S.hm - S.hp) * S.uV.x = S.Vp + S.kp * S.tp := by
    simp only [uV, Vp]; ring
  rw [this]
  have := mul_pos S.kp_pos S.tp_pos
  linarith

theorem mid_v_ev (hV : 0 < S.Vp) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      0 = S.tp + s * (S.tm - S.tp) + δ * (C3.slide S.uV S.eF1 η).x ∧
      0 = S.hp + s * (-S.hm - S.hp) + δ * (C3.slide S.uV S.eF1 η).z := by
  obtain ⟨s, δ, h1, h2, h3, h4, h5⟩ := S.mid_v hV
  exact mid_slide_gen S.tp S.hp S.tm (-S.hm) 0 0 S.uV.x S.uV.z S.eF1.x S.eF1.z
    (by simpa [eF1] using S.uD_ne hV) ⟨s, δ, h1, h2, h3, by linarith, by linarith⟩

theorem mid_xa_ev (hV : 0 < S.Vp) (hW : S.Wp < S.Vp) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      1 = S.tp + s * (S.tm - S.tp) + δ * (C3.slide S.uV S.eF1 η).x ∧
      0 = S.hp + s * (-S.hm - S.hp) + δ * (C3.slide S.uV S.eF1 η).z := by
  obtain ⟨s, δ, h1, h2, h3, h4, h5⟩ := S.mid_xa hV hW
  exact mid_slide_gen S.tp S.hp S.tm (-S.hm) 1 0 S.uV.x S.uV.z S.eF1.x S.eF1.z
    (by simpa [eF1] using S.uD_ne hV) ⟨s, δ, h1, h2, h3, by linarith, by linarith⟩


theorem vN4_pcyc
    (D2n : 0 < -S.hm * S.sm * S.sp * S.tp - S.hp * S.sm * S.sp * S.tm + S.hm * S.sm * S.tp + S.hm * S.sp * S.tp + S.hp * S.sm * S.tm + S.hp * S.sp * S.tm - S.km * S.sp * S.tp - S.kp * S.sm * S.tm - S.hm * S.tp - S.hp * S.tm + S.km * S.tp + S.kp * S.tm)
    (Vp : 0 < -S.hm * S.sp * S.tp - S.hp * S.sp * S.tm + S.hm * S.tp + S.hp * S.tm - S.kp * S.tm)
    (A1z : 0 < S.hm * S.tp + S.hp * S.tm - S.hp) (A1 : 0 < S.hm * S.tp + S.hp * S.tm - S.hm) :
    PCyc4 1 S.uV (⟨S.tp, 0, S.hp⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ :=
  PCyc4_of_all (vN4_cyc S D2n Vp A1z A1)

/-- `m2+` projects strictly inside `V`'s 4-cycle rim for small `η > 0` along the slide. -/
theorem vN4_rest_ev
    (D2n : 0 < -S.hm * S.sm * S.sp * S.tp - S.hp * S.sm * S.sp * S.tm + S.hm * S.sm * S.tp + S.hm * S.sp * S.tp + S.hp * S.sm * S.tm + S.hp * S.sp * S.tm - S.km * S.sp * S.tp - S.kp * S.sm * S.tm - S.hm * S.tp - S.hp * S.tm + S.km * S.tp + S.kp * S.tm)
    (Vp : 0 < -S.hm * S.sp * S.tp - S.hp * S.sp * S.tm + S.hm * S.tp + S.hp * S.tm - S.kp * S.tm)
    (A1z : 0 < S.hm * S.tp + S.hp * S.tm - S.hp) (A1 : 0 < S.hm * S.tp + S.hp * S.tm - S.hm) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), PRest4 1 (C3.slide S.uV S.eF1 η) (⟨S.tp, 0, S.hp⟩ : C3)
      ⟨S.tm, 0, -S.hm⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨0, S.sp, S.kp⟩ := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := S.vN4_pcyc D2n Vp A1z A1
  have hV : 0 < S.Vp := by unfold Shape18.Vp; linarith
  have t0 : PS 1 S.uV ((⟨S.tm, 0, -S.hm⟩ : C3).sub ⟨S.tp, 0, S.hp⟩)
      ((⟨0, S.sp, S.kp⟩ : C3).sub ⟨S.tp, 0, S.hp⟩) := by
    unfold PS at c2 ⊢; rw [one_mul] at c2 ⊢
    exact S.m2p_pos _ _ c2.le (le_of_eq (Dc_zero_right _ _ _).symm) (Or.inl c2)
  have t1 : PS 1 S.uV ((⟨0, S.sm, -S.km⟩ : C3).sub ⟨S.tm, 0, -S.hm⟩)
      ((⟨0, S.sp, S.kp⟩ : C3).sub ⟨S.tm, 0, -S.hm⟩) := by
    unfold PS at c3 c4 ⊢; rw [one_mul] at c3 c4 ⊢
    exact S.m2p_pos _ _ c3.le c4.le (Or.inl c3)
  have t2 : PS 1 S.uV ((⟨0, 1, 0⟩ : C3).sub ⟨0, S.sm, -S.km⟩)
      ((⟨0, S.sp, S.kp⟩ : C3).sub ⟨0, S.sm, -S.km⟩) := by
    unfold PS at c5 ⊢; rw [one_mul] at c5 ⊢
    exact S.m2p_pos _ _ (le_of_eq (Dc_self _ _).symm) c5.le (Or.inr c5)
  filter_upwards [PS_ev 1 S.uV S.eF1 _ _ t0, PS_ev 1 S.uV S.eF1 _ _ t1, PS_ev 1 S.uV S.eF1 _ _ t2,
    S.tang_ev hV] with η a b c d
  exact ⟨a, b, c, d⟩

theorem vNt_cyc_ev
    (D2p : 0 < S.hm * S.sm * S.sp * S.tp + S.hp * S.sm * S.sp * S.tm - S.hm * S.sm * S.tp - S.hm * S.sp * S.tp - S.hp * S.sm * S.tm - S.hp * S.sp * S.tm + S.km * S.sp * S.tp + S.kp * S.sm * S.tm + S.hm * S.tp + S.hp * S.tm - S.km * S.tp - S.kp * S.tm)
    (Vp : 0 < -S.hm * S.sp * S.tp - S.hp * S.sp * S.tm + S.hm * S.tp + S.hp * S.tm - S.kp * S.tm)
    (A1z : 0 < S.hm * S.tp + S.hp * S.tm - S.hp) (A1 : 0 < S.hm * S.tp + S.hp * S.tm - S.hm) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ i j : ZMod 3, j ≠ i → j ≠ i + 1 →
      PS 1 (C3.slide S.uV S.eF1 η)
        ((tri (⟨S.tp, 0, S.hp⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, 1, 0⟩ (i + 1)).sub
          (tri (⟨S.tp, 0, S.hp⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, 1, 0⟩ i))
        ((tri (⟨S.tp, 0, S.hp⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, 1, 0⟩ j).sub
          (tri (⟨S.tp, 0, S.hp⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, 1, 0⟩ i)) := by
  refine eventually_all.mpr fun i => eventually_all.mpr fun j => ?_
  by_cases h : j ≠ i ∧ j ≠ i + 1
  · filter_upwards [PS_ev 1 S.uV S.eF1 _ _ (vNt_cyc S D2p Vp A1z A1 i j h.1 h.2)] with η hη _ _
      using hη
  · exact Filter.Eventually.of_forall fun η hi hj => absurd ⟨hi, hj⟩ h

/-- `m2+` projects strictly inside `V`'s triangle rim for small `η > 0` along the slide. -/
theorem vNt_rest1_ev
    (D2p : 0 < S.hm * S.sm * S.sp * S.tp + S.hp * S.sm * S.sp * S.tm - S.hm * S.sm * S.tp - S.hm * S.sp * S.tp - S.hp * S.sm * S.tm - S.hp * S.sp * S.tm + S.km * S.sp * S.tp + S.kp * S.sm * S.tm + S.hm * S.tp + S.hp * S.tm - S.km * S.tp - S.kp * S.tm)
    (Vp : 0 < -S.hm * S.sp * S.tp - S.hp * S.sp * S.tm + S.hm * S.tp + S.hp * S.tm - S.kp * S.tm)
    (A1z : 0 < S.hm * S.tp + S.hp * S.tm - S.hp) (A1 : 0 < S.hm * S.tp + S.hp * S.tm - S.hm) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ i : ZMod 3,
      PS 1 (C3.slide S.uV S.eF1 η)
        ((tri (⟨S.tp, 0, S.hp⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, 1, 0⟩ (i + 1)).sub
          (tri (⟨S.tp, 0, S.hp⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, 1, 0⟩ i))
        ((⟨0, S.sp, S.kp⟩ : C3).sub
          (tri (⟨S.tp, 0, S.hp⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, 1, 0⟩ i)) := by
  have hV : 0 < S.Vp := by unfold Shape18.Vp; linarith
  have c02 := vNt_cyc S D2p Vp A1z A1 0 2 (by decide) (by decide)
  have c10 := vNt_cyc S D2p Vp A1z A1 1 0 (by decide) (by decide)
  obtain ⟨b0, b1, b2⟩ := zmod3_add_one
  simp only [b0, b1, b2, tri_0, tri_1, tri_2] at c02 c10
  have t0 : PS 1 S.uV ((⟨S.tm, 0, -S.hm⟩ : C3).sub ⟨S.tp, 0, S.hp⟩)
      ((⟨0, S.sp, S.kp⟩ : C3).sub ⟨S.tp, 0, S.hp⟩) := by
    unfold PS at c02 ⊢; rw [one_mul] at c02 ⊢
    exact S.m2p_pos _ _ c02.le (le_of_eq (Dc_zero_right _ _ _).symm) (Or.inl c02)
  have t1 : PS 1 S.uV ((⟨0, 1, 0⟩ : C3).sub ⟨S.tm, 0, -S.hm⟩)
      ((⟨0, S.sp, S.kp⟩ : C3).sub ⟨S.tm, 0, -S.hm⟩) := by
    unfold PS at c10 ⊢; rw [one_mul] at c10 ⊢
    exact S.m2p_pos _ _ (le_of_eq (Dc_self _ _).symm) c10.le (Or.inr c10)
  filter_upwards [PS_ev 1 S.uV S.eF1 _ _ t0, PS_ev 1 S.uV S.eF1 _ _ t1, S.tang_ev hV]
    with η a b c i
  rcases zmod3_cases i with rfl | rfl | rfl <;> simp only [b0, b1, b2, tri_0, tri_1, tri_2]
  · exact a
  · exact b
  · exact c

/-- `m2-` stays strictly inside `V`'s triangle rim along the slide. -/
theorem vNt_rest2_ev
    (D2p : 0 < S.hm * S.sm * S.sp * S.tp + S.hp * S.sm * S.sp * S.tm - S.hm * S.sm * S.tp - S.hm * S.sp * S.tp - S.hp * S.sm * S.tm - S.hp * S.sp * S.tm + S.km * S.sp * S.tp + S.kp * S.sm * S.tm + S.hm * S.tp + S.hp * S.tm - S.km * S.tp - S.kp * S.tm)
    (Vp : 0 < -S.hm * S.sp * S.tp - S.hp * S.sp * S.tm + S.hm * S.tp + S.hp * S.tm - S.kp * S.tm)
    (A1z : 0 < S.hm * S.tp + S.hp * S.tm - S.hp) (A1 : 0 < S.hm * S.tp + S.hp * S.tm - S.hm) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ i : ZMod 3,
      PS 1 (C3.slide S.uV S.eF1 η)
        ((tri (⟨S.tp, 0, S.hp⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, 1, 0⟩ (i + 1)).sub
          (tri (⟨S.tp, 0, S.hp⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, 1, 0⟩ i))
        ((⟨0, S.sm, -S.km⟩ : C3).sub
          (tri (⟨S.tp, 0, S.hp⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, 1, 0⟩ i)) :=
  eventually_all.mpr fun i => PS_ev 1 S.uV S.eF1 _ _ (vNt_rest2 S D2p Vp A1z A1 i)

end Shape18

namespace Frame18
variable {x : Fin 7 → ℝ³} (F : Frame18 x)

/-! ### (ii) The slide Rupert theorems: one hyperplane instead of the HDN items -/

/-- **`V` with the 4-cycle rim, off the hyperplane `ClassH`** (replaces the `hnd` of `vN4_rupert`
by `¬ F.ClassH`). -/
theorem vN4_slide_rupert (hx : Function.Injective x) (hD2 : F.S.D2p < 0) (hV : 0 < F.S.Vp)
    (hA1z : 0 < F.S.hm * F.S.tp - F.S.hp * (1 - F.S.tm))
    (hA1 : 0 < F.S.hp * F.S.tm - F.S.hm * (1 - F.S.tp)) (hH : ¬ F.ClassH)
    (hB : F.dV 6 < F.dV 0 ∨ F.dV 4 < F.dV 0 ∨ F.dV 6 < F.dV 2 ∨ F.dV 4 < F.dV 2) :
    IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have hsp1 := F.S.sp_lt
  have ux : 0 < -F.S.sp * F.S.tp + F.S.tp := by nlinarith [mul_pos htp (sub_pos.2 hsp1)]
  have hD2' : 0 < -F.S.hm * F.S.sm * F.S.sp * F.S.tp - F.S.hp * F.S.sm * F.S.sp * F.S.tm +
      F.S.hm * F.S.sm * F.S.tp + F.S.hm * F.S.sp * F.S.tp + F.S.hp * F.S.sm * F.S.tm +
      F.S.hp * F.S.sp * F.S.tm - F.S.km * F.S.sp * F.S.tp - F.S.kp * F.S.sm * F.S.tm -
      F.S.hm * F.S.tp - F.S.hp * F.S.tm + F.S.km * F.S.tp + F.S.kp * F.S.tm := by
    unfold Shape18.D2p at hD2; linarith
  have hV' : 0 < -F.S.hm * F.S.sp * F.S.tp - F.S.hp * F.S.sp * F.S.tm + F.S.hm * F.S.tp +
      F.S.hp * F.S.tm - F.S.kp * F.S.tm := by unfold Shape18.Vp at hV; linarith
  have hA1z' : 0 < F.S.hm * F.S.tp + F.S.hp * F.S.tm - F.S.hp := by linarith
  have hA1' : 0 < F.S.hm * F.S.tp + F.S.hp * F.S.tm - F.S.hm := by linarith
  have hW : F.S.Wp < F.S.Vp := by
    unfold Shape18.Wp Shape18.Vp
    have := F.S.roof_p'
    nlinarith [mul_pos hA1z (sub_pos.2 (F.S.sp_lt)), F.S.kp_pos, F.S.tm_lt, F.S.tm_pos]
  have hAq := F.vN4_A hV
  have hnp : NoPersistHDN (fun i : ZMod 4 => x (quad 0 6 2 4 i)) (F.toFrame7.fvC F.S.uV)
      (F.toFrame7.fvC F.S.eF1) :=
    (F.noPersistHDN_or_classH_N4 hx hD2 hV hA1z hA1).resolve_right hH
  have hnd := F.toFrame7.eventually_noHDNRim_slide (quad 0 6 2 4) F.S.uV F.S.eF1 hnp
  have hcyc := (F.S.vN4_pcyc hD2' hV' hA1z' hA1').ev F.S.eF1
  have hrest := F.S.vN4_rest_ev hD2' hV' hA1z' hA1'
  have hmv := F.S.mid_v_ev hV
  have hmxa := F.S.mid_xa_ev hV hW
  have hux := eventually_pos_affine (A := -F.S.sp * F.S.tp + F.S.tp) (B := F.S.tm - F.S.tp)
    (Or.inl ux)
  have hzev : ∀ᶠ η in 𝓝[>] (0 : ℝ), IsRobustUnimodal
      (quad (F.toFrame7.GG (F.toFrame7.ptC 0) (C3.slide F.S.uV F.S.eF1 η))
        (F.toFrame7.GG (F.toFrame7.ptC 6) (C3.slide F.S.uV F.S.eF1 η))
        (F.toFrame7.GG (F.toFrame7.ptC 2) (C3.slide F.S.uV F.S.eF1 η))
        (F.toFrame7.GG (F.toFrame7.ptC 4) (C3.slide F.S.uV F.S.eF1 η))) := by
    have h0 := Q4_ev_strict
      (z := quad (F.dV 0) (F.dV 6) (F.dV 2) (F.dV 4))
      (w := quad (F.toFrame7.GG (F.toFrame7.ptC 0) F.S.eF1) (F.toFrame7.GG (F.toFrame7.ptC 6) F.S.eF1)
        (F.toFrame7.GG (F.toFrame7.ptC 2) F.S.eF1) (F.toFrame7.GG (F.toFrame7.ptC 4) F.S.eF1))
      (by simpa only [quad_0, quad_1, quad_2, quad_3] using hAq)
      (by simpa only [quad_0, quad_1, quad_2, quad_3] using hB)
    filter_upwards [h0] with η hη
    obtain ⟨hA', hB'⟩ := hη
    simp only [quad_0, quad_1, quad_2, quad_3] at hA' hB'
    simp only [Frame7.GG_slide]
    simp only [dV] at hA' hB'
    exact robust_quad_of_nws hA' hB'
  obtain ⟨η, hnd', hc, hr, hm5, hm3, hu, hz⟩ :=
    (hnd.and (hcyc.and (hrest.and (hmv.and (hmxa.and (hux.and hzev)))))).exists
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  refine F.toFrame7.vertex4_rim hx 0 6 2 4 _ _ _ _ F.ptC_0 F.ptC_6 F.ptC_2 F.ptC_4 ({5, 3} : Finset (Fin 7))
    ?_ 1 (Or.inl rfl) (C3.slide F.S.uV F.S.eF1 η)
    (Or.inl (by simp only [C3.slide, Shape18.uV, Shape18.eF1]; exact hu.ne')) hc ?_ ?_ hnd' ?_
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl <;> decide
  · intro j' hjM h0 h1 h2 h3
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · rw [ptC_1]; exact hr
    · exact absurd rfl h2
    · exact absurd (by simp) hjM
    · exact absurd rfl h3
    · exact absurd (by simp) hjM
    · exact absurd rfl h1
  · simpa only [ptC_0, ptC_6, ptC_2, ptC_4] using hz
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · obtain ⟨s, δ, hs0, hs1, hδ, ex, ez⟩ := hm5
      refine ⟨0, s, δ, hs0, hs1, hδ, ?_, ?_, ?_⟩ <;>
        simp [quad_0, quad_1, ptC_5, C3.slide, Shape18.uV, Shape18.eF1] at ex ez ⊢ <;> linarith
    · obtain ⟨s, δ, hs0, hs1, hδ, ex, ez⟩ := hm3
      refine ⟨0, s, δ, hs0, hs1, hδ, ?_, ?_, ?_⟩ <;>
        simp [quad_0, quad_1, ptC_3, C3.slide, Shape18.uV, Shape18.eF1] at ex ez ⊢ <;> linarith

/-- **`V` with the triangle rim, off the hyperplane `ClassH`** (replaces the `hnd` of
`vNt_rupert`). -/
theorem vNt_slide_rupert (hx : Function.Injective x) (hD2 : 0 < F.S.D2p) (hV : 0 < F.S.Vp)
    (hA1z : 0 < F.S.hm * F.S.tp - F.S.hp * (1 - F.S.tm))
    (hA1 : 0 < F.S.hp * F.S.tm - F.S.hm * (1 - F.S.tp)) (hH : ¬ F.ClassH) :
    IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have hsp1 := F.S.sp_lt
  have ux : 0 < -F.S.sp * F.S.tp + F.S.tp := by nlinarith [mul_pos htp (sub_pos.2 hsp1)]
  have hD2' : 0 < F.S.hm * F.S.sm * F.S.sp * F.S.tp + F.S.hp * F.S.sm * F.S.sp * F.S.tm -
      F.S.hm * F.S.sm * F.S.tp - F.S.hm * F.S.sp * F.S.tp - F.S.hp * F.S.sm * F.S.tm -
      F.S.hp * F.S.sp * F.S.tm + F.S.km * F.S.sp * F.S.tp + F.S.kp * F.S.sm * F.S.tm +
      F.S.hm * F.S.tp + F.S.hp * F.S.tm - F.S.km * F.S.tp - F.S.kp * F.S.tm := by
    unfold Shape18.D2p at hD2; linarith
  have hV' : 0 < -F.S.hm * F.S.sp * F.S.tp - F.S.hp * F.S.sp * F.S.tm + F.S.hm * F.S.tp +
      F.S.hp * F.S.tm - F.S.kp * F.S.tm := by unfold Shape18.Vp at hV; linarith
  have hA1z' : 0 < F.S.hm * F.S.tp + F.S.hp * F.S.tm - F.S.hp := by linarith
  have hA1' : 0 < F.S.hm * F.S.tp + F.S.hp * F.S.tm - F.S.hm := by linarith
  have hW : F.S.Wp < F.S.Vp := by
    unfold Shape18.Wp Shape18.Vp
    have := F.S.roof_p'
    nlinarith [mul_pos hA1z (sub_pos.2 (F.S.sp_lt)), F.S.kp_pos, F.S.tm_lt, F.S.tm_pos]
  have hc : ∀ i, F.toFrame7.ptC (tri 0 6 4 i) =
      tri (⟨F.S.tp, 0, F.S.hp⟩ : C3) ⟨F.S.tm, 0, -F.S.hm⟩ ⟨0, 1, 0⟩ i := by
    intro i
    rcases zmod3_cases i with rfl | rfl | rfl <;>
      simp [tri_0, tri_1, tri_2, ptC_0, ptC_6, ptC_4]
  have hnp : NoPersistHDN (fun i : ZMod 3 => x (tri 0 6 4 i)) (F.toFrame7.fvC F.S.uV)
      (F.toFrame7.fvC F.S.eF1) :=
    (F.noPersistHDN_or_classH_Nt hx hD2 hV hA1z hA1).resolve_right hH
  have hnd := F.toFrame7.eventually_noHDNRim_slide (tri 0 6 4) F.S.uV F.S.eF1 hnp
  have hcyc := F.S.vNt_cyc_ev hD2' hV' hA1z' hA1'
  have hr1 := F.S.vNt_rest1_ev hD2' hV' hA1z' hA1'
  have hr2 := F.S.vNt_rest2_ev hD2' hV' hA1z' hA1'
  have hmv := F.S.mid_v_ev hV
  have hmxa := F.S.mid_xa_ev hV hW
  have hux := eventually_pos_affine (A := -F.S.sp * F.S.tp + F.S.tp) (B := F.S.tm - F.S.tp)
    (Or.inl ux)
  obtain ⟨η, hnd', hc', hr1', hr2', hm5, hm3, hu⟩ :=
    (hnd.and (hcyc.and (hr1.and (hr2.and (hmv.and (hmxa.and hux)))))).exists
  obtain ⟨b0, b1, b2⟩ := zmod3_add_one
  refine F.toFrame7.rupert_vertex_or_rim hx (k := 3) (by norm_num) (tri 0 6 4) {5, 3} 1
    (Or.inl rfl) (C3.slide F.S.uV F.S.eF1 η)
    (Or.inl (by simp only [C3.slide, Shape18.uV, Shape18.eF1]; exact hu.ne')) ?_ ?_ ?_ ?_ hnd' ?_
  · intro m hm i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl <;> rcases zmod3_cases i with rfl | rfl | rfl <;>
      simp [tri_0, tri_1, tri_2]
  · intro i j h1 h2
    simp only [hc]
    exact hc' i j h1 h2
  · intro j' hj' hjc i
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj'
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (by simp [tri_0]) (hjc 0)
    · simp only [hc]; rw [ptC_1]; exact hr1' i
    · simp only [hc]; rw [ptC_2]; exact hr2' i
    · exact absurd rfl hj'.2
    · exact absurd (by simp [tri_2]) (hjc 2)
    · exact absurd rfl hj'.1
    · exact absurd (by simp [tri_1]) (hjc 1)
  · have hf : (fun i => F.toFrame7.GG (F.toFrame7.ptC (tri 0 6 4 i)) (C3.slide F.S.uV F.S.eF1 η)) =
        tri (F.toFrame7.GG (F.toFrame7.ptC 0) (C3.slide F.S.uV F.S.eF1 η))
          (F.toFrame7.GG (F.toFrame7.ptC 6) (C3.slide F.S.uV F.S.eF1 η))
          (F.toFrame7.GG (F.toFrame7.ptC 4) (C3.slide F.S.uV F.S.eF1 η)) := by
      funext i
      rcases zmod3_cases i with rfl | rfl | rfl <;> simp [tri_0, tri_1, tri_2]
    by_cases hlev : F.toFrame7.GG (F.toFrame7.ptC 0) (C3.slide F.S.uV F.S.eF1 η) =
          F.toFrame7.GG (F.toFrame7.ptC 6) (C3.slide F.S.uV F.S.eF1 η) ∧
        F.toFrame7.GG (F.toFrame7.ptC 6) (C3.slide F.S.uV F.S.eF1 η) =
          F.toFrame7.GG (F.toFrame7.ptC 4) (C3.slide F.S.uV F.S.eF1 η)
    · right
      refine ⟨rfl, fun i j => ?_⟩
      have e : ∀ i, F.toFrame7.GG (F.toFrame7.ptC (tri 0 6 4 i)) (C3.slide F.S.uV F.S.eF1 η) =
          tri (F.toFrame7.GG (F.toFrame7.ptC 0) (C3.slide F.S.uV F.S.eF1 η))
            (F.toFrame7.GG (F.toFrame7.ptC 6) (C3.slide F.S.uV F.S.eF1 η))
            (F.toFrame7.GG (F.toFrame7.ptC 4) (C3.slide F.S.uV F.S.eF1 η)) i :=
        fun i => congrFun hf i
      rw [e i, e j]
      rcases zmod3_cases i with rfl | rfl | rfl <;> rcases zmod3_cases j with rfl | rfl | rfl <;>
        simp only [tri_0, tri_1, tri_2] <;> linarith [hlev.1, hlev.2]
    · left
      rw [hf]
      exact isRobustUnimodal_three hlev
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · obtain ⟨s, δ, hs0, hs1, hδ, ex, ez⟩ := hm5
      refine ⟨0, s, δ, hs0, hs1, hδ, ?_, ?_, ?_⟩ <;>
        simp [tri_0, tri_1, hc, ptC_5, ptC_0, ptC_6, C3.slide, Shape18.uV, Shape18.eF1] at ex ez ⊢ <;>
        linarith
    · obtain ⟨s, δ, hs0, hs1, hδ, ex, ez⟩ := hm3
      refine ⟨0, s, δ, hs0, hs1, hδ, ?_, ?_, ?_⟩ <;>
        simp [tri_0, tri_1, hc, ptC_3, ptC_0, ptC_6, C3.slide, Shape18.uV, Shape18.eF1] at ex ez ⊢ <;>
        linarith

/-- **The `V` side of 27.59 off `ClassH`** (as `Vside`, with `hnd` replaced by `¬ F.ClassH`). -/
theorem Vside_slide (hx : Function.Injective x) (hVp : F.S.dp < F.S.A1 * F.S.tp)
    (h1 : F.S.am < F.S.bp) (h2 : F.S.ap < F.S.bm) (hD2 : F.S.D2p ≠ 0) (hH : ¬ F.ClassH) :
    IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have htp1 := F.S.tp_lt; have hsp1 := F.S.sp_lt
  have hV := F.dV_pos_of hVp
  have hA1 := sub_pos.2 (F.A1_of h1)
  have hA1z : 0 < F.S.hm * F.S.tp - F.S.hp * (1 - F.S.tm) := sub_pos.2 (F.zFrame.A1_of h2)
  rcases lt_or_gt_of_ne hD2 with hneg | hpos
  · rcases F.tA_or hx (F.A1_of h1) with h | ⟨f1, f2, f3, f4⟩
    · exact h
    · refine F.vN4_slide_rupert hx hneg hV hA1z hA1 hH ?_
      by_contra hc
      push Not at hc
      obtain ⟨c1, c2, c3, c4⟩ := hc
      rw [F.dA_0, F.dA_4] at f1
      rw [F.dV_0, F.dV_4] at c2
      have hgg : 0 < F.gg := F.g_pos
      have hroof := F.S.roof_p'
      nlinarith [mul_nonneg (mul_pos htp (sub_pos.2 hsp1)).le (sub_nonneg.2 f1),
        mul_nonneg (sub_pos.2 htp1).le (sub_nonneg.2 c2),
        mul_pos (mul_pos hgg F.S.hp_pos) (sub_pos.2 hroof)]
  · exact F.vNt_slide_rupert hx hpos hV hA1z hA1 hH

end Frame18

/-!
## Proof summary

* `persist_gen` (the classification, 27.35-27.38 (a), 27.40): a persistent extremal pair `Y' - Y` is
  perpendicular to `uV` and `e1`, hence (the determinant is `Vp + k+ t+ > 0`) to `u1` and `e`
  (`persist_perp`); then `⟪Y'-Y, ·⟫ = ν y` on the rim corners (`persist_vals`), with `ν ≠ 0`
  (`persist_nu_ne`).  Extremality forces `Y' = xb` (the only corner with `y = 1`) and `Y` on the
  chord `[m1+, m1-]` (`y = 0`), and the perpendicularity to `e` is `ClassH`.  So the corner `m2-` and the
  level edge of 27.40 never occur (they have `y < 1`).
* The slide: the strict tests of `vN4_cyc` / `vNt_cyc` persist (`PS_ev`); `m2+` lies in the plane of the
  face `014` edge-on at `uV` (`Dc_m2p`), so its tests against the three other sides are strict and
  the test against `[xb, m1+]` equals `η (Vp + k+ t+)` along `+eF1` (`tang_slide`); the middles
  `v`, `xa` stay over the chord (`mid_slide_gen`); the depths stay robustly unimodal
  (`Q4_ev_strict`) or the triangle is not level (a level triangle has an HDN, excluded by `NoHDNRim`).
-/

end Minimality.CaseC18

end
