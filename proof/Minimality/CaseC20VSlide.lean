module

public import Minimality.CaseC20TestsNR
public import Minimality.SlideRim
public import Minimality.CaseC18VSlide

@[expose] public section

/-!
# Type 20: `V` and `T_A` slid along `F1`'s circle
(`FEWER-FACES-PROOFS.md` Theorem 27.41 / Props 27.38, 27.39 for type 20, Lemma 27.71a; stage M5)

Frame dictionary (type 18 -> type 20): `xa` 3 -> 1, `xb` 4 -> 6, `m1+` 0 -> 0, `m1-` 6 -> 3,
`m2+` 1 -> 2, `m2-` 2 -> 4, `v` 5 -> 5.  In frame coordinates the four rim corners
`(m1+, m1-, m2-, xb)` are the same points `(t+,0,h+), (t-,0,-h-), (0,s-,-k-), (0,1,0)` and
`Shape20.u_vN4` is the type-18 `uV`, so `eF1`, the hyperplane and the whole persistent-pair
argument carry over from `CaseC18VSlide`.

* `V` (rim `quad 0 3 4 6`, view `u_vN4`, slide `eF1 = m1- - m1+`).
* `T_A` (rim `quad 0 6 4 3`, view `u_tANR = (t+ - 1, 0, h+)`, slide `(0,0,-1)`): both vectors lie in
  `span(u1, e)` (`t+ < 1`), so a persistent pair is again perpendicular to `u1`, `e`, hence has
  `<w, x v - x 5> = nu * y_v`, and the pair is again `xb <-> [m1+, m1-]`: the SAME hyperplane
  `ClassH` (`A12 (h+ + h-) = A11 (t+ h- + t- h+)`).
* `R`: `F.rFrame.ClassH` is `A12 (k+ + k-) = A22 (s+ k- + s- k+)` (`ClassHR`; paper `rho*'`).
-/

namespace Minimality.CaseC20

open Finset Filter Minimality.CaseC09 Minimality.CaseC18
open scoped RealInnerProductSpace Topology

namespace Shape20
variable (S : Shape20)

/-- The slide direction `m1- - m1+` of `F1`'s circle, in frame coordinates (`y = 0`). -/
def eF1 : C3 := ⟨S.tm - S.tp, 0, -S.hm - S.hp⟩

end Shape20

namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- **Class `H_F1`** (Prop. 27.38 (a) / 27.39, corner `xb`): the `G`-perpendicular from `xb` to the
line `m1+ m1-` is horizontal at the views of `F1`'s circle; `A12 (h+ + h-) = A11 (t+ h- + t- h+)`.
Same hyperplane for `V` and for `T_A` (Lemma 27.71a). -/
def ClassH : Prop :=
  F.a12 * (F.S.hp + F.S.hm) = F.a11 * (F.S.tp * F.S.hm + F.S.tm * F.S.hp)

/-- The `R`-image hyperplane, in the variables of `F` (corner `xa`): `A12 (k+ + k-) = A22 (s+ k- + s- k+)`,
i.e. `A12/A22 = rho*' = (s- k+ + s+ k-)/(k+ + k-)`. -/
def ClassHR : Prop :=
  F.a12 * (F.S.kp + F.S.km) = F.a22 * (F.S.sp * F.S.km + F.S.sm * F.S.kp)

/-- `V^R`'s and `T_A^R`'s hyperplane is `ClassHR`. -/
theorem classH_rFrame_iff : F.rFrame.ClassH ↔ F.ClassHR := by
  have e12 : F.rFrame.a12 = F.a12 := by
    show ⟪x 6 - x 5, x 1 - x 5⟫ = _
    exact real_inner_comm _ _
  have e11 : F.rFrame.a11 = F.a22 := rfl
  unfold ClassH ClassHR
  rw [e12, e11]
  show F.a12 * (F.S.km + F.S.kp) = F.a22 * (F.S.sm * F.S.kp + F.S.sp * F.S.km) ↔ _
  constructor <;> intro h <;> linarith

/-! ### The persistent-pair classification -/

/-- The `y`-coordinate (frame) of the rim corners `m1+, m1-, m2-, xb`. -/
noncomputable def yv (v : Fin 7) : ℝ := if v = 4 then F.S.sm else if v = 6 then 1 else 0

theorem yv_facts (v : Fin 7) (hv : v = 0 ∨ v = 3 ∨ v = 4 ∨ v = 6) :
    0 ≤ F.yv v ∧ F.yv v ≤ 1 ∧ (F.yv v = 1 → v = 6) ∧ (F.yv v = 0 → v = 0 ∨ v = 3) := by
  have h1 := F.S.sm_pos; have h2 := F.S.sm_lt
  have e0 : F.yv 0 = 0 := by simp [yv]
  have e3 : F.yv 3 = 0 := by simp [yv]
  have e4 : F.yv 4 = F.S.sm := by simp [yv]
  have e6 : F.yv 6 = 1 := by simp [yv]
  rcases hv with rfl | rfl | rfl | rfl
  · rw [e0]; exact ⟨le_rfl, zero_le_one, fun h => by norm_num at h, fun _ => Or.inl rfl⟩
  · rw [e3]; exact ⟨le_rfl, zero_le_one, fun h => by norm_num at h, fun _ => Or.inr rfl⟩
  · rw [e4]; exact ⟨h1.le, h2.le, fun h => absurd h h2.ne, fun h => absurd h h1.ne'⟩
  · rw [e6]; exact ⟨zero_le_one, le_rfl, fun _ => rfl, fun h => by norm_num at h⟩

theorem persist_nu_ne (w : ℝ³) (hw : w ≠ 0) (hA : ⟪w, x 1 - x 5⟫ = 0) (hB : ⟪w, F.e⟫ = 0) :
    ⟪w, x 6 - x 5⟫ ≠ 0 := by
  intro h0
  obtain ⟨p, hp⟩ := F.toFrame7.decomp w
  apply hw
  have h : ⟪w, F.toFrame7.fvC p⟫ = 0 := by
    show ⟪w, p.x • (x 1 - x 5) + p.y • (x 6 - x 5) + p.z • F.e⟫ = 0
    rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
      inner_smul_right, hA, h0, hB]; ring
  rw [← hp] at h
  exact inner_self_eq_zero.mp h

theorem persist_vals (w : ℝ³) (hA : ⟪w, x 1 - x 5⟫ = 0) (hB : ⟪w, F.e⟫ = 0) (v : Fin 7)
    (hv : v = 0 ∨ v = 3 ∨ v = 4 ∨ v = 6) :
    ⟪w, x v - x 5⟫ = F.yv v * ⟪w, x 6 - x 5⟫ := by
  rcases hv with rfl | rfl | rfl | rfl
  · have : x 0 - x 5 = F.S.tp • (x 1 - x 5) + F.S.hp • F.e := by rw [F.x0_eq]; abel
    rw [this, inner_add_right, inner_smul_right, inner_smul_right, hA, hB]; simp [yv]
  · have : x 3 - x 5 = F.S.tm • (x 1 - x 5) - F.S.hm • F.e := by rw [F.x3_eq]; abel
    rw [this, inner_sub_right, inner_smul_right, inner_smul_right, hA, hB]; simp [yv]
  · have : x 4 - x 5 = F.S.sm • (x 6 - x 5) - F.S.km • F.e := by rw [F.x4_eq]; abel
    rw [this, inner_sub_right, inner_smul_right, inner_smul_right, hB]; simp [yv]
  · simp [yv]

/-- The core of the classification, for a positive `ν = ⟪Y' - Y, u2⟫`: the double normal runs from
the chord `[m1+, m1-]` to `xb`, and its perpendicularity to `e` is `ClassH`. -/
theorem persist_core {k : ℕ} [NeZero k] (c : ZMod k → Fin 7)
    (hcr : ∀ i, c i = 0 ∨ c i = 3 ∨ c i = 4 ∨ c i = 6)
    (h0 : ∃ m, c m = 0) (h6 : ∃ m, c m = 6)
    (i j : ZMod k) (Y Y' : ℝ³) (hY : Y ∈ segment ℝ (x (c i)) (x (c (i + 1))))
    (hY' : Y' ∈ segment ℝ (x (c j)) (x (c (j + 1)))) (hne : Y' ≠ Y)
    (hA : ⟪Y' - Y, x 1 - x 5⟫ = 0) (hB : ⟪Y' - Y, F.e⟫ = 0)
    (hext : ∀ m, ⟪Y' - Y, x (c m) - Y'⟫ ≤ 0 ∧ ⟪Y - Y', x (c m) - Y⟫ ≤ 0)
    (hν : 0 < ⟪Y' - Y, x 6 - x 5⟫) : F.ClassH := by
  set w := Y' - Y with hw
  set ν := ⟪w, x 6 - x 5⟫ with hνdef
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
  obtain ⟨m4, hm4⟩ := h6
  obtain ⟨m0, hm0⟩ := h0
  have hT' : ⟪w, Y' - x 5⟫ = α' * (F.yv (c j) * ν) + β' * (F.yv (c (j + 1)) * ν) := by
    rw [← hY'eq, conv α' β' _ _ hαβ', vals _ (hcr j), vals _ (hcr (j + 1))]
  have hext4 := (hext m4).1
  rw [sub_in, vals _ (hcr m4), hm4] at hext4
  have hy4 : F.yv 6 = 1 := by simp [yv]
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
  have hY'4 : Y' = x 6 := by
    rw [← hY'eq]
    have e1 : α' • x (c j) = α' • x 6 := by
      rcases mul_eq_zero.mp hq1 with h | h
      · rw [h, zero_smul, zero_smul]
      · rw [a2 (by linarith)]
    have e2 : β' • x (c (j + 1)) = β' • x 6 := by
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
  have split0 : ∀ (a : ℝ) (v : Fin 7), 0 ≤ a → (v = 0 ∨ v = 3 ∨ v = 4 ∨ v = 6) →
      a * F.yv v = 0 → ∃ p q : ℝ, 0 ≤ p ∧ 0 ≤ q ∧ p + q = a ∧ a • x v = p • x 0 + q • x 3 := by
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
  have hYab : Y = a • x 0 + b • x 3 := by
    calc Y = α • x (c i) + β • x (c (i + 1)) := hYeq.symm
      _ = (p1 • x 0 + q1 • x 3) + (p2 • x 0 + q2 • x 3) := by rw [hv1, hv2]
      _ = a • x 0 + b • x 3 := by rw [ha, hb]; module
  have hb' : b = 1 - a := by linarith
  subst hb'
  have hwexp : w = (x 6 - x 5) - a • (F.S.tp • (x 1 - x 5) + F.S.hp • F.e) -
      (1 - a) • (F.S.tm • (x 1 - x 5) - F.S.hm • F.e) := by
    rw [hw, hY'4, hYab, F.x0_eq, F.x3_eq]; module
  have i1 : ⟪F.e, x 1 - x 5⟫ = 0 := by rw [real_inner_comm]; exact F.inner_u1_e
  have i2 : ⟪x 6 - x 5, x 1 - x 5⟫ = F.a12 := real_inner_comm (x 1 - x 5) (x 6 - x 5)
  have i3 : ⟪x 1 - x 5, x 1 - x 5⟫ = F.a11 := rfl
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

/-- **The persistent-pair classification** for any rim with corners among `m1+, m1-, m2-, xb` that
contains `m1+` and `xb`, along a slide `u + eta e'` with `u, e'` both in the plane `span(u1, e)`
(`hperp`: a vector perpendicular to `u` and `e'` is perpendicular to `u1` and `e`). -/
theorem persist_gen {k : ℕ} [NeZero k] (c : ZMod k → Fin 7)
    (hcr : ∀ i, c i = 0 ∨ c i = 3 ∨ c i = 4 ∨ c i = 6)
    (h0 : ∃ m, c m = 0) (h6 : ∃ m, c m = 6) (u e' : C3)
    (hperp : ∀ w : ℝ³, ⟪w, F.toFrame7.fvC u⟫ = 0 → ⟪w, F.toFrame7.fvC e'⟫ = 0 →
      ⟪w, x 1 - x 5⟫ = 0 ∧ ⟪w, F.e⟫ = 0) :
    NoPersistHDN (fun i => x (c i)) (F.toFrame7.fvC u) (F.toFrame7.fvC e') ∨ F.ClassH := by
  by_cases hH : F.ClassH
  · exact Or.inr hH
  left
  intro i j Y hY Y' hY' hne hu he hext
  obtain ⟨hA, hB⟩ := hperp (Y' - Y) hu he
  have hν := F.persist_nu_ne (Y' - Y) (sub_ne_zero.2 hne) hA hB
  have hsw : Y - Y' = -(Y' - Y) := (neg_sub Y' Y).symm
  rcases lt_or_gt_of_ne hν with hneg | hpos
  · refine hH (F.persist_core c hcr h0 h6 j i Y' Y hY' hY hne.symm ?_ ?_ ?_ ?_)
    · rw [hsw, inner_neg_left, hA, neg_zero]
    · rw [hsw, inner_neg_left, hB, neg_zero]
    · intro m; exact (hext m).symm
    · rw [hsw, inner_neg_left]; linarith
  · exact hH (F.persist_core c hcr h0 h6 i j Y Y' hY hY' hne hA hB hext hpos)

/-- `V`: a vector perpendicular to `u_vN4` and `eF1` is perpendicular to `u1` and `e` (the
determinant is `Vp + k+ t+ > 0`). -/
theorem perp_vN4
    (hV : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm)
    (w : ℝ³) (h1 : ⟪w, F.toFrame7.fvC F.S.u_vN4⟫ = 0)
    (h2 : ⟪w, F.toFrame7.fvC F.S.eF1⟫ = 0) : ⟪w, x 1 - x 5⟫ = 0 ∧ ⟪w, F.e⟫ = 0 := by
  have hu : F.toFrame7.fvC F.S.u_vN4 = (-F.S.sp * F.S.tp + F.S.tp) • (x 1 - x 5) +
      (0 : ℝ) • (x 6 - x 5) + (-F.S.hp * F.S.sp + F.S.hp - F.S.kp) • F.e := rfl
  have he : F.toFrame7.fvC F.S.eF1 = (F.S.tm - F.S.tp) • (x 1 - x 5) +
      (0 : ℝ) • (x 6 - x 5) + (-F.S.hm - F.S.hp) • F.e := rfl
  rw [hu, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
    inner_smul_right] at h1
  rw [he, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
    inner_smul_right] at h2
  have hd : (-F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm) +
      F.S.kp * F.S.tp ≠ 0 := by
    have := mul_pos F.S.kp_pos F.S.tp_pos; linarith
  constructor
  · apply mul_left_cancel₀ hd
    linear_combination (-(-F.S.hm - F.S.hp)) * h1 + (-F.S.hp * F.S.sp + F.S.hp - F.S.kp) * h2
  · apply mul_left_cancel₀ hd
    linear_combination (-(-F.S.sp * F.S.tp + F.S.tp)) * h2 + (F.S.tm - F.S.tp) * h1

/-- **`V`'s 4-cycle rim `(m1+, m1-, m2-, xb) = (0, 3, 4, 6)` along `F1`'s circle**: no persistent
double normal, or `ClassH`. -/
theorem noPersistHDN_or_classH_vN4
    (hV : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm) :
    NoPersistHDN (fun i : ZMod 4 => x (quad 0 3 4 6 i)) (F.toFrame7.fvC F.S.u_vN4)
        (F.toFrame7.fvC F.S.eF1) ∨ F.ClassH := by
  refine F.persist_gen (quad 0 3 4 6) (fun i => ?_) ⟨0, by simp [quad_0]⟩ ⟨3, by simp [quad_3]⟩
    _ _ (F.perp_vN4 hV)
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp [quad_0, quad_1, quad_2, quad_3]

/-- **`T_A`'s rim `(m1+, xb, m2-, m1-) = (0, 6, 4, 3)` along the circle of `0135`** (slide
direction `(0,0,-1)`, view `u_tANR`): no persistent double normal, or `ClassH` (same hyperplane as
`V`).  `fvC u_tANR = (t+ - 1) u1 + h+ e`, `fvC (0,0,-1) = -e`, `t+ < 1`. -/
theorem noPersistHDN_or_classH_tANR :
    NoPersistHDN (fun i : ZMod 4 => x (quad 0 6 4 3 i)) (F.toFrame7.fvC F.S.u_tANR)
        (F.toFrame7.fvC ⟨0, 0, -1⟩) ∨ F.ClassH := by
  refine F.persist_gen (quad 0 6 4 3) (fun i => ?_) ⟨0, by simp [quad_0]⟩ ⟨1, by simp [quad_1]⟩
    _ _ ?_
  · rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp [quad_0, quad_1, quad_2, quad_3]
  · intro w h1 h2
    have hu : F.toFrame7.fvC F.S.u_tANR = (F.S.tp - 1) • (x 1 - x 5) +
        (0 : ℝ) • (x 6 - x 5) + F.S.hp • F.e := rfl
    have he : F.toFrame7.fvC (⟨0, 0, -1⟩ : C3) = (0 : ℝ) • (x 1 - x 5) +
        (0 : ℝ) • (x 6 - x 5) + (-1 : ℝ) • F.e := rfl
    rw [hu, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
      inner_smul_right] at h1
    rw [he, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
      inner_smul_right] at h2
    have hB : ⟪w, F.e⟫ = 0 := by linarith
    refine ⟨?_, hB⟩
    have h3 : (F.S.tp - 1) * ⟪w, x 1 - x 5⟫ = 0 := by rw [hB] at h1; linarith
    exact (mul_eq_zero.mp h3).resolve_left (sub_neg.mpr F.S.tp_lt).ne

end Frame20

/-! ### The slide tests for `V` -/

namespace Shape20
variable (S : Shape20)

/-- `m2+ = sp xb + (1 - sp) m1+ - u_vN4` (it lies in the plane of the face, edge-on at `u_vN4`). -/
theorem Dc_m2p (a P : C3) :
    Dc a ((⟨0, S.sp, S.kp⟩ : C3).sub P) S.u_vN4 =
      S.sp * Dc a ((⟨0, 1, 0⟩ : C3).sub P) S.u_vN4 +
        (1 - S.sp) * Dc a ((⟨S.tp, 0, S.hp⟩ : C3).sub P) S.u_vN4 := by
  simp only [Dc, C3.sub, u_vN4]; ring

theorem m2p_pos (a P : C3) (h1 : 0 ≤ Dc a ((⟨0, 1, 0⟩ : C3).sub P) S.u_vN4)
    (h2 : 0 ≤ Dc a ((⟨S.tp, 0, S.hp⟩ : C3).sub P) S.u_vN4)
    (h : 0 < Dc a ((⟨0, 1, 0⟩ : C3).sub P) S.u_vN4 ∨ 0 < Dc a ((⟨S.tp, 0, S.hp⟩ : C3).sub P) S.u_vN4) :
    0 < Dc a ((⟨0, S.sp, S.kp⟩ : C3).sub P) S.u_vN4 := by
  rw [Dc_m2p]
  have hsp := S.sp_pos; have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  rcases h with h | h
  · nlinarith [mul_pos hsp h, mul_nonneg hsp1.le h2]
  · nlinarith [mul_pos hsp1 h, mul_nonneg hsp.le h1]

/-- The tangent test of `m2+` along the slide: it is exactly `η (Vp + k+ t+)`. -/
theorem tang_slide (η : ℝ) :
    PS 1 (C3.slide S.u_vN4 S.eF1 η) ((⟨S.tp, 0, S.hp⟩ : C3).sub ⟨0, 1, 0⟩)
        ((⟨0, S.sp, S.kp⟩ : C3).sub ⟨0, 1, 0⟩) ↔
      0 < η * ((-S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.tm - S.kp*S.tm) + S.kp * S.tp) := by
  have : Dc ((⟨S.tp, 0, S.hp⟩ : C3).sub ⟨0, 1, 0⟩) ((⟨0, S.sp, S.kp⟩ : C3).sub ⟨0, 1, 0⟩)
      (C3.slide S.u_vN4 S.eF1 η) =
      η * ((-S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.tm - S.kp*S.tm) + S.kp * S.tp) := by
    simp only [Dc, C3.sub, C3.slide, u_vN4, eF1]; ring
  unfold PS
  rw [this, one_mul]

theorem tang_ev
    (hV : 0 < -S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.tm - S.kp*S.tm) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), PS 1 (C3.slide S.u_vN4 S.eF1 η)
      ((⟨S.tp, 0, S.hp⟩ : C3).sub ⟨0, 1, 0⟩) ((⟨0, S.sp, S.kp⟩ : C3).sub ⟨0, 1, 0⟩) := by
  filter_upwards [self_mem_nhdsWithin] with η hη
  rw [tang_slide]
  exact mul_pos hη (by have := mul_pos S.kp_pos S.tp_pos; linarith)

theorem uD_ne
    (hV : 0 < -S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.tm - S.kp*S.tm) :
    (S.tm - S.tp) * S.u_vN4.z - (-S.hm - S.hp) * S.u_vN4.x ≠ 0 := by
  have : (S.tm - S.tp) * S.u_vN4.z - (-S.hm - S.hp) * S.u_vN4.x =
      (-S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.tm - S.kp*S.tm) + S.kp * S.tp := by
    simp only [u_vN4]; ring
  rw [this]
  have := mul_pos S.kp_pos S.tp_pos
  linarith

theorem mid5_ev
    (hV : 0 < -S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.tm - S.kp*S.tm)
    (hVW : 0 < -S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.sp + S.hp*S.tm - S.hp - S.kp*S.tm + S.kp) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      0 = S.tp + s * (S.tm - S.tp) + δ * (C3.slide S.u_vN4 S.eF1 η).x ∧
      0 = S.hp + s * (-S.hm - S.hp) + δ * (C3.slide S.u_vN4 S.eF1 η).z := by
  obtain ⟨s, δ, h1, h2, h3, h4, h5, h6⟩ := vN4_mid5 S hV hVW
  exact mid_slide_gen S.tp S.hp S.tm (-S.hm) 0 0 S.u_vN4.x S.u_vN4.z S.eF1.x S.eF1.z
    (by simpa [eF1] using S.uD_ne hV) ⟨s, δ, h1, h2, h3, h4, h6⟩

theorem mid1_ev
    (hV : 0 < -S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.tm - S.kp*S.tm)
    (hVW : 0 < -S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.sp + S.hp*S.tm - S.hp - S.kp*S.tm + S.kp) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      1 = S.tp + s * (S.tm - S.tp) + δ * (C3.slide S.u_vN4 S.eF1 η).x ∧
      0 = S.hp + s * (-S.hm - S.hp) + δ * (C3.slide S.u_vN4 S.eF1 η).z := by
  obtain ⟨s, δ, h1, h2, h3, h4, h5, h6⟩ := vN4_mid1 S hV hVW
  exact mid_slide_gen S.tp S.hp S.tm (-S.hm) 1 0 S.u_vN4.x S.u_vN4.z S.eF1.x S.eF1.z
    (by simpa [eF1] using S.uD_ne hV) ⟨s, δ, h1, h2, h3, h4, h6⟩

/-- `m2+` projects strictly inside `V`'s 4-cycle rim for small `η > 0` along the slide. -/
theorem vN4_rest_ev
    (hV : 0 < -S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.tm - S.kp*S.tm)
    (hVW : 0 < -S.hm*S.sp*S.tp + S.hm*S.tp - S.hp*S.sp*S.tm + S.hp*S.sp + S.hp*S.tm - S.hp - S.kp*S.tm + S.kp) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), PRest4 1 (C3.slide S.u_vN4 S.eF1 η) (⟨S.tp, 0, S.hp⟩ : C3)
      ⟨S.tm, 0, -S.hm⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨0, S.sp, S.kp⟩ := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := vN4_pcyc S hV hVW
  have t0 : PS 1 S.u_vN4 ((⟨S.tm, 0, -S.hm⟩ : C3).sub ⟨S.tp, 0, S.hp⟩)
      ((⟨0, S.sp, S.kp⟩ : C3).sub ⟨S.tp, 0, S.hp⟩) := by
    unfold PS at c2 ⊢; rw [one_mul] at c2 ⊢
    exact S.m2p_pos _ _ c2.le (le_of_eq (Shape18.Dc_zero_right _ _ _).symm) (Or.inl c2)
  have t1 : PS 1 S.u_vN4 ((⟨0, S.sm, -S.km⟩ : C3).sub ⟨S.tm, 0, -S.hm⟩)
      ((⟨0, S.sp, S.kp⟩ : C3).sub ⟨S.tm, 0, -S.hm⟩) := by
    unfold PS at c3 c4 ⊢; rw [one_mul] at c3 c4 ⊢
    exact S.m2p_pos _ _ c3.le c4.le (Or.inl c3)
  have t2 : PS 1 S.u_vN4 ((⟨0, 1, 0⟩ : C3).sub ⟨0, S.sm, -S.km⟩)
      ((⟨0, S.sp, S.kp⟩ : C3).sub ⟨0, S.sm, -S.km⟩) := by
    unfold PS at c5 ⊢; rw [one_mul] at c5 ⊢
    exact S.m2p_pos _ _ (le_of_eq (Shape18.Dc_self _ _).symm) c5.le (Or.inr c5)
  filter_upwards [PS_ev 1 S.u_vN4 S.eF1 _ _ t0, PS_ev 1 S.u_vN4 S.eF1 _ _ t1,
    PS_ev 1 S.u_vN4 S.eF1 _ _ t2, S.tang_ev hV] with η a b c d
  exact ⟨a, b, c, d⟩

end Shape20

namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- **`V` of class `N4`, slid along `F1`'s circle**: `Frame20.vN4` with `hnd` replaced by
`¬ F.ClassH`.  The strict tests of `vN4_pcyc` persist; `m2+` (an edge-on middle at `u_vN4`) becomes
a strict rest point (its test against `[xb, m1+]` is `η (Vp + k+ t+) > 0`); `v`, `xa` stay middles
over the chord; the rim stays robustly unimodal; no horizontal double normal for small `η` since no
persistent double normal off `ClassH`. -/
theorem vN4_slide (hx : Function.Injective x)
    (hV : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm)
    (hVW : 0 < -F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.sp + F.S.hp*F.S.tm - F.S.hp - F.S.kp*F.S.tm + F.S.kp)
    (hA : F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 0 < F.dep F.S.u_vN4 6 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 3 ∨ F.dep F.S.u_vN4 4 < F.dep F.S.u_vN4 6)
    (hB : F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 0 ∨ F.dep F.S.u_vN4 3 < F.dep F.S.u_vN4 4 ∨ F.dep F.S.u_vN4 6 < F.dep F.S.u_vN4 4)
    (hH : ¬ F.ClassH) :
    IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have hsp1 := F.S.sp_lt
  have ux : 0 < -F.S.sp * F.S.tp + F.S.tp := by nlinarith [mul_pos htp (sub_pos.2 hsp1)]
  have hnp := (F.noPersistHDN_or_classH_vN4 hV).resolve_right hH
  have hnd := F.toFrame7.eventually_noHDNRim_slide (quad 0 3 4 6) F.S.u_vN4 F.S.eF1 hnp
  have hcyc := (vN4_pcyc F.S hV hVW).ev F.S.eF1
  have hrest := F.S.vN4_rest_ev hV hVW
  have hmv := F.S.mid5_ev hV hVW
  have hmxa := F.S.mid1_ev hV hVW
  have hux := eventually_pos_affine (A := -F.S.sp * F.S.tp + F.S.tp) (B := F.S.tm - F.S.tp)
    (Or.inl ux)
  have hzev : ∀ᶠ η in 𝓝[>] (0 : ℝ), IsRobustUnimodal
      (quad (F.dep (C3.slide F.S.u_vN4 F.S.eF1 η) 0) (F.dep (C3.slide F.S.u_vN4 F.S.eF1 η) 3)
        (F.dep (C3.slide F.S.u_vN4 F.S.eF1 η) 4) (F.dep (C3.slide F.S.u_vN4 F.S.eF1 η) 6)) := by
    have h0 := Q4_ev_strict
      (z := quad (F.dep F.S.u_vN4 0) (F.dep F.S.u_vN4 3) (F.dep F.S.u_vN4 4) (F.dep F.S.u_vN4 6))
      (w := quad (F.dep F.S.eF1 0) (F.dep F.S.eF1 3) (F.dep F.S.eF1 4) (F.dep F.S.eF1 6))
      (by simpa only [quad_0, quad_1, quad_2, quad_3] using hA)
      (by simpa only [quad_0, quad_1, quad_2, quad_3] using hB)
    filter_upwards [h0] with η hη
    obtain ⟨hA', hB'⟩ := hη
    simp only [quad_0, quad_1, quad_2, quad_3] at hA' hB'
    simp only [Frame20.dep_slide]
    exact robust_quad_of_nws hA' hB'
  obtain ⟨η, hnd', hc, hr, hm5, hm1, hu, hz⟩ :=
    (hnd.and (hcyc.and (hrest.and (hmv.and (hmxa.and (hux.and hzev)))))).exists
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  refine F.toFrame7.vertex4_rim hx 0 3 4 6 _ _ _ _ F.ptC_0 F.ptC_3 F.ptC_4 F.ptC_6
    ({5, 1} : Finset (Fin 7)) ?_ 1 (Or.inl rfl) (C3.slide F.S.u_vN4 F.S.eF1 η)
    (Or.inl (by simp only [C3.slide, Shape20.u_vN4, Shape20.eF1]; exact hu.ne')) hc ?_ ?_ hnd' ?_
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl <;> decide
  · intro j' hjM h0 h1 h2 h3
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · exact absurd (by simp) hjM
    · rw [F.ptC_2]; exact hr
    · exact absurd rfl h1
    · exact absurd rfl h2
    · exact absurd (by simp) hjM
    · exact absurd rfl h3
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using hz
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · obtain ⟨s, δ, hs0, hs1, hδ, ex, ez⟩ := hm5
      refine ⟨0, s, δ, hs0, hs1, hδ, ?_, ?_, ?_⟩ <;>
        simp [b0, quad_0, quad_1, F.ptC_5, C3.slide,
          Shape20.u_vN4, Shape20.eF1] at ex ez ⊢ <;> linarith
    · obtain ⟨s, δ, hs0, hs1, hδ, ex, ez⟩ := hm1
      refine ⟨0, s, δ, hs0, hs1, hδ, ?_, ?_, ?_⟩ <;>
        simp [b0, quad_0, quad_1, F.ptC_1, C3.slide,
          Shape20.u_vN4, Shape20.eF1] at ex ez ⊢ <;> linarith

/-- **`T_A` for `b+ < a-`** (as `Frame20.tANR'`): `hnp` replaced by `¬ F.ClassH`. -/
theorem tANR_slide (hx : Function.Injective x)
    (hA1 : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm)
    (hA : F.dep F.S.u_tANR 0 < F.dep F.S.u_tANR 6 ∨ F.dep F.S.u_tANR 0 < F.dep F.S.u_tANR 3 ∨ F.dep F.S.u_tANR 4 < F.dep F.S.u_tANR 6 ∨ F.dep F.S.u_tANR 4 < F.dep F.S.u_tANR 3)
    (hB : F.dep F.S.u_tANR 6 < F.dep F.S.u_tANR 0 ∨ F.dep F.S.u_tANR 3 < F.dep F.S.u_tANR 0 ∨ F.dep F.S.u_tANR 6 < F.dep F.S.u_tANR 4 ∨ F.dep F.S.u_tANR 3 < F.dep F.S.u_tANR 4)
    (hH : ¬ F.ClassH) :
    IsRupert (Finset.univ.image x) :=
  F.tANR' hx hA1 hA hB ((F.noPersistHDN_or_classH_tANR).resolve_right hH)

end Frame20

end Minimality.CaseC20

end
