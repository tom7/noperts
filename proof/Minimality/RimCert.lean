module

public import Minimality.LimitRim
public import Minimality.RobustEdge

@[expose] public section

/-!
# Rim certificates in point form (`FEWER-FACES-PROOFS.md` §18.2)

The crossing tests of the tier proofs end in a rim that is strictly convex and counterclockwise
at the view, with robustly unimodal depths, every other point inside, over a side (a middle) or
over a corner (a double or the other axle end).  `RimCertPts V u y` records exactly the part of
this that passes to limits (`RimCertAt` in label form): no horizontal double normal and no
classification of the other points with `δ ≠ 0` (both are checked at the limit shape).

* `RimCertPts`, `RimCert` (a rim with 3, 4 or 5 corners), `RimCertPts.toAt` (labels).
* `rimCertPts_of_class`: from the determinant tests, the robust depths, and every point either
  over a closed side of the rim (corner, double, middle) or strictly inside.
* `rimCertPts_quad`, `rimCertPts_tri`, `rimCertPts_quint`: explicit rims.
* `rimCert_edgePair_robust`, `rimCert_edgeTri_robust`: Lemma E with ties and triangle closings
  (`isRupert_edgePair_robust`, `isRupert_edgeTri_robust` without the horizontal double normal).
-/

namespace Minimality

open scoped RealInnerProductSpace
open Finset

/-- **A rim certificate in point form**: the cycle `y` of points of `V` is strictly convex and
counterclockwise at `u`, every point of `V` lies weakly left of every side, and the depths
along `u` are robustly unimodal. -/
structure RimCertPts {k : ℕ} (V : Finset ℝ³) (u : ℝ³) (y : ZMod k → ℝ³) : Prop where
  three : 3 ≤ k
  mem : ∀ i, y i ∈ V
  cyc : ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 → 0 < det3 (y (i + 1) - y i) (y j - y i) u
  left : ∀ z ∈ V, ∀ i : ZMod k, 0 ≤ det3 (y (i + 1) - y i) (z - y i) u
  robust : IsRobustUnimodal (fun i => ⟪y i, u⟫)

/-- **A rim certificate with 3, 4 or 5 corners** at the view `u`. -/
def RimCert (V : Finset ℝ³) (u : ℝ³) : Prop :=
  ∃ k : ℕ, (k = 3 ∨ k = 4 ∨ k = 5) ∧ ∃ y : ZMod k → ℝ³, RimCertPts V u y

theorem RimCertPts.smul {k : ℕ} {V : Finset ℝ³} {u : ℝ³} {y : ZMod k → ℝ³}
    (h : RimCertPts V u y) {c : ℝ} (hc : 0 < c) : RimCertPts V (c • u) y where
  three := h.three
  mem := h.mem
  cyc i j hi hj := by rw [det3_smul_right]; exact mul_pos hc (h.cyc i j hi hj)
  left z hz i := by rw [det3_smul_right]; exact mul_nonneg hc.le (h.left z hz i)
  robust := by
    simp only [real_inner_smul_right]
    exact h.robust.smul hc

theorem RimCertPts.rimCert {V : Finset ℝ³} {u : ℝ³} {k : ℕ} {y : ZMod k → ℝ³}
    (hk : k = 3 ∨ k = 4 ∨ k = 5) (h : RimCertPts V u y) : RimCert V u :=
  ⟨k, hk, y, h⟩

/-- **Labels for a rim of an indexed point set.** -/
theorem RimCertPts.toAt {n k : ℕ} {x : Fin n → ℝ³} {u : ℝ³} {y : ZMod k → ℝ³}
    (h : RimCertPts (univ.image x) u y) :
    ∃ lab : ZMod k → Fin n, (∀ i, x (lab i) = y i) ∧ RimCertAt x u lab := by
  choose lab hlab using fun i => mem_image.mp (h.mem i)
  have e : ∀ i, x (lab i) = y i := fun i => (hlab i).2
  refine ⟨lab, e, h.three, fun i j hi hj => ?_, fun m i => ?_, ?_⟩
  · rw [e, e, e]; exact h.cyc i j hi hj
  · rw [e, e]; exact h.left _ (mem_image_of_mem x (mem_univ m)) i
  · simp only [e]; exact h.robust

theorem det3_comb_seg (e₀ e₁ u a b : ℝ³) (s δ : ℝ) :
    det3 e₀ (a + s • (b - a) + δ • u - e₁) u =
      (1 - s) * det3 e₀ (a - e₁) u + s * det3 e₀ (b - e₁) u := by
  simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring

/-- **Rim certificates from a classification of the points**: the determinant tests, robust
depths, and every point of `V` over a closed side `[y j₁, y j₂]` of the rim (a corner, a double
over a corner, a middle) or strictly left of every side. -/
theorem rimCertPts_of_class (V : Finset ℝ³) (u : ℝ³) {k : ℕ} (hk : 3 ≤ k) (y : ZMod k → ℝ³)
    (hyV : ∀ i, y i ∈ V)
    (hcyc : ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 → 0 < det3 (y (i + 1) - y i) (y j - y i) u)
    (hclass : ∀ z ∈ V, (∃ j₁ j₂ : ZMod k, ∃ s δ : ℝ, 0 ≤ s ∧ s ≤ 1 ∧
      z = y j₁ + s • (y j₂ - y j₁) + δ • u) ∨
      ∀ i, 0 < det3 (y (i + 1) - y i) (z - y i) u)
    (hz : IsRobustUnimodal (fun i => ⟪y i, u⟫)) : RimCertPts V u y := by
  have corner : ∀ i j : ZMod k, 0 ≤ det3 (y (i + 1) - y i) (y j - y i) u := by
    intro i j
    by_cases h1 : j = i
    · subst h1; rw [sub_self]; simp [det3_expand]
    by_cases h2 : j = i + 1
    · subst h2; apply le_of_eq; simp only [det3_expand]; ring
    exact (hcyc i j h1 h2).le
  refine ⟨hk, hyV, hcyc, fun z hzV i => ?_, hz⟩
  rcases hclass z hzV with ⟨j₁, j₂, s, δ, hs0, hs1, rfl⟩ | h
  · rw [det3_comb_seg]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (corner i j₁), mul_nonneg hs0 (corner i j₂)]
  · exact (h i).le

/-- A corner is over a closed side. -/
theorem class_corner {k : ℕ} {y : ZMod k → ℝ³} {u : ℝ³} (j : ZMod k) :
    ∃ j₁ j₂ : ZMod k, ∃ s δ : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ y j = y j₁ + s • (y j₂ - y j₁) + δ • u :=
  ⟨j, j, 0, 0, le_rfl, zero_le_one, by simp⟩

/-- A double over a corner is over a closed side. -/
theorem class_double {k : ℕ} {y : ZMod k → ℝ³} {u z : ℝ³} (j : ZMod k) (t : ℝ)
    (hz : z = y j + t • u) :
    ∃ j₁ j₂ : ZMod k, ∃ s δ : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ z = y j₁ + s • (y j₂ - y j₁) + δ • u :=
  ⟨j, j, 0, t, le_rfl, zero_le_one, by simp [hz]⟩

/-- A middle over a side, chords from doubles allowed. -/
theorem class_middle {k : ℕ} {y : ZMod k → ℝ³} {u z : ℝ³} (j₁ j₂ : ZMod k) (t₁ t₂ s δ : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hz : z = (y j₁ + t₁ • u) + s • ((y j₂ + t₂ • u) - (y j₁ + t₁ • u)) + δ • u) :
    ∃ j₁ j₂ : ZMod k, ∃ s δ : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ z = y j₁ + s • (y j₂ - y j₁) + δ • u :=
  ⟨j₁, j₂, s, t₁ + s * (t₂ - t₁) + δ, hs0, hs1, by rw [hz]; module⟩

/-! ### Explicit rims -/

/-- **A quadrilateral rim** `y₀ y₁ y₂ y₃`: its eight tests, every point over a closed side or
strictly inside, robust depths. -/
theorem rimCertPts_quad (V : Finset ℝ³) {u y₀ y₁ y₂ y₃ : ℝ³} (h₀ : y₀ ∈ V) (h₁ : y₁ ∈ V)
    (h₂ : y₂ ∈ V) (h₃ : y₃ ∈ V)
    (c₁ : 0 < det3 (y₁ - y₀) (y₂ - y₀) u) (c₂ : 0 < det3 (y₁ - y₀) (y₃ - y₀) u)
    (c₃ : 0 < det3 (y₂ - y₁) (y₃ - y₁) u) (c₄ : 0 < det3 (y₂ - y₁) (y₀ - y₁) u)
    (c₅ : 0 < det3 (y₃ - y₂) (y₀ - y₂) u) (c₆ : 0 < det3 (y₃ - y₂) (y₁ - y₂) u)
    (c₇ : 0 < det3 (y₀ - y₃) (y₁ - y₃) u) (c₈ : 0 < det3 (y₀ - y₃) (y₂ - y₃) u)
    (hclass : ∀ z ∈ V, (∃ j₁ j₂ : ZMod 4, ∃ s δ : ℝ, 0 ≤ s ∧ s ≤ 1 ∧
      z = quad y₀ y₁ y₂ y₃ j₁ + s • (quad y₀ y₁ y₂ y₃ j₂ - quad y₀ y₁ y₂ y₃ j₁) + δ • u) ∨
      (0 < det3 (y₁ - y₀) (z - y₀) u ∧ 0 < det3 (y₂ - y₁) (z - y₁) u ∧
        0 < det3 (y₃ - y₂) (z - y₂) u ∧ 0 < det3 (y₀ - y₃) (z - y₃) u))
    (hz : IsRobustUnimodal (quad ⟪y₀, u⟫ ⟪y₁, u⟫ ⟪y₂, u⟫ ⟪y₃, u⟫)) :
    RimCertPts V u (quad y₀ y₁ y₂ y₃) := by
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  refine rimCertPts_of_class V u (by norm_num) _ ?_ ?_ (fun z hz => ?_) (by rw [quad_inner]; exact hz)
  · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
    exacts [h₀, h₁, h₂, h₃]
  · intro i j hi hj
    rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
    exacts [c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈]
  · rcases hclass z hz with h | ⟨r0, r1, r2, r3⟩
    · exact Or.inl h
    · refine Or.inr fun i => ?_
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
      exacts [r0, r1, r2, r3]

/-- **A triangle rim** `y₀ y₁ y₂` (counterclockwise): every point over a closed side or strictly
inside, the three depths not all equal. -/
theorem rimCertPts_tri (V : Finset ℝ³) {u y₀ y₁ y₂ : ℝ³} (h₀ : y₀ ∈ V) (h₁ : y₁ ∈ V)
    (h₂ : y₂ ∈ V) (c : 0 < det3 (y₁ - y₀) (y₂ - y₀) u)
    (hclass : ∀ z ∈ V, (∃ j₁ j₂ : ZMod 3, ∃ s δ : ℝ, 0 ≤ s ∧ s ≤ 1 ∧
      z = tri y₀ y₁ y₂ j₁ + s • (tri y₀ y₁ y₂ j₂ - tri y₀ y₁ y₂ j₁) + δ • u) ∨
      (0 < det3 (y₁ - y₀) (z - y₀) u ∧ 0 < det3 (y₂ - y₁) (z - y₁) u ∧
        0 < det3 (y₀ - y₂) (z - y₂) u))
    (hz : ¬ (⟪y₀, u⟫ = ⟪y₁, u⟫ ∧ ⟪y₁, u⟫ = ⟪y₂, u⟫)) :
    RimCertPts V u (tri y₀ y₁ y₂) := by
  obtain ⟨b0, b1, b2⟩ := zmod3_add_one
  have i1 : det3 (y₂ - y₁) (y₀ - y₁) u = det3 (y₁ - y₀) (y₂ - y₀) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i2 : det3 (y₀ - y₂) (y₁ - y₂) u = det3 (y₁ - y₀) (y₂ - y₀) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  refine rimCertPts_of_class V u le_rfl _ ?_ ?_ (fun z hz => ?_)
    (by rw [tri_inner]; exact isRobustUnimodal_three hz)
  · intro i; rcases zmod3_cases i with rfl | rfl | rfl
    exacts [h₀, h₁, h₂]
  · intro i j hi hj
    rcases zmod3_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [b0, b1, b2, tri_0, tri_1, tri_2, i1, i2]
    exacts [c, c, c]
  · rcases hclass z hz with h | ⟨r0, r1, r2⟩
    · exact Or.inl h
    · refine Or.inr fun i => ?_
      rcases zmod3_cases i with rfl | rfl | rfl <;> simp only [b0, b1, b2, tri_0, tri_1, tri_2]
      exacts [r0, r1, r2]

/-! ### Lemma E with ties, certificate form -/

/-- **One closing of an edge crossing, certified**: the rim `(y, a, c, b)` at `u`, the other
axle end `o = y + t u`, every other point a middle over a side at the apex (`EdgeMiddle` with
`o`) or strictly inside. -/
theorem rimCertPts_closing (V : Finset ℝ³) {u y o a b c : ℝ³} {t : ℝ} (ho : o = y + t • u)
    (hyV : y ∈ V) (haV : a ∈ V) (hbV : b ∈ V) (hcV : c ∈ V)
    (q₁ : 0 < det3 (a - y) (c - y) u) (q₂ : 0 < det3 (c - a) (b - a) u)
    (q₃ : 0 < det3 (b - c) (y - c) u) (q₄ : 0 < det3 (y - b) (a - b) u)
    (hV : ∀ z ∈ V, z = y ∨ z = o ∨ z = a ∨ z = b ∨ z = c ∨
      (∃ e : ℝ³, ∃ s δ : ℝ, (e = y ∨ e = o) ∧ 0 < s ∧ s < 1 ∧
        (z = e + s • (a - e) + δ • u ∨ z = b + s • (e - b) + δ • u)) ∨
      EdgeHidden u y a c b z)
    (hN : NWS4 (quad ⟪y, u⟫ ⟪a, u⟫ ⟪c, u⟫ ⟪b, u⟫)) : RimCertPts V u (quad y a c b) := by
  have i2 : det3 (a - y) (b - y) u = det3 (y - b) (a - b) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i4 : det3 (c - a) (y - a) u = det3 (a - y) (c - y) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i6 : det3 (b - c) (a - c) u = det3 (c - a) (b - a) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i8 : det3 (y - b) (c - b) u = det3 (b - c) (y - c) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  refine rimCertPts_quad V hyV haV hcV hbV q₁ (by rw [i2]; exact q₄) q₂ (by rw [i4]; exact q₁) q₃
    (by rw [i6]; exact q₂) q₄ (by rw [i8]; exact q₃) (fun z hz => ?_) hN.isRobustUnimodal
  rcases hV z hz with h | h | h | h | h | ⟨e, s, δ, he, hs0, hs1, hm⟩ | hid
  · exact Or.inl ⟨0, 0, 0, 0, le_rfl, zero_le_one, by rw [h]; simp [quad_0]⟩
  · exact Or.inl (class_double 0 t (by rw [h, ho]; rfl))
  · exact Or.inl ⟨1, 1, 0, 0, le_rfl, zero_le_one, by rw [h]; simp [quad_1]⟩
  · exact Or.inl ⟨3, 3, 0, 0, le_rfl, zero_le_one, by rw [h]; simp [quad_3]⟩
  · exact Or.inl ⟨2, 2, 0, 0, le_rfl, zero_le_one, by rw [h]; simp [quad_2]⟩
  · left
    obtain ⟨t', he'⟩ : ∃ t' : ℝ, e = y + t' • u := by
      rcases he with he | he
      · exact ⟨0, by rw [he]; simp⟩
      · exact ⟨t, by rw [he, ho]⟩
    rcases hm with hm | hm
    · exact class_middle (y := quad y a c b) 0 1 t' 0 s δ hs0.le hs1.le
        (by simp only [quad_0, quad_1, zero_smul, add_zero]; rw [hm, he'])
    · exact class_middle (y := quad y a c b) 3 0 0 t' s δ hs0.le hs1.le
        (by simp only [quad_0, quad_3, zero_smul, add_zero]; rw [hm, he'])
  · exact Or.inr hid

/-- **Lemma E with ties, certificate form** (`isRupert_edgePair_robust` without the horizontal
double normal): one of the closings `(v, a, c, b)`, `(w, a, c, b)` at `u = w − v` is a rim
certificate. -/
theorem rimCert_edgePair_robust {v w a b c : ℝ³} (V : Finset ℝ³)
    (hvV : v ∈ V) (hwV : w ∈ V) (haV : a ∈ V) (hbV : b ∈ V) (hcV : c ∈ V)
    (q₁ : 0 < det3 (a - v) (c - v) (w - v)) (q₂ : 0 < det3 (c - a) (b - a) (w - v))
    (q₃ : 0 < det3 (b - c) (v - c) (w - v)) (q₄ : 0 < det3 (v - b) (a - b) (w - v))
    (hE : det3 (b - a) (c - a) (v - a) * det3 (b - a) (c - a) (w - a) ≤ 0)
    (h3 : ¬ (⟪a, w - v⟫ = ⟪c, w - v⟫ ∧ ⟪c, w - v⟫ = ⟪b, w - v⟫))
    (hV : ∀ z ∈ V, z = v ∨ z = w ∨ z = a ∨ z = b ∨ z = c ∨ EdgeMid v w a b z ∨
      EdgeHidden (w - v) v a c b z) :
    RimCert V (w - v) := by
  have mid : ∀ z, EdgeMid v w a b z → ∃ e : ℝ³, ∃ s δ : ℝ, (e = v ∨ e = w) ∧ 0 < s ∧ s < 1 ∧
      (z = e + s • (a - e) + δ • (w - v) ∨ z = b + s • (e - b) + δ • (w - v)) := by
    rintro z ⟨s, δ, hs0, hs1, -, h⟩
    rcases h with h | h | h | h
    · exact ⟨v, s, -δ, Or.inl rfl, hs0, hs1, Or.inl (by rw [h]; module)⟩
    · exact ⟨v, s, -δ, Or.inl rfl, hs0, hs1, Or.inr (by rw [h]; module)⟩
    · exact ⟨w, s, δ, Or.inr rfl, hs0, hs1, Or.inl h⟩
    · exact ⟨w, s, δ, Or.inr rfl, hs0, hs1, Or.inr h⟩
  rcases edgePair_nws q₁ q₂ q₃ q₄ hE h3 with hN | hN
  · refine (rimCertPts_closing V (o := w) (t := 1) (by module) hvV haV hbV hcV q₁ q₂ q₃ q₄
      (fun z hz => ?_) hN).rimCert (by norm_num)
    rcases hV z hz with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (mid z h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  · refine (rimCertPts_closing V (o := v) (t := -1) (by module) hwV haV hbV hcV
      (by rw [det3_vw_both]; exact q₁) q₂ (by rw [det3_vw_right]; exact q₃)
      (by rw [det3_vw_left]; exact q₄) (fun z hz => ?_) hN).rimCert (by norm_num)
    rcases hV z hz with h | h | h | h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · obtain ⟨e, s, δ, he, hs0, hs1, hm⟩ := mid z h
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, s, δ, he.symm, hs0, hs1,
        hm⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h.shift)))))

/-- **A triangle closing, certificate form** (`isRupert_edgeTri_robust` without the horizontal
double normal). -/
theorem rimCert_edgeTri_robust {v w a b : ℝ³} (V : Finset ℝ³)
    (hvV : v ∈ V) (hwV : w ∈ V) (haV : a ∈ V) (hbV : b ∈ V)
    (hT : 0 < det3 (a - v) (b - v) (w - v))
    (hz : ¬ (⟪v, w - v⟫ = ⟪a, w - v⟫ ∧ ⟪a, w - v⟫ = ⟪b, w - v⟫))
    (hV : ∀ z ∈ V, z = v ∨ z = w ∨ z = a ∨ z = b ∨ EdgeMid v w a b z ∨
      TriHidden (w - v) v a b z) :
    RimCert V (w - v) := by
  refine (rimCertPts_tri V hvV haV hbV hT (fun z hz' => ?_) hz).rimCert (by norm_num)
  rcases hV z hz' with h | h | h | h | ⟨s, δ, hs0, hs1, -, hm⟩ | ⟨r1, r2, r3⟩
  · exact Or.inl ⟨0, 0, 0, 0, le_rfl, zero_le_one, by rw [h]; simp [tri_0]⟩
  · exact Or.inl (class_double (y := tri v a b) 0 1 (by rw [h, tri_0]; module))
  · exact Or.inl ⟨1, 1, 0, 0, le_rfl, zero_le_one, by rw [h]; simp [tri_1]⟩
  · exact Or.inl ⟨2, 2, 0, 0, le_rfl, zero_le_one, by rw [h]; simp [tri_2]⟩
  · left
    rcases hm with h | h | h | h
    · exact class_middle (y := tri v a b) 0 1 0 0 s (-δ) hs0.le hs1.le
        (by simp only [tri_0, tri_1, zero_smul, add_zero]; rw [h]; module)
    · exact class_middle (y := tri v a b) 2 0 0 0 s (-δ) hs0.le hs1.le
        (by simp only [tri_0, tri_2, zero_smul, add_zero]; rw [h]; module)
    · exact class_middle (y := tri v a b) 0 1 1 0 s δ hs0.le hs1.le
        (by simp only [tri_0, tri_1, zero_smul, add_zero, one_smul]; rw [h]; module)
    · exact class_middle (y := tri v a b) 2 0 0 1 s δ hs0.le hs1.le
        (by simp only [tri_0, tri_2, zero_smul, add_zero, one_smul]; rw [h]; module)
  · exact Or.inr ⟨r1, r2, r3⟩

/-! ### Ties at the segment views -/

/-- **At most one tie at the view along each segment** (the tie clause of `GenPosTie`, without
the parallel clause). -/
structure TieSeg (V : Finset ℝ³) : Prop where
  tie : ∀ v ∈ V, ∀ w ∈ V, v ≠ w → OneTieAt V (w - v)

theorem GenPosTie.toTieSeg {V : Finset ℝ³} (h : GenPosTie V) : TieSeg V := ⟨h.tie⟩

/-- `TieSeg`: at an edge view, no three points have equal depths (as `GenPosTie.noTriple`). -/
theorem TieSeg.noTriple {V : Finset ℝ³} (hg : TieSeg V) {v w s t r : ℝ³} (hv : v ∈ V)
    (hw : w ∈ V) (hs : s ∈ V) (ht : t ∈ V) (hr : r ∈ V) (hvw : v ≠ w) (hst : s ≠ t)
    (htr : t ≠ r) (hsr : s ≠ r) : ¬ (⟪s, w - v⟫ = ⟪t, w - v⟫ ∧ ⟪t, w - v⟫ = ⟪r, w - v⟫) := by
  rintro ⟨e1, e2⟩
  rcases hg.tie v hv w hw hvw s hs t ht t ht r hr hst htr e1 e2 with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact hst h1
  · exact hsr h1


/-! ### Orientation signs -/

theorem IsRobustUnimodal.sigma {k : ℕ} {z : ZMod k → ℝ} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hz : IsRobustUnimodal z) : IsRobustUnimodal (fun i => σ * z i) := by
  rcases hσ with rfl | rfl
  · simpa using hz
  · simpa using hz.neg

/-- A point over a closed side at the view `u` is over a closed side at `σ u` (`σ = ±1`). -/
theorem class_sigma {k : ℕ} {y : ZMod k → ℝ³} {u z : ℝ³} {σ : ℝ} (hσσ : σ * σ = 1)
    (h : ∃ j₁ j₂ : ZMod k, ∃ s δ : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ z = y j₁ + s • (y j₂ - y j₁) + δ • u) :
    ∃ j₁ j₂ : ZMod k, ∃ s δ : ℝ, 0 ≤ s ∧ s ≤ 1 ∧
      z = y j₁ + s • (y j₂ - y j₁) + δ • (σ • u) := by
  obtain ⟨j₁, j₂, s, δ, hs0, hs1, rfl⟩ := h
  refine ⟨j₁, j₂, s, σ * δ, hs0, hs1, ?_⟩
  rw [smul_smul, show σ * δ * σ = δ * (σ * σ) by ring, hσσ, mul_one]

theorem sigma_ne_zero {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : σ ≠ 0 := by
  rcases hσ with rfl | rfl <;> norm_num

theorem det3_sigma (a b u : ℝ³) (σ : ℝ) : σ * det3 a b u = det3 a b (σ • u) :=
  (det3_smul_right a b u σ).symm


end Minimality

end
