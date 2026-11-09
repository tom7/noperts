module

public import Minimality.RobustCert

@[expose] public section

/-!
# The octahedral axis test with depth ties (Theorem 18.3 for triangle and 4-corner rims)

The vertex-crossing test of Theorem 13.7 (`isRupert_axisTest_core`, `OctAxis.lean`) has a
triangle rim `a' b b'` or a quadrilateral rim `a' b a b'`.  It asked for distinct depths of the
four corners.  With Theorem 18.3 (`isRupert_of_vertexView_robust`) ties are allowed as long as
the rim stays robustly unimodal (§18.0, §18.4):
* a triangle is robustly unimodal unless its three depths are equal
  (`isRobustUnimodal_three`);
* a quadrilateral whose diagonals are not depth-separated is robustly unimodal unless three
  depths are equal or a level edge lies inside a monotone run (`isRobustUnimodal_quad`).

`QuadTie z₀ z₁ z₂ z₃` collects these two exclusions for the 4-cycle `z₀ z₁ z₂ z₃`; it is
implied by distinct depths (`QuadTie.of_nodup`).  Allowed: a tie between opposite corners, a
level edge at the top or the bottom, and any tie between two corners of the triangle rim.

* `isRupert_axisTest_core_robust`, `isRupert_axisTest_robust`: the forms of
  `isRupert_axisTest_core`, `isRupert_axisTest` with `QuadTie` in place of distinct depths.
-/

namespace Minimality

open scoped RealInnerProductSpace
open Finset

/-- **Ties on a 4-cycle that keep it robust** (given non-separated diagonals): no three equal
depths, and no level edge `zᵢ = zᵢ₊₁` whose outer neighbours lie strictly on opposite sides. -/
def QuadTie (z₀ z₁ z₂ z₃ : ℝ) : Prop :=
  ¬ (z₀ = z₁ ∧ z₁ = z₂) ∧ ¬ (z₀ = z₁ ∧ z₁ = z₃) ∧ ¬ (z₀ = z₂ ∧ z₂ = z₃) ∧
    ¬ (z₁ = z₂ ∧ z₂ = z₃) ∧
    ¬ (z₃ < z₀ ∧ z₀ = z₁ ∧ z₁ < z₂) ∧ ¬ (z₀ < z₃ ∧ z₀ = z₁ ∧ z₂ < z₁) ∧
    ¬ (z₀ < z₁ ∧ z₁ = z₂ ∧ z₂ < z₃) ∧ ¬ (z₁ < z₀ ∧ z₁ = z₂ ∧ z₃ < z₂) ∧
    ¬ (z₁ < z₂ ∧ z₂ = z₃ ∧ z₃ < z₀) ∧ ¬ (z₂ < z₁ ∧ z₂ = z₃ ∧ z₀ < z₃) ∧
    ¬ (z₂ < z₃ ∧ z₃ = z₀ ∧ z₀ < z₁) ∧ ¬ (z₃ < z₂ ∧ z₃ = z₀ ∧ z₁ < z₀)

/-- Distinct depths are allowed ties. -/
theorem QuadTie.of_nodup {z₀ z₁ z₂ z₃ : ℝ} (h : [z₀, z₁, z₂, z₃].Nodup) :
    QuadTie z₀ z₁ z₂ z₃ := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at h
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, h6, -⟩ := h
  refine ⟨fun h => h1 h.1, fun h => h1 h.1, fun h => h2 h.1, fun h => h4 h.1, fun h => h1 h.2.1,
    fun h => h1 h.2.1, fun h => h4 h.2.1, fun h => h4 h.2.1, fun h => h6 h.2.1, fun h => h6 h.2.1,
    fun h => h3 h.2.1.symm, fun h => h3 h.2.1.symm⟩

/-- **A 4-cycle with ties.**  If neither diagonal `{z₀, z₂}`, `{z₁, z₃}` lies strictly above the
other and the ties are allowed ones (`QuadTie`), the 4-cycle is robustly unimodal. -/
theorem isRobustUnimodal_quad {z₀ z₁ z₂ z₃ : ℝ} (hq : QuadTie z₀ z₁ z₂ z₃)
    (h1 : ¬ (max z₁ z₃ < min z₀ z₂)) (h2 : ¬ (max z₀ z₂ < min z₁ z₃)) :
    IsRobustUnimodal (quad z₀ z₁ z₂ z₃) := by
  obtain ⟨t1, t2, t3, t4, l1, l2, l3, l4, l5, l6, l7, l8⟩ := hq
  simp only [max_lt_iff, lt_min_iff, not_and_or, not_lt] at h1 h2
  have hpos : ∀ (B : ZMod 4) (a b c d : ℕ), a < b → b < c → c < d → d < 4 →
      a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 := fun B a b c d h1 h2 h3 h4 => by omega
  refine ⟨fun B a b c d hab hbc hcd hdk h => ?_, fun i j l hij hjl hil e1 e2 => ?_,
    fun B a b c d hab hbc hcd hdk e => ?_⟩
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := hpos B a b c d hab hbc hcd hdk
    simp only [Nat.cast_zero, add_zero, Nat.cast_one, Nat.cast_ofNat] at h
    rcases zmod4_table B with ⟨rfl, e1, e2, e3⟩ | ⟨rfl, e1, e2, e3⟩ | ⟨rfl, e1, e2, e3⟩ |
      ⟨rfl, e1, e2, e3⟩ <;> rw [e1, e2, e3] at h <;>
      simp only [quad_0, quad_1, quad_2, quad_3] at h <;> obtain ⟨k1, k2, k3, k4⟩ := h <;>
      rcases h1 with (h | h) | (h | h) <;> rcases h2 with (h' | h') | (h' | h') <;> linarith
  · rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
      rcases zmod4_cases l with rfl | rfl | rfl | rfl <;>
      simp only [quad_0, quad_1, quad_2, quad_3] at e1 e2 <;>
      first
        | exact hij rfl | exact hjl rfl | exact hil rfl
        | exact t1 ⟨by linarith, by linarith⟩ | exact t2 ⟨by linarith, by linarith⟩
        | exact t3 ⟨by linarith, by linarith⟩ | exact t4 ⟨by linarith, by linarith⟩
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := hpos B a b c d hab hbc hcd hdk
    simp only [Nat.cast_zero, add_zero, Nat.cast_one, Nat.cast_ofNat] at e ⊢
    rcases zmod4_table B with ⟨rfl, e1, e2, e3⟩ | ⟨rfl, e1, e2, e3⟩ | ⟨rfl, e1, e2, e3⟩ |
      ⟨rfl, e1, e2, e3⟩ <;> rw [e1, e2] at e <;> rw [e1, e2, e3] <;>
      simp only [quad_0, quad_1, quad_2, quad_3] at e ⊢
    · exact ⟨fun h => l3 ⟨h.1, e, h.2⟩, fun h => l4 ⟨h.1, e, h.2⟩⟩
    · exact ⟨fun h => l5 ⟨h.1, e, h.2⟩, fun h => l6 ⟨h.1, e, h.2⟩⟩
    · exact ⟨fun h => l7 ⟨h.1, e, h.2⟩, fun h => l8 ⟨h.1, e, h.2⟩⟩
    · exact ⟨fun h => l1 ⟨h.1, e, h.2⟩, fun h => l2 ⟨h.1, e, h.2⟩⟩

theorem QuadTie.mul {z₀ z₁ z₂ z₃ : ℝ} (h : QuadTie z₀ z₁ z₂ z₃) {t : ℝ} (ht : t = 1 ∨ t = -1) :
    QuadTie (t * z₀) (t * z₁) (t * z₂) (t * z₃) := by
  rcases ht with rfl | rfl
  · simpa using h
  · obtain ⟨t1, t2, t3, t4, l1, l2, l3, l4, l5, l6, l7, l8⟩ := h
    unfold QuadTie
    simp only [neg_one_mul, neg_inj, neg_lt_neg_iff]
    exact ⟨t1, t2, t3, t4, fun h => l2 ⟨h.1, h.2.1, h.2.2⟩, fun h => l1 ⟨h.1, h.2.1, h.2.2⟩,
      fun h => l4 ⟨h.1, h.2.1, h.2.2⟩, fun h => l3 ⟨h.1, h.2.1, h.2.2⟩,
      fun h => l6 ⟨h.1, h.2.1, h.2.2⟩, fun h => l5 ⟨h.1, h.2.1, h.2.2⟩,
      fun h => l8 ⟨h.1, h.2.1, h.2.2⟩, fun h => l7 ⟨h.1, h.2.1, h.2.2⟩⟩

theorem tri_robust_smul {σ x y w : ℝ} (hσ0 : σ ≠ 0) (h : ¬ (x = y ∧ y = w)) :
    IsRobustUnimodal (tri (σ * x) (σ * y) (σ * w)) :=
  isRobustUnimodal_three fun ⟨h1, h2⟩ => h ⟨mul_left_cancel₀ hσ0 h1, mul_left_cancel₀ hσ0 h2⟩

theorem quad_robust_smul {σ z₀ z₁ z₂ z₃ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hz : QuadTie z₀ z₁ z₂ z₃)
    (h1 : ¬ (max z₁ z₃ < min z₀ z₂)) (h2 : ¬ (max z₀ z₂ < min z₁ z₃)) :
    IsRobustUnimodal (quad (σ * z₀) (σ * z₁) (σ * z₂) (σ * z₃)) := by
  rcases hσ with rfl | rfl
  · simpa only [one_mul] using isRobustUnimodal_quad hz h1 h2
  · have := isRobustUnimodal_quad (hz.mul (Or.inr rfl)) (z₀ := -1 * z₀) (z₁ := -1 * z₁)
      (z₂ := -1 * z₂) (z₃ := -1 * z₃) (by
        simp only [neg_one_mul, max_neg_neg, min_neg_neg, neg_lt_neg_iff]; exact h2) (by
        simp only [neg_one_mul, max_neg_neg, min_neg_neg, neg_lt_neg_iff]; exact h1)
    exact this

/-- **The vertex crossing at `a'`, certified, with ties** (Proposition 8.8 with Theorem 18.3).  The
screen data at the view `u` (orientation `σ = ±1`): the corner `a'` between the sides towards
`b` and `b'` (`σ T > 0`, `T = det(b − a', b' − a', u)`), `a` inside that corner (`σ Γ > 0`,
`σ B > 0`); every point of `V` is `a, a', b, b'` or an admissible extra point (hidden, or a
middle at the apex, such as the middles `c`, `c'`).  Then:
* if `a` is on the inner side of `b b'` (`σ det(b' − b, a − b, u) > 0`), the rim is the
  triangle `a' b b'`, robustly unimodal since its three depths are not all equal
  (`QuadTie`), and `V` is Rupert;
* if `a` is beyond `b b'` (`< 0`), the rim is the quadrilateral `a' b a b'`; with the ties of
  `QuadTie` it is robustly unimodal unless its diagonals `[a', a]`, `[b, b']` are
  depth-separated, and then `V` is Rupert.
No horizontal double normal at `u` (`NoHDNAt`) is assumed. -/
theorem isRupert_axisTest_core_robust {a a' b b' u : ℝ³} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hT : 0 < σ * det3 (b - a') (b' - a') u) (hΓ : 0 < σ * det3 (b - a') (a - a') u)
    (hB : 0 < σ * det3 (a - a') (b' - a') u)
    (hz : QuadTie ⟪a', u⟫ ⟪b, u⟫ ⟪a, u⟫ ⟪b', u⟫)
    (V : Finset ℝ³) (ha : a ∈ V) (ha' : a' ∈ V) (hb : b ∈ V) (hb' : b' ∈ V)
    (hV : ∀ v ∈ V, v = a ∨ v = a' ∨ v = b ∨ v = b' ∨ AxisExtra a a' b b' u v)
    (hnd : NoHDNAt V u) :
    (0 < σ * det3 (b' - b) (a - b) u → IsRupert V) ∧
    (σ * det3 (b' - b) (a - b) u < 0 → ¬ DepthSep a' a b b' u → IsRupert V) := by
  classical
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσ0 : σ ≠ 0 := by rintro rfl; norm_num at hσσ
  have hu0 : u ≠ 0 := by rintro rfl; simp [det3] at hT
  have hw0 : σ • u ≠ 0 := smul_ne_zero hσ0 hu0
  have hdw : ∀ x y, det3 x y (σ • u) = σ * det3 x y u := fun x y => by
    simp only [det3, real_inner_smul_right]
  have hiw : ∀ x, ⟪x, σ • u⟫ = σ * ⟪x, u⟫ := fun x => real_inner_smul_right _ _ _
  have hndw : NoHDNAt V (σ • u) := by
    rcases hσ with rfl | rfl
    · rwa [one_smul]
    · rw [neg_one_smul]; exact hnd.neg
  have i1 : det3 (b' - b) (a' - b) u = det3 (b - a') (b' - a') u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i2 : det3 (a' - b') (b - b') u = det3 (b - a') (b' - a') u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i3 : det3 (a' - b') (a - b') u = det3 (a - a') (b' - a') u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i4 : det3 (a - b) (a' - b) u = det3 (b - a') (a - a') u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i5 : det3 (a - b) (b' - b) u = -det3 (b' - b) (a - b) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i6 : det3 (b' - a) (a' - a) u = det3 (a - a') (b' - a') u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i7 : det3 (b' - a) (b - a) u = -det3 (b' - b) (a - b) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  -- the corners are not middles
  have nmid : ∀ y, ApexMid a' b b' u y → y ≠ a ∧ y ≠ a' ∧ y ≠ b ∧ y ≠ b' := by
    intro y hy
    have hsT : ∀ s : ℝ, 0 < s → s < 1 → 0 < s * (σ * det3 (b - a') (b' - a') u) ∧
        0 < (1 - s) * (σ * det3 (b - a') (b' - a') u) :=
      fun s h0 h1 => ⟨mul_pos h0 hT, mul_pos (by linarith) hT⟩
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩ <;> rw [e] at hy <;>
      rcases apexMid_sides hy with ⟨h1, s, hs0, hs1, h2⟩ | ⟨h1, s, hs0, hs1, h2⟩ <;>
      (try simp only [sub_self, det3_zero_mid, det3_zero_left', det3_self_left] at h1 h2) <;>
      obtain ⟨t1, t2⟩ := hsT s hs0 hs1 <;>
      first
        | nlinarith [congrArg (σ * ·) h1, congrArg (σ * ·) h2]
        | nlinarith [congrArg (σ * ·) h2]
  set M := V.filter (ApexMid a' b b' u) with hM
  refine ⟨fun hα => ?_, fun hα hsep => ?_⟩
  · -- the rim is the triangle `a' b b'`
    obtain ⟨b0, b1, b2⟩ := zmod3_add_one
    refine isRupert_of_vertexView_robust V M (σ • u) hw0 (k := 3) le_rfl (tri a' b b') ?_ ?_ ?_ ?_
      ?_ hndw ?_
    · intro i; rcases zmod3_cases i with rfl | rfl | rfl
      exacts [ha', hb, hb']
    · intro i hi
      obtain ⟨-, hmid⟩ := mem_filter.mp hi
      rcases zmod3_cases i with rfl | rfl | rfl
      exacts [(nmid _ hmid).2.1 rfl, (nmid _ hmid).2.2.1 rfl, (nmid _ hmid).2.2.2 rfl]
    · intro i j hi hj
      rcases zmod3_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp only [b0, b1, b2, tri_0, tri_1, tri_2, hdw, i1, i2]
      exacts [hT, hT, hT]
    · intro y hy hyM hyx i
      have h0 := hyx 0; have h1 := hyx 1; have h2 := hyx 2
      simp only [tri_0, tri_1, tri_2] at h0 h1 h2
      rcases hV y hy with e | e | e | e | hext
      · rw [e]
        rcases zmod3_cases i with rfl | rfl | rfl <;>
          simp only [b0, b1, b2, tri_0, tri_1, tri_2, hdw, i3]
        exacts [hΓ, hα, hB]
      · exact absurd e h0
      · exact absurd e h1
      · exact absurd e h2
      · rcases hext with ⟨w₁, w₂, w₃, w₄, μ, p1, p2, p3, p4, hsum, rfl⟩ | hmid
        · rcases zmod3_cases i with rfl | rfl | rfl <;>
            simp only [b0, b1, b2, tri_0, tri_1, tri_2, hdw] <;>
            rw [det3_hidden _ _ _ _ _ _ _ hsum] <;>
            simp only [sub_self, det3_zero_mid, det3_self_left, i1, i2, i3]
          · nlinarith [mul_pos p1 hΓ, mul_pos p4 hT]
          · nlinarith [mul_pos p1 hα, mul_pos p2 hT]
          · nlinarith [mul_pos p1 hB, mul_pos p3 hT]
        · exact absurd (mem_filter.mpr ⟨hy, hmid⟩) hyM
    · rw [tri_inner]
      simp only [hiw]
      exact tri_robust_smul hσ0 hz.2.1
    · intro m hm
      obtain ⟨-, hmid⟩ := mem_filter.mp hm
      rcases hmid with ⟨s, δ, hs0, hs1, hδ, rfl⟩ | ⟨s, δ, hs0, hs1, hδ, rfl⟩
      · exact ⟨0, s, σ * δ, hs0, hs1, mul_ne_zero hσ0 hδ, by
          simp only [b0, tri_0, tri_1]; exact mid_view hσσ⟩
      · exact ⟨2, 1 - s, σ * δ, by linarith, by linarith, mul_ne_zero hσ0 hδ, by
          simp only [b2, tri_0, tri_2]; exact mid_view' hσσ⟩
  · -- the rim is the quadrilateral `a' b a b'`
    obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
    have hα' : 0 < σ * -det3 (b' - b) (a - b) u := by linarith
    refine isRupert_of_vertexView_robust V M (σ • u) hw0 (k := 4) (by norm_num) (quad a' b a b')
      ?_ ?_ ?_ ?_ ?_ hndw ?_
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
      exacts [ha', hb, ha, hb']
    · intro i hi
      obtain ⟨-, hmid⟩ := mem_filter.mp hi
      rcases zmod4_cases i with rfl | rfl | rfl | rfl
      exacts [(nmid _ hmid).2.1 rfl, (nmid _ hmid).2.2.1 rfl, (nmid _ hmid).1 rfl,
        (nmid _ hmid).2.2.2 rfl]
    · intro i j hi hj
      rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3, hdw, i2, i3, i4, i5, i6, i7]
      exacts [hΓ, hT, hα', hΓ, hB, hα', hT, hB]
    · intro y hy hyM hyx i
      have h0 := hyx 0; have h1 := hyx 1; have h2 := hyx 2; have h3 := hyx 3
      simp only [quad_0, quad_1, quad_2, quad_3] at h0 h1 h2 h3
      rcases hV y hy with e | e | e | e | hext
      · exact absurd e h2
      · exact absurd e h0
      · exact absurd e h1
      · exact absurd e h3
      · rcases hext with ⟨w₁, w₂, w₃, w₄, μ, p1, p2, p3, p4, hsum, rfl⟩ | hmid
        · rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
            simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3, hdw] <;>
            rw [det3_hidden _ _ _ _ _ _ _ hsum] <;>
            simp only [sub_self, det3_zero_mid, det3_self_left, i2, i3, i4, i5, i6, i7]
          · nlinarith [mul_pos p1 hΓ, mul_pos p4 hT]
          · nlinarith [mul_pos p2 hΓ, mul_pos p4 hα']
          · nlinarith [mul_pos p2 hB, mul_pos p3 hα']
          · nlinarith [mul_pos p1 hB, mul_pos p3 hT]
        · exact absurd (mem_filter.mpr ⟨hy, hmid⟩) hyM
    · rw [quad_inner]
      simp only [hiw]
      exact quad_robust_smul hσ hz (fun h => hsep (Or.inr h)) (fun h => hsep (Or.inl h))
    · intro m hm
      obtain ⟨-, hmid⟩ := mem_filter.mp hm
      rcases hmid with ⟨s, δ, hs0, hs1, hδ, rfl⟩ | ⟨s, δ, hs0, hs1, hδ, rfl⟩
      · exact ⟨0, s, σ * δ, hs0, hs1, mul_ne_zero hσ0 hδ, by
          simp only [a0, quad_0, quad_1]; exact mid_view hσσ⟩
      · exact ⟨3, 1 - s, σ * δ, by linarith, by linarith, mul_ne_zero hσ0 hδ, by
          simp only [a3, quad_0, quad_3]; exact mid_view' hσσ⟩

/-- **One test of Theorem 13.7, with ties**: the vertex crossing at `a'` of the faces `a'bc`,
`a'b'c'` of an octahedron, at the view `u₁ = axisView` (Lemma 13.5), under the far-end
inequalities `|[a b]| < |[a c]|`, `|[a b']| < |[a c']|` (the far ends are `b`, `b'`; `c`, `c'`
are middles).  Outside the special positions (`P(a)` on the line `P(b) P(b')`; ties among the
depths of `a', b, a, b'` other than those of `QuadTie`) and without a horizontal double normal,
either `V` is Rupert, or the rim is the quadrilateral `a' b a b'` with depth-separated
diagonals, and then the projections of `[a', a]` and `[b, b']`, and those of `[a', a]` and
`[c, c']`, meet along `u₁`.  The points of `V` other than the vertices are hidden or middles at
the apex (`AxisExtra`, Lemma 13.8). -/
theorem isRupert_axisTest_robust {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c')
    (hfar₁ : |galeD G.l G.m a b| < |galeD G.l G.m a c|)
    (hfar₂ : |galeD G.l G.m a b'| < |galeD G.l G.m a c'|)
    (hP : det3 (b' - b) (a - b) (axisView G.l G.m a a' b c) ≠ 0)
    (hz : QuadTie ⟪a', axisView G.l G.m a a' b c⟫ ⟪b, axisView G.l G.m a a' b c⟫
      ⟪a, axisView G.l G.m a a' b c⟫ ⟪b', axisView G.l G.m a a' b c⟫)
    (V : Finset ℝ³) (hO : ({a, a', b, b', c, c'} : Finset ℝ³) ⊆ V)
    (hV : ∀ v ∈ V, v ∈ ({a, a', b, b', c, c'} : Finset ℝ³) ∨
      AxisExtra a a' b b' (axisView G.l G.m a a' b c) v)
    (hnd : NoHDNAt V (axisView G.l G.m a a' b c)) :
    IsRupert V ∨ (SegMeet a' a b b' (axisView G.l G.m a a' b c) ∧
      SegMeet a' a c c' (axisView G.l G.m a a' b c) ∧
      DepthSep a' a b b' (axisView G.l G.m a a' b c)) := by
  obtain ⟨σ, s, δ, s', δ', hσ, hs0, hs1, hδ, hc, hs0', hs1', hδ', hc', hT, hΓ, hB⟩ :=
    axis_test_facts F G hfar₁ hfar₂
  set u := axisView G.l G.m a a' b c
  have hV' : ∀ v ∈ V, v = a ∨ v = a' ∨ v = b ∨ v = b' ∨ AxisExtra a a' b b' u v := by
    intro v hv
    rcases hV v hv with h | h
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, δ, hs0, hs1, hδ, h.trans hc⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨s', δ', hs0', hs1', hδ', h.trans hc'⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  have mem : ∀ x ∈ ({a, a', b, b', c, c'} : Finset ℝ³), x ∈ V := fun x hx => hO hx
  obtain ⟨K1, K2⟩ := isRupert_axisTest_core_robust hσ hT hΓ hB hz V (mem a (by simp))
    (mem a' (by simp)) (mem b (by simp)) (mem b' (by simp)) hV' hnd
  have hσα : σ * det3 (b' - b) (a - b) u ≠ 0 :=
    mul_ne_zero (by rcases hσ with rfl | rfl <;> norm_num) hP
  rcases lt_or_gt_of_ne hσα with hα | hα
  · by_cases hsep : DepthSep a' a b b' u
    · obtain ⟨m1, m2⟩ := axisTest_meets hσ hs0 hs1 hc hs0' hs1' hc' hT hΓ hB hα
      exact Or.inr ⟨m1, m2, hsep⟩
    · exact Or.inl (K2 hα hsep)
  · exact Or.inl (K1 hα)

end Minimality

end
