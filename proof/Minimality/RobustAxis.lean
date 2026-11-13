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

end Minimality

end
