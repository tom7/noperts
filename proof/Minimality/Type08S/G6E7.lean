module

public import Minimality.Type08S.G6E6

@[expose] public section

set_option autoImplicit true

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- **A class-(d) HDN of `R1` is a horizontal double normal of the polygon `{b, c', b', c}`** at
the view `b - d` (item (3)): `¬ NoHDNAt {b, c', b', c} (b - d)`. -/
theorem classD1_hdn {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (hT : IsT a' b c d) (hD : ClassD1 b b' c c' d) :
    ¬ NoHDNAt ({b, c', b', c} : Finset ℝ³) (b - d) := by
  intro hno
  obtain ⟨e1, e2, e3, o, ν, v1, C0, w1, ha, w3, α, β1, γ4, β6, hF, hν, hv1, hha, hα, hβ1, hγ,
    hβ6, hu, hd, hb, hc, haa, ha', hb', hc', hv, hdep⟩ := h1_setup N hT hD.1
  obtain ⟨s, t, hs0, hs1, ht0, ht1, hf1, hf2⟩ := hD.2
  have i1 := fun X Y z => inner_pt_1 hF o X Y z
  have i2 := fun X Y z => inner_pt_2 hF o X Y z
  rw [hu, real_inner_smul_right] at hf1
  have hfe3 : ⟪(c' + s • (b' - c')) - (c + t • (b - c)), e3⟫ = 0 :=
    (mul_eq_zero.mp hf1).resolve_left hν.ne'
  rw [hv, inner_add_right, real_inner_smul_right, real_inner_smul_right, hfe3] at hf2
  have hfe1 : ⟪(c' + s • (b' - c')) - (c + t • (b - c)), e1⟫ = 0 := by
    have : v1 * ⟪(c' + s • (b' - c')) - (c + t • (b - c)), e1⟫ = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hv1
  rw [inner_sub_left] at hfe1 hfe3
  have hQ2 : ⟪c + t • (b - c), e2⟫ = ⟪o, e2⟫ + 0 := by
    rw [inner_add_left, real_inner_smul_left, inner_sub_left, hc, hb, i2, i2]; ring
  have hP2 : ⟪c' + s • (b' - c'), e2⟫ = ⟪o, e2⟫ + α * ha := by
    rw [inner_add_left, real_inner_smul_left, inner_sub_left, hc', hb', i2, i2]; ring
  have hlt : ⟪c + t • (b - c), e2⟫ < ⟪c' + s • (b' - c'), e2⟫ := by
    rw [hQ2, hP2]; nlinarith [mul_pos (sub_pos.mpr hα) hha]
  have hS : ∀ p ∈ ({b, c', b', c} : Finset ℝ³), ⟪o, e2⟫ + 0 ≤ ⟪p, e2⟫ ∧
      ⟪p, e2⟫ ≤ ⟪o, e2⟫ + α * ha := by
    intro p hp
    simp only [mem_insert, mem_singleton] at hp
    have : 0 < α * ha := mul_pos (by linarith) hha
    rcases hp with rfl | rfl | rfl | rfl
    · rw [hb, i2]; constructor <;> linarith
    · rw [hc', i2]; constructor <;> linarith
    · rw [hb', i2]; constructor <;> linarith
    · rw [hc, i2]; constructor <;> linarith
  have hseg : ∀ (p q : ℝ³) (r : ℝ), 0 ≤ r → r ≤ 1 → p + r • (q - p) ∈ segment ℝ p q := by
    intro p q r h0 h1
    exact ⟨1 - r, r, by linarith, h0, by ring, by module⟩
  have hseg' : ∀ (p q : ℝ³) (r : ℝ), 0 ≤ r → r ≤ 1 → p + r • (q - p) ∈ segment ℝ q p := by
    intro p q r h0 h1
    exact ⟨r, 1 - r, h0, by linarith, by ring, by module⟩
  have hno' := hno
  rw [hu] at hno'
  have hzz : ∀ i, i = (0 : ZMod 4) ∨ i = 1 ∨ i = 2 ∨ i = 3 := zmod4_cases
  have e01 : (1 : ZMod 4) + 1 = 2 := by decide
  have e31 : (3 : ZMod 4) + 1 = 0 := by decide
  rcases lt_or_gt_of_ne hv1 with hneg | hpos
  · have hq : ∀ i, (!₂[⟪(quad b c' b' c) i, e1⟫, ⟪(quad b c' b' c) i, e2⟫] : ℝ²) =
        quad (!₂[⟪o, e1⟫ + (-v1), ⟪o, e2⟫ + 0] : ℝ²) !₂[⟪o, e1⟫ + (-v1 + α * w1), ⟪o, e2⟫ + α * ha]
          !₂[⟪o, e1⟫ + (-v1 * (1 - γ4) + α * w1), ⟪o, e2⟫ + α * ha] !₂[⟪o, e1⟫ + 0, ⟪o, e2⟫ + 0] i := by
      intro i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, hb, hc', hb', hc, i1, i2]
    refine hdn_contra hF hν _ hno' (quad b c' b' c) ?_ ?_ (P := c' + s • (b' - c'))
      (Q := c + t • (b - c)) (i := 1) (j := 3) ?_ ?_ ?_ ?_ hlt ?_
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
      · show b ∈ ({b, c', b', c} : Finset ℝ³); simp
      · show c' ∈ ({b, c', b', c} : Finset ℝ³); simp
      · show b' ∈ ({b, c', b', c} : Finset ℝ³); simp
      · show c ∈ ({b, c', b', c} : Finset ℝ³); simp
    · rw [show (fun i => (!₂[⟪(quad b c' b' c) i, e1⟫, ⟪(quad b c' b' c) i, e2⟫] : ℝ²)) = _ from
        funext hq]
      refine ccw4 ?_ ?_ ?_
      · nlinarith [mul_pos (show 0 < α by linarith) hha]
      · linarith
      · nlinarith [mul_pos (neg_pos.mpr hneg) (show 0 < γ4 by linarith)]
    · simpa only [quad_1, quad_2, e01] using hseg c' b' s hs0.le hs1.le
    · simpa only [quad_3, quad_0, e31] using hseg c b t ht0.le ht1.le
    · linarith
    · linarith
    · intro i; rw [hQ2, hP2]; rcases zmod4_cases i with rfl | rfl | rfl | rfl
      · exact hS b (by simp)
      · exact hS c' (by simp)
      · exact hS b' (by simp)
      · exact hS c (by simp)
  · have hq : ∀ i, (!₂[⟪(quad c b' c' b) i, e1⟫, ⟪(quad c b' c' b) i, e2⟫] : ℝ²) =
        quad (!₂[⟪o, e1⟫ + 0, ⟪o, e2⟫ + 0] : ℝ²)
          !₂[⟪o, e1⟫ + (-v1 * (1 - γ4) + α * w1), ⟪o, e2⟫ + α * ha]
          !₂[⟪o, e1⟫ + (-v1 + α * w1), ⟪o, e2⟫ + α * ha] !₂[⟪o, e1⟫ + (-v1), ⟪o, e2⟫ + 0] i := by
      intro i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, hb, hc', hb', hc, i1, i2]
    refine hdn_contra hF hν _ hno' (quad c b' c' b) ?_ ?_ (P := c' + s • (b' - c'))
      (Q := c + t • (b - c)) (i := 1) (j := 3) ?_ ?_ ?_ ?_ hlt ?_
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
      · show c ∈ ({b, c', b', c} : Finset ℝ³); simp
      · show b' ∈ ({b, c', b', c} : Finset ℝ³); simp
      · show c' ∈ ({b, c', b', c} : Finset ℝ³); simp
      · show b ∈ ({b, c', b', c} : Finset ℝ³); simp
    · rw [show (fun i => (!₂[⟪(quad c b' c' b) i, e1⟫, ⟪(quad c b' c' b) i, e2⟫] : ℝ²)) = _ from
        funext hq]
      refine ccw4 ?_ ?_ ?_
      · nlinarith [mul_pos (show 0 < α by linarith) hha]
      · linarith
      · nlinarith [mul_pos hpos (show 0 < γ4 by linarith)]
    · simpa only [quad_1, quad_2, e01] using hseg' c' b' s hs0.le hs1.le
    · simpa only [quad_3, quad_0, e31] using hseg' c b t ht0.le ht1.le
    · linarith
    · linarith
    · intro i; rw [hQ2, hP2]; rcases zmod4_cases i with rfl | rfl | rfl | rfl
      · exact hS c (by simp)
      · exact hS b' (by simp)
      · exact hS c' (by simp)
      · exact hS b (by simp)

end Type08Sp
end Minimality
