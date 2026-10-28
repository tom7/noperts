module

public import Minimality.Type08S.Defs08
public import Minimality.Type08S.G6S

@[expose] public section

set_option autoImplicit true

/-!
# G6' bridge, part 3: the orthonormal frame at `ℓ` from `(a - d, b - d, c - d)`
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

theorem inner_cross_cross' (a b : ℝ³) :
    ⟪cross a b, cross a b⟫ = ⟪a, a⟫ * ⟪b, b⟫ - ⟪a, b⟫ ^ 2 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial, cross]
  simp; ring

theorem inner_cross_left (a b : ℝ³) : ⟪cross a b, a⟫ = 0 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial, cross]
  simp; ring

theorem inner_cross_right (a b : ℝ³) : ⟪cross a b, b⟫ = 0 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial, cross]
  simp; ring

theorem det3_eq_inner (a b c : ℝ³) : det3 a b c = ⟪a, cross b c⟫ := by
  simp only [det3, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial, cross]
  simp; ring

theorem fr_of_orth {a b : ℝ³} (ha : ⟪a, a⟫ = 1) (hb : ⟪b, b⟫ = 1) (hab : ⟪a, b⟫ = 0) :
    Fr (cross a b) a b := by
  have hba : ⟪b, a⟫ = 0 := by rw [real_inner_comm]; exact hab
  have h1 : cross (cross a b) a = b := by
    rw [cross_cross_eq, ha, hba, one_smul, zero_smul, sub_zero]
  have h3 : cross b (cross a b) = a := by
    rw [cross_anti', cross_cross_eq, hab, hb, zero_smul, one_smul, zero_sub, neg_neg]
  refine ⟨?_, ha, hb, ?_, ?_, hab, h1, rfl, h3⟩
  · rw [inner_cross_cross', ha, hb, hab]; norm_num
  · exact inner_cross_left a b
  · exact inner_cross_right a b

theorem Fr.expand {e1 e2 e3 : ℝ³} (hF : Fr e1 e2 e3) (x : ℝ³) :
    x = ⟪x, e1⟫ • e1 + ⟪x, e2⟫ • e2 + ⟪x, e3⟫ • e3 := by
  have h := cramer e1 e2 e3 x
  have d123 : det3 e1 e2 e3 = 1 := by rw [det3, hF.c12, hF.n33]
  have d1 : det3 x e2 e3 = ⟪x, e1⟫ := by rw [det3_eq_inner, hF.c23]
  have d2 : det3 e1 x e3 = ⟪x, e2⟫ := by
    have : det3 e1 x e3 = det3 x e3 e1 := by simp only [det3_expand]; ring
    rw [this, det3_eq_inner, hF.c31]
  have d3 : det3 e1 e2 x = ⟪x, e3⟫ := by
    have : det3 e1 e2 x = det3 x e1 e2 := by simp only [det3_expand]; ring
    rw [this, det3_eq_inner, hF.c12]
  rw [d123, d1, d2, d3, one_smul] at h
  exact h

/-- The frame at `ℓ`: `e3 ∥ u = b - d`, `e2` the normal of the plane of `Q_bc`, `⟪w, e2⟫ > 0`. -/
theorem frame_exists {w u v : ℝ³} (hdet : det3 w u v ≠ 0) :
    ∃ e1 e2 e3 : ℝ³, Fr e1 e2 e3 ∧ ⟪u, e1⟫ = 0 ∧ ⟪u, e2⟫ = 0 ∧ 0 < ⟪u, e3⟫ ∧ ⟪v, e2⟫ = 0 ∧
      ⟪v, e1⟫ ≠ 0 ∧ 0 < ⟪w, e2⟫ := by
  have hn0 : cross u v ≠ 0 := by
    intro h; apply hdet
    have : det3 w u v = ⟪w, cross u v⟫ := det3_eq_inner w u v
    rw [this, h, inner_zero_right]
  have hu0 : u ≠ 0 := by
    intro h; apply hdet; rw [h]; simp [det3_expand]
  have hnn : 0 < ‖cross u v‖ := norm_pos_iff.mpr hn0
  have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  have hwn : ⟪w, cross u v⟫ ≠ 0 := by rw [← det3_eq_inner]; exact hdet
  -- sign
  obtain ⟨s, hs, hsw⟩ : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ 0 < s * ⟪w, cross u v⟫ := by
    rcases lt_or_gt_of_ne hwn with h | h
    · exact ⟨-1, Or.inr rfl, by linarith⟩
    · exact ⟨1, Or.inl rfl, by linarith⟩
  set e2 : ℝ³ := (s / ‖cross u v‖) • cross u v with he2
  set e3 : ℝ³ := (1 / ‖u‖) • u with he3
  have hs2 : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hn2 : ⟪cross u v, cross u v⟫ = ‖cross u v‖ ^ 2 := real_inner_self_eq_norm_sq _
  have hu2 : ⟪u, u⟫ = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq _
  have ha : ⟪e2, e2⟫ = 1 := by
    rw [he2, real_inner_smul_left, real_inner_smul_right, hn2]
    field_simp; nlinarith [hs2]
  have hb : ⟪e3, e3⟫ = 1 := by
    rw [he3, real_inner_smul_left, real_inner_smul_right, hu2]
    field_simp
  have hab : ⟪e2, e3⟫ = 0 := by
    rw [he2, he3, real_inner_smul_left, real_inner_smul_right, inner_cross_left u v]
    simp
  have hF := fr_of_orth ha hb hab
  have hue : u = ‖u‖ • e3 := by rw [he3, smul_smul]; field_simp; simp
  have hnu : ⟪u, cross u v⟫ = 0 := by rw [real_inner_comm]; exact inner_cross_left u v
  have hnv : ⟪v, cross u v⟫ = 0 := by rw [real_inner_comm]; exact inner_cross_right u v
  refine ⟨cross e2 e3, e2, e3, hF, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hue, real_inner_smul_left, real_inner_comm, hF.n13, mul_zero]
  · rw [he2, real_inner_smul_right, hnu, mul_zero]
  · rw [hue, real_inner_smul_left, hF.n33, mul_one]; exact hun
  · rw [he2, real_inner_smul_right, hnv, mul_zero]
  · have hvc : cross e2 e3 = ((s / ‖cross u v‖) * (1 / ‖u‖)) • cross (cross u v) u := by
      rw [he2, he3, cross_smul_l, cross_smul_r, smul_smul]
    rw [hvc, real_inner_smul_right, cross_cross_eq, inner_sub_right, real_inner_smul_right,
      real_inner_smul_right, real_inner_comm u v]
    have := inner_cross_cross' u v
    rw [hn2] at this
    have e : ⟪u, u⟫ * ⟪v, v⟫ - ⟪v, u⟫ ^ 2 = ‖cross u v‖ ^ 2 := by rw [real_inner_comm u v]; exact this.symm
    have hc : (s / ‖cross u v‖) * (1 / ‖u‖) ≠ 0 := by
      have : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
      positivity
    have h2 : ⟪u, u⟫ * ⟪v, v⟫ - ⟪v, u⟫ ^ 2 ≠ 0 := by rw [e]; positivity
    rw [real_inner_comm u v] at h2
    exact mul_ne_zero hc (by rwa [← sq])
  · rw [he2, real_inner_smul_right]
    have : s / ‖cross u v‖ * ⟪w, cross u v⟫ = (s * ⟪w, cross u v⟫) / ‖cross u v‖ := by ring
    rw [this]; positivity

end Type08Sp
end Minimality
