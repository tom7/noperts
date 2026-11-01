module

public import Minimality.Type16UF

@[expose] public section


/-!
# U1: the EV1 leaf `LDE (6,3,5,4)`  (`ζ < 0`, `φF(0,6) > 0`, `φH(0,6) < 0`)
-/

set_option autoImplicit true
set_option linter.unusedVariables false
open scoped RealInnerProductSpace
open Finset Filter

namespace Minimality
namespace H16U
open TwoRay Type08Sp Type08Sp.C2 V2

variable {x : Fin 7 → ℝ³}

/-- Normal-form point as a frame point (the `a, b, z` given by equalities). -/
theorem nfP_key (N : NF16 x) (α β γ a b z : ℝ) (ha : a = 1 - α - γ + (N.p + N.r - 1) / N.q * β)
    (hb : b = β / N.q) (hz : z = N.p * β / N.q - α) :
    nfP N.o N.E₁ N.E₂ N.E₃ α β γ = fpoint (x 3 - x 6) (x 4 - x 6) (x 6 - x 0) (x 6) (a, b, z) := by
  rw [nfP_eq_fpoint, ha, hb, hz]

set_option maxHeartbeats 1600000 in
theorem h16u_ev1_L2_cell (T : Type16 x) (hζ : ⟪x 5 - x 3, x 6 - x 0⟫ < 0)
    (hF : 0 < T.ff 5 (x 6) - T.ff 5 (x 0)) (hH : T.ff 7 (x 6) - T.ff 7 (x 0) < 0)
    (d1 : ⟪x 6, x 6 - x 0⟫ ≠ ⟪x 3, x 6 - x 0⟫) (d2 : ⟪x 6, x 6 - x 0⟫ ≠ ⟪x 5, x 6 - x 0⟫)
    (d3 : ⟪x 6, x 6 - x 0⟫ ≠ ⟪x 4, x 6 - x 0⟫) (d4 : ⟪x 3, x 6 - x 0⟫ ≠ ⟪x 4, x 6 - x 0⟫)
    (d5 : ⟪x 5, x 6 - x 0⟫ ≠ ⟪x 4, x 6 - x 0⟫) :
    HasLexCellAt (univ.image x) (x 6 - x 0) := by
  obtain ⟨P⟩ := exists_par T
  have hR1 := R1_neg T P hF
  have hR2 := R2_neg T P hH
  set N := P.N with hN
  have hq := N.hq
  set s : ℝ := (N.p + N.r - 1) / N.q with hs
  have hsq : s * N.q = N.p + N.r - 1 := by rw [hs]; field_simp
  have mem : ∀ i, x i ∈ univ.image x := fun i => mem_image_of_mem x (mem_univ i)
  have hq' : N.q ≠ 0 := hq.ne'
  -- corner points
  have c3 : x 6 + (x 3 - x 6) = x 3 := by abel
  have c4 : x 6 + (x 4 - x 6) = x 4 := by abel
  have c5 : fpoint (x 3 - x 6) (x 4 - x 6) (x 6 - x 0) (x 6) (1 + s, 1 / N.q, N.p / N.q) = x 5 := by
    rw [N.x5, nfP_key N 0 1 0 (1 + s) (1 / N.q) (N.p / N.q) (by rw [hs]; ring) (by ring) (by ring)]
  -- depths
  have dep : ∀ α β γ, ⟪nfP N.o N.E₁ N.E₂ N.E₃ α β γ, x 6 - x 0⟫ =
      ⟪x 3, x 6 - x 0⟫ + α * ⟪N.E₁, x 6 - x 0⟫ + β * ⟪N.E₂, x 6 - x 0⟫ + γ * ⟪N.E₃, x 6 - x 0⟫ := by
    intro α β γ
    rw [depth_nf, show N.o = x 3 from by
      have := N.x3; simp only [nfP] at this; simpa using this.symm]
  have z6 : ⟪x 6, x 6 - x 0⟫ = ⟪x 3, x 6 - x 0⟫ + ⟪N.E₃, x 6 - x 0⟫ := by
    have := dep 0 0 1; rw [← N.x6] at this; linarith
  have z5 : ⟪x 5, x 6 - x 0⟫ = ⟪x 3, x 6 - x 0⟫ + ⟪x 5 - x 3, x 6 - x 0⟫ := by
    have := dep 0 1 0; rw [← N.x5, m2_eq N] at this; linarith
  have z4 : ⟪x 4, x 6 - x 0⟫ = ⟪x 3, x 6 - x 0⟫ + N.p * ⟪N.E₁, x 6 - x 0⟫ + N.q * ⟪x 5 - x 3, x 6 - x 0⟫ +
      N.r * ⟪N.E₃, x 6 - x 0⟫ := by
    have := dep N.p N.q N.r; rw [← N.x4, m2_eq N] at this; linarith
  have m13 := m13_pos N
  have hspq : 0 < N.p + N.q + N.r - 1 := N.t046_5
  have hp := N.hp; have hr := N.hr
  set m1 := ⟪N.E₁, x 6 - x 0⟫ with hm1
  set m3 := ⟪N.E₃, x 6 - x 0⟫ with hm3
  set m2 := ⟪x 5 - x 3, x 6 - x 0⟫ with hm2
  refine h16u_ev1_cyc4 (univ.image x) (x 3 - x 6) (x 4 - x 6) (x 6 - x 0) (x 6) (frame6_det N) (1 + s) (1 / N.q)
    (N.p / N.q) (by rw [hs]; have := N.t046_5; have : 0 < N.p + N.q + N.r - 1 := this
                    have : (N.p + N.r - 1) / N.q + 1 = (N.p + N.q + N.r - 1) / N.q := by field_simp; ring
                    linarith [div_pos ‹0 < N.p + N.q + N.r - 1› hq])
    (by positivity) (by rw [hs]; have : 0 < (N.p + N.r) / N.q := by positivity
                        have e : 1 + (N.p + N.r - 1) / N.q + 1 / N.q = 1 + (N.p + N.r) / N.q := by field_simp; ring
                        linarith)
    (by rw [c3]; exact mem 3) (mem 6) (by rw [c5]; exact mem 5) (by rw [c4]; exact mem 4) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals try simp only [c3, c4, c5]
  · exact d1
  · exact d2
  · exact d3
  · intro h; linarith
  · exact d4
  · exact d5
  · -- hn1
    rintro ⟨-, -, h3, -⟩
    linarith
  · -- hn2
    rintro ⟨h1, h2, h3, h4⟩
    set u4 := N.p * m1 + N.q * m2 + N.r * m3 with hu4
    have hm3n : m3 < 0 := by linarith
    have hm2n : m2 < 0 := by linarith
    have hu4m3 : m3 < u4 := by linarith
    have hu4m2 : m2 < u4 := by linarith
    have e1 := mul_pos (add_pos hp hr) (sub_pos.2 hu4m3)
    have e2 := mul_pos hq (sub_pos.2 hu4m2)
    have e3 := mul_pos hp (sub_pos.2 m13)
    have hu4lt : u4 < (N.p + N.r) * m3 + N.q * m2 := by rw [hu4]; nlinarith
    have hneg : (N.p + N.r) * m3 + N.q * m2 < 0 := by
      nlinarith [mul_neg_of_pos_of_neg (add_pos hp hr) hm3n, mul_neg_of_pos_of_neg hq hm2n]
    have hu4pos : 0 < u4 := by
      by_contra hc; push Not at hc
      nlinarith [mul_nonneg hspq.le (neg_nonneg.2 hc)]
    linarith
  · intro y hy hy6 hy3 hy5 hy4
    obtain ⟨j, -, rfl⟩ := mem_image.1 hy
    fin_cases j
    · exact ⟨0, 0, -1, (N.x0).trans (nfP_key N 1 0 0 0 0 (-1) (by ring) (by simp) (by ring)),
        Or.inr ⟨rfl, rfl, by norm_num⟩⟩
    · refine ⟨1 - 0 - N.d + s * N.g, N.g / N.q, N.p * N.g / N.q - 0,
        (N.x1).trans (nfP_key N 0 N.g N.d _ _ _ rfl rfl rfl), Or.inl ⟨?_, ?_, ?_, ?_⟩⟩
      · have e : 1 - 0 - N.d + s * N.g = (N.g * (N.p + N.r - 1) - N.q * (N.d - 1)) / N.q := by
          rw [hs]; field_simp; ring
        rw [e]; exact div_pos N.t0146 hq
      · exact div_pos N.hg hq
      · have e : (1 + s - 1) * (N.g / N.q) - 1 / N.q * (1 - 0 - N.d + s * N.g - 1) = N.d / N.q := by
          rw [hs]; field_simp; ring
        rw [e]; exact div_pos N.hd hq
      · have e : -(1 + s) * (N.g / N.q - 1 / N.q) - (1 - 1 / N.q) * (1 - 0 - N.d + s * N.g - (1 + s)) =
            -((N.g - 1) * (N.p + N.r) - N.d * (N.q - 1)) / N.q := by
          rw [hs]; field_simp; ring
        rw [e]; exact div_pos (by linarith) hq
    · refine ⟨1 - N.a - 0 + s * N.b, N.b / N.q, N.p * N.b / N.q - N.a,
        (N.x2).trans (nfP_key N N.a N.b 0 _ _ _ rfl rfl rfl), Or.inl ⟨?_, ?_, ?_, ?_⟩⟩
      · have e : 1 - N.a - 0 + s * N.b = (N.b * (N.p + N.r - 1) - N.q * (N.a - 1)) / N.q := by
          rw [hs]; field_simp; ring
        rw [e]; exact div_pos N.t0246 hq
      · exact div_pos N.hb hq
      · have e : (1 + s - 1) * (N.b / N.q) - 1 / N.q * (1 - N.a - 0 + s * N.b - 1) = N.a / N.q := by
          rw [hs]; field_simp; ring
        rw [e]; exact div_pos N.ha hq
      · have e : -(1 + s) * (N.b / N.q - 1 / N.q) - (1 - 1 / N.q) * (1 - N.a - 0 + s * N.b - (1 + s)) =
            -((N.b - 1) * (N.p + N.r) - N.a * (N.q - 1)) / N.q := by
          rw [hs]; field_simp; ring
        rw [e]; exact div_pos (by linarith) hq
    · exact absurd rfl hy3
    · exact absurd rfl hy4
    · exact absurd rfl hy5
    · exact absurd rfl hy6

end H16U
end Minimality
