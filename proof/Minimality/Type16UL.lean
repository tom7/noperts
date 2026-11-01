module

public import Minimality.Type16UK
public import Minimality.Type16UF

@[expose] public section


/-!
# U1: the EV1 leaf `LDE (6,3,5,2,4)` (5-cycle), cell lemma
-/

set_option autoImplicit true
set_option linter.unusedVariables false
open scoped RealInnerProductSpace
open Finset Filter

namespace Minimality
namespace H16U
open TwoRay Type08Sp Type08Sp.C2 V2

variable {x : Fin 7 → ℝ³}

theorem nf_c31 (N : NF16 x) (R1 : (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1) < 0)
    (R2 : 0 < (N.b - 1) * (N.p + N.r) - N.a * (N.q - 1)) : 0 < N.b * (N.p + N.r) - N.q * N.a := by
  have ha := N.ha; have hb := N.hb; have hg := N.hg; have hd := N.hd; have hp := N.hp; have hq := N.hq
  have hr := N.hr; have hab := N.hab; have hgd := N.hgd; have t046_5 := N.t046_5; have t0246 := N.t0246
  have t0146 := N.t0146; have t024_1 := N.t024_1; have t146_2 := N.t146_2; have t245_6 := N.t245_6
  have t145_0 := N.t145_0; have tB125 := N.tB125
  nlinarith [mul_pos ha hb, mul_pos hp hq, mul_pos hb hp]

theorem nf_z1 (N : NF16 x) (R1 : (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1) < 0)
    (R2 : 0 < (N.b - 1) * (N.p + N.r) - N.a * (N.q - 1)) :
    0 < (1 - N.a) * (N.q - N.g) - (1 - N.d) * (N.q - N.b) + (N.p + N.r - 1) * (N.b - N.g) := by
  have ha := N.ha; have hb := N.hb; have hg := N.hg; have hd := N.hd; have hp := N.hp; have hq := N.hq
  have hr := N.hr; have hab := N.hab; have hgd := N.hgd; have t046_5 := N.t046_5; have t0246 := N.t0246
  have t0146 := N.t0146; have t024_1 := N.t024_1; have t146_2 := N.t146_2; have t245_6 := N.t245_6
  have t145_0 := N.t145_0; have tB125 := N.tB125
  nlinarith [mul_pos ha hb, mul_pos hp hq, mul_pos hb hp]

theorem nf_pat43 (N : NF16 x) (R1 : (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1) < 0)
    (R2 : 0 < (N.b - 1) * (N.p + N.r) - N.a * (N.q - 1)) (G : 1 < N.p + N.r) (m1 m2 m3 : ℝ) (hm13 : m1 < m3)
    (hm2 : m2 < 0) (h1 : m3 < 0) (h2 : N.a * m1 + N.b * m2 < N.p * m1 + N.q * m2 + N.r * m3)
    (h3 : m3 < N.p * m1 + N.q * m2 + N.r * m3) : False := by
  have ha := N.ha; have hb := N.hb; have hg := N.hg; have hd := N.hd; have hp := N.hp; have hq := N.hq
  have hr := N.hr; have hab := N.hab; have hgd := N.hgd; have t046_5 := N.t046_5; have t0246 := N.t0246
  have t0146 := N.t0146; have t024_1 := N.t024_1; have t146_2 := N.t146_2; have t245_6 := N.t245_6
  have t145_0 := N.t145_0; have tB125 := N.tB125
  nlinarith [mul_pos ha hb, mul_pos hp hq]


set_option maxHeartbeats 3200000 in
theorem h16u_ev1_L1_cell (T : Type16 x) (hζ : ⟪x 5 - x 3, x 6 - x 0⟫ < 0)
    (hF : 0 < T.ff 5 (x 6) - T.ff 5 (x 0)) (hH : 0 < T.ff 7 (x 6) - T.ff 7 (x 0))
    (hG : T.ff 4 (x 5) < T.ff 4 (x 3)) (hX : ⟪x 0, x 6 - x 0⟫ ≤ ⟪x 3, x 6 - x 0⟫)
    (d63 : ⟪x 6, x 6 - x 0⟫ ≠ ⟪x 3, x 6 - x 0⟫) (d65 : ⟪x 6, x 6 - x 0⟫ ≠ ⟪x 5, x 6 - x 0⟫)
    (d62 : ⟪x 6, x 6 - x 0⟫ ≠ ⟪x 2, x 6 - x 0⟫) (d64 : ⟪x 6, x 6 - x 0⟫ ≠ ⟪x 4, x 6 - x 0⟫)
    (d32 : ⟪x 3, x 6 - x 0⟫ ≠ ⟪x 2, x 6 - x 0⟫) (d34 : ⟪x 3, x 6 - x 0⟫ ≠ ⟪x 4, x 6 - x 0⟫)
    (d52 : ⟪x 5, x 6 - x 0⟫ ≠ ⟪x 2, x 6 - x 0⟫) (d54 : ⟪x 5, x 6 - x 0⟫ ≠ ⟪x 4, x 6 - x 0⟫)
    (d24 : ⟪x 2, x 6 - x 0⟫ ≠ ⟪x 4, x 6 - x 0⟫) :
    HasLexCellAt (univ.image x) (x 6 - x 0) := by
  obtain ⟨P⟩ := exists_par T
  have hR1 := R1_neg T P hF
  have hR2 := R2_pos T P hH
  set N := P.N with hN
  have hq := N.hq
  have hq' : N.q ≠ 0 := hq.ne'
  set s : ℝ := (N.p + N.r - 1) / N.q with hs
  have hsq : s * N.q = N.p + N.r - 1 := by rw [hs]; field_simp
  have hspos : 0 < s := by
    have h1 := P.eE5; have h2 := P.eE3
    rw [h1, h2] at hG
    by_contra hc; push Not at hc
    nlinarith [mul_nonneg (neg_nonneg.2 P.he3.le) (neg_nonneg.2 hc)]
  have G : 1 < N.p + N.r := by
    have : 0 < s * N.q := mul_pos hspos hq
    linarith
  have mem : ∀ i, x i ∈ univ.image x := fun i => mem_image_of_mem x (mem_univ i)
  have c3 : x 6 + (x 3 - x 6) = x 3 := by abel
  have c4 : x 6 + (x 4 - x 6) = x 4 := by abel
  have c5 : fpoint (x 3 - x 6) (x 4 - x 6) (x 6 - x 0) (x 6) (1 + s, 1 / N.q, N.p / N.q) = x 5 := by
    rw [N.x5, nfP_key N 0 1 0 (1 + s) (1 / N.q) (N.p / N.q) (by rw [hs]; ring) (by ring) (by ring)]
  have c2 : fpoint (x 3 - x 6) (x 4 - x 6) (x 6 - x 0) (x 6) (1 - N.a + s * N.b, N.b / N.q, N.p * N.b / N.q - N.a) = x 2 := by
    rw [N.x2, nfP_key N N.a N.b 0 (1 - N.a + s * N.b) (N.b / N.q) (N.p * N.b / N.q - N.a) (by rw [hs]; ring)
      rfl (by ring)]
  -- depths
  have dep : ∀ α β γ, ⟪nfP N.o N.E₁ N.E₂ N.E₃ α β γ, x 6 - x 0⟫ =
      ⟪x 3, x 6 - x 0⟫ + α * ⟪N.E₁, x 6 - x 0⟫ + β * ⟪N.E₂, x 6 - x 0⟫ + γ * ⟪N.E₃, x 6 - x 0⟫ := by
    intro α β γ
    rw [depth_nf, show N.o = x 3 from by
      have := N.x3; simp only [nfP] at this; simpa using this.symm]
  have z6 : ⟪x 6, x 6 - x 0⟫ = ⟪x 3, x 6 - x 0⟫ + ⟪N.E₃, x 6 - x 0⟫ := by
    have := dep 0 0 1; rw [← N.x6] at this; linarith
  have z0 : ⟪x 0, x 6 - x 0⟫ = ⟪x 3, x 6 - x 0⟫ + ⟪N.E₁, x 6 - x 0⟫ := by
    have := dep 1 0 0; rw [← N.x0] at this; linarith
  have z5 : ⟪x 5, x 6 - x 0⟫ = ⟪x 3, x 6 - x 0⟫ + ⟪x 5 - x 3, x 6 - x 0⟫ := by
    have := dep 0 1 0; rw [← N.x5, m2_eq N] at this; linarith
  have z2 : ⟪x 2, x 6 - x 0⟫ = ⟪x 3, x 6 - x 0⟫ + N.a * ⟪N.E₁, x 6 - x 0⟫ + N.b * ⟪x 5 - x 3, x 6 - x 0⟫ := by
    have := dep N.a N.b 0; rw [← N.x2, m2_eq N] at this; linarith
  have z4 : ⟪x 4, x 6 - x 0⟫ = ⟪x 3, x 6 - x 0⟫ + N.p * ⟪N.E₁, x 6 - x 0⟫ + N.q * ⟪x 5 - x 3, x 6 - x 0⟫ +
      N.r * ⟪N.E₃, x 6 - x 0⟫ := by
    have := dep N.p N.q N.r; rw [← N.x4, m2_eq N] at this; linarith
  have m13 := m13_pos N
  set m1 := ⟪N.E₁, x 6 - x 0⟫ with hm1
  set m3 := ⟪N.E₃, x 6 - x 0⟫ with hm3
  set m2 := ⟪x 5 - x 3, x 6 - x 0⟫ with hm2
  have hm1le : m1 ≤ 0 := by rw [z0] at hX; linarith
  -- real facts
  have hc31 := nf_c31 N hR1 hR2
  have hZ' := nf_z1 N hR1 hR2
  have hZ : 0 < N.d * (N.b - 1) - N.a * (N.g - 1) := by
    have e : (N.p + N.r) * (N.d * (N.b - 1) - N.a * (N.g - 1)) =
        N.d * ((N.b - 1) * (N.p + N.r) - N.a * (N.q - 1)) - N.a * ((N.g - 1) * (N.p + N.r) - N.d * (N.q - 1)) := by
      ring
    have h1 := mul_pos N.hd hR2
    have h2 := mul_pos N.ha (neg_pos.2 hR1)
    by_contra hc; push Not at hc
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ N.p + N.r) (neg_nonneg.2 hc)]
  have ex0 : fpoint (x 3 - x 6) (x 4 - x 6) (x 6 - x 0) (x 6) (0, 0, 0) = x 6 := by
    simp [fpoint, fcomb]
  have ex1 : fpoint (x 3 - x 6) (x 4 - x 6) (x 6 - x 0) (x 6) (1, 0, 0) = x 3 := by
    simp [fpoint, fcomb]
  have ex4 : fpoint (x 3 - x 6) (x 4 - x 6) (x 6 - x 0) (x 6) (0, 1, 0) = x 4 := by
    simp [fpoint, fcomb]
  have f0 := cyc5_0 (1 + s) (1 / N.q) (N.p / N.q) (1 - N.a + s * N.b) (N.b / N.q) (N.p * N.b / N.q - N.a)
  have f1 := cyc5_1 (1 + s) (1 / N.q) (N.p / N.q) (1 - N.a + s * N.b) (N.b / N.q) (N.p * N.b / N.q - N.a)
  have f2 := cyc5_2 (1 + s) (1 / N.q) (N.p / N.q) (1 - N.a + s * N.b) (N.b / N.q) (N.p * N.b / N.q - N.a)
  have f3 := cyc5_3 (1 + s) (1 / N.q) (N.p / N.q) (1 - N.a + s * N.b) (N.b / N.q) (N.p * N.b / N.q - N.a)
  have f4 := cyc5_4 (1 + s) (1 / N.q) (N.p / N.q) (1 - N.a + s * N.b) (N.b / N.q) (N.p * N.b / N.q - N.a)
  have e0 : fpoint (x 3 - x 6) (x 4 - x 6) (x 6 - x 0) (x 6) (cyc5 (1 + s) (1 / N.q) (N.p / N.q)
    (1 - N.a + s * N.b) (N.b / N.q) (N.p * N.b / N.q - N.a) 0) = x 6 := by rw [f0, ex0]
  have e1 : fpoint (x 3 - x 6) (x 4 - x 6) (x 6 - x 0) (x 6) (cyc5 (1 + s) (1 / N.q) (N.p / N.q)
    (1 - N.a + s * N.b) (N.b / N.q) (N.p * N.b / N.q - N.a) 1) = x 3 := by rw [f1, ex1]
  have e2 : fpoint (x 3 - x 6) (x 4 - x 6) (x 6 - x 0) (x 6) (cyc5 (1 + s) (1 / N.q) (N.p / N.q)
    (1 - N.a + s * N.b) (N.b / N.q) (N.p * N.b / N.q - N.a) 2) = x 5 := by rw [f2, c5]
  have e3 : fpoint (x 3 - x 6) (x 4 - x 6) (x 6 - x 0) (x 6) (cyc5 (1 + s) (1 / N.q) (N.p / N.q)
    (1 - N.a + s * N.b) (N.b / N.q) (N.p * N.b / N.q - N.a) 3) = x 2 := by rw [f3, c2]
  have e4 : fpoint (x 3 - x 6) (x 4 - x 6) (x 6 - x 0) (x 6) (cyc5 (1 + s) (1 / N.q) (N.p / N.q)
    (1 - N.a + s * N.b) (N.b / N.q) (N.p * N.b / N.q - N.a) 4) = x 4 := by rw [f4, ex4]
  refine h16u_ev1_hasLexCellAt (univ.image x) (x 3 - x 6) (x 4 - x 6) (x 6 - x 0) (x 6) (frame6_det N) (k := 5)
    (by norm_num)
    (cyc5 (1 + s) (1 / N.q) (N.p / N.q) (1 - N.a + s * N.b) (N.b / N.q) (N.p * N.b / N.q - N.a))
    (cyc5_0 _ _ _ _ _ _) (cyc5_1 _ _ _ _ _ _)
    (by have : (-1 : ZMod 5) = 4 := by decide
        rw [this]; exact cyc5_4 _ _ _ _ _ _) ?_ ?_ ?_ (σP := 1) (σQ := 1) one_ne_zero one_ne_zero ?_
  · -- hmem
    intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    · rw [e0]; exact mem 6
    · rw [e1]; exact mem 3
    · rw [e2]; exact mem 5
    · rw [e3]; exact mem 2
    · rw [e4]; exact mem 4
  · exact pent_hconv N.a N.b N.p N.q N.r N.ha N.hb N.hp hq N.hr N.hab N.t0246 hc31 hR2 N.t046_5
  · -- hdep
    have hinj : ∀ i j : ZMod 5, ⟪fpoint (x 3 - x 6) (x 4 - x 6) (x 6 - x 0) (x 6) (cyc5 (1 + s) (1 / N.q)
        (N.p / N.q) (1 - N.a + s * N.b) (N.b / N.q) (N.p * N.b / N.q - N.a) i), x 6 - x 0⟫ =
        ⟪fpoint (x 3 - x 6) (x 4 - x 6) (x 6 - x 0) (x 6) (cyc5 (1 + s) (1 / N.q)
        (N.p / N.q) (1 - N.a + s * N.b) (N.b / N.q) (N.p * N.b / N.q - N.a) j), x 6 - x 0⟫ → i = j := by
      intro i j h
      rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
        simp only [e0, e1, e2, e3, e4] at h <;>
        first
          | rfl
          | exact absurd h d63 | exact absurd h.symm d63 | exact absurd h d65 | exact absurd h.symm d65
          | exact absurd h d62 | exact absurd h.symm d62 | exact absurd h d64 | exact absurd h.symm d64
          | exact absurd h d32 | exact absurd h.symm d32 | exact absurd h d34 | exact absurd h.symm d34
          | exact absurd h d52 | exact absurd h.symm d52 | exact absurd h d54 | exact absurd h.symm d54
          | exact absurd h d24 | exact absurd h.symm d24
          | (exfalso; rw [z5] at h; linarith)
    refine lexUni5_of _ hinj ?_
    simp only [e0, e1, e2, e3, e4]
    have hm2n : m2 < 0 := hζ
    refine peaks5_eq_one _ _ _ _ _ d63 (by rw [z5]; intro h; linarith) d52 d24 (fun h => d64 h.symm) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨-, ⟨h3, -⟩⟩; rw [z5] at h3; linarith
    · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      rw [z6] at h1; rw [z5, z2] at h3; rw [z2, z4] at h4
      have hm3n : m3 < 0 := by linarith
      exact pat_core N.a N.b N.p N.q N.r m1 m2 m3 N.ha N.hp hq N.hr G N.t0246 hR2 (by linarith) m13 hm2n (by linarith)
        (by linarith)
    · rintro ⟨⟨h1, h2⟩, h3⟩; rw [z5] at h1; linarith
    · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      rw [z5, z2] at h1; rw [z4, z2] at h2
      exact pat_core N.a N.b N.p N.q N.r m1 m2 m3 N.ha N.hp hq N.hr G N.t0246 hR2 hm1le m13 hm2n (by linarith)
        (by linarith)
    · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      rw [z2, z4] at h1; rw [z6, z4] at h2; rw [z6] at h3
      have hm3n : m3 < 0 := by linarith
      exact nf_pat43 N hR1 hR2 G m1 m2 m3 m13 hm2n hm3n (by linarith) (by linarith)
  · -- hV
    intro y hy hyx
    obtain ⟨j, -, rfl⟩ := mem_image.1 hy
    fin_cases j
    · exact ⟨(0, 0, -1), (N.x0).trans (nfP_key N 1 0 0 0 0 (-1) (by ring) (by simp) (by ring)),
        Or.inr (Or.inr (Or.inr ⟨-1, rfl, by norm_num, by norm_num⟩))⟩
    · refine ⟨(1 - 0 - N.d + s * N.g, N.g / N.q, N.p * N.g / N.q - 0),
        (N.x1).trans (nfP_key N 0 N.g N.d _ _ _ rfl rfl rfl), Or.inl ?_⟩
      exact pent_inside1 N.a N.b N.g N.d N.p N.q N.r (N.p * N.g / N.q - 0) N.ha N.hb N.hg N.hp hq N.hr N.t0246
        N.t0146 N.hd hR2 N.t046_5 (by linarith) hZ hZ'
    · exact absurd e3.symm (hyx 3)
    · exact absurd e1.symm (hyx 1)
    · exact absurd e4.symm (hyx 4)
    · exact absurd e2.symm (hyx 2)
    · exact absurd e0.symm (hyx 0)

end H16U
end Minimality
