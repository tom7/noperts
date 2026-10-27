module

public import Minimality.HEnd

@[expose] public section

namespace Minimality
open scoped RealInnerProductSpace Topology
open Filter

theorem inner_eq3 (p q : ℝ³) : ⟪p, q⟫ = p 0 * q 0 + p 1 * q 1 + p 2 * q 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem cross_apply0 (a b : ℝ³) : cross a b 0 = a 1 * b 2 - a 2 * b 1 := by simp [cross]
theorem cross_apply1 (a b : ℝ³) : cross a b 1 = a 2 * b 0 - a 0 * b 2 := by simp [cross]
theorem cross_apply2 (a b : ℝ³) : cross a b 2 = a 0 * b 1 - a 1 * b 0 := by simp [cross]

/-- Gram expansion in the frame `e`, `u₀`, `u₀ × e`. -/
theorem parseval_w (e u p q : ℝ³) (he : ⟪e, u⟫ = 0) :
    (⟪e, e⟫ * ⟪u, u⟫) * ⟪p, q⟫ = ⟪u, u⟫ * ⟪p, e⟫ * ⟪q, e⟫ + ⟪e, e⟫ * ⟪p, u⟫ * ⟪q, u⟫ +
      ⟪p, cross u e⟫ * ⟪q, cross u e⟫ := by
  simp only [inner_eq3, cross_apply0, cross_apply1, cross_apply2] at he ⊢
  linear_combination (((e 0 * u 0 + e 1 * u 1 + e 2 * u 2) * (p 0 * q 0 + p 1 * q 1 + p 2 * q 2)) -
    (p 0 * e 0 + p 1 * e 1 + p 2 * e 2) * (q 0 * u 0 + q 1 * u 1 + q 2 * u 2) -
    (p 0 * u 0 + p 1 * u 1 + p 2 * u 2) * (q 0 * e 0 + q 1 * e 1 + q 2 * e 2)) * he


theorem hdet_inner (e n u p q w : ℝ³) :
    hdet ⟪e, p⟫ ⟪n, p⟫ ⟪u, p⟫ ⟪e, q⟫ ⟪n, q⟫ ⟪u, q⟫ ⟪e, w⟫ ⟪n, w⟫ ⟪u, w⟫ =
      det3 e n u * det3 p q w := by
  simp only [hdet, det3_expand, inner_eq3]
  ring


/-! ### The frame of a horizontal end -/

/-- The slope `τ = ⟪g − v, u₀⟫ / ⟪u₀, u₀⟫` of `g` along the edge direction. -/
noncomputable def hfTau (v g u0 : ℝ³) : ℝ := ⟪g - v, u0⟫ / ⟪u0, u0⟫

/-- The horizontal direction `e = (g − v) − τ u₀` (orthogonal to `u₀`). -/
noncomputable def hfE (v g u0 : ℝ³) : ℝ³ := (g - v) - hfTau v g u0 • u0

/-- Frame data: the edge direction `u₀`, the base `v` and far corner `g` of the face `G`, whose
plane has the affine function `fG` (normal `N`). -/
structure HFrame (v g u0 N : ℝ³) (fG : ℝ³ → ℝ) : Prop where
  hu : 0 < ⟪u0, u0⟫
  hN : ∀ y z, fG y - fG z = ⟪N, y - z⟫
  hv : fG v = 0
  hg : fG g = 0
  hNu : ⟪N, u0⟫ = 0
  hNN : 0 < ⟪N, N⟫
  hee : 0 < ⟪hfE v g u0, hfE v g u0⟫

/-- The shadow cross product in the frame. -/
def crossXY (P Q S : V3) : ℝ := (Q.x - P.x) * (S.y - P.y) - (Q.y - P.y) * (S.x - P.x)

/-- The frame coordinates of a point. -/
noncomputable def hfΦ (v g u0 : ℝ³) (fG : ℝ³ → ℝ) (x : ℝ³) : V3 :=
  ⟨⟪x - v, hfE v g u0⟫, -fG x, ⟪x - g, u0⟫⟩

/-- The affine function with the frame coefficients of a facet function `f`. -/
noncomputable def hfFc (v g u0 N : ℝ³) (f : ℝ³ → ℝ) (Nf : ℝ³) : Fc :=
  ⟨⟪Nf, hfE v g u0⟫ / ⟪hfE v g u0, hfE v g u0⟫, -(⟪Nf, N⟫ / ⟪N, N⟫), ⟪Nf, u0⟫ / ⟪u0, u0⟫,
    f v + ⟪Nf, u0⟫ * ⟪g - v, u0⟫ / ⟪u0, u0⟫⟩

namespace HFrame
variable {v g u0 N : ℝ³} {fG : ℝ³ → ℝ} (F : HFrame v g u0 N fG)
include F

theorem inner_e_u : ⟪hfE v g u0, u0⟫ = 0 := by
  have := F.hu
  simp only [hfE, hfTau, inner_sub_left, real_inner_smul_left]
  field_simp
  ring

theorem inner_N_e : ⟪N, hfE v g u0⟫ = 0 := by
  have h0 : ⟪N, g - v⟫ = 0 := by rw [← F.hN, F.hg, F.hv]; ring
  rw [hfE, inner_sub_right, real_inner_smul_right, F.hNu, h0]; ring

/-- Parseval in the orthogonal frame `e`, `N`, `u₀`. -/
theorem parseval (p q : ℝ³) :
    ⟪p, q⟫ = ⟪p, hfE v g u0⟫ * ⟪q, hfE v g u0⟫ / ⟪hfE v g u0, hfE v g u0⟫ +
      ⟪p, u0⟫ * ⟪q, u0⟫ / ⟪u0, u0⟫ + ⟪p, N⟫ * ⟪q, N⟫ / ⟪N, N⟫ := by
  set e := hfE v g u0 with he
  have hE : 0 < ⟪e, e⟫ := F.hee
  have hU := F.hu
  have hNN := F.hNN
  have h1 := parseval_w e u0 p q F.inner_e_u
  have h2p := parseval_w e u0 p N F.inner_e_u
  have h2q := parseval_w e u0 q N F.inner_e_u
  have h3 := parseval_w e u0 N N F.inner_e_u
  have hNe : ⟪N, e⟫ = 0 := F.inner_N_e
  have hNu := F.hNu
  rw [hNe, hNu] at h2p h2q h3
  set w := cross u0 e
  have hS : 0 < ⟪e, e⟫ * ⟪u0, u0⟫ := mul_pos hE hU
  have key : ⟪p, w⟫ * ⟪q, w⟫ * ⟪N, N⟫ = (⟪e, e⟫ * ⟪u0, u0⟫) * ⟪p, N⟫ * ⟪q, N⟫ := by
    apply mul_left_cancel₀ hS.ne'
    linear_combination (⟪p, w⟫ * ⟪q, w⟫) * h3 - (⟪q, w⟫ * ⟪N, w⟫) * h2p - ((⟪e, e⟫ * ⟪u0, u0⟫) * ⟪p, N⟫) * h2q
  field_simp
  linear_combination ⟪N, N⟫ * h1 + key


theorem ev_hfΦ {f : ℝ³ → ℝ} {Nf : ℝ³} (hf : ∀ y z, f y - f z = ⟪Nf, y - z⟫) (x : ℝ³) :
    (hfFc v g u0 N f Nf).ev (hfΦ v g u0 fG x) = f x := by
  have hp := F.parseval Nf (x - v)
  have h1 : f x = f v + ⟪Nf, x - v⟫ := by linarith [hf x v]
  have h2 : ⟪x - v, N⟫ = fG x := by rw [real_inner_comm, ← F.hN, F.hv]; ring
  have h3 : ⟪x - v, u0⟫ = ⟪x - g, u0⟫ + ⟪g - v, u0⟫ := by
    rw [← inner_add_left]; congr 1; abel
  have hU := F.hu.ne'
  simp only [Fc.ev, hfFc, hfΦ]
  rw [h1, hp, h2, h3]
  ring

/-- The orientation tests in the frame: `tst` of the frame images is `D₀ · det3`. -/
theorem tst_hfΦ (δ : ℝ) (P Q S : ℝ³) :
    tst (vw ⟪hfE v g u0, hfE v g u0⟫ ⟪u0, u0⟫ δ) (hfΦ v g u0 fG P) (hfΦ v g u0 fG Q)
      (hfΦ v g u0 fG S) =
      det3 (hfE v g u0) (-N) u0 * det3 (Q - P) (S - P) (hfE v g u0 - δ • u0) := by
  have e1 : ∀ R T : ℝ³, (hfΦ v g u0 fG R).x - (hfΦ v g u0 fG T).x = ⟪R - T, hfE v g u0⟫ := by
    intro R T; simp only [hfΦ]; rw [← inner_sub_left]; congr 1; abel
  have e2 : ∀ R T : ℝ³, (hfΦ v g u0 fG R).y - (hfΦ v g u0 fG T).y = ⟪-N, R - T⟫ := by
    intro R T; simp only [hfΦ]; rw [inner_neg_left, ← F.hN]; ring
  have e3 : ∀ R T : ℝ³, (hfΦ v g u0 fG R).z - (hfΦ v g u0 fG T).z = ⟪R - T, u0⟫ := by
    intro R T; simp only [hfΦ]; rw [← inner_sub_left]; congr 1; abel
  have hE := F.inner_e_u
  have hNe := F.inner_N_e
  have hNu := F.hNu
  rw [← hdet_inner (hfE v g u0) (-N) u0 (Q - P) (S - P) (hfE v g u0 - δ • u0)]
  simp only [tst, vw, e1, e2, e3]
  have a1 : ⟪hfE v g u0, hfE v g u0 - δ • u0⟫ = ⟪hfE v g u0, hfE v g u0⟫ := by
    rw [inner_sub_right, real_inner_smul_right, hE]; ring
  have a2 : ⟪-N, hfE v g u0 - δ • u0⟫ = 0 := by
    rw [inner_neg_left, inner_sub_right, real_inner_smul_right, hNu, hNe]; ring
  have a3 : ⟪u0, hfE v g u0 - δ • u0⟫ = -(δ * ⟪u0, u0⟫) := by
    rw [inner_sub_right, real_inner_smul_right, real_inner_comm (hfE v g u0) u0, hE]; ring
  rw [a1, a2, a3]
  simp only [real_inner_comm (Q - P) (hfE v g u0), real_inner_comm (S - P) (hfE v g u0),
    real_inner_comm (Q - P) (-N), real_inner_comm (S - P) (-N),
    real_inner_comm (Q - P) u0, real_inner_comm (S - P) u0]


theorem hfΦ_x_sub (R T : ℝ³) : (hfΦ v g u0 fG R).x - (hfΦ v g u0 fG T).x = ⟪R - T, hfE v g u0⟫ := by
  simp only [hfΦ]; rw [← inner_sub_left]; congr 1; abel

theorem hfΦ_y_sub (R T : ℝ³) : (hfΦ v g u0 fG R).y - (hfΦ v g u0 fG T).y = ⟪-N, R - T⟫ := by
  simp only [hfΦ]; rw [inner_neg_left, ← F.hN]; ring

theorem hfΦ_z_sub (R T : ℝ³) : (hfΦ v g u0 fG R).z - (hfΦ v g u0 fG T).z = ⟪R - T, u0⟫ := by
  simp only [hfΦ]; rw [← inner_sub_left]; congr 1; abel

/-- `D₀² = E · ⟪N,N⟫ · U ≠ 0`. -/
theorem D0_sq : det3 (hfE v g u0) (-N) u0 * det3 (hfE v g u0) (-N) u0 =
    ⟪hfE v g u0, hfE v g u0⟫ * ⟪N, N⟫ * ⟪u0, u0⟫ := by
  have h := hdet_inner (hfE v g u0) (-N) u0 (hfE v g u0) (-N) u0
  have e1 := F.inner_e_u
  have e2 := F.inner_N_e
  have e3 := F.hNu
  have e4 : ⟪-N, hfE v g u0⟫ = 0 := by rw [inner_neg_left, e2]; simp
  have e5 : ⟪hfE v g u0, -N⟫ = 0 := by rw [real_inner_comm, e4]
  have e6 : ⟪-N, u0⟫ = 0 := by rw [inner_neg_left, e3]; simp
  have e7 : ⟪u0, -N⟫ = 0 := by rw [real_inner_comm, e6]
  have e8 : ⟪u0, hfE v g u0⟫ = 0 := by rw [real_inner_comm, e1]
  have e9 : ⟪-N, -N⟫ = ⟪N, N⟫ := by simp
  rw [e1, e5, e8, e4, e7, e6, e9] at h
  simp only [hdet] at h
  linear_combination -h

theorem D0_ne : det3 (hfE v g u0) (-N) u0 ≠ 0 := by
  intro h0
  have := F.D0_sq
  rw [h0] at this
  have h1 := F.hee; have h2 := F.hNN; have h3 := F.hu
  have : 0 < ⟪hfE v g u0, hfE v g u0⟫ * ⟪N, N⟫ * ⟪u0, u0⟫ := by positivity
  linarith

theorem det3_u0_coord (P Q S : ℝ³) :
    det3 (hfE v g u0) (-N) u0 * det3 (Q - P) (S - P) u0 =
      ⟪u0, u0⟫ * crossXY (hfΦ v g u0 fG P) (hfΦ v g u0 fG Q) (hfΦ v g u0 fG S) := by
  have h := hdet_inner (hfE v g u0) (-N) u0 (Q - P) (S - P) u0
  have e1 := F.inner_e_u
  have e3 := F.hNu
  have e6 : ⟪-N, u0⟫ = 0 := by rw [inner_neg_left, e3]; simp
  rw [e1, e6] at h
  simp only [hdet] at h
  simp only [crossXY, hfΦ_x_sub F, hfΦ_y_sub F]
  simp only [real_inner_comm (hfE v g u0) (Q - P), real_inner_comm (hfE v g u0) (S - P),
    real_inner_comm (-N) (Q - P), real_inner_comm (-N) (S - P)]
  linear_combination -h


theorem shadow_sign (P Q S P' Q' S' : ℝ³)
    (h : 0 < det3 (Q - P) (S - P) u0 * det3 (Q' - P') (S' - P') u0) :
    0 < crossXY (hfΦ v g u0 fG P) (hfΦ v g u0 fG Q) (hfΦ v g u0 fG S) *
      crossXY (hfΦ v g u0 fG P') (hfΦ v g u0 fG Q') (hfΦ v g u0 fG S') := by
  have h1 := F.det3_u0_coord P Q S
  have h2 := F.det3_u0_coord P' Q' S'
  have hD := F.D0_sq
  have hU := F.hu
  have hpos : 0 < ⟪hfE v g u0, hfE v g u0⟫ * ⟪N, N⟫ * ⟪u0, u0⟫ := by
    have := F.hee; have := F.hNN; positivity
  set D0 := det3 (hfE v g u0) (-N) u0
  set c1 := crossXY (hfΦ v g u0 fG P) (hfΦ v g u0 fG Q) (hfΦ v g u0 fG S)
  set c2 := crossXY (hfΦ v g u0 fG P') (hfΦ v g u0 fG Q') (hfΦ v g u0 fG S')
  have key : (D0 * D0) * (det3 (Q - P) (S - P) u0 * det3 (Q' - P') (S' - P') u0) =
      (⟪u0, u0⟫ * ⟪u0, u0⟫) * (c1 * c2) := by
    calc (D0 * D0) * (det3 (Q - P) (S - P) u0 * det3 (Q' - P') (S' - P') u0)
        = (D0 * det3 (Q - P) (S - P) u0) * (D0 * det3 (Q' - P') (S' - P') u0) := by ring
      _ = _ := by rw [h1, h2]; ring
  rw [hD] at key
  have : 0 < (⟪u0, u0⟫ * ⟪u0, u0⟫) * (c1 * c2) := by rw [← key]; exact mul_pos hpos h
  exact pos_of_mul_pos_right this (mul_pos hU hU).le


/-- The frame coordinates determine the point. -/
theorem hfΦ_inj {P Q : ℝ³} (h : hfΦ v g u0 fG P = hfΦ v g u0 fG Q) : P = Q := by
  have hx := congrArg V3.x h
  have hy := congrArg V3.y h
  have hz := congrArg V3.z h
  simp only [hfΦ] at hx hy hz
  have h1 : ⟪P - Q, hfE v g u0⟫ = 0 := by
    rw [show P - Q = (P - v) - (Q - v) by abel, inner_sub_left]; linarith
  have h2 : ⟪P - Q, u0⟫ = 0 := by
    have : ⟪P - g, u0⟫ - ⟪Q - g, u0⟫ = ⟪P - Q, u0⟫ := by
      rw [← inner_sub_left]; congr 1; abel
    linarith
  have h3 : ⟪P - Q, N⟫ = 0 := by
    rw [real_inner_comm, ← F.hN]; linarith
  have hp := F.parseval (P - Q) (P - Q)
  rw [h1, h2, h3] at hp
  simp only [zero_mul, zero_div, add_zero] at hp
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hp)

/-- A point of the plane `G` with prescribed `x`- and `z`-coordinates over a chord. -/
theorem mid_of_coords {P Q m : ℝ³} (s δ' δ : ℝ) (hP : fG P = 0) (hQ : fG Q = 0) (hm : fG m = 0)
    (hx : (hfΦ v g u0 fG m).x = (hfΦ v g u0 fG P).x + s * ((hfΦ v g u0 fG Q).x -
      (hfΦ v g u0 fG P).x) + δ' * ⟪hfE v g u0, hfE v g u0⟫)
    (hz : (hfΦ v g u0 fG m).z = (hfΦ v g u0 fG P).z + s * ((hfΦ v g u0 fG Q).z -
      (hfΦ v g u0 fG P).z) - δ' * δ * ⟪u0, u0⟫) :
    m = P + s • (Q - P) + δ' • (hfE v g u0 - δ • u0) := by
  apply F.hfΦ_inj
  have hyN : fG (P + s • (Q - P) + δ' • (hfE v g u0 - δ • u0)) = 0 := by
    have h1 := F.hN (P + s • (Q - P) + δ' • (hfE v g u0 - δ • u0)) P
    rw [show P + s • (Q - P) + δ' • (hfE v g u0 - δ • u0) - P =
        s • (Q - P) + δ' • (hfE v g u0 - δ • u0) by abel, inner_add_right,
      real_inner_smul_right, real_inner_smul_right,
      inner_sub_right N (hfE v g u0) (δ • u0), real_inner_smul_right, F.inner_N_e, F.hNu,
      ← F.hN Q P] at h1
    rw [hP, hQ] at h1
    linarith
  have heu' : ⟪u0, hfE v g u0⟫ = 0 := by rw [real_inner_comm]; exact F.inner_e_u
  have hxx : ⟪(P + s • (Q - P) + δ' • (hfE v g u0 - δ • u0)) - v, hfE v g u0⟫ =
      ⟪P - v, hfE v g u0⟫ + s * (⟪Q - v, hfE v g u0⟫ - ⟪P - v, hfE v g u0⟫) +
        δ' * ⟪hfE v g u0, hfE v g u0⟫ := by
    have e1 : (P + s • (Q - P) + δ' • (hfE v g u0 - δ • u0)) - v =
        (P - v) + s • ((Q - v) - (P - v)) + δ' • (hfE v g u0 - δ • u0) := by
      simp only [smul_sub]; abel
    rw [e1]
    simp only [inner_add_left, inner_sub_left, real_inner_smul_left, heu']
    ring
  have hzz : ⟪(P + s • (Q - P) + δ' • (hfE v g u0 - δ • u0)) - g, u0⟫ =
      ⟪P - g, u0⟫ + s * (⟪Q - g, u0⟫ - ⟪P - g, u0⟫) - δ' * δ * ⟪u0, u0⟫ := by
    have e1 : (P + s • (Q - P) + δ' • (hfE v g u0 - δ • u0)) - g =
        (P - g) + s • ((Q - g) - (P - g)) + δ' • (hfE v g u0 - δ • u0) := by
      simp only [smul_sub]; abel
    rw [e1]
    simp only [inner_add_left, inner_sub_left, real_inner_smul_left, F.inner_e_u]
    ring
  simp only [hfΦ]
  simp only [hfΦ] at hx hz
  rw [hxx, hzz, hyN, hm]
  simp only [V3.mk.injEq]
  exact ⟨hx, trivial, hz⟩

end HFrame

end Minimality
end
