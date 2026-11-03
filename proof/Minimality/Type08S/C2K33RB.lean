module

public import Minimality.Type08S.C2K33RA
public import Minimality.Type08S.C2K32GB

@[expose] public section

set_option maxHeartbeats 1000000
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option maxHeartbeats 12800000
set_option maxRecDepth 100000
open scoped RealInnerProductSpace
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

/-- `ori(c', b, a') = n_cba . u0` with `u0 = adj(G) n1`, `n1 = (a-a') x (b'-a')`; `G` = Gram of `(a-d, b-d, c-d)`. -/
def k28b2rOri (α1 β1 β6 γ6 pp s qq qr rr : ℝ) : ℝ :=
  (1 - β1) * γ6 * ((qq * rr - qr ^ 2) * (-(β1 * β6)) + (-s * (rr - qr)) * (γ6 * (1 - α1) - β1) +
      (-s * (qq - qr)) * (β6 * (α1 - 1))) +
    α1 * γ6 * ((-s * (rr - qr)) * (-(β1 * β6)) + (pp * rr - s ^ 2) * (γ6 * (1 - α1) - β1) +
      (s ^ 2 - pp * qr) * (β6 * (α1 - 1))) +
    α1 * (1 - β6) * ((-s * (qq - qr)) * (-(β1 * β6)) + (s ^ 2 - pp * qr) * (γ6 * (1 - α1) - β1) +
      (pp * qq - s ^ 2) * (β6 * (α1 - 1)))

theorem k28b2r_tsc_of {D : ℝ} (hD : 0 < D) {e f v : ℝ × ℝ × ℝ} (h : 0 < e.1 * f.2.1 - e.2.1 * f.1) :
    TSc D e f v := by
  refine Or.inl ?_
  simp only [d3]
  linarith [mul_pos hD h]

theorem k28b2r_step_lt {p q r d : ℝ³} {L : List (ℝ × ℝ)} {s t : ℝ × ℝ × ℝ}
    (h : ⟪fpoint p q r d s, r⟫ < ⟪fpoint p q r d t, r⟫) : K25Step p q r d L s t :=
  ⟨h.le, fun e => absurd e h.ne⟩

theorem k28b2r_inj {a e β6 g6 up uq ur : ℝ} (hur : 0 < ur) (he : 0 < e) (hg6 : 0 < g6) (hb6 : 0 < β6)
    (hs : β6 + g6 = 1 + e) : ∀ i j : ZMod 5, k28b2rY a e β6 g6 up uq ur i = k28b2rY a e β6 g6 up uq ur j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  have e3 := congrArg (fun t => t.2.2) h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [k28b2rY_0, k28b2rY_1, k28b2rY_2, k28b2rY_3, k28b2rY_4] at e1 e2 e3; linarith)

theorem k28b2_R15 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hβ : 1 < β1) (hσ : β6 + γ6 = β1)
    (hL : ⟪a - c', a - d⟫ = 0)
    (hMp : 0 < ⟪b - d, c - d⟫ * ⟪a - d, a - d⟫ - ⟪a - d, b - d⟫ ^ 2)
    (hΛ : 0 ≤ (β1 - 1) * (⟪b - d, c - d⟫ * ⟪a - d, a - d⟫ - ⟪a - d, b - d⟫ ^ 2) +
      (γ6 - 1) * (⟪c - d, c - d⟫ - ⟪b - d, c - d⟫) * ⟪a - d, a - d⟫)
    (hori : k28b2rOri α1 β1 β6 γ6 ⟪a - d, a - d⟫ ⟪a - d, b - d⟫ ⟪b - d, b - d⟫ ⟪b - d, c - d⟫ ⟪c - d, c - d⟫ < 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hdet, hc', hb', ha', hα1', hβ1', h1, hβ6', hγ6', h3⟩ := hC
  obtain ⟨m1, m2, m3⟩ := hM
  obtain ⟨hr1, hr2⟩ := hrel
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  have hp0 : p ≠ 0 := by intro h0; apply hdet; rw [h0]; simp [det3_expand]
  have hpp : 0 < ⟪p, p⟫ := real_inner_self_pos.2 hp0
  have hm1 : ⟪p, q⟫ = ⟪p, r⟫ := by
    have : ⟪p, b - c⟫ = ⟪p, q⟫ - ⟪p, r⟫ := by
      rw [← inner_sub_right]; congr 1; rw [hq, hr]; abel
    linarith
  have hqp : ⟪q, p⟫ = ⟪p, q⟫ := real_inner_comm _ _
  have hrp : ⟪r, p⟫ = ⟪p, r⟫ := real_inner_comm _ _
  have hrq : ⟪r, q⟫ = ⟪q, r⟫ := real_inner_comm _ _
  have hQR : ⟪q, r⟫ < ⟪q, q⟫ := by
    have e : c' - d = α1 • p + β1 • q := by rw [hc', hp, hq]; module
    have e2 : b - c = q - r := by rw [hq, hr]; abel
    rw [e, e2] at m2
    simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real, inner_sub_right] at m2
    have h0 : α1 * (⟪p, q⟫ - ⟪p, r⟫) = 0 := by rw [hm1]; ring
    nlinarith [m2, h0, hqp, hrp]
  have hRT : ⟪q, r⟫ < ⟪r, r⟫ := by
    have e : b' - d = α1 • p + β1 • r := by rw [hb', hp, hr]; module
    have e2 : b - c = q - r := by rw [hq, hr]; abel
    rw [e, e2] at m3
    simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real, inner_sub_right] at m3
    have h0 : α1 * (⟪p, q⟫ - ⟪p, r⟫) = 0 := by rw [hm1]; ring
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg hβ1'.le (sub_nonneg.2 hh), m3, h0, hrq]
  have hs : ⟪p, q⟫ < 0 := by
    have hW : 0 < ⟪q, q⟫ + ⟪r, r⟫ - 2 * ⟪q, r⟫ := by linarith
    have h1' : 0 < (β1 - 1) * (⟪q, q⟫ * ⟪r, r⟫ - ⟪q, r⟫ ^ 2) := mul_pos (by linarith) hr2
    by_contra hh; push Not at hh
    have h2 : 0 ≤ α1 * ⟪p, q⟫ * (⟪q, q⟫ + ⟪r, r⟫ - 2 * ⟪q, r⟫) :=
      mul_nonneg (mul_nonneg hα1'.le hh) hW.le
    nlinarith [hr1]
  have hLe : (1 - α1) * ⟪p, p⟫ - β1 * ⟪p, q⟫ = 0 := by
    have e : a - c' = (1 - α1) • p - β1 • q := by rw [hc', hp, hq]; module
    rw [e] at hL
    simp only [inner_sub_left, inner_smul_left, RCLike.conj_to_real, hqp] at hL
    linarith
  have hα1 : 1 < α1 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg (sub_nonneg.2 hh) hpp.le, mul_pos hβ1' (neg_pos.2 hs), hLe]
  have hspr : ⟪p, r⟫ = ⟪p, q⟫ := hm1.symm
  clear_value p q r
  -- point relations
  have ha2 : a = d + p := by rw [hp]; abel
  have hb2 : b = d + q := by rw [hq]; abel
  have hc2 : c = d + r := by rw [hr]; abel
  have hc'2 := hc'
  have hb'2 := hb'
  have ha'2 := ha'
  -- real parametrisation
  obtain ⟨ea, rfl⟩ : ∃ ea, α1 = 1 + ea := ⟨α1 - 1, by ring⟩
  obtain ⟨ee, rfl⟩ : ∃ ee, β1 = 1 + ee := ⟨β1 - 1, by ring⟩
  obtain rfl : γ6 = 1 + ee - β6 := by linarith
  have hea : 0 < ea := by linarith
  have hee : 0 < ee := by linarith
  obtain ⟨w, hwd⟩ : ∃ w : ℝ, w = ⟪p, p⟫ / (1 + ee) ^ 2 := ⟨_, rfl⟩
  have hb1 : 0 < 1 + ee := by linarith
  have hw : 0 < w := by rw [hwd]; positivity
  have Epp : ⟪p, p⟫ = (1 + ee) ^ 2 * w := by rw [hwd]; field_simp
  have Es : ⟪p, q⟫ = -(ea * (1 + ee) * w) := by
    have : (1 + ee) * ⟪p, q⟫ = (1 + ee) * (-(ea * (1 + ee) * w)) := by rw [Epp] at hLe; nlinarith [hLe]
    exact mul_left_cancel₀ hb1.ne' this
  have Es2 : ⟪p, r⟫ = -(ea * (1 + ee) * w) := by rw [hspr, Es]
  obtain ⟨Mv, hMd⟩ : ∃ Mv : ℝ, Mv = (⟪q, r⟫ * ⟪p, p⟫ - ⟪p, q⟫ ^ 2) / ⟪p, p⟫ := ⟨_, rfl⟩
  have hMv : 0 < Mv := by rw [hMd]; exact div_pos hMp hpp
  have hMpp : Mv * ⟪p, p⟫ = ⟪q, r⟫ * ⟪p, p⟫ - ⟪p, q⟫ ^ 2 := by rw [hMd]; field_simp
  have Eqr : ⟪q, r⟫ = Mv + ea ^ 2 * w := by
    have : (⟪q, r⟫ - Mv - ea ^ 2 * w) * ⟪p, p⟫ = 0 := by
      rw [Epp] at hMpp ⊢; rw [Es] at hMpp; linear_combination (-1 : ℝ) * hMpp
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hpp.ne'
  obtain ⟨kap, hkd⟩ : ∃ kap : ℝ, kap = ⟪q, q⟫ - ⟪q, r⟫ := ⟨_, rfl⟩
  obtain ⟨rho, hrd⟩ : ∃ rho : ℝ, rho = ⟪r, r⟫ - ⟪q, r⟫ := ⟨_, rfl⟩
  have hk : 0 < kap := by rw [hkd]; linarith
  have hrho : 0 < rho := by rw [hrd]; linarith
  have Eqq : ⟪q, q⟫ = Mv + kap + ea ^ 2 * w := by rw [Eqr] at hkd; linarith
  have Err : ⟪r, r⟫ = Mv + rho + ea ^ 2 * w := by rw [Eqr] at hrd; linarith
  have hrel' : ee * ((Mv + kap) * (Mv + rho) - Mv ^ 2) = ea * (ea + 1 + ee) * w * (kap + rho) := by
    rw [Es, Eqq, Eqr, Err] at hr1
    linear_combination hr1
  have hL0 : 0 ≤ ee * Mv + (1 + ee - β6 - 1) * rho := by
    have h5 : 0 ≤ ⟪p, p⟫ * (ee * Mv + (1 + ee - β6 - 1) * rho) := by
      have : (1 + ee - 1) * (⟪q, r⟫ * ⟪p, p⟫ - ⟪p, q⟫ ^ 2) +
          (1 + ee - β6 - 1) * (⟪r, r⟫ - ⟪q, r⟫) * ⟪p, p⟫ = ⟪p, p⟫ * (ee * Mv + (1 + ee - β6 - 1) * rho) := by
        rw [← hMpp, hrd]; ring
      rw [← this]; exact hΛ
    by_contra hh; push Not at hh
    nlinarith [mul_pos hpp (neg_pos.2 hh)]
  -- the view
  obtain ⟨up, hup⟩ : ∃ up : ℝ, up = ((-1)*Mv*β6*ee*kap + (-1)*Mv*β6*ee*rho + (-1)*Mv*β6*kap + (-1)*Mv*β6*rho + (-2)*ea*ee*rho*w + (-1)*ea*ee^2*rho*w + (-1)*ea*rho*w + (-2)*ea^2*ee*rho*w + (-1)*ea^2*ee^2*rho*w + (-1)*ea^2*rho*w + (-1)*β6*ee*kap*rho + (-1)*β6*kap*rho) := ⟨_, rfl⟩
  obtain ⟨uq, huq⟩ : ∃ uq : ℝ, uq = ((-3)*Mv*ea*ee*w + (-3)*Mv*ea*ee^2*w + (-1)*Mv*ea*ee^3*w + (-1)*Mv*ea*w + (-3)*Mv*ee*w + (-3)*Mv*ee^2*w + (-1)*Mv*ee^3*w + (-1)*Mv*w + (-3)*ea*ee*rho*w + (-3)*ea*ee^2*rho*w + (-1)*ea*ee^3*rho*w + (-1)*ea*rho*w + (-3)*ee*rho*w + (-3)*ee^2*rho*w + (-1)*ee^3*rho*w + (-1)*rho*w) := ⟨_, rfl⟩
  obtain ⟨ur, hur⟩ : ∃ ur : ℝ, ur = (3*Mv*ea*ee*w + 3*Mv*ea*ee^2*w + Mv*ea*ee^3*w + Mv*ea*w + 3*Mv*ee*w + 3*Mv*ee^2*w + Mv*ee^3*w + Mv*w) := ⟨_, rfl⟩
  have hur0 : 0 < ur := by rw [hur]; positivity
  have hori' : (1 - (1 + ee)) * (1 + ee - β6) * up + (1 + ea) * (1 + ee - β6) * uq +
      (1 + ea) * (1 - β6) * ur < 0 := by
    unfold k28b2rOri at hori
    rw [Epp, Es, Eqq, Eqr, Err] at hori
    rw [hup, huq, hur]
    linarith [hori]
  have hg6 : 0 < 1 + ee - β6 := by linarith
  have hsum : β6 + (1 + ee - β6) = 1 + ee := by ring
  obtain ⟨hcyc, hrest⟩ := k28b2r_min ea ee β6 (1 + ee - β6) w Mv rho kap up uq ur hea hee hβ6' hg6 hsum hw hMv
    hrho hk hrel' hup huq hur hL0 hori'
  -- frame
  obtain ⟨u0, hu0⟩ : ∃ u0 : ℝ³, u0 = up • p + uq • q + ur • r := ⟨_, rfl⟩
  obtain ⟨ι, hιd⟩ : ∃ ι : ℝ, ι = ur⁻¹ := ⟨_, rfl⟩
  have hι : ur * ι = 1 := by rw [hιd]; field_simp
  have hι' : ι * ur = 1 := by rw [mul_comm]; exact hι
  have hι0 : 0 < ι := by rw [hιd]; positivity
  obtain ⟨P, hP⟩ : ∃ P : ℝ³, P = ι • p := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ³, Q = ι • q := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ³, R = ι • u0 := ⟨_, rfl⟩
  have hp' : p = ur • P := by rw [hP, smul_smul, hι, one_smul]
  have hq' : q = ur • Q := by rw [hQ, smul_smul, hι, one_smul]
  have hr' : r = R - up • P - uq • Q := by
    have : R - up • P - uq • Q = (ι * ur) • r := by rw [hR, hP, hQ, hu0]; module
    rw [this, hι', one_smul]
  have hΔ : det3 P Q R ≠ 0 := by
    have : det3 P Q R = ι ^ 3 * ur * det3 p q r := by
      rw [hP, hQ, hR, hu0]
      simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [this]; exact mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hι0.ne') hur0.ne') hdet
  have hRne : R ≠ 0 := k17f_r0 hΔ
  have E0 : fpoint P Q R d (0, 0, 0) = d := by rw [k17f_fp]; simp
  have E1 : fpoint P Q R d (ur, 0, 0) = a := by rw [k17f_fp, ha2, hp']; module
  have E2 : fpoint P Q R d ((1 + ea) * ur - (1 + ee) * up, -((1 + ee) * uq), 1 + ee) = b' := by
    rw [k17f_fp, hb'2, hp', hr']; module
  have E3 : fpoint P Q R d (-((1 + ee - β6) * up), β6 * ur - (1 + ee - β6) * uq, 1 + ee - β6) = a' := by
    rw [k17f_fp, ha'2, hq', hr']; module
  have E4 : fpoint P Q R d (0, ur, 0) = b := by rw [k17f_fp, hb2, hq']; module
  have Ec' : fpoint P Q R d (k28b2rYc' ea ee up uq ur) = c' := by
    unfold k28b2rYc'; rw [k17f_fp, hc'2, hp', hq']; module
  have Ec : fpoint P Q R d (k28b2rYc up uq) = c := by
    unfold k28b2rYc; rw [k17f_fp, hc2, hr']; module
  have hY0 : fpoint P Q R d (k28b2rY ea ee β6 (1 + ee - β6) up uq ur 0) = d := by rw [k28b2rY_0]; exact E0
  have hY1 : fpoint P Q R d (k28b2rY ea ee β6 (1 + ee - β6) up uq ur 1) = a := by rw [k28b2rY_1]; exact E1
  have hY2 : fpoint P Q R d (k28b2rY ea ee β6 (1 + ee - β6) up uq ur 2) = b' := by rw [k28b2rY_2]; exact E2
  have hY3 : fpoint P Q R d (k28b2rY ea ee β6 (1 + ee - β6) up uq ur 3) = a' := by rw [k28b2rY_3]; exact E3
  have hY4 : fpoint P Q R d (k28b2rY ea ee β6 (1 + ee - β6) up uq ur 4) = b := by rw [k28b2rY_4]; exact E4
  -- depths
  have Dt0 : 0 < Mv * kap + Mv * rho + kap * rho := by positivity
  have hdp : ⟪p, u0⟫ = -((1 + ee) * β6) * ((1 + ee) ^ 2 * w * (Mv * kap + Mv * rho + kap * rho)) := by
    rw [hu0, inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, Epp, Es, Es2, hup, huq, hur]; ring
  have hdq : ⟪q, u0⟫ = -(((1 + ee - β6) * ea + (1 + ee))) * ((1 + ee) ^ 2 * w * (Mv * kap + Mv * rho + kap * rho)) := by
    rw [hu0, inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, hqp, Eqq, Eqr, Es, hup, huq, hur]; ring
  have hdr : ⟪r, u0⟫ = (β6 * ea) * ((1 + ee) ^ 2 * w * (Mv * kap + Mv * rho + kap * rho)) := by
    rw [hu0, inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, hrp, hrq, Err, Eqr, Es2, hup, huq, hur]; ring
  have DG0 : 0 < (1 + ee) ^ 2 * w * (Mv * kap + Mv * rho + kap * rho) := by positivity
  have hpR : ⟪p, R⟫ = ι * ⟪p, u0⟫ := by rw [hR, real_inner_smul_right]
  have hqR : ⟪q, R⟫ = ι * ⟪q, u0⟫ := by rw [hR, real_inner_smul_right]
  have hrR : ⟪r, R⟫ = ι * ⟪r, u0⟫ := by rw [hR, real_inner_smul_right]
  have zA : ⟪a, R⟫ = ⟪d, R⟫ + ι * ⟪p, u0⟫ := by rw [ha2, inner_add_left, hpR]
  have zB : ⟪b, R⟫ = ⟪d, R⟫ + ι * ⟪q, u0⟫ := by rw [hb2, inner_add_left, hqR]
  have zB' : ⟪b', R⟫ = ⟪d, R⟫ + (1 + ea) * (ι * ⟪p, u0⟫) + (1 + ee) * (ι * ⟪r, u0⟫) := by
    rw [hb'2, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left, hpR, hrR]
  have zA' : ⟪a', R⟫ = ⟪d, R⟫ + β6 * (ι * ⟪q, u0⟫) + (1 + ee - β6) * (ι * ⟪r, u0⟫) := by
    rw [ha'2, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left, hqR, hrR]
  have hap : ι * ⟪p, u0⟫ < 0 := by
    rw [hdp]; have := mul_pos hι0 (mul_pos (mul_pos hb1 hβ6') DG0); linarith [this]
  have hbq : ι * ⟪q, u0⟫ < 0 := by
    rw [hdq]
    have : 0 < ((1 + ee - β6) * ea + (1 + ee)) := by linarith [mul_pos hg6 hea]
    nlinarith [mul_pos (mul_pos hι0 this) DG0]
  have hz1 : ⟪b', R⟫ = ⟪a, R⟫ := by
    rw [zB', zA, hdp, hdr]; ring
  have hz2 : ⟪a', R⟫ = ⟪b', R⟫ := by
    rw [zA', zB', hdp, hdq, hdr]; ring
  obtain ⟨m0, m1', m2', m3', m4, p0, p1, p2, p3, p4⟩ := k19_z5
  -- cone
  have ip : ∀ (x y z : ℝ) (w' : ℝ³), ⟪x • p + y • q + z • r, w'⟫ = x * ⟪p, w'⟫ + y * ⟪q, w'⟫ + z * ⟪r, w'⟫ := by
    intro x y z w'; simp only [inner_add_left, real_inner_smul_left]
  have hA : a - b' = (-ea) • p + (0 : ℝ) • q + (-(1 + ee)) • r := by rw [ha2, hb'2]; module
  have hB : b' - a' = (1 + ea) • p + (-β6) • q + β6 • r := by rw [hb'2, ha'2]; module
  have g1 : ⟪a - b', P⟫ = ι * (-ea * ⟪p, p⟫ + 0 * ⟪q, p⟫ + (-(1 + ee)) * ⟪r, p⟫) := by
    rw [hA, hP, real_inner_smul_right, ip]
  have g2 : ⟪a - b', Q⟫ = ι * (-ea * ⟪p, q⟫ + 0 * ⟪q, q⟫ + (-(1 + ee)) * ⟪r, q⟫) := by
    rw [hA, hQ, real_inner_smul_right, ip]
  have g3 : ⟪b' - a', P⟫ = ι * ((1 + ea) * ⟪p, p⟫ + (-β6) * ⟪q, p⟫ + β6 * ⟪r, p⟫) := by
    rw [hB, hP, real_inner_smul_right, ip]
  have g4 : ⟪b' - a', Q⟫ = ι * ((1 + ea) * ⟪p, q⟫ + (-β6) * ⟪q, q⟫ + β6 * ⟪r, q⟫) := by
    rw [hB, hQ, real_inner_smul_right, ip]
  have hDd : ⟪a - b', P⟫ * ⟪b' - a', Q⟫ - ⟪a - b', Q⟫ * ⟪b' - a', P⟫ = ι := by
    rw [g1, g2, g3, g4, hqp, hrp, hrq, Epp, Es, Es2, Eqq, Eqr]
    calc _ = ι ^ 2 * ur := by rw [hur]; ring
      _ = ι := by rw [sq, mul_assoc, hι', mul_one]
  obtain ⟨L, hLd⟩ : ∃ L : List (ℝ × ℝ), L = [(⟪a - b', P⟫, ⟪a - b', Q⟫), (⟪b' - a', P⟫, ⟪b' - a', Q⟫)] := ⟨_, rfl⟩
  have hl1 : (⟪a - b', P⟫, ⟪a - b', Q⟫) ∈ L := by rw [hLd]; simp
  have hl2 : (⟪b' - a', P⟫, ⟪b' - a', Q⟫) ∈ L := by rw [hLd]; simp
  have stepT2 : K25Step P Q R d L (k28b2rY ea ee β6 (1 + ee - β6) up uq ur 2)
      (k28b2rY ea ee β6 (1 + ee - β6) up uq ur 1) := by
    refine ⟨by rw [hY2, hY1]; exact hz1.le, fun _ v1 v2 hv => ?_⟩
    rw [hY1, hY2]; exact hv _ hl1
  have stepT3 : K25Step P Q R d L (k28b2rY ea ee β6 (1 + ee - β6) up uq ur 3)
      (k28b2rY ea ee β6 (1 + ee - β6) up uq ur 2) := by
    refine ⟨by rw [hY3, hY2]; exact hz2.le, fun _ v1 v2 hv => ?_⟩
    rw [hY2, hY3]; exact hv _ hl2
  have stepA : K25Step P Q R d L (k28b2rY ea ee β6 (1 + ee - β6) up uq ur 1)
      (k28b2rY ea ee β6 (1 + ee - β6) up uq ur 0) :=
    k28b2r_step_lt (by rw [hY1, hY0, zA]; linarith)
  have stepB : K25Step P Q R d L (k28b2rY ea ee β6 (1 + ee - β6) up uq ur 4)
      (k28b2rY ea ee β6 (1 + ee - β6) up uq ur 0) :=
    k28b2r_step_lt (by rw [hY4, hY0, zB]; linarith)
  have hmem : ∀ i, fpoint P Q R d (k28b2rY ea ee β6 (1 + ee - β6) up uq ur i) ∈ V8 a a' b b' c c' d := by
    intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · rw [hY0]; simp [V8]
    · rw [hY1]; simp [V8]
    · rw [hY2]; simp [V8]
    · rw [hY3]; simp [V8]
    · rw [hY4]; simp [V8]
  refine ⟨R, hRne, ?_⟩
  refine k25_tie_cell (V8 a a' b b' c c' d) P Q R d hΔ (k := 5) (by norm_num)
    (k28b2rY ea ee β6 (1 + ee - β6) up uq ur) (k28b2r_inj hur0 hee hg6 hβ6' hsum) hmem L
    (by rw [hLd]; simp) ?_ ?_ 0 ?_ ?_ ?_
    (ρ1 := ⟪b' - a', Q⟫ - ⟪a - b', Q⟫) (ρ2 := ⟪a - b', P⟫ - ⟪b' - a', P⟫) (δ1 := 0) (δ2 := 0) ?_
  · intro v1 v2 _ D hD i j h1 h2
    exact k28b2r_tsc_of hD (hcyc i j h1 h2)
  · intro y hy hyx
    have hV : y = fpoint P Q R d (k28b2rY ea ee β6 (1 + ee - β6) up uq ur 0) ∨
        y = fpoint P Q R d (k28b2rY ea ee β6 (1 + ee - β6) up uq ur 1) ∨
        y = fpoint P Q R d (k28b2rY ea ee β6 (1 + ee - β6) up uq ur 2) ∨
        y = fpoint P Q R d (k28b2rY ea ee β6 (1 + ee - β6) up uq ur 3) ∨
        y = fpoint P Q R d (k28b2rY ea ee β6 (1 + ee - β6) up uq ur 4) ∨
        y = fpoint P Q R d (k28b2rYc' ea ee up uq ur) ∨ y = fpoint P Q R d (k28b2rYc up uq) := by
      rw [hY0, hY1, hY2, hY3, hY4, Ec', Ec]
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 rfl).elim
    · exact (hyx 1 rfl).elim
    · exact (hyx 2 rfl).elim
    · exact (hyx 3 rfl).elim
    · exact (hyx 4 rfl).elim
    · exact ⟨_, rfl, fun v1 v2 _ D hD i => k28b2r_tsc_of hD (hrest _ (by simp) i)⟩
    · exact ⟨_, rfl, fun v1 v2 _ D hD i => k28b2r_tsc_of hD (hrest _ (by simp) i)⟩
  · rw [m0]; exact stepB
  · rw [p0]; exact stepA
  · intro i hi
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hi
    · left; rw [m1']; exact stepA
    · left; rw [m2']; exact stepT2
    · left; rw [m3']; exact stepT3
    · right; rw [p4]; exact stepB
  · intro l hl
    rw [hLd] at hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · left; simp only; linarith [hDd, hι0]
    · left; simp only; linarith [hDd, hι0]

end C2
end Type08Sp
end Minimality
