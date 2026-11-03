module

public import Minimality.Type08S.C2K46TRA
public import Minimality.Type08S.C2K46LB
public import Minimality.Type08S.C2K46CB
public import Minimality.Type08S.C2K46CpB
public import Minimality.Type08S.C2K46UB

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
open scoped RealInnerProductSpace
open Minimality Minimality.Type08Sp Minimality.Type08Sp.C2

namespace Minimality.Type08Sp.C2


theorem a2mc_all {σ l m ea : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hm : 0 < m)
    (hea : ea = l^2*σ^2/(2*(1+σ^2))) (hR1 : ea ≤ σ^2 * (2 + ea)) (hR2 : ea * σ^2 < 2 + ea) :
    IsRupert (V8 (m • Minimality.pt (2+ea) 0 0) (m • Minimality.pt (-ea*(2+ea)) (l*(2+ea)/2) (l*σ*(2+ea)/2))
      (m • Minimality.pt (-ea) l 0) (m • Minimality.pt (2+ea) 0 (l*σ*(2+ea))) (m • Minimality.pt (-ea) 0 (l*σ))
      (m • Minimality.pt (2+ea) (l*(2+ea)) 0) (m • Minimality.pt 0 0 0)) := by
  by_cases h1 : σ^2 ≤ 2/9
  · exact a2mc_L hσ hl hm hea hR1 hR2 (by linarith)
  by_cases h2 : σ^2 ≤ 3/2
  · exact a2mc_C hσ hl hm hea hR1 hR2 (by linarith) (by linarith)
  by_cases h3 : σ^2 < 9/2
  · exact a2mc_Cp hσ hl hm hea hR1 hR2 (by linarith) (by linarith)
  · exact a2mc_U hσ hl hm hea hR1 hR2 (by linarith)

theorem k55_pt_congr {a b c a' b' c' : ℝ} (h1 : a = a') (h2 : b = b') (h3 : c = c') :
    Minimality.pt a b c = Minimality.pt a' b' c' := by subst h1 h2 h3; rfl

theorem k55_smul_pt (m x y z : ℝ) : m • Minimality.pt x y z = Minimality.pt (m*x) (m*y) (m*z) := by
  ext i; fin_cases i <;> simp [Minimality.pt]

def K55G (p q r : ℝ³) (ea m kk rr : ℝ) : Prop :=
  ⟪p,p⟫ = (2+ea)^2*(m*m) ∧ ⟪p,q⟫ = -(ea*(2+ea)*(m*m)) ∧ ⟪p,r⟫ = -(ea*(2+ea)*(m*m)) ∧
  ⟪q,r⟫ = ea^2*(m*m) ∧ ⟪q,q⟫ = kk*kk + ea^2*(m*m) ∧ ⟪r,r⟫ = rr*rr + ea^2*(m*m)

theorem k55_bil {p q r : ℝ³} {ea m kk rr : ℝ} (G : K55G p q r ea m kk rr) (u v z u' v' z' : ℝ) :
    ⟪u•p+v•q+z•r, u'•p+v'•q+z'•r⟫ =
      u*u'*((2+ea)^2*(m*m)) + (u*v'+v*u')*(-(ea*(2+ea)*(m*m))) + (u*z'+z*u')*(-(ea*(2+ea)*(m*m)))
      + (v*z'+z*v')*(ea^2*(m*m)) + v*v'*(kk*kk + ea^2*(m*m)) + z*z'*(rr*rr + ea^2*(m*m)) := by
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := G
  have hqp : ⟪q,p⟫ = ⟪p,q⟫ := real_inner_comm _ _
  have hrp : ⟪r,p⟫ = ⟪p,r⟫ := real_inner_comm _ _
  have hrq : ⟪r,q⟫ = ⟪q,r⟫ := real_inner_comm _ _
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real, hqp, hrp, hrq, g1, g2, g3, g4, g5, g6]
  ring

noncomputable def k55S (p q r : ℝ³) (ea m : ℝ) : ℝ³ :=
  (1/((2+ea)*m)) • ((1:ℝ)•p+(0:ℝ)•q+(0:ℝ)•r)
noncomputable def k55T (p q r : ℝ³) (ea kk : ℝ) : ℝ³ :=
  (1/((2+ea)*kk)) • (ea•p+(2+ea)•q+(0:ℝ)•r)
noncomputable def k55N (p q r : ℝ³) (ea rr : ℝ) : ℝ³ :=
  (1/((2+ea)*rr)) • (ea•p+(0:ℝ)•q+(2+ea)•r)

theorem k55_isFrame {p q r : ℝ³} {ea m kk rr : ℝ} (G : K55G p q r ea m kk rr)
    (hea : 0 < ea) (hm : 0 < m) (hk : 0 < kk) (hr : 0 < rr) :
    IsFrame (k55S p q r ea m) (k55T p q r ea kk) (k55N p q r ea rr) := by
  have hs : 0 < 2 + ea := by linarith
  unfold IsFrame k55S k55T k55N
  simp only [inner_smul_left, inner_smul_right, RCLike.conj_to_real, k55_bil G]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

theorem k55_phi {p q r : ℝ³} {ea m kk rr : ℝ} (G : K55G p q r ea m kk rr)
    (hea : 0 < ea) (hm : 0 < m) (hk : 0 < kk) (hr : 0 < rr) (u v z : ℝ) :
    (orthoFrameMat (k55S p q r ea m) (k55T p q r ea kk) (k55N p q r ea rr)).toEuclideanLin
      (u•p+v•q+z•r) = Minimality.pt (m*(u*(2+ea)-(v+z)*ea)) (kk*v) (rr*z) := by
  have hs : 0 < 2 + ea := by linarith
  rw [orthoFrameMat_apply]
  unfold k55S k55T k55N
  simp only [inner_smul_left, inner_smul_right, RCLike.conj_to_real, k55_bil G]
  apply k55_pt_congr <;> field_simp <;> ring

theorem k46_tie_rupert {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hβ : 1 < β1) (hσ : β6 + γ6 = β1) (hL : ⟪a - c', a - d⟫ = 0)
    (h : K45SigRest a a' b b' c c' d α1 β1 β6 γ6) : IsRupert (V8 a a' b b' c c' d) := by
  obtain ⟨ea, w, kap, rho, hea, hw, hk, hrho, hα, hβ1e, hβ6e, hγ6e, gpp, gpq, gpr, gqr, gqq, grr,
    hkr, hO, hlit⟩ := k55_chart hC hM hrel hβ hσ hL h
  obtain ⟨hdet, hc', hb', ha', -⟩ := hC
  obtain ⟨m, hm, rfl⟩ : ∃ m, 0 < m ∧ w = m*m :=
    ⟨Real.sqrt w, Real.sqrt_pos.2 hw, (Real.mul_self_sqrt hw.le).symm⟩
  obtain ⟨kk, hkk, rfl⟩ : ∃ m, 0 < m ∧ kap = m*m :=
    ⟨Real.sqrt kap, Real.sqrt_pos.2 hk, (Real.mul_self_sqrt hk.le).symm⟩
  obtain ⟨rr, hrr, rfl⟩ : ∃ m, 0 < m ∧ rho = m*m :=
    ⟨Real.sqrt rho, Real.sqrt_pos.2 hrho, (Real.mul_self_sqrt hrho.le).symm⟩
  subst hα hβ1e hβ6e hγ6e
  have G : K55G (a-d) (b-d) (c-d) ea m kk rr := ⟨gpp, gpq, gpr, gqr, gqq, grr⟩
  have hs : 0 < 2 + ea := by linarith
  have e : ∀ (x : ℝ³) (u v z : ℝ), x - d = u•(a-d)+v•(b-d)+z•(c-d) →
      (orthoFrameMat (k55S (a-d) (b-d) (c-d) ea m) (k55T (a-d) (b-d) (c-d) ea kk)
        (k55N (a-d) (b-d) (c-d) ea rr)).toEuclideanLin (x - d) =
      Minimality.pt (m*(u*(2+ea)-(v+z)*ea)) (kk*v) (rr*z) := by
    intro x u v z hx
    rw [hx]; exact k55_phi G hea hm hkk hrr u v z
  have hsig : 0 < rr / kk := by positivity
  have hl : 0 < kk / m := by positivity
  have hea' : ea = (kk/m)^2*(rr/kk)^2/(2*(1+(rr/kk)^2)) := by
    rw [eq_div_iff (by positivity)]
    field_simp
    nlinarith [hkr]
  have hR1 : ea ≤ (rr/kk)^2 * (2 + ea) := by
    rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [hO]
  have hR2 : ea * (rr/kk)^2 < 2 + ea := by
    have : ea * (rr/kk)^2 = ea * (rr*rr) / (kk*kk) := by field_simp
    rw [this, div_lt_iff₀ (by positivity)]
    nlinarith [hlit]
  have hfin := a2mc_all hsig hl hm hea' hR1 hR2
  refine isRupert_of_frame_image _ (v := d) (k55_isFrame G hea hm hkk hrr) ?_
  simp only [V8, Finset.image_insert, Finset.image_singleton]
  have e2 : ∀ (x : ℝ³) (u v z X Y Z : ℝ), x - d = u•(a-d)+v•(b-d)+z•(c-d) →
      m*(u*(2+ea)-(v+z)*ea) = m*X → kk*v = m*Y → rr*z = m*Z →
      (orthoFrameMat (k55S (a-d) (b-d) (c-d) ea m) (k55T (a-d) (b-d) (c-d) ea kk)
        (k55N (a-d) (b-d) (c-d) ea rr)).toEuclideanLin (x - d) = m • Minimality.pt X Y Z := by
    intro x u v z X Y Z hx h1 h2 h3
    rw [e x u v z hx, k55_smul_pt]
    exact k55_pt_congr h1 h2 h3
  have t : ∀ q : ℝ, q = q := fun _ => rfl
  rw [e2 a 1 0 0 (2+ea) 0 0 (by module) (by ring1) (by ring1) (by ring1),
    e2 a' 0 ((2+ea)/2) ((2+ea)/2) (-ea*(2+ea)) (kk/m*(2+ea)/2) (kk/m*(rr/kk)*(2+ea)/2)
      (by rw [ha']; module) (by ring1) (by field_simp) (by field_simp),
    e2 b 0 1 0 (-ea) (kk/m) 0 (by module) (by ring1) (by field_simp) (by ring1),
    e2 b' (1+ea) 0 (2+ea) (2+ea) 0 (kk/m*(rr/kk)*(2+ea)) (by rw [hb']; module) (by ring1)
      (by ring1) (by field_simp),
    e2 c 0 0 1 (-ea) 0 (kk/m*(rr/kk)) (by module) (by ring1) (by ring1) (by field_simp),
    e2 c' (1+ea) (2+ea) 0 (2+ea) (kk/m*(2+ea)) 0 (by rw [hc']; module) (by ring1)
      (by field_simp) (by ring1),
    e2 d 0 0 0 0 0 0 (by simp) (by ring1) (by ring1) (by ring1)]
  exact hfin

end Minimality.Type08Sp.C2
