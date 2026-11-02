module

public import Minimality.Type08S.C2K16R

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- K17B safe sub-leaf: CCW quad `(a, c', a', b')` in the frame `(q, r, b'-c)`, `a = (0,-κ,ι)`, `κ = (β1-1)/α1`, `ι = 1/α1`. -/
def k17bCyc (κ ι β1 β6 γ6 : ℝ) : ZMod 4 → ℝ × ℝ × ℝ :=
  ![(0, -κ, ι), (β1, -(β1 - 1), 1), (β6, γ6, 0), (0, 1, 1)]

theorem k17bCyc_0 : k17bCyc κ ι β1 β6 γ6 0 = (0, -κ, ι) := rfl
theorem k17bCyc_1 : k17bCyc κ ι β1 β6 γ6 1 = (β1, -(β1 - 1), 1) := rfl
theorem k17bCyc_2 : k17bCyc κ ι β1 β6 γ6 2 = (β6, γ6, 0) := rfl
theorem k17bCyc_3 : k17bCyc κ ι β1 β6 γ6 3 = (0, 1, 1) := rfl

theorem k17b_inj {κ ι β1 β6 γ6 : ℝ} (hκ : 0 < κ) (hβ1 : 1 < β1) (hb6 : 0 < β6) :
    ∀ i j : ZMod 4, k17bCyc κ ι β1 β6 γ6 i = k17bCyc κ ι β1 β6 γ6 j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  have e3 := congrArg (fun t => t.2.2) h
  rcases z4_cases i with rfl | rfl | rfl | rfl <;> rcases z4_cases j with rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [k17bCyc_0, k17bCyc_1, k17bCyc_2, k17bCyc_3] at e1 e2 e3; linarith)

set_option maxHeartbeats 3200000 in
theorem k17b_tsc {κ ι β1 β6 γ6 v1 v2 : ℝ} (hκ : 0 < κ) (hκε : κ < β1 - 1) (hι : 0 < ι) (hβ1 : 1 < β1)
    (hb6 : 0 < β6) (hγ6 : 1 < γ6) (hv1 : 0 < v1) (hcone : β6 * v2 < (γ6 - 1) * v1) :
    (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      TSc 1 (k17bCyc κ ι β1 β6 γ6 (i + 1) - k17bCyc κ ι β1 β6 γ6 i)
        (k17bCyc κ ι β1 β6 γ6 j - k17bCyc κ ι β1 β6 γ6 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 1, 0), (0, 0, 0)], ∀ i : ZMod 4,
      TSc 1 (k17bCyc κ ι β1 β6 γ6 (i + 1) - k17bCyc κ ι β1 β6 γ6 i)
        (t - k17bCyc κ ι β1 β6 γ6 i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3⟩ := z4_add
  have e1 : 0 < β1 - 1 := by linarith
  have e2 : 0 < (β1 - 1) - κ := by linarith
  have g1 : 0 < γ6 - 1 := by linarith
  have s1 : 0 < β6 + γ6 - 1 := by linarith
  have p1 := mul_pos hκ e1
  have p2 := mul_pos hκ hb6
  have p3 := mul_pos e1 hb6
  have p4 := mul_pos e2 hb6
  have p5 := mul_pos hκ (by linarith : (0:ℝ) < β1)
  have p6 := mul_pos (by linarith : (0:ℝ) < β1) g1
  have p7 := mul_pos (by linarith : (0:ℝ) < β1) hb6
  have p8 := mul_pos hb6 s1
  have p9 := mul_pos (by linarith : (0:ℝ) < β1) s1
  have p10 := mul_pos e1 g1
  have p11 := mul_pos e1 s1
  have p12 := mul_pos hb6 g1
  have p13 := mul_pos hκ hv1
  have p14 := mul_pos hι hv1
  have p15 := mul_pos e1 hv1
  have p16 := mul_pos hb6 hv1
  have p17 := mul_pos e2 hv1
  have p18 := mul_pos hκ g1
  have p19 := mul_pos e2 (by linarith : (0:ℝ) < β1)
  have p20 := mul_pos hκ e2
  have p21 := mul_pos (add_pos hκ hι) hv1
  have p22 := mul_pos (sub_pos.2 hcone) hb6
  constructor
  · intro i j h1 h2
    rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      rcases z4_cases j with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k17bCyc_0, k17bCyc_1, k17bCyc_2, k17bCyc_3, f0, f1, f2, f3,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;>
      rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k17bCyc_0, k17bCyc_1, k17bCyc_2, k17bCyc_3, f0, f1, f2, f3,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))


/-- Quad `(b', a, c', a')`-type unimodality, in the two rotations used by the safe sub-leaf. -/
theorem k17b_quad_uni (z w : ZMod 4 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (hab : z 0 < z 3) (hcb : z 1 < z 3) (hs : z 1 < z 0 ∨ z 1 < z 2) : LexUni z w := by
  by_cases h : z 1 < z 2
  · -- rotation by one: `(c', a', b', a)`
    refine lexUni_unshift1 ?_
    refine k6m_quad_uni _ _ ?_ ?_ ?_
    · intro i j h1 h2; exact (add_left_injective (1 : ZMod 4)) (hinj _ _ h1 h2)
    · simpa [show (1 : ZMod 4) + 1 = 2 by decide] using h
    · simpa [show (3 : ZMod 4) + 1 = 0 by decide, show (2 : ZMod 4) + 1 = 3 by decide] using hab
  · -- `a' ≤ c' < a < b'`: rotation by two: `(a', b', a, c')`
    have hca : z 1 < z 0 := hs.resolve_right h
    have h23 : z 2 < z 3 := by linarith [not_lt.1 h]
    refine lexUni_unshift1 (lexUni_unshift1 ?_)
    refine k6m_quad_uni _ _ ?_ ?_ ?_
    · intro i j h1 h2; exact (add_left_injective (1 : ZMod 4)) ((add_left_injective (1 : ZMod 4)) (hinj _ _ (by simpa [add_assoc] using h1) (by simpa [add_assoc] using h2)))
    · simpa [add_assoc, show (1 : ZMod 4) + 1 = 2 by decide, show (2 : ZMod 4) + 1 = 3 by decide, show (0 : ZMod 4) + 1 + 1 = 2 by decide] using h23
    · simpa [add_assoc, show (1 : ZMod 4) + 1 = 2 by decide, show (3 : ZMod 4) + 2 = 1 by decide, show (2 : ZMod 4) + 2 = 0 by decide] using hca


set_option maxHeartbeats 3200000 in
theorem k17b_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {κ ι β1 β6 γ6 : ℝ}
    (hκ : 0 < κ) (hκε : κ < β1 - 1) (hι : 0 < ι) (hβ1 : 1 < β1) (hb6 : 0 < β6) (hγ6 : 1 < γ6)
    (hmem : ∀ i, fpoint P Q R d (k17bCyc κ ι β1 β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, -κ, ι) ∨ y = fpoint P Q R d (β1, -(β1 - 1), 1) ∨
      y = fpoint P Q R d (β6, γ6, 0) ∨ y = fpoint P Q R d (0, 1, 1) ∨ y = fpoint P Q R d (1, 0, 0) ∨
      y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, 0))
    (hab : ⟪fpoint P Q R d (0, -κ, ι), R⟫ < ⟪fpoint P Q R d (0, 1, 1), R⟫)
    (hcb : ⟪fpoint P Q R d (β1, -(β1 - 1), 1), R⟫ < ⟪fpoint P Q R d (0, 1, 1), R⟫)
    (hs : ⟪fpoint P Q R d (β1, -(β1 - 1), 1), R⟫ < ⟪fpoint P Q R d (0, -κ, ι), R⟫ ∨
      ⟪fpoint P Q R d (β1, -(β1 - 1), 1), R⟫ < ⟪fpoint P Q R d (β6, γ6, 0), R⟫) :
    HasLexCellAt V R := by
  refine cyc_cell V P Q R d hΔ (k := 4) (by norm_num) (k17bCyc κ ι β1 β6 γ6)
    (k17b_inj hκ hβ1 hb6) hmem [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 1, 0), (0, 0, 0)] ?_
    (u1 := 1) (u2 := 0) (t1 := 0) (t2 := -1) (lo := 0) (hi := 1) (by norm_num) (by norm_num)
    (fun v1 v2 => 0 < v1 ∧ β6 * v2 < (γ6 - 1) * v1) ?_ ?_ ?_
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inl ⟨3, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam h0 h1
    refine ⟨by simp, ?_⟩
    simp only [mul_zero, add_zero, zero_add, mul_one, mul_neg]
    nlinarith [mul_pos hb6 h0]
  · intro v1 v2 ⟨hv1, hc⟩
    exact k17b_tsc hκ hκε hι hβ1 hb6 hγ6 hv1 hc
  · intro v1 v2 ⟨hv1, hc⟩ hL
    refine k17b_quad_uni _ _ hL ?_ ?_ ?_
    · simpa only [k17bCyc_0, k17bCyc_3] using hab
    · simpa only [k17bCyc_1, k17bCyc_3] using hcb
    · simpa only [k17bCyc_0, k17bCyc_1, k17bCyc_2] using hs

theorem k17b_psd (p q r : ℝ³) (m : ℝ) (h1 : ⟪p, q⟫ = m) (h2 : ⟪p, r⟫ = m)
    (hdet : 0 < ⟪q, q⟫ * ⟪r, r⟫ - ⟪q, r⟫ ^ 2) :
    m ^ 2 * (⟪q, q⟫ + ⟪r, r⟫ - 2 * ⟪q, r⟫) ≤ ⟪p, p⟫ * (⟪q, q⟫ * ⟪r, r⟫ - ⟪q, r⟫ ^ 2) := by
  set D := ⟪q, q⟫ * ⟪r, r⟫ - ⟪q, r⟫ ^ 2 with hD
  have hw := real_inner_self_nonneg (x := D • p + (-(m * (⟪r, r⟫ - ⟪q, r⟫))) • q + (-(m * (⟪q, q⟫ - ⟪q, r⟫))) • r)
  rw [k6m_ip] at hw
  have e1 : ⟪p, q⟫ = ⟪q, p⟫ := real_inner_comm _ _
  have e2 : ⟪p, r⟫ = ⟪r, p⟫ := real_inner_comm _ _
  rw [h1, h2] at hw
  have : 0 ≤ D * (D * ⟪p, p⟫ - m ^ 2 * (⟪q, q⟫ + ⟪r, r⟫ - 2 * ⟪q, r⟫)) := by
    rw [hD] at hw ⊢; nlinarith [hw]
  have := (mul_nonneg_iff_of_pos_left hdet).1 this
  linarith


theorem k17b_balg {α ε pp m qq qr rr : ℝ} (hα : 1 < α) (hε : 0 < ε) (hdet : 0 < qq * rr - qr ^ 2)
    (hW : 0 < qq + rr - 2 * qr) (hP : m ^ 2 * (qq + rr - 2 * qr) ≤ pp * (qq * rr - qr ^ 2))
    (hc : α * m * (qq + rr - 2 * qr) = -ε * (qq * rr - qr ^ 2)) (hrq : qr < rr) :
    0 < α * (α - 1) * pp + ((α - 1) * ε + α * (1 + ε)) * m + (1 + ε) * ε * rr := by
  set D := qq * rr - qr ^ 2 with hD
  set W := qq + rr - 2 * qr with hWd
  have e : (α * (α - 1) * pp + ((α - 1) * ε + α * (1 + ε)) * m + (1 + ε) * ε * rr) * D * W =
      (1 + ε) * ε * D * (rr - qr) ^ 2 + α * (α - 1) * W * (pp * D - m ^ 2 * W) := by
    have hDW : D = qq * rr - qr ^ 2 := hD
    have hWW : W = qq + rr - 2 * qr := hWd
    rw [hDW, hWW] at hc ⊢
    linear_combination ((α - 1) * m * (qq + rr - 2 * qr) + (1 + ε) * (qq * rr - qr ^ 2)) * hc
  have h1 : 0 < (1 + ε) * ε * D * (rr - qr) ^ 2 := by
    have : 0 < rr - qr := by linarith
    positivity
  have h2 : 0 ≤ α * (α - 1) * W * (pp * D - m ^ 2 * W) :=
    mul_nonneg (by have : 0 < α - 1 := by linarith
                   positivity) (by linarith)
  have h3 : 0 < (α * (α - 1) * pp + ((α - 1) * ε + α * (1 + ε)) * m + (1 + ε) * ε * rr) * D * W := by
    rw [e]; linarith
  have hDW : 0 < D * W := mul_pos hdet hW
  have : 0 < (α * (α - 1) * pp + ((α - 1) * ε + α * (1 + ε)) * m + (1 + ε) * ε * rr) * (D * W) := by
    linarith [h3, mul_assoc (α * (α - 1) * pp + ((α - 1) * ε + α * (1 + ε)) * m + (1 + ε) * ε * rr) D W]
  exact (mul_pos_iff_of_pos_right hDW).1 this


theorem k17b_balg' {α β1 pp m qq qr rr : ℝ} (hα : 1 < α) (hβ1 : 1 < β1) (hdet : 0 < qq * rr - qr ^ 2)
    (hW : 0 < qq + rr - 2 * qr) (hP : m ^ 2 * (qq + rr - 2 * qr) ≤ pp * (qq * rr - qr ^ 2))
    (hc : α * m * (qq + rr - 2 * qr) = -(β1 - 1) * (qq * rr - qr ^ 2)) (hrq : qr < rr) :
    0 < α * (α - 1) * pp + ((α - 1) * (β1 - 1) + α * β1) * m + β1 * (β1 - 1) * rr := by
  have := k17b_balg (ε := β1 - 1) hα (by linarith) hdet hW hP hc hrq
  have e : (1 : ℝ) + (β1 - 1) = β1 := by ring
  rw [e] at this
  exact this

set_option maxHeartbeats 6400000 in
/-- **K17B safe sub-leaf of L2** (`ζ_{b'-c}(c', a) < 0 ∨ ζ_{b'-c}(c', a') < 0`): the quad `(a, b', a', c')` at `b' - c`. -/
theorem k17b_safe {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 1 < β6) (hγ6 : 1 < γ6)
    (hM : K6sM a a' b b' c c' d) (hrel : K16Rel a b c d α1 β1)
    (hsafe : ⟪c' - a, b' - c⟫ < 0 ∨ ⟪c' - a', b' - c⟫ < 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨m1, m2, m3⟩ := hM
  obtain ⟨hr1, hr2⟩ := hrel
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  set Rv := b' - c with hRvdef
  have hRv : Rv = α1 • p + (β1 - 1) • r := by rw [hRvdef, hb', hp, hr]; module
  have hα0 : α1 ≠ 0 := by intro h; linarith
  have hΔ : det3 q r Rv ≠ 0 := by
    have e : det3 q r Rv = α1 * det3 (a - d) (b - d) (c - d) := by
      rw [hRv]
      simp only [hp, hq, hr, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e]; exact mul_ne_zero hα0 hdet
  have hm1 : ⟪p, q⟫ = ⟪p, r⟫ := by
    have : ⟪p, b - c⟫ = ⟪p, q⟫ - ⟪p, r⟫ := by
      rw [← inner_sub_right]; congr 1; rw [hq, hr]; abel
    linarith
  have hqr : ⟪q, r⟫ = ⟪r, q⟫ := real_inner_comm _ _
  have hpr : ⟪r, p⟫ = ⟪p, r⟫ := real_inner_comm _ _
  have hqp : ⟪q, p⟫ = ⟪p, q⟫ := real_inner_comm _ _
  have hRT : ⟪q, r⟫ < ⟪r, r⟫ := by
    have e : b' - d = α1 • p + β1 • r := by rw [hb', hp, hr]; module
    have e2 : b - c = q - r := by rw [hq, hr]; abel
    rw [e, e2] at m3
    simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real, inner_sub_right] at m3
    have h0 : α1 * (⟪p, q⟫ - ⟪p, r⟫) = 0 := by rw [hm1]; ring
    nlinarith [m3, h0, hqp, hpr]
  have hQR : ⟪q, r⟫ < ⟪q, q⟫ := by
    have e : c' - d = α1 • p + β1 • q := by rw [hc', hp, hq]; module
    have e2 : b - c = q - r := by rw [hq, hr]; abel
    rw [e, e2] at m2
    simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real, inner_sub_right] at m2
    have h0 : α1 * (⟪p, q⟫ - ⟪p, r⟫) = 0 := by rw [hm1]; ring
    nlinarith [m2, h0, hqp, hpr]
  have hW : 0 < ⟪q, q⟫ + ⟪r, r⟫ - 2 * ⟪q, r⟫ := by linarith
  have hP := k17b_psd p q r ⟪p, q⟫ rfl hm1.symm hr2
  have hc : α1 * ⟪p, q⟫ * (⟪q, q⟫ + ⟪r, r⟫ - 2 * ⟪q, r⟫) = -(β1 - 1) * (⟪q, q⟫ * ⟪r, r⟫ - ⟪q, r⟫ ^ 2) := hr1
  have hBA := k17b_balg' hα1 hβ1 hr2 hW hP hc hRT
  -- depth facts
  have gR : ∀ x y z : ℝ, ⟪x • p + y • q + z • r, Rv⟫ =
      x * (α1 * ⟪p, p⟫ + (β1 - 1) * ⟪p, r⟫) + y * (α1 * ⟪p, q⟫ + (β1 - 1) * ⟪q, r⟫) +
        z * (α1 * ⟪p, r⟫ + (β1 - 1) * ⟪r, r⟫) := by
    intro x y z
    have e : Rv = α1 • p + (0:ℝ) • q + (β1 - 1) • r := by rw [hRv]; module
    rw [e, k6m_ip]
    ring
  set κ : ℝ := (β1 - 1) / α1 with hκdef
  set ι : ℝ := 1 / α1 with hιdef
  have hα1p : 0 < α1 := by linarith
  have hκ : 0 < κ := div_pos (by linarith) hα1p
  have hι : 0 < ι := div_pos one_pos hα1p
  have hκε : κ < β1 - 1 := by
    rw [hκdef, div_lt_iff₀ hα1p]; nlinarith
  have hpa : a = d + p := by rw [hp]; abel
  have eO : fpoint q r Rv d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eB : fpoint q r Rv d (1, 0, 0) = b := by simp only [fpoint, fcomb, hq]; module
  have eC : fpoint q r Rv d (0, 1, 0) = c := by simp only [fpoint, fcomb, hr]; module
  have eB' : fpoint q r Rv d (0, 1, 1) = b' := by
    simp only [fpoint, fcomb, hRvdef]; module
  have eA' : fpoint q r Rv d (β6, γ6, 0) = a' := by rw [ha']; simp only [fpoint, fcomb, hq, hr]; module
  have eA : fpoint q r Rv d (0, -κ, ι) = a := by
    rw [hpa]; simp only [fpoint, fcomb]; rw [hRv]
    match_scalars <;> (try simp only [hκdef, hιdef]) <;> field_simp <;> ring
  have eC' : fpoint q r Rv d (β1, -(β1 - 1), 1) = c' := by
    rw [hc']; simp only [fpoint, fcomb]; rw [hRv, hp, hq]; module
  have e1 : b' - a = (α1 - 1) • p + (0:ℝ) • q + β1 • r := by rw [hb', hp, hr]; module
  have e2 : b' - c' = (0:ℝ) • p + (-β1) • q + β1 • r := by rw [hb', hc', hp, hq, hr]; module
  have inner_lt : ∀ X Y : ℝ³, 0 < ⟪Y - X, Rv⟫ → ⟪X, Rv⟫ < ⟪Y, Rv⟫ := by
    intro X Y h; rw [inner_sub_left] at h; linarith
  have hsp : ⟪p, r⟫ = ⟪p, q⟫ := hm1.symm
  have hab : ⟪a, Rv⟫ < ⟪b', Rv⟫ := by
    apply inner_lt; rw [e1, gR]; rw [hsp] at *; nlinarith [hBA]
  have hcb : ⟪c', Rv⟫ < ⟪b', Rv⟫ := by
    apply inner_lt; rw [e2, gR, hsp]
    nlinarith [mul_pos (mul_pos (by linarith : (0:ℝ) < β1) (by linarith : (0:ℝ) < β1 - 1)) (sub_pos.2 hRT), hqr]
  have hs : ⟪c', Rv⟫ < ⟪a, Rv⟫ ∨ ⟪c', Rv⟫ < ⟪a', Rv⟫ := by
    rcases hsafe with h | h
    · left; rw [inner_sub_left] at h; linarith
    · right; rw [inner_sub_left] at h; linarith
  have hb6' : 0 < β6 := by linarith
  refine ⟨Rv, ?_, ?_⟩
  · intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  refine k17b_frame (V8 a a' b b' c c' d) q r Rv d hΔ hκ hκε hι hβ1 hb6' hγ6 ?_ ?_ ?_ ?_ ?_
  · intro i
    rcases z4_cases i with rfl | rfl | rfl | rfl
    · simp only [k17bCyc_0, eA]; simp [V8]
    · simp only [k17bCyc_1, eC']; simp [V8]
    · simp only [k17bCyc_2, eA']; simp [V8]
    · simp only [k17bCyc_3, eB']; simp [V8]
  · intro y hy
    rw [eA, eC', eA', eB', eB, eC, eO]
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  · rw [eA, eB']; exact hab
  · rw [eC', eB']; exact hcb
  · rw [eC', eA, eA']; exact hs

theorem k17b_pent_uni (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h01 : z 0 < z 1) (h12 : z 1 < z 2) (h23 : z 2 < z 3) (h43 : z 4 < z 3) : LexUni z w := by
  obtain ⟨M, hM⟩ := exists_key z w hinj
  refine lexUni_of_key z w (fun i => M * z i + w i) hinj hM ?_
  have lt : ∀ i j, z i < z j → M * z i + w i < M * z j + w j := fun i j h => (hM i j).1 (Or.inl h)
  have hk := k6m_key_inj z w hinj M hM
  refine k5d_uni_of_nopair (by decide) _ hk ?_
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_sub1
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have k01 := lt _ _ h01
  have k12 := lt _ _ h12
  have k23 := lt _ _ h23
  have k43 := lt _ _ h43
  intro i j h1 h2 h3 ⟨⟨pi1, pi2⟩, ⟨pj1, pj2⟩⟩
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact h1 rfl
    | exact h2 (by decide)
    | exact h3 (by decide)
    | (simp only [s0, s1, s2, s3, s4, f0, f1, f2, f3, f4] at pi1 pi2 pj1 pj2
       linarith)


/-- K17B arc rule cell: CCW pentagon `(d, b, a', b', a)` in the frame `(q, r, u)`, `a = (x, 0, w)`. -/
def k17bCyc2 (x w α1 β1 β6 γ6 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  ![(0, 0, 0), (1, 0, 0), (β6, γ6, 0), (α1 * x, β1, α1 * w), (x, 0, w)]

theorem k17bCyc2_0 : k17bCyc2 x w α1 β1 β6 γ6 0 = (0, 0, 0) := rfl
theorem k17bCyc2_1 : k17bCyc2 x w α1 β1 β6 γ6 1 = (1, 0, 0) := rfl
theorem k17bCyc2_2 : k17bCyc2 x w α1 β1 β6 γ6 2 = (β6, γ6, 0) := rfl
theorem k17bCyc2_3 : k17bCyc2 x w α1 β1 β6 γ6 3 = (α1 * x, β1, α1 * w) := rfl
theorem k17bCyc2_4 : k17bCyc2 x w α1 β1 β6 γ6 4 = (x, 0, w) := rfl

theorem k17b2_inj {x w α1 β1 β6 γ6 : ℝ} (hα : 0 < α1) (hx : x < 0) (hβ1 : 0 < β1) (hb6 : 0 < β6) (hγ6 : 0 < γ6) :
    ∀ i j : ZMod 5, k17bCyc2 x w α1 β1 β6 γ6 i = k17bCyc2 x w α1 β1 β6 γ6 j → i = j := by
  intro i j h
  have hax := mul_neg_of_pos_of_neg hα hx
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  have e3 := congrArg (fun t => t.2.2) h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [k17bCyc2_0, k17bCyc2_1, k17bCyc2_2, k17bCyc2_3, k17bCyc2_4] at e1 e2 e3; linarith)

set_option maxHeartbeats 6400000 in
theorem k17b2_tsc {x w α1 β1 β6 γ6 v1 v2 : ℝ} (hx : x < 0) (hw : 0 < w) (hα1 : 1 < α1) (hβ1 : 1 < β1)
    (hb6 : 1 < β6) (hγ6 : 1 < γ6) (hσ : β1 < β6 + γ6) (hL3 : α1 * x + β1 < 1) (hc1 : 0 < (α1 - 1) * x + β1)
    (hv2 : v2 < 0) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k17bCyc2 x w α1 β1 β6 γ6 (i + 1) - k17bCyc2 x w α1 β1 β6 γ6 i)
        (k17bCyc2 x w α1 β1 β6 γ6 j - k17bCyc2 x w α1 β1 β6 γ6 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (1 : ℝ), (0 : ℝ)), (α1 * x + β1, 0, α1 * w)], ∀ i : ZMod 5,
      TSc 1 (k17bCyc2 x w α1 β1 β6 γ6 (i + 1) - k17bCyc2 x w α1 β1 β6 γ6 i)
        (t - k17bCyc2 x w α1 β1 β6 γ6 i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have nx : 0 < -x := by linarith
  have a1 : 0 < α1 - 1 := by linarith
  have b1 : 0 < β1 - 1 := by linarith
  have b6 : 0 < β6 - 1 := by linarith
  have g1 : 0 < γ6 - 1 := by linarith
  have sg : 0 < β6 + γ6 - β1 := by linarith
  have l3 : 0 < 1 - α1 * x - β1 := by linarith
  have nv : 0 < -v2 := by linarith
  have q1 := mul_pos nx a1
  have q2 := mul_pos nx g1
  have q3 := mul_pos (mul_pos nx a1) g1
  have q4 := mul_pos (by linarith : (0:ℝ) < α1) nx
  have q5 := mul_pos (mul_pos (by linarith : (0:ℝ) < α1) nx) g1
  have q6 := mul_pos (by linarith : (0:ℝ) < β1) b6
  have q7 := mul_pos (by linarith : (0:ℝ) < β1) sg
  have q8 := mul_pos (by linarith : (0:ℝ) < β1) (by linarith : (0:ℝ) < β1)
  have q9 := mul_pos (by linarith : (0:ℝ) < β1) hc1
  have q10 := mul_pos (by linarith : (0:ℝ) < β1) l3
  have q11 := mul_pos g1 l3
  have q12 := mul_pos (by linarith : (0:ℝ) < α1) nx
  have q13 := mul_pos hw nv
  have q14 := mul_pos (mul_pos hw nv) (by linarith : (0:ℝ) < α1)
  have q15 := mul_pos (mul_pos hw nv) (by linarith : (0:ℝ) < β1)
  have q16 := mul_pos (mul_pos hw nv) nx
  have q17 := mul_pos (mul_pos hw nv) hc1
  have q18 := mul_pos (mul_pos hw nv) l3
  have q19 := mul_pos (mul_pos hw nv) (by linarith : (0:ℝ) < α1 - 1)
  have q20 := mul_pos (mul_pos nx a1) b1
  have q21 := mul_pos nx b1
  have q22 := mul_pos (mul_pos nx a1) (by linarith : (0:ℝ) < β1)
  have q23 := mul_pos (mul_pos nx (by linarith : (0:ℝ) < α1)) (by linarith : (0:ℝ) < β1)
  have q24 := mul_pos (mul_pos nx (by linarith : (0:ℝ) < α1)) b6
  have q25 := mul_pos sg nx
  have q26 := mul_pos (mul_pos (by linarith : (0:ℝ) < β1) b6) g1
  constructor
  · intro i j h1 h2
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k17bCyc2_0, k17bCyc2_1, k17bCyc2_2, k17bCyc2_3, k17bCyc2_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k17bCyc2_0, k17bCyc2_1, k17bCyc2_2, k17bCyc2_3, k17bCyc2_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))


set_option maxHeartbeats 3200000 in
theorem k17b2_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {x w α1 β1 β6 γ6 : ℝ}
    (hx : x < 0) (hw : 0 < w) (hα1 : 1 < α1) (hβ1 : 1 < β1) (hb6 : 1 < β6) (hγ6 : 1 < γ6) (hσ : β1 < β6 + γ6)
    (hL3 : α1 * x + β1 < 1) (hc1 : 0 < (α1 - 1) * x + β1)
    (hmem : ∀ i, fpoint P Q R d (k17bCyc2 x w α1 β1 β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
      y = fpoint P Q R d (β6, γ6, 0) ∨ y = fpoint P Q R d (α1 * x, β1, α1 * w) ∨ y = fpoint P Q R d (x, 0, w) ∨
      y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (α1 * x + β1, 0, α1 * w))
    (h01 : ⟪fpoint P Q R d (0, 0, 0), R⟫ < ⟪fpoint P Q R d (1, 0, 0), R⟫)
    (h12 : ⟪fpoint P Q R d (1, 0, 0), R⟫ < ⟪fpoint P Q R d (β6, γ6, 0), R⟫)
    (h23 : ⟪fpoint P Q R d (β6, γ6, 0), R⟫ < ⟪fpoint P Q R d (α1 * x, β1, α1 * w), R⟫)
    (h43 : ⟪fpoint P Q R d (x, 0, w), R⟫ < ⟪fpoint P Q R d (α1 * x, β1, α1 * w), R⟫) :
    HasLexCellAt V R := by
  refine cyc_cell V P Q R d hΔ (k := 5) (by norm_num) (k17bCyc2 x w α1 β1 β6 γ6)
    (k17b2_inj (by linarith) hx (by linarith) (by linarith) (by linarith)) hmem
    [((0 : ℝ), (1 : ℝ), (0 : ℝ)), (α1 * x + β1, 0, α1 * w)] ?_
    (u1 := 0) (u2 := -1) (t1 := 1) (t2 := 0) (lo := 0) (hi := 1) (by norm_num) (by norm_num)
    (fun v1 v2 => v2 < 0) ?_ ?_ ?_
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inl ⟨3, rfl⟩
    · exact Or.inl ⟨4, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam h0 h1
    simp
  · intro v1 v2 hv2
    exact k17b2_tsc hx hw hα1 hβ1 hb6 hγ6 hσ hL3 hc1 hv2
  · intro v1 v2 hv2 hL
    refine k17b_pent_uni _ _ hL ?_ ?_ ?_ ?_
    · simpa only [k17bCyc2_0, k17bCyc2_1] using h01
    · simpa only [k17bCyc2_1, k17bCyc2_2] using h12
    · simpa only [k17bCyc2_2, k17bCyc2_3] using h23
    · simpa only [k17bCyc2_4, k17bCyc2_3] using h43


set_option maxHeartbeats 6400000 in
/-- **K17B arc rule S2.2** (view `u = A (a-d) - B (b-d)`, `A > 0`; the witness view `u_b*` of K15 is the instance
`A = |⟪N,b-d⟫|, B = sign · ⟪N,a-d⟫`, `N = b + b' - 2a'`, with `hE` automatic).  Cell `(a,d,b,a',b')`. -/
theorem k17b_S22 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 A B : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 1 < β6) (hγ6 : 1 < γ6) (hσ : β1 < β6 + γ6) (hA : 0 < A)
    (hE : ⟪(b - a') + (b' - a'), A • (a - d) - B • (b - d)⟫ = 0)
    (hL1 : 0 < ⟪a' - b, A • (a - d) - B • (b - d)⟫) (hL2 : 0 < ⟪b' - a, A • (a - d) - B • (b - d)⟫)
    (hL3 : 0 < det3 (a - d) (b - d) (c - d) * det3 (a' - b) (c' - b) (A • (a - d) - B • (b - d)))
    (hB : B < 0) (hc1 : 0 < (α1 - 1) * B + β1 * A) (hZ : 0 < ⟪b - d, A • (a - d) - B • (b - d)⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  set u := A • p - B • q with hu
  have hA0 : A ≠ 0 := hA.ne'
  have hΔ : det3 q r u ≠ 0 := by
    have e : det3 q r u = A * det3 (a - d) (b - d) (c - d) := by
      rw [hu]
      simp only [hp, hq, hr, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e]; exact mul_ne_zero hA0 hdet
  have hdetL : det3 (a' - b) (c' - b) u =
      -γ6 * (α1 * B + (β1 - 1) * A) * det3 (a - d) (b - d) (c - d) := by
    rw [hu, ha', hc']
    simp only [hp, hq, hr, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hD2 : 0 < det3 (a - d) (b - d) (c - d) ^ 2 := by positivity
  have hL3' : α1 * B + (β1 - 1) * A < 0 := by
    rw [hdetL] at hL3
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ γ6) hh) hD2.le]
  set x : ℝ := B / A with hxdef
  set w : ℝ := 1 / A with hwdef
  have hx : x < 0 := div_neg_of_neg_of_pos hB hA
  have hw : 0 < w := div_pos one_pos hA
  have hL3x : α1 * x + β1 < 1 := by
    rw [hxdef]
    have : (α1 * B + (β1 - 1) * A) / A < 0 := div_neg_of_neg_of_pos hL3' hA
    have e : (α1 * B + (β1 - 1) * A) / A = α1 * (B / A) + β1 - 1 := by field_simp; ring
    linarith
  have hc1x : 0 < (α1 - 1) * x + β1 := by
    rw [hxdef]
    have : 0 < ((α1 - 1) * B + β1 * A) / A := div_pos hc1 hA
    have e : ((α1 - 1) * B + β1 * A) / A = (α1 - 1) * (B / A) + β1 := by field_simp
    linarith
  have hpa : a = d + p := by rw [hp]; abel
  have eO : fpoint q r u d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eB : fpoint q r u d (1, 0, 0) = b := by simp only [fpoint, fcomb, hq]; module
  have eC : fpoint q r u d (0, 1, 0) = c := by simp only [fpoint, fcomb, hr]; module
  have eA' : fpoint q r u d (β6, γ6, 0) = a' := by rw [ha']; simp only [fpoint, fcomb, hq, hr]; module
  have eA : fpoint q r u d (x, 0, w) = a := by
    rw [hpa]; simp only [fpoint, fcomb]; rw [hu]
    match_scalars <;> (try simp only [hxdef, hwdef]) <;> field_simp <;> ring
  have eB' : fpoint q r u d (α1 * x, β1, α1 * w) = b' := by
    rw [hb']; simp only [fpoint, fcomb]; rw [hu, hp, hr]
    match_scalars <;> (try simp only [hxdef, hwdef]) <;> field_simp <;> ring
  have eC' : fpoint q r u d (α1 * x + β1, 0, α1 * w) = c' := by
    rw [hc']; simp only [fpoint, fcomb]; rw [hu, hp, hq]
    match_scalars <;> (try simp only [hxdef, hwdef]) <;> field_simp <;> ring
  have inner_lt : ∀ X Y : ℝ³, 0 < ⟪Y - X, u⟫ → ⟪X, u⟫ < ⟪Y, u⟫ := by
    intro X Y h; rw [inner_sub_left] at h; linarith
  have h01 : ⟪d, u⟫ < ⟪b, u⟫ := inner_lt _ _ hZ
  have h12 : ⟪b, u⟫ < ⟪a', u⟫ := by
    apply inner_lt; rw [inner_sub_left] at hL1 ⊢; linarith
  have h23 : ⟪a', u⟫ < ⟪b', u⟫ := by
    rw [inner_add_left, inner_sub_left, inner_sub_left] at hE
    rw [inner_sub_left] at hL1
    linarith
  have h43 : ⟪a, u⟫ < ⟪b', u⟫ := by
    apply inner_lt; exact hL2
  have hb6' : 0 < β6 := by linarith
  refine ⟨u, ?_, ?_⟩
  · intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  refine k17b2_frame (V8 a a' b b' c c' d) q r u d hΔ hx hw hα1 hβ1 hβ6 hγ6 hσ hL3x hc1x ?_ ?_ ?_ ?_ ?_ ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k17bCyc2_0, eO]; simp [V8]
    · simp only [k17bCyc2_1, eB]; simp [V8]
    · simp only [k17bCyc2_2, eA']; simp [V8]
    · simp only [k17bCyc2_3, eB']; simp [V8]
    · simp only [k17bCyc2_4, eA]; simp [V8]
  · intro y hy
    rw [eO, eB, eA', eB', eA, eC, eC']
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  · rw [eO, eB]; exact h01
  · rw [eB, eA']; exact h12
  · rw [eA', eB']; exact h23
  · rw [eA, eB']; exact h43


theorem k17b_V8_swap (a a' b b' c c' d : ℝ³) : V8 a a' c c' b b' d = V8 a a' b b' c c' d := by
  ext y; simp only [V8, Finset.mem_insert, Finset.mem_singleton]; tauto

set_option maxHeartbeats 6400000 in
/-- **K17B arc rule S2.1** (mirror of S2.2: `b ↔ c`, `b' ↔ c'`, `β6 ↔ γ6`; view `u = A (a-d) - B (c-d)`, `A > 0`).
Cell `(a,d,c,a',c')`. -/
theorem k17b_S21 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 A B : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 1 < β6) (hγ6 : 1 < γ6) (hσ : β1 < β6 + γ6) (hA : 0 < A)
    (hE : ⟪(c - a') + (c' - a'), A • (a - d) - B • (c - d)⟫ = 0)
    (hL1 : 0 < ⟪a' - c, A • (a - d) - B • (c - d)⟫) (hL2 : 0 < ⟪c' - a, A • (a - d) - B • (c - d)⟫)
    (hL3 : 0 < det3 (a - d) (c - d) (b - d) * det3 (a' - c) (b' - c) (A • (a - d) - B • (c - d)))
    (hB : B < 0) (hc1 : 0 < (α1 - 1) * B + β1 * A) (hZ : 0 < ⟪c - d, A • (a - d) - B • (c - d)⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  rw [← k17b_V8_swap]
  refine k17b_S22 (a := a) (a' := a') (b := c) (b' := c') (c := b) (c' := b') (d := d) (α1 := α1) (β1 := β1)
    (β6 := γ6) (γ6 := β6) (A := A) (B := B) ?_ hb' hc' (by rw [ha']; abel) hα1 hβ1 hγ6 hβ6
    (by linarith) hA hE hL1 hL2 hL3 hB hc1 hZ
  intro h; apply hdet
  have : det3 (a - d) (c - d) (b - d) = -det3 (a - d) (b - d) (c - d) := by
    simp only [det3_expand]; ring
  rw [this] at h; linarith


/-- Witness view `u_*` of K15: `N = (x - a') + (x' - a')` (`x = b` or `c`), `y = x - d`, `p = a - d`; sign `s` makes `A > 0`. -/
noncomputable def k17bAA (N y : ℝ³) : ℝ := (if 0 < ⟪N, y⟫ then (1 : ℝ) else -1) * ⟪N, y⟫
noncomputable def k17bBB (N p y : ℝ³) : ℝ := (if 0 < ⟪N, y⟫ then (1 : ℝ) else -1) * ⟪N, p⟫
noncomputable def k17bUU (N p y : ℝ³) : ℝ³ := k17bAA N y • p - k17bBB N p y • y

theorem k17b_hE (N p y : ℝ³) : ⟪N, k17bUU N p y⟫ = 0 := by
  unfold k17bUU k17bAA k17bBB
  rw [inner_sub_right, inner_smul_right, inner_smul_right]; ring

/-- The literal package of rule S2.2 (view `u_b*`, cell `(a,d,b,a',b')`). -/
def K17bS22 (a a' b b' c c' d : ℝ³) (α1 β1 : ℝ) : Prop :=
  0 < k17bAA ((b - a') + (b' - a')) (b - d) ∧
  0 < ⟪a' - b, k17bUU ((b - a') + (b' - a')) (a - d) (b - d)⟫ ∧
  0 < ⟪b' - a, k17bUU ((b - a') + (b' - a')) (a - d) (b - d)⟫ ∧
  0 < det3 (a - d) (b - d) (c - d) * det3 (a' - b) (c' - b) (k17bUU ((b - a') + (b' - a')) (a - d) (b - d)) ∧
  k17bBB ((b - a') + (b' - a')) (a - d) (b - d) < 0 ∧
  0 < (α1 - 1) * k17bBB ((b - a') + (b' - a')) (a - d) (b - d) + β1 * k17bAA ((b - a') + (b' - a')) (b - d) ∧
  0 < ⟪b - d, k17bUU ((b - a') + (b' - a')) (a - d) (b - d)⟫

/-- The literal package of rule S2.1 (view `u_c*`, cell `(a,d,c,a',c')`). -/
def K17bS21 (a a' b b' c c' d : ℝ³) (α1 β1 : ℝ) : Prop :=
  0 < k17bAA ((c - a') + (c' - a')) (c - d) ∧
  0 < ⟪a' - c, k17bUU ((c - a') + (c' - a')) (a - d) (c - d)⟫ ∧
  0 < ⟪c' - a, k17bUU ((c - a') + (c' - a')) (a - d) (c - d)⟫ ∧
  0 < det3 (a - d) (c - d) (b - d) * det3 (a' - c) (b' - c) (k17bUU ((c - a') + (c' - a')) (a - d) (c - d)) ∧
  k17bBB ((c - a') + (c' - a')) (a - d) (c - d) < 0 ∧
  0 < (α1 - 1) * k17bBB ((c - a') + (c' - a')) (a - d) (c - d) + β1 * k17bAA ((c - a') + (c' - a')) (c - d) ∧
  0 < ⟪c - d, k17bUU ((c - a') + (c' - a')) (a - d) (c - d)⟫

theorem k17b_S22w {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 1 < β6) (hγ6 : 1 < γ6) (hσ : β1 < β6 + γ6)
    (h : K17bS22 a a' b b' c c' d α1 β1) : HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hA, hL1, hL2, hL3, hB, hc1, hZ⟩ := h
  exact k17b_S22 hdet hc' hb' ha' hα1 hβ1 hβ6 hγ6 hσ hA (k17b_hE _ _ _) hL1 hL2 hL3 hB hc1 hZ

theorem k17b_S21w {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 1 < β6) (hγ6 : 1 < γ6) (hσ : β1 < β6 + γ6)
    (h : K17bS21 a a' b b' c c' d α1 β1) : HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hA, hL1, hL2, hL3, hB, hc1, hZ⟩ := h
  exact k17b_S21 hdet hc' hb' ha' hα1 hβ1 hβ6 hγ6 hσ hA (k17b_hE _ _ _) hL1 hL2 hL3 hB hc1 hZ



theorem k17b_tri_uni (z w : ZMod 3 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j) : LexUni z w :=
  k6m_lexUni3 z w hinj

/-- Triangle `(c', a', b')` in the frame `(a'-c', b'-c', u)` based at `c'` (K6M2 rule 0 at the line view `L34`). -/
def k17bCycT : ZMod 3 → ℝ × ℝ × ℝ := ![(0, 0, 0), (1, 0, 0), (0, 1, 0)]

theorem k17bCycT_0 : k17bCycT 0 = (0, 0, 0) := rfl
theorem k17bCycT_1 : k17bCycT 1 = (1, 0, 0) := rfl
theorem k17bCycT_2 : k17bCycT 2 = (0, 1, 0) := rfl

theorem k17bT_inj : ∀ i j : ZMod 3, k17bCycT i = k17bCycT j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  rcases (by decide : ∀ i : ZMod 3, i = 0 ∨ i = 1 ∨ i = 2) i with rfl | rfl | rfl <;>
    rcases (by decide : ∀ i : ZMod 3, i = 0 ∨ i = 1 ∨ i = 2) j with rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [k17bCycT_0, k17bCycT_1, k17bCycT_2] at e1 e2; first | (norm_num at e1; done) | (norm_num at e2))

set_option maxHeartbeats 3200000 in
theorem k17bT_tsc {xa za xb zb yc xd yd zd v1 v2 : ℝ} (hxa : 0 < xa) (hxa1 : xa < 1) (hza : za < 0)
    (hxb : 0 < xb) (hzb : zb < 0) (hyc : 0 < yc) (hbc : xb + yc < 1) (hxd : 0 < xd) (hyd : 0 < yd)
    (hd : xd + yd < 1) (hxb1 : xb < 1) (hv1 : 0 < v1) (hv2 : 0 < v2) :
    (∀ i j : ZMod 3, j ≠ i → j ≠ i + 1 →
      TSc 1 (k17bCycT (i + 1) - k17bCycT i) (k17bCycT j - k17bCycT i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), xa, za), (xb, 0, zb), (xb, yc, zb), (xd, yd, zd)], ∀ i : ZMod 3,
      TSc 1 (k17bCycT (i + 1) - k17bCycT i) (t - k17bCycT i) (v1, v2, 0)) := by
  have f0 : (0 : ZMod 3) + 1 = 1 := by decide
  have f1 : (1 : ZMod 3) + 1 = 2 := by decide
  have f2 : (2 : ZMod 3) + 1 = 0 := by decide
  have p1 := mul_pos hv1 (neg_pos.2 hza)
  have p2 := mul_pos hv2 (neg_pos.2 hzb)
  constructor
  · intro i j h1 h2
    rcases (by decide : ∀ i : ZMod 3, i = 0 ∨ i = 1 ∨ i = 2) i with rfl | rfl | rfl <;>
      rcases (by decide : ∀ i : ZMod 3, i = 0 ∨ i = 1 ∨ i = 2) j with rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k17bCycT_0, k17bCycT_1, k17bCycT_2, f0, f1, f2,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl <;>
      rcases (by decide : ∀ i : ZMod 3, i = 0 ∨ i = 1 ∨ i = 2) i with rfl | rfl | rfl <;>
      (simp only [TSc, d3, k17bCycT_0, k17bCycT_1, k17bCycT_2, f0, f1, f2,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 3200000 in
theorem k17bT_frame (V : Finset ℝ³) (P Q R d0 : ℝ³) (hΔ : det3 P Q R ≠ 0)
    {xa za xb zb yc xd yd zd : ℝ} (hxa : 0 < xa) (hxa1 : xa < 1) (hza : za < 0)
    (hxb : 0 < xb) (hzb : zb < 0) (hyc : 0 < yc) (hbc : xb + yc < 1) (hxd : 0 < xd) (hyd : 0 < yd)
    (hd : xd + yd < 1) (hxb1 : xb < 1)
    (hmem : ∀ i, fpoint P Q R d0 (k17bCycT i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d0 (0, 0, 0) ∨ y = fpoint P Q R d0 (1, 0, 0) ∨ y = fpoint P Q R d0 (0, 1, 0) ∨
      y = fpoint P Q R d0 (0, xa, za) ∨ y = fpoint P Q R d0 (xb, 0, zb) ∨ y = fpoint P Q R d0 (xb, yc, zb) ∨
      y = fpoint P Q R d0 (xd, yd, zd)) :
    HasLexCellAt V R := by
  refine cyc_cell V P Q R d0 hΔ (k := 3) (by norm_num) k17bCycT k17bT_inj hmem
    [((0 : ℝ), xa, za), (xb, 0, zb), (xb, yc, zb), (xd, yd, zd)] ?_
    (u1 := 1) (u2 := 1) (t1 := 0) (t2 := 1) (lo := 0) (hi := 1) (by norm_num) (by norm_num)
    (fun v1 v2 => 0 < v1 ∧ 0 < v2) ?_ ?_ ?_
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam h0 h1
    refine ⟨by simp, ?_⟩
    simp only [mul_zero, add_zero, zero_add, mul_one]
    linarith
  · intro v1 v2 ⟨hv1, hv2⟩
    exact k17bT_tsc hxa hxa1 hza hxb hzb hyc hbc hxd hyd hd hxb1 hv1 hv2
  · intro v1 v2 _ hL
    exact k17b_tri_uni _ _ hL


set_option maxHeartbeats 12800000 in
/-- **K6M2 rule 0** (metric-free): triangle `(c', a', b')` at the line view `L34`, valid whenever
`α1 + β1 - 1 < (α1-1)(β1-1)(β6+γ6-1)` (this is the orientation-free form of `det3[L34](a,d,a') > 0`).
Frame based at `c'`: `(a'-c', b'-c', u)`, `u = -(α1β1σ')(a-c') + (γ6 S)(b'-c')`, `S = α1+β1-1`, `σ' = β6+γ6-1`. -/
theorem k17b_R0 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 1 < β6) (hγ6 : 1 < γ6)
    (hR0 : α1 + β1 - 1 < (α1 - 1) * (β1 - 1) * (β6 + γ6 - 1)) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨p, rfl⟩ : ∃ p, a = d + p := ⟨a - d, by abel⟩
  obtain ⟨q, rfl⟩ : ∃ q, b = d + q := ⟨b - d, by abel⟩
  obtain ⟨r, rfl⟩ : ∃ r, c = d + r := ⟨c - d, by abel⟩
  simp only [add_sub_cancel_left] at hdet hc' hb' ha'
  subst hc' hb' ha'
  have hS : 0 < α1 + β1 - 1 := by linarith
  have hσ : 0 < β6 + γ6 - 1 := by linarith
  have hT : 0 < (α1 - 1) * (β6 + γ6 - 1) := mul_pos (by linarith) hσ
  have hW : 0 < (α1 - 1) * (β6 + γ6 - 1) + (α1 + β1 - 1) := by linarith
  have hk : 0 < α1 * β1 * (β6 + γ6 - 1) := by positivity
  have hα0 : 0 < α1 := by linarith
  have hβ0 : 0 < β1 := by linarith
  have hγ0 : 0 < γ6 := by linarith
  set u : ℝ³ := (-(α1 * β1 * (β6 + γ6 - 1))) • ((d + p) - (d + α1 • p + β1 • q)) +
    (γ6 * (α1 + β1 - 1)) • ((d + α1 • p + β1 • r) - (d + α1 • p + β1 • q)) with hu
  have hΔ : det3 ((d + β6 • q + γ6 • r) - (d + α1 • p + β1 • q)) ((d + α1 • p + β1 • r) - (d + α1 • p + β1 • q)) u ≠ 0 := by
    have e : det3 ((d + β6 • q + γ6 • r) - (d + α1 • p + β1 • q)) ((d + α1 • p + β1 • r) - (d + α1 • p + β1 • q)) u =
        α1 * β1 * (β6 + γ6 - 1) * β1 * ((α1 - 1) * (β6 + γ6 - 1) + (α1 + β1 - 1)) * det3 p q r := by
      rw [hu]
      simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e]
    exact mul_ne_zero (by positivity) hdet
  set S : ℝ := α1 + β1 - 1 with hSdef
  set σ' : ℝ := β6 + γ6 - 1 with hσdef
  set T : ℝ := (α1 - 1) * σ' with hTdef
  have hS0 : S ≠ 0 := hS.ne'
  have hσ0 : σ' ≠ 0 := hσ.ne'
  have hW0 : T + S ≠ 0 := hW.ne'
  have hk0 : α1 * β1 * σ' ≠ 0 := hk.ne'
  have hα00 : α1 ≠ 0 := hα0.ne'
  have hβ00 : β1 ≠ 0 := hβ0.ne'
  set xa : ℝ := γ6 * S / (α1 * β1 * σ') with hxadef
  set za : ℝ := -1 / (α1 * β1 * σ') with hzadef
  set xb : ℝ := S / (T + S) with hxbdef
  set zb : ℝ := -1 / (β1 * (T + S)) with hzbdef
  set yc : ℝ := 1 / β1 with hycdef
  set xd : ℝ := β1 / (T + S) with hxddef
  set yd : ℝ := γ6 / (β1 * σ') with hyddef
  set zd : ℝ := -(1 / S) * (1 / (β1 * σ') + 1 / (T + S)) with hzddef
  set cp : ℝ³ := d + α1 • p + β1 • q with hcp
  set P : ℝ³ := (d + β6 • q + γ6 • r) - cp with hP
  set Q : ℝ³ := (d + α1 • p + β1 • r) - cp with hQ
  have eC' : fpoint P Q u cp (0, 0, 0) = cp := by simp [fpoint, fcomb]
  have eA' : fpoint P Q u cp (1, 0, 0) = d + β6 • q + γ6 • r := by simp only [fpoint, fcomb, hP]; module
  have eB' : fpoint P Q u cp (0, 1, 0) = d + α1 • p + β1 • r := by simp only [fpoint, fcomb, hQ]; module
  have eA : fpoint P Q u cp (0, xa, za) = d + p := by
    simp only [fpoint, fcomb, hP, hQ, hu, hcp, hxadef, hzadef]
    match_scalars <;> field_simp <;> ring
  have eB : fpoint P Q u cp (xb, 0, zb) = d + q := by
    simp only [fpoint, fcomb, hP, hQ, hu, hcp, hxbdef, hzbdef]
    match_scalars <;> field_simp <;> (try simp only [hSdef, hTdef, hσdef]) <;> ring
  have eC : fpoint P Q u cp (xb, yc, zb) = d + r := by
    simp only [fpoint, fcomb, hP, hQ, hu, hcp, hxbdef, hzbdef, hycdef]
    match_scalars <;> field_simp <;> (try simp only [hSdef, hTdef, hσdef]) <;> ring
  have eD : fpoint P Q u cp (xd, yd, zd) = d := by
    simp only [fpoint, fcomb, hP, hQ, hu, hcp, hxddef, hyddef, hzddef]
    match_scalars <;> field_simp <;> (try simp only [hSdef, hTdef, hσdef]) <;> ring
  have hxa0 : 0 < xa := by rw [hxadef]; positivity
  have hxa1 : xa < 1 := by
    rw [hxadef, div_lt_one hk]
    have : 0 < α1 * β1 * (β6 - 1) + γ6 * ((α1 - 1) * (β1 - 1)) := by
      have := mul_pos (mul_pos hα0 hβ0) (sub_pos.2 hβ6)
      have := mul_pos hγ0 (mul_pos (sub_pos.2 hα1) (sub_pos.2 hβ1))
      linarith
    simp only [hSdef, hσdef]; nlinarith
  have hza0 : za < 0 := by rw [hzadef]; exact div_neg_of_neg_of_pos (by norm_num) hk
  have hxb0 : 0 < xb := by rw [hxbdef]; positivity
  have hxb1 : xb < 1 := by rw [hxbdef, div_lt_one hW]; linarith
  have hzb0 : zb < 0 := by rw [hzbdef]; exact div_neg_of_neg_of_pos (by norm_num) (mul_pos hβ0 hW)
  have hyc0 : 0 < yc := by rw [hycdef]; positivity
  have hbc : xb + yc < 1 := by
    rw [hxbdef, hycdef, div_add_div _ _ hW0 hβ00, div_lt_one (mul_pos hW hβ0)]
    simp only [hTdef, hSdef, hσdef] at hR0 ⊢
    nlinarith
  have hxd0 : 0 < xd := by rw [hxddef]; positivity
  have hyd0 : 0 < yd := by rw [hyddef]; positivity
  have hd : xd + yd < 1 := by
    rw [hxddef, hyddef, div_add_div _ _ hW0 (mul_ne_zero hβ00 hσ0), div_lt_one (mul_pos hW (mul_pos hβ0 hσ))]
    have h1 : (β1 - 1) * (T + S) > β1 * S := by
      simp only [hTdef, hSdef, hσdef] at hR0 ⊢; nlinarith
    have h2 : (β1 - 1) * (T + S) > β1 * β1 := by nlinarith
    have h3 : 0 < β6 - 1 := by linarith
    have h4 : γ6 < σ' := by rw [hσdef]; linarith
    nlinarith [mul_pos hW hσ, mul_pos hσ (sub_pos.2 h4), mul_pos hW (sub_pos.2 h4), mul_pos hσ (sub_pos.2 h2)]
  have hmem : ∀ i : ZMod 3, fpoint P Q u cp (k17bCycT i) ∈ V8 (d + p) (d + β6 • q + γ6 • r) (d + q)
      (d + α1 • p + β1 • r) (d + r) cp d := by
    intro i
    rcases (by decide : ∀ i : ZMod 3, i = 0 ∨ i = 1 ∨ i = 2) i with rfl | rfl | rfl
    · simp only [k17bCycT_0, eC']; simp [V8]
    · simp only [k17bCycT_1, eA']; simp [V8]
    · simp only [k17bCycT_2, eB']; simp [V8]
  refine ⟨u, ?_, ?_⟩
  · intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  refine k17bT_frame (zd := zd) _ P Q u cp hΔ hxa0 hxa1 hza0 hxb0 hzb0 hyc0 hbc hxd0 hyd0 hd hxb1 hmem ?_
  intro y hy
  rw [eC', eA', eB', eA, eB, eC, eD]
  simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
  tauto


/-- Leftover of the K17B part of L2: `R0` fails, both safe literals fail (non-strictly) and neither arc rule fires. -/
def K17bL2Left (a a' b b' c c' d : ℝ³) (α1 β1 β6 γ6 : ℝ) : Prop :=
  (α1 - 1) * (β1 - 1) * (β6 + γ6 - 1) ≤ α1 + β1 - 1 ∧
  0 ≤ ⟪c' - a, b' - c⟫ ∧ 0 ≤ ⟪c' - a', b' - c⟫ ∧ ¬ K17bS22 a a' b b' c c' d α1 β1 ∧ ¬ K17bS21 a a' b b' c c' d α1 β1

theorem k17b_l2 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 1 < β6) (hγ6 : 1 < γ6) (hσ : β1 < β6 + γ6)
    (hM : K6sM a a' b b' c c' d) (hrel : K16Rel a b c d α1 β1) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K17bL2Left a a' b b' c c' d α1 β1 β6 γ6 := by
  by_cases h0 : α1 + β1 - 1 < (α1 - 1) * (β1 - 1) * (β6 + γ6 - 1)
  · exact Or.inl (k17b_R0 hdet hc' hb' ha' hα1 hβ1 hβ6 hγ6 h0)
  by_cases hs : ⟪c' - a, b' - c⟫ < 0 ∨ ⟪c' - a', b' - c⟫ < 0
  · exact Or.inl (k17b_safe hdet hc' hb' ha' hα1 hβ1 hβ6 hγ6 hM hrel hs)
  by_cases h2 : K17bS22 a a' b b' c c' d α1 β1
  · exact Or.inl (k17b_S22w hdet hc' hb' ha' hα1 hβ1 hβ6 hγ6 hσ h2)
  by_cases h1 : K17bS21 a a' b b' c c' d α1 β1
  · exact Or.inl (k17b_S21w hdet hc' hb' ha' hα1 hβ1 hβ6 hγ6 hσ h1)
  push Not at hs h0
  exact Or.inr ⟨h0, hs.1, hs.2, h2, h1⟩

end C2
end Type08Sp
end Minimality
