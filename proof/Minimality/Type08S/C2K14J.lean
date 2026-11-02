module

public import Minimality.Type08S.C2K14I

@[expose] public section


/-!
# K14 / J: Ta box C tie `D_c < 0 ∧ ζ_C = 0`: peak lemma, frame cell and the closing lemma
(The cell never uses `ζ_C = 0`; only `D_c < 0`, `α1 > 1 > α4 > 0`, `γ4 > 1`, `β1 > 1`, `β6 > 1`.)
-/
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

/-- Pentagon `(c', b', c, d, b)` (indices `0..4`) with `c < d < b` and not (`c' ≤ b`, `c' ≤ b'`, `c ≤ b'`). -/
theorem k14_pent_uni_zc (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h23 : z 2 < z 3) (h34 : z 3 < z 4) (hbad : z 0 ≤ z 4 → z 0 ≤ z 1 → z 2 ≤ z 1 → False) : LexUni z w := by
  obtain ⟨M, hM⟩ := exists_key z w hinj
  refine lexUni_of_key z w (fun i => M * z i + w i) hinj hM ?_
  have lt : ∀ i j, z i < z j → M * z i + w i < M * z j + w j := fun i j h => (hM i j).1 (Or.inl h)
  have back : ∀ i j, M * z i + w i < M * z j + w j → z i ≤ z j := by
    intro i j h
    rcases (hM i j).2 h with h' | ⟨h1, h2⟩
    · exact h'.le
    · exact h1.le
  have hk := k6m_key_inj z w hinj M hM
  refine k5d_uni_of_nopair (by decide) _ hk ?_
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_sub1
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have k23 := lt _ _ h23
  have k34 := lt _ _ h34
  intro i j h1 h2 h3 ⟨⟨pi1, pi2⟩, ⟨pj1, pj2⟩⟩
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact h1 rfl
    | exact h2 (by decide)
    | exact h3 (by decide)
    | (simp only [s0, s1, s2, s3, s4, f0, f1, f2, f3, f4] at pi1 pi2 pj1 pj2
       first
       | linarith
       | exact hbad (back _ _ (by linarith)) (back _ _ (by linarith)) (back _ _ (by linarith)))

set_option maxHeartbeats 3200000 in
theorem k14_zc_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {α1 β1 α4 γ4 β6 : ℝ}
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hα4 : 0 < α4) (hα41 : α4 < 1) (hγ4 : 1 < γ4) (hb6 : 1 < β6)
    (hmem : ∀ i, fpoint P Q R d (k14ZcCyc α1 β1 α4 γ4 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (α1, 0, β1) ∨ y = fpoint P Q R d (α4, γ4, 0) ∨
      y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (0, 0, 1) ∨
      y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (0, 1, β6))
    (h23 : ⟪fpoint P Q R d (0, 1, 0), R⟫ < ⟪fpoint P Q R d (0, 0, 0), R⟫)
    (h34 : ⟪fpoint P Q R d (0, 0, 0), R⟫ < ⟪fpoint P Q R d (0, 0, 1), R⟫)
    (hbad : ⟪fpoint P Q R d (α1, 0, β1), R⟫ ≤ ⟪fpoint P Q R d (0, 0, 1), R⟫ →
      ⟪fpoint P Q R d (α1, 0, β1), R⟫ ≤ ⟪fpoint P Q R d (α4, γ4, 0), R⟫ →
      ⟪fpoint P Q R d (0, 1, 0), R⟫ ≤ ⟪fpoint P Q R d (α4, γ4, 0), R⟫ → False) :
    HasLexCellAt V R := by
  refine cyc_cell V P Q R d hΔ (k := 5) (by norm_num) (k14ZcCyc α1 β1 α4 γ4)
    (k14Zc_inj hα1 (by linarith) hα41 hγ4) hmem [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 1, β6)] ?_
    (u1 := -1) (u2 := 1) (t1 := 0) (t2 := 1) (lo := 0) (hi := 1) (by norm_num) (by norm_num)
    (fun v1 v2 => v1 < 0 ∧ 0 < v2) ?_ ?_ ?_
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
    refine ⟨by simp, ?_⟩
    simp only [mul_zero, add_zero, zero_add, mul_one]
    linarith
  · intro v1 v2 ⟨hv1, hc⟩
    exact k14Zc_tsc hα1 hβ1 hα4 hα41 hγ4 hb6 hv1 hc
  · intro v1 v2 ⟨hv1, hc⟩ hL
    refine k14_pent_uni_zc _ _ hL ?_ ?_ ?_
    · simpa only [k14ZcCyc_2, k14ZcCyc_3] using h23
    · simpa only [k14ZcCyc_3, k14ZcCyc_4] using h34
    · simpa only [k14ZcCyc_0, k14ZcCyc_1, k14ZcCyc_2, k14ZcCyc_4] using hbad

set_option maxHeartbeats 3200000 in
/-- **Ta box C, `D_c < 0`** (so also the tie `ζ_C = 0`; view `d - b`): closed. -/
theorem k14_TaC_hasLexCell {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT : IsT a' b c d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0)
    (hfar : W.F.a'bc.f c' < W.F.a'bc.f a)
    (hβ : 0 < det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d))
    (hα : det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) < 0)
    (hβ6 : 0 < det3 (a' - b) (c - d) (a - d) * det3 (a - d) (b - d) (c - d))
    (hD : ⟪b - d, c - d⟫ < 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα1, hβ1, hαβ, hα4, hγ4, hαγ, hβ6p, hfar'⟩ :=
    norm08w_coordsT W hT
  have hκ' := (planar_a_iff hdet hc' hb').1 hκ
  rw [det_beta1 hc'] at hβ
  rw [det_alpha4 hb'] at hα
  rw [k5f_det_beta6 ha'] at hβ6
  have hΔ2 : 0 < det3 (a - d) (b - d) (c - d) ^ 2 := by positivity
  have hβ11 : 1 < β1 := by nlinarith
  have hα41 : α4 < 1 := by nlinarith
  have hβ61 : 1 < β6 := by nlinarith
  have hγ41 : 1 < γ4 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg hα1.le (by linarith : 0 ≤ 1 - γ4), mul_pos hα4 (sub_pos.2 hβ11)]
  have hα1' : 1 < α1 := hfar' hfar
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  have hqr : ⟪q, r⟫ < 0 := hD
  have hq0 : q ≠ 0 := by intro h0; apply hdet; rw [h0]; simp [det3_expand]
  have hqq : 0 < ⟪q, q⟫ := real_inner_self_pos.2 hq0
  have hΔ : det3 p r q ≠ 0 := by
    intro h; apply hdet
    simp only [det3_expand] at h ⊢; linarith
  have eO : fpoint p r q d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eA : fpoint p r q d (1, 0, 0) = a := by simp only [fpoint, fcomb, hp]; module
  have eB : fpoint p r q d (0, 0, 1) = b := by simp only [fpoint, fcomb, hq]; module
  have eC : fpoint p r q d (0, 1, 0) = c := by simp only [fpoint, fcomb, hr]; module
  have eC' : fpoint p r q d (α1, 0, β1) = c' := by rw [hc']; simp only [fpoint, fcomb, hp, hq]; module
  have eB' : fpoint p r q d (α4, γ4, 0) = b' := by rw [hb']; simp only [fpoint, fcomb, hp, hr]; module
  have eA' : fpoint p r q d (0, 1, β6) = a' := by rw [ha']; simp only [fpoint, fcomb, hq, hr]; module
  have hne : q ≠ 0 := hq0
  refine ⟨q, hne, ?_⟩
  have key : ∀ x y z : ℝ, ⟪x • p + y • r + z • q, q⟫ = x * ⟪p, q⟫ + y * ⟪r, q⟫ + z * ⟪q, q⟫ := by
    intro x y z
    simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real]
  have hrq : ⟪r, q⟫ = ⟪q, r⟫ := real_inner_comm _ _
  have inner_lt : ∀ X Y : ℝ³, ⟪X - Y, q⟫ < 0 → ⟪X, q⟫ < ⟪Y, q⟫ := by
    intro X Y h; rw [inner_sub_left] at h; linarith
  have inner_le : ∀ X Y : ℝ³, ⟪X, q⟫ ≤ ⟪Y, q⟫ → ⟪X - Y, q⟫ ≤ 0 := by
    intro X Y h; rw [inner_sub_left]; linarith
  refine k14_zc_frame (V8 a a' b b' c c' d) p r q d hΔ hα1' hβ11 hα4 hα41 hγ41 hβ61 ?_ ?_ ?_ ?_ ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k14ZcCyc_0, eC']; simp [V8]
    · simp only [k14ZcCyc_1, eB']; simp [V8]
    · simp only [k14ZcCyc_2, eC]; simp [V8]
    · simp only [k14ZcCyc_3, eO]; simp [V8]
    · simp only [k14ZcCyc_4, eB]; simp [V8]
  · intro y hy
    rw [eC', eB', eC, eO, eB, eA, eA']
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  · rw [eC, eO]
    apply inner_lt
    have : c - d = (0:ℝ) • p + (1:ℝ) • r + (0:ℝ) • q := by rw [hr]; module
    rw [this, key]; linarith
  · rw [eO, eB]
    apply inner_lt
    have : d - b = (0:ℝ) • p + (0:ℝ) • r + (-1:ℝ) • q := by rw [hq]; module
    rw [this, key]; linarith
  · intro h1 h2 h3
    rw [eC', eB] at h1
    rw [eC', eB'] at h2
    rw [eC, eB'] at h3
    have g2 := inner_le _ _ h2
    have g3 := inner_le _ _ h3
    have e2 : c' - b' = (α1 - α4) • p + (-γ4) • r + β1 • q := by rw [hc', hb', hp, hq, hr]; module
    have e3 : c - b' = (-α4) • p + (1 - γ4) • r + (0:ℝ) • q := by rw [hb', hp, hr]; module
    rw [e2, key] at g2
    rw [e3, key] at g3
    rw [hrq] at g2 g3
    have t1 : 0 < (γ4 - 1) * (-⟪q, r⟫) := mul_pos (by linarith) (neg_pos.2 hqr)
    have t2 : 0 < γ4 * (-⟪q, r⟫) := mul_pos (by linarith) (neg_pos.2 hqr)
    have t3 : 0 < β1 * ⟪q, q⟫ := mul_pos (by linarith) hqq
    have hs1 : ⟪p, q⟫ < 0 := by
      by_contra hh; push Not at hh
      have := mul_nonneg (by linarith : (0:ℝ) ≤ α1 - α4) hh
      linarith
    have hs2 : 0 < ⟪p, q⟫ := by
      by_contra hh; push Not at hh
      have := mul_nonneg hα4.le (neg_nonneg.2 hh)
      linarith
    linarith

end C2
end Type08Sp
end Minimality
