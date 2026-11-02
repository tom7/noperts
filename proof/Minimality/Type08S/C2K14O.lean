module

public import Minimality.Type08S.C2K14N

@[expose] public section


/-!
# K14 / O: M box H5, single-literal rule `⟪a - d, a - c'⟫ > 0` (view `a - d`, quadrilateral `(a, b', a', c')`)
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

/-- Quadrilateral `(a, c', a', b')` (indices `0..3`): `c', b' < a` and `a' < c', b'`. -/
theorem k14_quad_uni_h5 (z w : ZMod 4 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h10 : z 1 < z 0) (h30 : z 3 < z 0) (h21 : z 2 < z 1) (h23 : z 2 < z 3) : LexUni z w := by
  obtain ⟨M, hM⟩ := exists_key z w hinj
  refine lexUni_of_key z w (fun i => M * z i + w i) hinj hM ?_
  have lt : ∀ i j, z i < z j → M * z i + w i < M * z j + w j := fun i j h => (hM i j).1 (Or.inl h)
  have hk := k6m_key_inj z w hinj M hM
  refine k5d_uni_of_nopair (by decide) _ hk ?_
  obtain ⟨s0, s1, s2, s3⟩ := z4_sub1
  obtain ⟨f0, f1, f2, f3⟩ := z4_add
  have k10 := lt _ _ h10
  have k30 := lt _ _ h30
  have k21 := lt _ _ h21
  have k23 := lt _ _ h23
  intro i j h1 h2 h3 ⟨⟨pi1, pi2⟩, ⟨pj1, pj2⟩⟩
  rcases z4_cases i with rfl | rfl | rfl | rfl <;> rcases z4_cases j with rfl | rfl | rfl | rfl <;>
    first
    | exact h1 rfl
    | exact h2 (by decide)
    | exact h3 (by decide)
    | (simp only [s0, s1, s2, s3, f0, f1, f2, f3] at pi1 pi2 pj1 pj2
       linarith)

set_option maxHeartbeats 3200000 in
theorem k14_h5_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {α1 β1 β6 γ6 : ℝ}
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hb6 : 0 < β6) (hγ6 : 0 < γ6) (hσ : β1 < β6 + γ6)
    (hmem : ∀ i, fpoint P Q R d (k14H5Cyc α1 β1 β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 0, 1) ∨ y = fpoint P Q R d (β1, 0, α1) ∨
      y = fpoint P Q R d (β6, γ6, 0) ∨ y = fpoint P Q R d (0, β1, α1) ∨ y = fpoint P Q R d (1, 0, 0) ∨
      y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, 0))
    (h10 : ⟪fpoint P Q R d (β1, 0, α1), R⟫ < ⟪fpoint P Q R d (0, 0, 1), R⟫)
    (h30 : ⟪fpoint P Q R d (0, β1, α1), R⟫ < ⟪fpoint P Q R d (0, 0, 1), R⟫)
    (h21 : ⟪fpoint P Q R d (β6, γ6, 0), R⟫ < ⟪fpoint P Q R d (β1, 0, α1), R⟫)
    (h23 : ⟪fpoint P Q R d (β6, γ6, 0), R⟫ < ⟪fpoint P Q R d (0, β1, α1), R⟫) :
    HasLexCellAt V R := by
  refine cyc_cell V P Q R d hΔ (k := 4) (by norm_num) (k14H5Cyc α1 β1 β6 γ6)
    (k14H5_inj hβ1 hb6 hγ6) hmem [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 1, 0), (0, 0, 0)] ?_
    (u1 := 1) (u2 := 1) (t1 := 0) (t2 := 1) (lo := 0) (hi := 1) (by norm_num) (by norm_num)
    (fun v1 v2 => 0 < v1 ∧ 0 < v2) ?_ ?_ ?_
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
    simp only [mul_zero, add_zero, zero_add, mul_one]
    linarith
  · intro v1 v2 ⟨hv1, hv2⟩
    exact k14H5_tsc hα1 hβ1 hb6 hγ6 hσ hv1 hv2
  · intro v1 v2 ⟨hv1, hv2⟩ hL
    refine k14_quad_uni_h5 _ _ hL ?_ ?_ ?_ ?_
    · simpa only [k14H5Cyc_1, k14H5Cyc_0] using h10
    · simpa only [k14H5Cyc_3, k14H5Cyc_0] using h30
    · simpa only [k14H5Cyc_2, k14H5Cyc_1] using h21
    · simpa only [k14H5Cyc_2, k14H5Cyc_3] using h23

set_option maxHeartbeats 6400000 in
/-- **H5 rule 4**: `α1, β1 > 1`, `σ > β1`, `⟪a - d, a - c'⟫ > 0` (view `a - d`; box shape of `β6, γ6` irrelevant). -/
theorem k14_H5_hasLexCell {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hσ : β1 < β6 + γ6)
    (hM : K6sM a a' b b' c c' d) (hlit : 0 < ⟪a - d, a - c'⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨m1, m2, m3⟩ := hM
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  have hΔ : det3 q r p ≠ 0 := by
    intro h; apply hdet
    simp only [det3_expand] at h ⊢; linarith
  have hp0 : p ≠ 0 := by intro h0; apply hdet; rw [h0]; simp [det3_expand]
  have hpp : 0 < ⟪p, p⟫ := real_inner_self_pos.2 hp0
  have hm1 : ⟪p, q⟫ = ⟪p, r⟫ := by
    have : ⟪p, b - c⟫ = ⟪p, q⟫ - ⟪p, r⟫ := by
      rw [← inner_sub_right]; congr 1; rw [hq, hr]; abel
    linarith
  have eO : fpoint q r p d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eA : fpoint q r p d (0, 0, 1) = a := by simp only [fpoint, fcomb, hp]; module
  have eB : fpoint q r p d (1, 0, 0) = b := by simp only [fpoint, fcomb, hq]; module
  have eC : fpoint q r p d (0, 1, 0) = c := by simp only [fpoint, fcomb, hr]; module
  have eC' : fpoint q r p d (β1, 0, α1) = c' := by rw [hc']; simp only [fpoint, fcomb, hp, hq]; module
  have eB' : fpoint q r p d (0, β1, α1) = b' := by rw [hb']; simp only [fpoint, fcomb, hp, hr]; module
  have eA' : fpoint q r p d (β6, γ6, 0) = a' := by rw [ha']; simp only [fpoint, fcomb, hq, hr]; module
  have hp0' : p ≠ 0 := hp0
  refine ⟨p, hp0, ?_⟩
  have key : ∀ x y z : ℝ, ⟪x • q + y • r + z • p, p⟫ = x * ⟪q, p⟫ + y * ⟪r, p⟫ + z * ⟪p, p⟫ := by
    intro x y z
    simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real]
  have hqp : ⟪q, p⟫ = ⟪p, q⟫ := real_inner_comm _ _
  have hrp : ⟪r, p⟫ = ⟪p, r⟫ := real_inner_comm _ _
  have inner_lt : ∀ X Y : ℝ³, ⟪X - Y, p⟫ < 0 → ⟪X, p⟫ < ⟪Y, p⟫ := by
    intro X Y h; rw [inner_sub_left] at h; linarith
  -- the literal in coordinates
  have hlit' : 0 < (1 - α1) * ⟪p, p⟫ - β1 * ⟪p, q⟫ := by
    have e : a - c' = (1 - α1) • p + (-β1) • q + (0:ℝ) • r := by rw [hc', hp, hq]; module
    have : ⟪a - d, a - c'⟫ = ⟪p, (1 - α1) • p + (-β1) • q + (0:ℝ) • r⟫ := by rw [e]
    rw [this] at hlit
    simp only [inner_add_right, inner_smul_right] at hlit
    rw [← hm1] at hlit
    linarith
  have hs : ⟪p, q⟫ < 0 := by
    have : 0 ≤ (α1 - 1) * ⟪p, p⟫ := mul_nonneg (by linarith) hpp.le
    nlinarith
  refine k14_h5_frame (V8 a a' b b' c c' d) q r p d hΔ hα1 hβ1 hβ6 hγ6 hσ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i
    rcases z4_cases i with rfl | rfl | rfl | rfl
    · simp only [k14H5Cyc_0, eA]; simp [V8]
    · simp only [k14H5Cyc_1, eC']; simp [V8]
    · simp only [k14H5Cyc_2, eA']; simp [V8]
    · simp only [k14H5Cyc_3, eB']; simp [V8]
  · intro y hy
    rw [eA, eC', eA', eB', eB, eC, eO]
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  · rw [eC', eA]
    apply inner_lt
    have : c' - a = β1 • q + (0:ℝ) • r + (α1 - 1) • p := by rw [hc', hp, hq]; module
    rw [this, key, hqp, hrp, ← hm1]
    nlinarith
  · rw [eB', eA]
    apply inner_lt
    have : b' - a = (0:ℝ) • q + β1 • r + (α1 - 1) • p := by rw [hb', hp, hr]; module
    rw [this, key, hqp, hrp, ← hm1]
    nlinarith
  · rw [eA', eC']
    apply inner_lt
    have : a' - c' = (β6 - β1) • q + γ6 • r + (-α1) • p := by rw [ha', hc', hp, hq, hr]; module
    rw [this, key, hqp, hrp, ← hm1]
    nlinarith [mul_pos (by linarith : (0:ℝ) < β6 + γ6 - β1) (neg_pos.2 hs)]
  · rw [eA', eB']
    apply inner_lt
    have : a' - b' = β6 • q + (γ6 - β1) • r + (-α1) • p := by rw [ha', hb', hp, hq, hr]; module
    rw [this, key, hqp, hrp, ← hm1]
    nlinarith [mul_pos (by linarith : (0:ℝ) < β6 + γ6 - β1) (neg_pos.2 hs)]

end C2
end Type08Sp
end Minimality
