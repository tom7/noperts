module

public import Minimality.Type08S.C2K5LJ

@[expose] public section


/-!
# K5L / K: K5c, FC-ab at `u0 = a - b'` (QPc `α4 < 1`, QTc `α4 < 1`), frame form

Frame `(P,Q,R) = (b - d, c - d, a - b')`; `σ = 1/(1 - α4)`, `κ = γ4/(1 - α4)`; points over `d`:
`d = 0, b = (1,0,0), c = (0,1,0), a = (0,κ,σ), b' = (0,κ,σ-1), c' = (β1, κα1, α1σ), a' = (β6, κ(1-β6), 0)`
(`a'` on the diagonal `[b, a]` of `Q_ab` by `κ_c = 0`).  Face `Q_ab = (a, d, b, c')`.
Cone `v1 > 0, κ(1-α1) v1 + β1 v2 < 0`.
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

def krCyc (κ σ α1 β1 : ℝ) : ZMod 4 → ℝ × ℝ × ℝ := ![(0, κ, σ), (0, 0, 0), (1, 0, 0), (β1, κ * α1, α1 * σ)]

theorem krCyc_0 : krCyc κ σ α1 β1 0 = (0, κ, σ) := rfl
theorem krCyc_1 : krCyc κ σ α1 β1 1 = (0, 0, 0) := rfl
theorem krCyc_2 : krCyc κ σ α1 β1 2 = (1, 0, 0) := rfl
theorem krCyc_3 : krCyc κ σ α1 β1 3 = (β1, κ * α1, α1 * σ) := rfl

set_option maxHeartbeats 3200000 in
theorem kr_tsc {κ σ α1 β1 β6 v1 v2 : ℝ} (hκ : 1 < κ) (hσ : 0 < σ) (hα1 : 0 < α1) (hβ1 : 0 < β1)
    (hαβ : 1 < α1 + β1) (hb6 : 0 < β6) (hb61 : β6 < 1) (hv1 : 0 < v1)
    (hcone : κ * (1 - α1) * v1 + β1 * v2 < 0) :
    (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      TSc 1 (krCyc κ σ α1 β1 (i + 1) - krCyc κ σ α1 β1 i) (krCyc κ σ α1 β1 j - krCyc κ σ α1 β1 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (1 : ℝ), (0 : ℝ)), (β6, κ * (1 - β6), 0), (0, κ, σ - 1)], ∀ i : ZMod 4,
      TSc 1 (krCyc κ σ α1 β1 (i + 1) - krCyc κ σ α1 β1 i) (t - krCyc κ σ α1 β1 i) (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3⟩ := z4_add
  have k0 : 0 < κ := by linarith
  have g : 0 < 1 - β6 := by linarith
  have m1 := mul_pos hβ1 k0
  have m2 := mul_pos hσ hv1
  have m3 := mul_pos k0 hv1
  have m4 := mul_pos (mul_pos k0 hβ1) hα1
  have m5 := mul_pos k0 (sub_pos.2 hαβ)
  have m6 := mul_pos hβ1 (sub_pos.2 hκ)
  have m7 := mul_pos (mul_pos k0 g) (sub_pos.2 hαβ)
  have m8 := mul_pos (mul_pos hβ1 k0) hb6
  have m9 := mul_pos k0 hb6
  have m10 := mul_pos k0 g
  have m11 := mul_pos (mul_pos k0 hb6) (sub_pos.2 hαβ)
  have m12 := mul_pos (mul_pos hβ1 k0) g
  have m13 := mul_pos hσ (neg_pos.2 hcone)
  have m14 := mul_pos hσ hα1
  have m15 : 0 < β1 + κ * α1 - 1 := by nlinarith
  have m16 := mul_pos hσ (sub_pos.2 hκ)
  have m17 := mul_pos (mul_pos hβ1 k0) hv1
  have m18 := mul_pos hσ (mul_pos hβ1 hv1)
  have m19 := mul_pos (mul_pos hσ k0) hv1
  have m20 : 0 < κ * (β1 + α1 - 1) * (1 - β6) := by nlinarith
  have m21 := mul_pos hσ (mul_pos hα1 hv1)
  have m22 := mul_pos (mul_pos hσ hα1) (neg_pos.2 hcone)
  have m23 := mul_pos hσ (mul_pos hb6 hv1)
  have m24 := mul_pos hσ (mul_pos hb6 k0)
  have m25 := mul_pos hσ (mul_pos m10 hv1)
  constructor
  · intro i j h1 h2
    rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      rcases z4_cases j with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, krCyc_0, krCyc_1, krCyc_2, krCyc_3, s0, s1, s2, s3, Prod.fst_sub, Prod.snd_sub,
          Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;>
      rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, krCyc_0, krCyc_1, krCyc_2, krCyc_3, s0, s1, s2, s3, Prod.fst_sub, Prod.snd_sub,
          Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

theorem kr_inj {κ σ α1 β1 : ℝ} (hκ : 0 < κ) (hα1 : 0 < α1) (hβ1 : 0 < β1) :
    ∀ i j : ZMod 4, krCyc κ σ α1 β1 i = krCyc κ σ α1 β1 j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  have m := mul_pos hκ hα1
  rcases z4_cases i with rfl | rfl | rfl | rfl <;> rcases z4_cases j with rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [krCyc_0, krCyc_1, krCyc_2, krCyc_3] at e1 e2; linarith)

theorem k5c_fcab_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {κ σ α1 β1 β6 : ℝ}
    (hκ : 1 < κ) (hσ : 0 < σ) (hα1 : 0 < α1) (hβ1 : 0 < β1) (hαβ : 1 < α1 + β1) (hb6 : 0 < β6)
    (hb61 : β6 < 1)
    (hmem : ∀ i, fpoint P Q R d (krCyc κ σ α1 β1 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, κ, σ) ∨ y = fpoint P Q R d (0, 0, 0) ∨
      y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (β1, κ * α1, α1 * σ) ∨
      y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (β6, κ * (1 - β6), 0) ∨
      y = fpoint P Q R d (0, κ, σ - 1)) :
    HasLexCellAt V R := by
  have k0 : 0 < κ := by linarith
  have hβ : 0 < 1 + (α1 - 1) / β1 := by
    have : (α1 - 1) / β1 > -1 := by rw [gt_iff_lt, lt_div_iff₀ hβ1]; linarith
    linarith
  refine fc_cell V P Q R d hΔ (krCyc κ σ α1 β1) (β := 1 + (α1 - 1) / β1) (γ := 1 / β1) hβ
    (by positivity) ?_ ?_ (kr_inj k0 hα1 hβ1) hmem
    [((0 : ℝ), (1 : ℝ), (0 : ℝ)), (β6, κ * (1 - β6), 0), (0, κ, σ - 1)] ?_
    (u1 := 1) (u2 := -(κ * (1 - α1) + 1) / β1) (t1 := 0) (t2 := -1) (lo := 0) (hi := 1) (by norm_num)
    (by norm_num) (fun v1 v2 => 0 < v1 ∧ κ * (1 - α1) * v1 + β1 * v2 < 0) ?_ ?_
  · have : 1 + (α1 - 1) / β1 + 1 / β1 = 1 + α1 / β1 := by field_simp; ring
    rw [this]; have := div_pos hα1 hβ1; linarith
  · simp only [krCyc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Prod.ext_iff,
      Prod.smul_mk, Prod.mk_sub_mk, Prod.mk_add_mk, smul_eq_mul]
    refine ⟨?_, ?_, ?_⟩ <;> first | (field_simp; ring) | field_simp
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
    have hq : -(κ * (1 - α1) + 1) / β1 * β1 = -(κ * (1 - α1) + 1) := div_mul_cancel₀ _ hβ1.ne'
    simp only [mul_zero, add_zero, mul_one, mul_neg]
    nlinarith [mul_pos hβ1 h0]
  · intro v1 v2 ⟨hv1, hc⟩
    exact kr_tsc hκ hσ hα1 hβ1 hαβ hb6 hb61 hv1 hc

end C2
end Type08Sp
end Minimality
