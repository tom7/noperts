module

public import Minimality.Type08S.C2K5LB

@[expose] public section


/-!
# K5L / C: K5e, the face cell `Q_bc` at `b' - c` (frame form)

Frame `(P,Q,R) = (b - d, a - d, b' - c)`, points over `d`:
`d = 0, b = (1,0,0), a = (0,1,0), c = (0,m,s), a' = (β6,m,s) (T: γ6 = 1), c' = (β1,α1,0), b' = (0,m,s+1)`;
`m > 1`, `s < 0`, `α1 = m (1 - β1)`, `0 < β1 < 1`.  Cycle `(d, b, a', c)`; tilt cone `v1 < 0 < v2`.
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- cycle `(d, b, a', c)` of K5e. -/
def kcCyc (m s β6 : ℝ) : ZMod 4 → ℝ × ℝ × ℝ := ![(0, 0, 0), (1, 0, 0), (β6, m, s), (0, m, s)]

theorem kcCyc_0 : kcCyc m s β6 0 = (0, 0, 0) := rfl
theorem kcCyc_1 : kcCyc m s β6 1 = (1, 0, 0) := rfl
theorem kcCyc_2 : kcCyc m s β6 2 = (β6, m, s) := rfl
theorem kcCyc_3 : kcCyc m s β6 3 = (0, m, s) := rfl

set_option maxHeartbeats 1600000 in
theorem kc_tsc {m s β6 β1 α1 v1 v2 : ℝ} (hm : 1 < m) (hs : s < 0) (hb6 : 0 < β6) (hβ1 : 0 < β1)
    (hβ11 : β1 < 1) (hα1 : α1 = m * (1 - β1)) (hv1 : v1 < 0) (hv2 : 0 < v2) :
    (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      TSc 1 (kcCyc m s β6 (i + 1) - kcCyc m s β6 i) (kcCyc m s β6 j - kcCyc m s β6 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (1 : ℝ), (0 : ℝ)), (β1, α1, 0), (0, m, s + 1)], ∀ i : ZMod 4,
      TSc 1 (kcCyc m s β6 (i + 1) - kcCyc m s β6 i) (t - kcCyc m s β6 i) (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3⟩ := z4_add
  subst hα1
  have m0 : 0 < m := by linarith
  have k1 := mul_pos m0 hb6
  have k2 := mul_pos hb6 (sub_pos.2 hm)
  have k3 := mul_pos m0 hβ1
  have k4 := mul_pos (mul_pos m0 hb6) (sub_pos.2 hβ11)
  have k5 := mul_pos (mul_pos m0 hβ1) hb6
  have k6 := mul_pos m0 (neg_pos.2 hv1)
  have k7 := mul_pos hb6 hv2
  have k8 := mul_pos (neg_pos.2 hs) (neg_pos.2 hv1)
  have k9 := mul_pos m0 (sub_pos.2 hβ11)
  have k10 := mul_pos (mul_pos m0 (sub_pos.2 hβ11)) hb6
  have k11 := mul_pos (sub_pos.2 hm) (neg_pos.2 hv1)
  have k12 := mul_pos (sub_pos.2 hm) hb6
  have k13 := mul_pos (mul_pos m0 (sub_pos.2 hβ11)) (sub_pos.2 hm)
  constructor
  · intro i j h1 h2
    rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      rcases z4_cases j with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, kcCyc_0, kcCyc_1, kcCyc_2, kcCyc_3, s0, s1, s2, s3, Prod.fst_sub, Prod.snd_sub,
          Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;>
      rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, kcCyc_0, kcCyc_1, kcCyc_2, kcCyc_3, s0, s1, s2, s3, Prod.fst_sub, Prod.snd_sub,
          Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))


theorem kc_inj {m s β6 : ℝ} (hm : 0 < m) (hb6 : 0 < β6) : ∀ i j : ZMod 4, kcCyc m s β6 i = kcCyc m s β6 j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  rcases z4_cases i with rfl | rfl | rfl | rfl <;> rcases z4_cases j with rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [kcCyc_0, kcCyc_1, kcCyc_2, kcCyc_3] at e1 e2; linarith)

/-- **K5e, `β1 < 1`: the face cell `Q_bc = (d, b, a', c)` at the base view `R`.** -/
theorem k5e_fcbc_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {m s β6 β1 α1 : ℝ}
    (hm : 1 < m) (hs : s < 0) (hb6 : 0 < β6) (hβ1 : 0 < β1) (hβ11 : β1 < 1) (hα1 : α1 = m * (1 - β1))
    (hmem : ∀ i, fpoint P Q R d (kcCyc m s β6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
      y = fpoint P Q R d (β6, m, s) ∨ y = fpoint P Q R d (0, m, s) ∨ y = fpoint P Q R d (0, 1, 0) ∨
      y = fpoint P Q R d (β1, α1, 0) ∨ y = fpoint P Q R d (0, m, s + 1)) :
    HasLexCellAt V R := by
  have m0 : 0 < m := by linarith
  refine fc_cell V P Q R d hΔ (kcCyc m s β6) (β := β6) (γ := 1) hb6 one_pos (by linarith) ?_
    (kc_inj m0 hb6) hmem [((0 : ℝ), (1 : ℝ), (0 : ℝ)), (β1, α1, 0), (0, m, s + 1)] ?_
    (u1 := -1) (u2 := 0) (t1 := 0) (t2 := 1) (lo := 0) (hi := 1) (by norm_num) (by norm_num)
    (fun v1 v2 => v1 < 0 ∧ 0 < v2) ?_ ?_
  · simp only [kcCyc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Prod.ext_iff]
    simp
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inl ⟨3, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam h0 h1; constructor <;> simp <;> linarith
  · intro v1 v2 ⟨hv1, hv2⟩
    exact kc_tsc hm hs hb6 hβ1 hβ11 hα1 hv1 hv2

end C2
end Type08Sp
end Minimality
