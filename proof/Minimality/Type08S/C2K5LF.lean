module

public import Minimality.Type08S.C2K5LE

@[expose] public section


/-!
# K5L / F: generic cycle cell + the K5e pentagon `(a, d, c, a', c')` at `b' - c` (frame form, `β1 > 1`)

Frame `(P,Q,R) = (b - d, a - d, b' - c)`; points over `d`:
`d = 0, b = (1,0,0), a = (0,1,0), c = (0,m,s), a' = (β6,m,s), c' = (β1,α1,0), b' = (0,m,s+1)`,
`m < 0`, `s > 0`, `α1 = m (1 - β1)`, `β1 > 1`, `α1 ≥ 1`.  Metric: `⟪P,R⟫ = 0` (`b'-c ⟂ b-d`), `⟪P,Q⟫ < 0`.
Cone: `v1 < 0, v2 < 0, ⟪P, v⟫ > 0`.
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

theorem cyc_cell (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (X : ZMod k → ℝ × ℝ × ℝ) (hX : ∀ i j, X i = X j → i = j) (hmem : ∀ i, fpoint p q r d (X i) ∈ V)
    (O : List (ℝ × ℝ × ℝ))
    (hVall : ∀ y ∈ V, (∃ i, y = fpoint p q r d (X i)) ∨ ∃ t ∈ O, y = fpoint p q r d t)
    {u1 u2 t1 t2 lo hi : ℝ} (hut : u1 * t2 - u2 * t1 ≠ 0) (hlh : lo < hi)
    (C : ℝ → ℝ → Prop) (hC : ∀ lam, lo < lam → lam < hi → C (u1 + lam * t1) (u2 + lam * t2))
    (hT : ∀ v1 v2, C v1 v2 →
      (∀ i j, j ≠ i → j ≠ i + 1 → TSc 1 (X (i + 1) - X i) (X j - X i) (v1, v2, 0)) ∧
      (∀ t ∈ O, ∀ i, TSc 1 (X (i + 1) - X i) (t - X i) (v1, v2, 0)))
    (hlex : ∀ v1 v2, C v1 v2 →
      (∀ i j, ⟪fpoint p q r d (X i), r⟫ = ⟪fpoint p q r d (X j), r⟫ →
        ⟪fpoint p q r d (X i), fcomb p q r v1 v2 0⟫ = ⟪fpoint p q r d (X j), fcomb p q r v1 v2 0⟫ → i = j) →
      LexUni (fun i => ⟪fpoint p q r d (X i), r⟫) (fun i => ⟪fpoint p q r d (X i), fcomb p q r v1 v2 0⟫)) :
    HasLexCellAt V r := by
  obtain ⟨lam, hl0, hl1, hL⟩ := exists_sep_tilt p q r d hΔ X hX hut hlh
  set v1 := u1 + lam * t1
  set v2 := u2 + lam * t2
  have hCv := hC lam hl0 hl1
  obtain ⟨hcy, hre⟩ := hT v1 v2 hCv
  have hlex' := hlex v1 v2 hCv hL
  rcases hΔ.lt_or_gt with hneg | hpos
  · have hD : 0 < -det3 p q r := by linarith
    refine ⟨k, inferInstance, fun i => fpoint p q r d (X (-i)), fcomb p q r v1 v2 0, ?_⟩
    have := lexCell_coord V p q r d (k := k) hk (fun i => X (-i)) (v1, v2, 0)
      (fun i => hmem (-i))
      (hcyc_rev (fun i j h1 h2 => tsc_scale hD (hcy i j h1 h2))) ?_ (lexUni_neg hlex')
    · simpa using this
    · intro y hy hyx
      rcases hVall y hy with ⟨i, rfl⟩ | ⟨t, ht, rfl⟩
      · exact (hyx (-i) (by simp)).elim
      · exact ⟨t, rfl, hrest_rev (fun i => tsc_scale hD (hre t ht i))⟩
  · refine ⟨k, inferInstance, fun i => fpoint p q r d (X i), fcomb p q r v1 v2 0, ?_⟩
    have := lexCell_coord V p q r d (k := k) hk X (v1, v2, 0) hmem
      (fun i j h1 h2 => tsc_scale hpos (hcy i j h1 h2)) ?_ hlex'
    · simpa using this
    · intro y hy hyx
      rcases hVall y hy with ⟨i, rfl⟩ | ⟨t, ht, rfl⟩
      · exact (hyx i rfl).elim
      · exact ⟨t, rfl, fun i => tsc_scale hpos (hre t ht i)⟩

/-- cycle `(a, d, c, a', c')` of K5e (`β1 > 1`). -/
def kpCyc (m s β6 β1 α1 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  ![(0, 1, 0), (0, 0, 0), (0, m, s), (β6, m, s), (β1, α1, 0)]

theorem kpCyc_0 : kpCyc m s β6 β1 α1 0 = (0, 1, 0) := rfl
theorem kpCyc_1 : kpCyc m s β6 β1 α1 1 = (0, 0, 0) := rfl
theorem kpCyc_2 : kpCyc m s β6 β1 α1 2 = (0, m, s) := rfl
theorem kpCyc_3 : kpCyc m s β6 β1 α1 3 = (β6, m, s) := rfl
theorem kpCyc_4 : kpCyc m s β6 β1 α1 4 = (β1, α1, 0) := rfl

set_option maxHeartbeats 3200000 in
theorem kp_tsc {m s β6 β1 α1 v1 v2 : ℝ} (hm : m < 0) (hs : 0 < s) (hb6 : 0 < β6) (hβ1 : 1 < β1)
    (hα1 : α1 = m * (1 - β1)) (hα11 : 1 ≤ α1) (hv1 : v1 < 0) (hv2 : v2 < 0) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (kpCyc m s β6 β1 α1 (i + 1) - kpCyc m s β6 β1 α1 i) (kpCyc m s β6 β1 α1 j - kpCyc m s β6 β1 α1 i)
        (v1, v2, 0)) ∧
    (∀ t ∈ [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, m, s + 1)], ∀ i : ZMod 5,
      TSc 1 (kpCyc m s β6 β1 α1 (i + 1) - kpCyc m s β6 β1 α1 i) (t - kpCyc m s β6 β1 α1 i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have nm : 0 < -m := by linarith
  have hb1 : 0 < β1 - 1 := by linarith
  have k1 := mul_pos nm hb6
  have k2 := mul_pos hb6 hs
  have k3 := mul_pos nm hb1
  have k4 := mul_pos hs (neg_pos.2 hv1)
  have k5 := mul_pos nm (neg_pos.2 hv1)
  have k6 := mul_pos hb6 (neg_pos.2 hv2)
  have k7 := mul_pos (mul_pos nm hb6) hb1
  have k9 := mul_nonneg hb6.le (sub_nonneg.2 hα11)
  have k10 : 0 < β1 * (1 - m) := mul_pos (by linarith) (by linarith)
  have k11 : 0 < β1 * (-m) := mul_pos (by linarith) nm
  have k12 : 0 < (α1 - m) * β6 := mul_pos (by linarith) hb6
  have k13 : 0 < β6 * α1 := mul_pos hb6 (by linarith)
  have k14 : 0 < (s + 1) * (-v1) := mul_pos (by linarith) (neg_pos.2 hv1)
  have k15 : 0 < β1 * (1 - α1 - m + α1) := mul_pos (by linarith) (by linarith)
  constructor
  · intro i j h1 h2
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, kpCyc_0, kpCyc_1, kpCyc_2, kpCyc_3, kpCyc_4, f0, f1, f2, f3, f4, Prod.fst_sub,
          Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, kpCyc_0, kpCyc_1, kpCyc_2, kpCyc_3, kpCyc_4, f0, f1, f2, f3, f4, Prod.fst_sub,
          Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
