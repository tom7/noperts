module

public import Minimality.Type08S.C2K17GD4A

@[expose] public section


/-!
# K17GD / GD4: the slice `K14TaC` (Ta box C: `α4 < 1`, `β1 > 1`, `β6 > 1`, `D_c = ⟪b-d,c-d⟫ = 0`), generic part `⟪a-d,b-d⟫ ≠ 0`

`p,q,r = a-d,b-d,c-d`, `⟪q,r⟫ = 0`; `γ4 > 1` from `κ_a = 0`.
* `⟪p,q⟫ < 0` (`ζ(a,d) > 0`): cell C1 `(a,c',a',b,d)` at `r`; cone only `v1, v2 < 0` (`α4 < 1`: `b'` is on the edge `d a`);
  the depth tie `z(b) = z(d)` is broken by the tilt `(-1, -λ δ0)`, `δ0 = -⟪p,q⟫/⟪q,q⟫`: `w(b) > w(d)` and `w(a) < w(d)` (Cauchy-Schwarz).
* `⟪p,q⟫ > 0`: cell D `(a,c',b',c,d)` at `q` (frame `(p,r,q)`); `c'` is the unique depth peak, no tie matters.
* Leftover `⟪p,q⟫ = 0` (= `ζ(a,d) = 0`, the S1.8 tie).
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

set_option maxHeartbeats 3200000 in
theorem k17gdC1b_frame (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0) {α1 β1 β6 α4 γ4 : ℝ}
    (hα1 : 1 < α1) (hβ1 : 0 < β1) (hβ6 : 1 < β6) (hα4 : 0 < α4) (hα41 : α4 < 1) (hγ4 : 0 < γ4)
    (hqr : ⟪q, r⟫ = 0) (hpq : ⟪p, q⟫ < 0)
    (hmem : ∀ i, fpoint p q r d (k17gdC1 α1 β1 β6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint p q r d (1, 0, 0) ∨ y = fpoint p q r d (α1, β1, 0) ∨
      y = fpoint p q r d (0, β6, 1) ∨ y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (0, 0, 0) ∨
      y = fpoint p q r d (0, 0, 1) ∨ y = fpoint p q r d (α4, 0, γ4)) :
    HasLexCellAt V r := by
  have hr0 : r ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hq0 : q ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hp0 : p ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hA : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  have hqq : 0 < ⟪q, q⟫ := real_inner_self_pos.2 hq0
  have hpp : 0 < ⟪p, p⟫ := real_inner_self_pos.2 hp0
  have hcs := real_inner_mul_inner_self_le p q
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint p q r d t, r⟫ = ⟪d, r⟫ + t.1 * ⟪p, r⟫ + t.2.1 * ⟪q, r⟫ + t.2.2 * ⟪r, r⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have a1 := sub_pos.2 hα1
  obtain ⟨δ0, hδ0⟩ : ∃ δ0 : ℝ, δ0 * ⟪q, q⟫ = -⟪p, q⟫ := ⟨-⟪p, q⟫ / ⟪q, q⟫, by field_simp⟩
  have hδpos : 0 < δ0 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg (neg_nonneg.2 hh) hqq.le]
  have hinj : ∀ i j, k17gdC1 α1 β1 β6 i = k17gdC1 α1 β1 β6 j → i = j := by
    intro i j h
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      simp only [k17gdC1, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4, Prod.mk.injEq] at h <;>
      first | rfl | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h) |
        (exfalso; obtain ⟨h1, h2, h3⟩ := h; nlinarith)
  refine cyc_cell V p q r d hΔ (k := 5) (by norm_num) (k17gdC1 α1 β1 β6) hinj hmem
    [(0, 0, 1), (α4, 0, γ4)] ?_ (u1 := -1) (u2 := 0) (t1 := 0) (t2 := -δ0) (lo := 0) (hi := 1)
    (by rw [show (-1:ℝ) * (-δ0) - 0 * 0 = δ0 by ring]; exact hδpos.ne') (by norm_num)
    (fun v1 v2 => v1 = -1 ∧ -δ0 < v2 ∧ v2 < 0) ?_ ?_ ?_
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by simp [k17gdC1, pc5_0]⟩
    · exact Or.inl ⟨1, by simp [k17gdC1, pc5_1]⟩
    · exact Or.inl ⟨2, by simp [k17gdC1, pc5_2]⟩
    · exact Or.inl ⟨3, by simp [k17gdC1, pc5_3]⟩
    · exact Or.inl ⟨4, by simp [k17gdC1, pc5_4]⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam hl0 hl1
    refine ⟨by ring, by nlinarith, by nlinarith⟩
  · intro v1 v2 hv
    obtain ⟨h1, h2, h3⟩ := hv
    have hv1 : v1 < 0 := by rw [h1]; norm_num
    refine ⟨k17gdC1b_tsc hα1 hβ1 hβ6 hv1 h3, ?_⟩
    intro t ht i
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact (k17gdC1b_rest hα1 hβ1 hβ6 hα4 hα41 hγ4 hv1 h3).1 i
    · exact (k17gdC1b_rest hα1 hβ1 hβ6 hα4 hα41 hγ4 hv1 h3).2 i
  · intro v1 v2 hv hsep
    obtain ⟨h1, h2, h3⟩ := hv
    set z : ZMod 5 → ℝ := fun i => ⟪fpoint p q r d (k17gdC1 α1 β1 β6 i), r⟫ with hzdef
    set w : ZMod 5 → ℝ := fun i => ⟪fpoint p q r d (k17gdC1 α1 β1 β6 i), fcomb p q r v1 v2 0⟫ with hwdef
    have z0 : z 0 = ⟪d, r⟫ + ⟪p, r⟫ := by simp only [hzdef, k17gdC1, pc5_0, hz]; ring
    have z1 : z 1 = ⟪d, r⟫ + α1 * ⟪p, r⟫ + β1 * ⟪q, r⟫ := by simp only [hzdef, k17gdC1, pc5_1, hz]; ring
    have z2 : z 2 = ⟪d, r⟫ + β6 * ⟪q, r⟫ + ⟪r, r⟫ := by simp only [hzdef, k17gdC1, pc5_2, hz]; ring
    have z3 : z 3 = ⟪d, r⟫ + ⟪q, r⟫ := by simp only [hzdef, k17gdC1, pc5_3, hz]; ring
    have z4 : z 4 = ⟪d, r⟫ := by simp only [hzdef, k17gdC1, pc5_4, hz]; ring
    have w0 : w 0 = v1 * (⟪d, p⟫ + ⟪p, p⟫) + v2 * (⟪d, q⟫ + ⟪p, q⟫) := by
      simp only [hwdef, k17gdC1, pc5_0, k17f_wexp]; ring
    have w3 : w 3 = v1 * (⟪d, p⟫ + ⟪p, q⟫) + v2 * (⟪d, q⟫ + ⟪q, q⟫) := by
      simp only [hwdef, k17gdC1, pc5_3, k17f_wexp]; ring
    have w4 : w 4 = v1 * ⟪d, p⟫ + v2 * ⟪d, q⟫ := by
      simp only [hwdef, k17gdC1, pc5_4, k17f_wexp]; ring
    have hwb : w 4 < w 3 := by
      rw [w3, w4, h1]; nlinarith
    have hwa : w 0 < w 4 := by
      rw [w0, w4, h1]
      have : v2 * ⟪p, q⟫ < δ0 * (-⟪p, q⟫) := by nlinarith
      nlinarith
    have h43 : LexLt (z 4, w 4) (z 3, w 3) := k17gd_ll' (by rw [z4, z3, hqr]; ring) hwb
    have h32 : LexLt (z 3, w 3) (z 2, w 2) := k17gd_ll (by rw [z3, z2, hqr]; linarith)
    have h0 : LexLt (z 0, w 0) (z 4, w 4) ∨ LexLt (z 0, w 0) (z 1, w 1) := by
      rcases lt_trichotomy ⟪p, r⟫ 0 with hp | hp | hp
      · left; exact k17gd_ll (by rw [z0, z4]; linarith)
      · left; exact k17gd_ll' (by rw [z0, z4, hp]; ring) hwa
      · right; exact k17gd_ll (by rw [z0, z1, hqr]; nlinarith)
    exact k17gd_lexUni5_A z w hsep h32 h43 h0

set_option maxHeartbeats 3200000 in
theorem k17gdD_frame (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p r q ≠ 0) {α1 β1 α4 γ4 β6 : ℝ}
    (hα1 : 1 < α1) (hβ1 : 0 < β1) (hα4 : 0 < α4) (hα41 : α4 < 1) (hγ4 : 1 < γ4) (hβ6 : 1 < β6)
    (hqr : ⟪r, q⟫ = 0) (hpq : 0 < ⟪p, q⟫)
    (hmem : ∀ i, fpoint p r q d (k17gdD α1 β1 α4 γ4 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint p r q d (1, 0, 0) ∨ y = fpoint p r q d (α1, 0, β1) ∨
      y = fpoint p r q d (α4, γ4, 0) ∨ y = fpoint p r q d (0, 1, 0) ∨ y = fpoint p r q d (0, 0, 0) ∨
      y = fpoint p r q d (0, 0, 1) ∨ y = fpoint p r q d (0, 1, β6)) :
    HasLexCellAt V q := by
  have hq0 : q ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hqq : 0 < ⟪q, q⟫ := real_inner_self_pos.2 hq0
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint p r q d t, q⟫ = ⟪d, q⟫ + t.1 * ⟪p, q⟫ + t.2.1 * ⟪r, q⟫ + t.2.2 * ⟪q, q⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have a5 := sub_pos.2 hγ4
  obtain ⟨t2, ht2def⟩ : ∃ t2 : ℝ, t2 = (γ4 - 1) / (α4 + γ4) := ⟨_, rfl⟩
  have hden : 0 < α4 + γ4 := by linarith
  have ht2 : 0 < t2 := by rw [ht2def]; exact div_pos a5 hden
  have ht2e : t2 * (α4 + γ4) = γ4 - 1 := by rw [ht2def]; field_simp
  have hinj : ∀ i j, k17gdD α1 β1 α4 γ4 i = k17gdD α1 β1 α4 γ4 j → i = j := by
    intro i j h
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      simp only [k17gdD, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4, Prod.mk.injEq] at h <;>
      first | rfl | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h) |
        (exfalso; obtain ⟨h1, h2, h3⟩ := h; nlinarith)
  refine cyc_cell V p r q d hΔ (k := 5) (by norm_num) (k17gdD α1 β1 α4 γ4) hinj hmem
    [(0, 0, 1), (0, 1, β6)] ?_ (u1 := -1) (u2 := 0) (t1 := 0) (t2 := -t2) (lo := 0) (hi := 1)
    (by rw [show (-1:ℝ) * (-t2) - 0 * 0 = t2 by ring]; exact ht2.ne') (by norm_num)
    (fun v1 v2 => v1 = -1 ∧ -t2 < v2 ∧ v2 < 0) ?_ ?_ ?_
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by simp [k17gdD, pc5_0]⟩
    · exact Or.inl ⟨1, by simp [k17gdD, pc5_1]⟩
    · exact Or.inl ⟨2, by simp [k17gdD, pc5_2]⟩
    · exact Or.inl ⟨3, by simp [k17gdD, pc5_3]⟩
    · exact Or.inl ⟨4, by simp [k17gdD, pc5_4]⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam hl0 hl1
    refine ⟨by ring, by nlinarith, by nlinarith⟩
  · intro v1 v2 hv
    obtain ⟨h1, h2, h3⟩ := hv
    have hv1 : v1 < 0 := by rw [h1]; norm_num
    have hc : 0 < -(γ4 - 1) * v1 + α4 * v2 := by rw [h1]; nlinarith
    refine ⟨k17gdD_tsc hα1 hβ1 hα4 hα41 hγ4 hv1 h3 hc, ?_⟩
    intro t ht i
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact (k17gdD_rest hα1 hβ1 hα4 hα41 hγ4 hβ6 hv1 h3 hc).1 i
    · exact (k17gdD_rest hα1 hβ1 hα4 hα41 hγ4 hβ6 hv1 h3 hc).2 i
  · intro v1 v2 hv hsep
    set z : ZMod 5 → ℝ := fun i => ⟪fpoint p r q d (k17gdD α1 β1 α4 γ4 i), q⟫ with hzdef
    set w : ZMod 5 → ℝ := fun i => ⟪fpoint p r q d (k17gdD α1 β1 α4 γ4 i), fcomb p r q v1 v2 0⟫ with hwdef
    have z0 : z 0 = ⟪d, q⟫ + ⟪p, q⟫ := by simp only [hzdef, k17gdD, pc5_0, hz]; ring
    have z1 : z 1 = ⟪d, q⟫ + α1 * ⟪p, q⟫ + β1 * ⟪q, q⟫ := by simp only [hzdef, k17gdD, pc5_1, hz]; ring
    have z2 : z 2 = ⟪d, q⟫ + α4 * ⟪p, q⟫ + γ4 * ⟪r, q⟫ := by simp only [hzdef, k17gdD, pc5_2, hz]; ring
    have z3 : z 3 = ⟪d, q⟫ + ⟪r, q⟫ := by simp only [hzdef, k17gdD, pc5_3, hz]; ring
    have z4 : z 4 = ⟪d, q⟫ := by simp only [hzdef, k17gdD, pc5_4, hz]; ring
    obtain ⟨t0, t1', t2', t3, t4, s0, s1, s2, s3, s4⟩ := k17gd_z5
    refine k17gd_lexUni_nb z w hsep 1 (by rw [t1', s1]; exact ⟨k17gd_ll (by rw [z0, z1]; nlinarith), k17gd_ll (by rw [z2, z1]; nlinarith)⟩) (fun i hi => ?_)
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · rw [s0]; right; exact k17gd_ll (by rw [z0, z1]; nlinarith)
    · exact absurd rfl hi
    · rw [t2']; left; exact k17gd_ll (by rw [z2, z1]; nlinarith)
    · rw [t3]; left; exact k17gd_ll (by rw [z3, z2, hqr]; nlinarith)
    · rw [s4]; right; exact k17gd_ll (by rw [z4, z0]; linarith)

end C2
end Type08Sp
end Minimality
