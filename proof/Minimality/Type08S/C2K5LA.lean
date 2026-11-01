module

public import Minimality.Type08S.C2FC1
public import Minimality.Type08S.C2FA3

@[expose] public section


/-!
# K5L / A: a generic planar-quad face cell (frame form, arbitrary third coordinates)

`fc_cell`: a cycle `X : ZMod 4 → ℝ×ℝ×ℝ` of frame points with `X 2 - X 0 = β (X 1 - X 0) + γ (X 3 - X 0)`
(`β, γ > 0`, `β + γ > 1`: convex face, affine depth and tilt), a segment of tilts `(u1 + λ t1, u2 + λ t2, 0)` all in
a cone `C` on which the `TSc` tests (stated with `D = 1`) hold; handles both signs of `det3 p q r`.
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem tsc_scale {D : ℝ} (hD : 0 < D) {e f v : ℝ × ℝ × ℝ} (h : TSc 1 e f v) : TSc D e f v := by
  unfold TSc at h ⊢
  rcases h with h | ⟨h1, h2⟩
  · left; rw [one_mul] at h; exact mul_pos hD h
  · right; rw [one_mul] at h1 h2; exact ⟨by rw [h1]; ring, mul_pos hD h2⟩

theorem inner_fpoint_rel (p q r d w : ℝ³) (X : ZMod 4 → ℝ × ℝ × ℝ) {β γ : ℝ}
    (hrel : X 2 - X 0 = β • (X 1 - X 0) + γ • (X 3 - X 0)) :
    ⟪fpoint p q r d (X 2), w⟫ - ⟪fpoint p q r d (X 0), w⟫ =
      β * (⟪fpoint p q r d (X 1), w⟫ - ⟪fpoint p q r d (X 0), w⟫) +
        γ * (⟪fpoint p q r d (X 3), w⟫ - ⟪fpoint p q r d (X 0), w⟫) := by
  have h1 := congrArg Prod.fst hrel
  have h2 := congrArg (fun t => t.2.1) hrel
  have h3 := congrArg (fun t => t.2.2) hrel
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
    smul_eq_mul] at h1 h2 h3
  simp only [inner_fpoint]
  linear_combination ⟪p, w⟫ * h1 + ⟪q, w⟫ * h2 + ⟪r, w⟫ * h3

theorem fc_cell (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0) (X : ZMod 4 → ℝ × ℝ × ℝ)
    {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (hs : 1 < β + γ)
    (hrel : X 2 - X 0 = β • (X 1 - X 0) + γ • (X 3 - X 0))
    (hX : ∀ i j, X i = X j → i = j) (hmem : ∀ i, fpoint p q r d (X i) ∈ V)
    (O : List (ℝ × ℝ × ℝ))
    (hVall : ∀ y ∈ V, (∃ i, y = fpoint p q r d (X i)) ∨ ∃ t ∈ O, y = fpoint p q r d t)
    {u1 u2 t1 t2 lo hi : ℝ} (hut : u1 * t2 - u2 * t1 ≠ 0) (hlh : lo < hi)
    (C : ℝ → ℝ → Prop) (hC : ∀ lam, lo < lam → lam < hi → C (u1 + lam * t1) (u2 + lam * t2))
    (hT : ∀ v1 v2, C v1 v2 →
      (∀ i j, j ≠ i → j ≠ i + 1 → TSc 1 (X (i + 1) - X i) (X j - X i) (v1, v2, 0)) ∧
      (∀ t ∈ O, ∀ i, TSc 1 (X (i + 1) - X i) (t - X i) (v1, v2, 0))) :
    HasLexCellAt V r := by
  obtain ⟨lam, hl0, hl1, hL⟩ := exists_sep_tilt p q r d hΔ X hX hut hlh
  set v1 := u1 + lam * t1
  set v2 := u2 + lam * t2
  obtain ⟨hcy, hre⟩ := hT v1 v2 (hC lam hl0 hl1)
  have hlex : LexUni (fun i => ⟪fpoint p q r d (X i), r⟫)
      (fun i => ⟪fpoint p q r d (X i), fcomb p q r v1 v2 0⟫) := by
    refine lexUni4_conv _ _ hβ hγ hs (inner_fpoint_rel p q r d r X hrel)
      (inner_fpoint_rel p q r d _ X hrel) ?_
    intro i j h1 h2
    exact hL i j h1 h2
  have hΔ' : ∀ D, 0 < D → True := fun _ _ => trivial
  rcases hΔ.lt_or_gt with hneg | hpos
  · have hD : 0 < -det3 p q r := by linarith
    refine ⟨4, inferInstance, fun i => fpoint p q r d (X (-i)), fcomb p q r v1 v2 0, ?_⟩
    have := lexCell_coord V p q r d (k := 4) (by norm_num) (fun i => X (-i)) (v1, v2, 0)
      (fun i => hmem (-i))
      (hcyc_rev (fun i j h1 h2 => tsc_scale hD (hcy i j h1 h2))) ?_ (lexUni_neg hlex)
    · simpa using this
    · intro y hy hyx
      rcases hVall y hy with ⟨i, rfl⟩ | ⟨t, ht, rfl⟩
      · exact (hyx (-i) (by simp)).elim
      · exact ⟨t, rfl, hrest_rev (fun i => tsc_scale hD (hre t ht i))⟩
  · refine ⟨4, inferInstance, fun i => fpoint p q r d (X i), fcomb p q r v1 v2 0, ?_⟩
    have := lexCell_coord V p q r d (k := 4) (by norm_num) X (v1, v2, 0) hmem
      (fun i j h1 h2 => tsc_scale hpos (hcy i j h1 h2)) ?_ hlex
    · simpa using this
    · intro y hy hyx
      rcases hVall y hy with ⟨i, rfl⟩ | ⟨t, ht, rfl⟩
      · exact (hyx i rfl).elim
      · exact ⟨t, rfl, fun i => tsc_scale hpos (hre t ht i)⟩

end C2
end Type08Sp
end Minimality
