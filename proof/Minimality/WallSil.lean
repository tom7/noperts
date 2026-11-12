module

public import Minimality.WallView
public import Minimality.SilS0XB

@[expose] public section

/-!
# Lemma WV in silhouette form

* `isRupert_of_wallView_cw`: Lemma WV (`isRupert_of_wallView`) for a clockwise rim (all rim
  determinants negative), by the view `-n` and the rim restarted at the ceiling run.
* `isRupert_of_wallSil`: Lemma WV for a silhouette cycle given as `h21b_SilDataL` at `(u, 0)` (each
  rim edge between a facet facing `u` and one facing away, every other vertex strictly off one of
  them), in either orientation.  So a facing pattern and a combinatorial cycle (`S0xCycOK`-style
  data) plus the wall shape of the levels give Rupert, with no orientation bookkeeping.
-/

set_option autoImplicit false

namespace Minimality

open scoped RealInnerProductSpace
open Finset

theorem wsil_inn3 (a b : ℝ³) : ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]; ring

theorem wsil_det3_neg (a b c : ℝ³) : det3 a b (-c) = -det3 a b c := by
  simp only [det3, inner_neg_right]

/-- `det3 (μ • (A × B)) w u = μ (⟪A, w⟫ ⟪B, u⟫ - ⟪B, w⟫ ⟪A, u⟫)`. -/
theorem wsil_det3_cross (μ : ℝ) (A B w u : ℝ³) :
    det3 (μ • cross A B) w u = μ * (⟪A, w⟫ * ⟪B, u⟫ - ⟪B, w⟫ * ⟪A, u⟫) := by
  simp only [det3, wsil_inn3, cross, PiLp.smul_apply, smul_eq_mul]
  simp
  ring

/-- **Lemma WV, clockwise form**: as `isRupert_of_wallView` with all rim determinants negative.
The view `-n` and the rim started at the ceiling run turn it into the counterclockwise form. -/
theorem isRupert_of_wallView_cw (V : Finset ℝ³) (n : ℝ³) (hn : n ≠ 0) {k : ℕ} [NeZero k]
    (hk : 3 ≤ k) (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → det3 (x (i + 1) - x i) (x j - x i) n < 0)
    (hrest : ∀ y ∈ V, (∀ j, y ≠ x j) → ∀ i, det3 (x (i + 1) - x i) (y - x i) n < 0)
    {s r r' : ℕ} (hS : WallShape (fun i => ⟪x i, n⟫) s r r') : IsRupert V := by
  obtain ⟨hsr, hrr, hrk, hfl, hri, hce, hfa⟩ := hS
  set R : ZMod k := (r : ZMod k)
  -- levels of the rotated list along `-n`, through the ℕ-indexed levels `g`
  set g : ℕ → ℝ := fun m => ⟪x (m : ZMod k), n⟫ with hg
  have hgk : ∀ m, g (m + k) = g m := by intro m; simp [hg]
  have hl : ∀ t : ℕ, ⟪x ((t : ZMod k) + R), -n⟫ = - g (t + r) := by
    intro t; simp [hg, R, inner_neg_right]
  have hl1 : ∀ t : ℕ, ⟪x (((t : ZMod k) + 1) + R), -n⟫ = - g (t + 1 + r) := by
    intro t; simpa using hl (t + 1)
  refine isRupert_of_wallView V (-n) (neg_ne_zero.2 hn) hk (fun i => x (i + R))
    (fun i => hxV _) ?_ ?_ (s := r' - r) (r := k - r) (r' := k - r + s) ?_
  · intro i j hj hj'
    have := hcyc (i + R) (j + R) (fun h => hj (add_right_cancel h))
      (fun h => hj' (by rw [add_right_comm] at h; exact add_right_cancel h))
    rw [show i + 1 + R = i + R + 1 by ring, wsil_det3_neg]; linarith
  · intro y hy hyx i
    have := hrest y hy (fun j h => hyx (j - R) (by simpa using h)) (i + R)
    rw [show i + 1 + R = i + R + 1 by ring, wsil_det3_neg]; linarith
  · refine ⟨by omega, by omega, by omega, ?_, ?_, ?_, ?_⟩
    · intro t ht
      rw [hl, hl1, show t + 1 + r = t + r + 1 by ring]
      have := hce (t + r) (by omega) (by omega)
      simp only [hg]; push_cast at this ⊢; linarith
    · intro t ht1 ht2
      rw [hl, hl1, show t + 1 + r = t + r + 1 by ring]
      by_cases hlast : t + r + 1 = k
      · have := hfa (t + r) (by omega) (by omega)
        simp only [hg]; push_cast at this ⊢; linarith
      · have := hfa (t + r) (by omega) (by omega)
        simp only [hg]; push_cast at this ⊢; linarith
    · intro t ht1 ht2
      rw [hl, hl1]
      have e1 : t + r = (t + r - k) + k := by omega
      have e2 : t + 1 + r = (t + r - k + 1) + k := by omega
      rw [e1, e2, hgk, hgk]
      have := hfl (t + r - k) (by omega)
      simp only [hg]; push_cast at this ⊢; linarith
    · intro t ht1 ht2
      rw [hl, hl1]
      have e1 : t + r = (t + r - k) + k := by omega
      have e2 : t + 1 + r = (t + r - k + 1) + k := by omega
      rw [e1, e2, hgk, hgk]
      have := hri (t + r - k) (by omega) (by omega)
      simp only [hg]; push_cast at this ⊢; linarith

/-- **Lemma WV from silhouette data.**  A cycle `c` of edges, each between a facet facing `u` and
one facing away (`h21b_SilDataL` at `(u, 0)`: strict facings, every other vertex strictly off one
of the two facets), whose levels `⟪x (c i), u⟫` have the wall shape.  Either orientation. -/
theorem isRupert_of_wallSil {n k : ℕ} [NeZero k] (hk : 3 ≤ k) {x : Fin n → ℝ³}
    (hx : Function.Injective x) {c : ZMod k → Fin n} (hc : Function.Injective c) {u : ℝ³}
    (hu : u ≠ 0) (D : H21.h21b_SilDataL k x c u 0) {s r r' : ℕ}
    (hS : WallShape (fun i => ⟪x (c i), u⟫) s r r') : IsRupert (univ.image x) := by
  choose μ hμ0 hd using H21.h21b_exists_mu hk hx hc D
  have hQ : ∀ i m, m ≠ c i → m ≠ c (i + 1) →
      0 < D.fA i (x m) * ⟪D.B i, u⟫ - D.fB i (x m) * ⟪D.A i, u⟫ := by
    intro i m h0 h1
    rcases H21.h21b_Q_pos D i m h0 h1 with h | ⟨_, h⟩
    · exact h
    · simp at h
  have hdet : ∀ i m, det3 (x (c (i + 1)) - x (c i)) (x m - x (c i)) u =
      μ i * (D.fA i (x m) * ⟪D.B i, u⟫ - D.fB i (x m) * ⟪D.A i, u⟫) := by
    intro i m
    rw [hd i, wsil_det3_cross]
    have ea : ⟪D.A i, x m - x (c i)⟫ = D.fA i (x m) := by
      rw [← D.hA i, D.zA0 i, sub_zero]
    have eb : ⟪D.B i, x m - x (c i)⟫ = D.fB i (x m) := by
      rw [← D.hB i, D.zB0 i, sub_zero]
    rw [ea, eb]
  have hoff : ∀ y ∈ univ.image x, (∀ j, y ≠ x (c j)) → ∃ m, y = x m ∧ ∀ j, m ≠ c j := by
    intro y hy hyx
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 hy
    exact ⟨m, rfl, fun j h => hyx j (by rw [h])⟩
  have hne : ∀ i j : ZMod k, j ≠ i → c j ≠ c i := fun i j h e => h (hc e)
  rcases H21.h21b_sign_agree hk hx hc D μ hμ0 hd with hp | hn
  · refine isRupert_of_wallView _ u hu hk (fun i => x (c i)) (fun i => mem_image_of_mem _ (mem_univ _))
      ?_ ?_ hS
    · intro i j hj hj'
      rw [hdet]; exact mul_pos (hp i) (hQ i _ (hne i j hj) (hne (i + 1) j hj'))
    · intro y hy hyx i
      obtain ⟨m, rfl, hm⟩ := hoff y hy hyx
      rw [hdet]; exact mul_pos (hp i) (hQ i m (hm i) (hm (i + 1)))
  · refine isRupert_of_wallView_cw _ u hu hk (fun i => x (c i))
      (fun i => mem_image_of_mem _ (mem_univ _)) ?_ ?_ hS
    · intro i j hj hj'
      rw [hdet]; exact mul_neg_of_neg_of_pos (hn i) (hQ i _ (hne i j hj) (hne (i + 1) j hj'))
    · intro y hy hyx i
      obtain ⟨m, rfl, hm⟩ := hoff y hy hyx
      rw [hdet]; exact mul_neg_of_neg_of_pos (hn i) (hQ i m (hm i) (hm (i + 1)))

end Minimality
