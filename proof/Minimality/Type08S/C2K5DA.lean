module

public import Minimality.Type08S.C2K5LP

@[expose] public section


/-!
# K5d / A: engine for the K5d cells (QPa, QTT)

* `k5d_exists_key`, `k5d_lex_of_real`: scalar key `M z + w` transfers lex unimodality.
* `k5d_uni_of_nopair`: a real cyclic sequence with no two non-adjacent peaks is unimodal.
* `k5d_cell`: generic cycle cell whose lex part is a *real* statement about the key
  `k0 + x U + y T + z B` of the frame points (key forward-monotone w.r.t. strict depth comparisons).
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

theorem k5d_exists_key {ι : Type*} (Z : ι → ℝ × ℝ) (L : List ι) :
    ∃ M : ℝ, ∀ s ∈ L, ∀ t ∈ L, LexLt (Z s) (Z t) →
      M * (Z s).1 + (Z s).2 < M * (Z t).1 + (Z t).2 := by
  classical
  have one : ∀ i j : ι, ∀ᶠ M in atTop, LexLt (Z i) (Z j) → M * (Z i).1 + (Z i).2 < M * (Z j).1 + (Z j).2 := by
    intro i j
    rcases lt_trichotomy (Z i).1 (Z j).1 with h | h | h
    · filter_upwards [eventually_gt_atTop (((Z i).2 - (Z j).2) / ((Z j).1 - (Z i).1))] with M hM
      intro _
      have hz : 0 < (Z j).1 - (Z i).1 := by linarith
      rw [div_lt_iff₀ hz] at hM
      nlinarith
    · exact Eventually.of_forall fun M hl => by
        rcases hl with hl | ⟨-, hl⟩
        · exact absurd h (ne_of_lt hl)
        · rw [h]; linarith
    · exact Eventually.of_forall fun M hl => by
        rcases hl with hl | ⟨hl, -⟩ <;> linarith
  have hall : ∀ᶠ M in atTop, ∀ s ∈ L.toFinset, ∀ t ∈ L.toFinset,
      LexLt (Z s) (Z t) → M * (Z s).1 + (Z s).2 < M * (Z t).1 + (Z t).2 := by
    rw [Filter.eventually_all_finset]; intro s _
    rw [Filter.eventually_all_finset]; intro t _
    exact one s t
  obtain ⟨M, hM⟩ := hall.exists
  exact ⟨M, fun s hs t ht => hM s (List.mem_toFinset.2 hs) t (List.mem_toFinset.2 ht)⟩

theorem k5d_lex_of_real {k : ℕ} [NeZero k] (z w : ZMod k → ℝ)
    (hinj : ∀ i j, z i = z j → w i = w j → i = j) (M : ℝ)
    (hM : ∀ i j, LexLt (z i, w i) (z j, w j) → M * z i + w i < M * z j + w j)
    (h : LexUni (fun _ => (0 : ℝ)) (fun i => M * z i + w i)) : LexUni z w := by
  refine lexUni_of_key z w (fun i => M * z i + w i) hinj (fun i j => ⟨hM i j, fun hlt => ?_⟩) h
  by_cases hij : (z i, w i) = (z j, w j)
  · have := hinj i j (congrArg Prod.fst hij) (congrArg Prod.snd hij)
    subst this; exact absurd hlt (lt_irrefl _)
  · rcases lexLt_total hij with h' | h'
    · exact h'
    · exact absurd (hM j i h') (not_lt.2 hlt.le)

theorem k5d_lex0 {x y : ℝ} : LexLt ((0 : ℝ), x) (0, y) ↔ x < y := by
  unfold LexLt
  constructor
  · rintro (h | ⟨-, h⟩)
    · exact absurd h (lt_irrefl _)
    · exact h
  · intro h; exact Or.inr ⟨rfl, h⟩

theorem k5d_uni_of_nopair {k : ℕ} [NeZero k] (hk1 : (1 : ZMod k) ≠ 0) (z : ZMod k → ℝ)
    (hinj : ∀ i j, z i = z j → i = j)
    (h : ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 → j ≠ i - 1 →
      ¬ ((z (i - 1) < z i ∧ z (i + 1) < z i) ∧ (z (j - 1) < z j ∧ z (j + 1) < z j))) :
    LexUni (fun _ => (0 : ℝ)) z := by
  classical
  refine ⟨fun i j _ h2 => hinj i j h2, ?_⟩
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image (Finset.univ : Finset (ZMod k)) z Finset.univ_nonempty
  rw [Finset.card_eq_one]
  refine ⟨m, ?_⟩
  have pm1 : z (m - 1) < z m := lt_of_le_of_ne (hm _ (Finset.mem_univ _)) (fun e => by
    have := hinj _ _ e
    apply hk1
    have h2 : m - 1 - m = m - m := by rw [this]
    simpa using h2)
  have pm2 : z (m + 1) < z m := lt_of_le_of_ne (hm _ (Finset.mem_univ _)) (fun e => by
    have := hinj _ _ e
    apply hk1
    have h2 : m + 1 - m = m - m := by rw [this]
    simpa using h2)
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, k5d_lex0]
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hjm
    by_cases hj1 : j = m + 1
    · subst hj1
      have := hm (m + 1 - 1) (Finset.mem_univ _)
      simp at h1; linarith [hm (m + 1) (Finset.mem_univ _)]
    by_cases hj2 : j = m - 1
    · subst hj2
      simp at h2; linarith [hm (m - 1) (Finset.mem_univ _)]
    exact h m j hjm hj1 hj2 ⟨⟨pm1, pm2⟩, h1, h2⟩
  · rintro rfl; exact ⟨pm1, pm2⟩

end C2
end Type08Sp
end Minimality
