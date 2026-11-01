module

public import Minimality.Type08S.P2RQ2
public import Minimality.Type08S.P2RKT2
public import Minimality.Type08S.P2RKT3
public import Minimality.Type08S.P2TX1

@[expose] public section

/-!
# C2 / FA1: lex unimodality by a scalar key, and the convex 4-cycle

* `lexUni_of_key`: if a real key `k` orders the lex pairs `(z i, w i)` (`LexLt ↔ <`), lex unimodality is the
  scalar unimodality of `k` (as `LexUni (fun _ => 0) k`).
* `exists_key`: such a key exists, `k = M z + w` for `M` large (finitely many pairs).
* `lexUni4_conv`: a 4-cycle whose lex pairs satisfy `P₂ - P₀ = β (P₁ - P₀) + γ (P₃ - P₀)` with `β, γ > 0`,
  `β + γ > 1` (a convex planar quadrilateral under an affine map) is lex unimodal once the pairs are distinct.
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- A scalar key ordering the lex pairs transfers lex unimodality. -/
theorem lexUni_of_key {k : ℕ} [NeZero k] (z w key : ZMod k → ℝ)
    (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (hkey : ∀ i j, LexLt (z i, w i) (z j, w j) ↔ key i < key j)
    (h : LexUni (fun _ => (0 : ℝ)) key) : LexUni z w := by
  classical
  refine ⟨hinj, ?_⟩
  rw [← h.2]
  congr 1
  apply Finset.filter_congr
  intro i _
  have e : ∀ j, LexLt (z j, w j) (z i, w i) ↔ LexLt ((fun _ => (0 : ℝ)) j, key j) ((fun _ => (0 : ℝ)) i, key i) := by
    intro j; rw [hkey]; simp [LexLt]
  rw [e, e]

/-- The key `M z + w` orders finitely many lex pairs for `M` large. -/
theorem exists_key {k : ℕ} [NeZero k] (z w : ZMod k → ℝ)
    (hinj : ∀ i j, z i = z j → w i = w j → i = j) :
    ∃ M : ℝ, ∀ i j, LexLt (z i, w i) (z j, w j) ↔ M * z i + w i < M * z j + w j := by
  have one : ∀ i j : ZMod k, ∀ᶠ M in atTop, LexLt (z i, w i) (z j, w j) → M * z i + w i < M * z j + w j := by
    intro i j
    rcases lt_trichotomy (z i) (z j) with h | h | h
    · filter_upwards [eventually_gt_atTop ((w i - w j) / (z j - z i))] with M hM
      intro _
      have hz : 0 < z j - z i := by linarith
      rw [div_lt_iff₀ hz] at hM
      nlinarith
    · exact Eventually.of_forall fun M hl => by
        rcases hl with hl | ⟨-, hl⟩
        · exact absurd h (ne_of_lt hl)
        · rw [h]; linarith
    · exact Eventually.of_forall fun M hl => by
        rcases hl with hl | ⟨hl, -⟩ <;> linarith
  have hall : ∀ᶠ M in atTop, ∀ i j : ZMod k, LexLt (z i, w i) (z j, w j) → M * z i + w i < M * z j + w j := by
    rw [eventually_all]; intro i; rw [eventually_all]; exact one i
  obtain ⟨M, hM⟩ := hall.exists
  refine ⟨M, fun i j => ⟨hM i j, fun hlt => ?_⟩⟩
  by_cases hij : (z i, w i) = (z j, w j)
  · have := hinj i j (congrArg Prod.fst hij) (congrArg Prod.snd hij)
    subst this; exact absurd hlt (lt_irrefl _)
  · rcases lexLt_total hij with h | h
    · exact h
    · exact absurd (hM j i h) (not_lt.2 hlt.le)

/-- Scalar: a convex 4-cycle (`k₂ - k₀ = β (k₁ - k₀) + γ (k₃ - k₀)`, `β, γ > 0`, `β + γ > 1`) has no alternation. -/
theorem noAlt4 {k0 k1 k2 k3 β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (hs : 1 < β + γ)
    (hrel : k2 - k0 = β * (k1 - k0) + γ * (k3 - k0)) :
    ¬ (max k1 k3 < min k0 k2) ∧ ¬ (max k0 k2 < min k1 k3) := by
  constructor
  · intro h
    rw [max_lt_iff, lt_min_iff, lt_min_iff] at h
    obtain ⟨⟨h10, h12⟩, h30, h32⟩ := h
    -- A = k2 - k1 > 0, B = k2 - k3 > 0, U = k0 - k1 > 0
    rcases le_or_gt γ 1 with hg | hg
    · nlinarith [mul_nonneg (sub_nonneg.2 hg) (sub_pos.2 h12).le, mul_pos hγ (sub_pos.2 h32),
        mul_pos (sub_pos.2 hs) (sub_pos.2 h10)]
    · nlinarith [mul_pos (sub_pos.2 hg) (sub_pos.2 h30), mul_pos hβ (sub_pos.2 h10)]
  · intro h
    rw [max_lt_iff, lt_min_iff, lt_min_iff] at h
    obtain ⟨⟨h01, h03⟩, h21, h23⟩ := h
    rcases le_or_gt γ 1 with hg | hg
    · nlinarith [mul_nonneg (sub_nonneg.2 hg) (sub_pos.2 h21).le, mul_pos hγ (sub_pos.2 h23),
        mul_pos (sub_pos.2 hs) (sub_pos.2 h01)]
    · nlinarith [mul_pos (sub_pos.2 hg) (sub_pos.2 h03), mul_pos hβ (sub_pos.2 h01)]

/-- **Convex 4-cycle.**  Distinct lex pairs with `P₂ - P₀ = β (P₁ - P₀) + γ (P₃ - P₀)` (both components),
`β, γ > 0`, `β + γ > 1`, are lex unimodal. -/
theorem lexUni4_conv (z w : ZMod 4 → ℝ) {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (hs : 1 < β + γ)
    (hz : z 2 - z 0 = β * (z 1 - z 0) + γ * (z 3 - z 0))
    (hw : w 2 - w 0 = β * (w 1 - w 0) + γ * (w 3 - w 0))
    (hinj : ∀ i j, z i = z j → w i = w j → i = j) : LexUni z w := by
  obtain ⟨M, hM⟩ := exists_key z w hinj
  set key : ZMod 4 → ℝ := fun i => M * z i + w i with hkey
  refine lexUni_of_key z w key hinj hM ?_
  have hrel : key 2 - key 0 = β * (key 1 - key 0) + γ * (key 3 - key 0) := by
    simp only [hkey]; linear_combination M * hz + hw
  obtain ⟨hna1, hna2⟩ := noAlt4 hβ hγ hs hrel
  refine lexUni_four _ key (fun _ _ => rfl) ?_ hna1 hna2
  intro i j hij hk
  have hne : (z i, w i) ≠ (z j, w j) := fun h => hij (hinj i j (congrArg Prod.fst h) (congrArg Prod.snd h))
  rcases lexLt_total hne with h | h
  · exact absurd hk (ne_of_lt ((hM i j).1 h))
  · exact absurd hk.symm (ne_of_lt ((hM j i).1 h))

end C2
end Type08Sp
end Minimality
