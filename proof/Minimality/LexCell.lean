module

public import Minimality.RimCellClosed

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality.LexCell

open Minimality Minimality.H21

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}

/-- Lexicographic positivity of a triple of reals. -/
def LexPos3 (a b c : ℝ) : Prop := 0 < a ∨ (a = 0 ∧ (0 < b ∨ (b = 0 ∧ 0 < c)))

/-- `p < q` lexicographically (strictly) on triples. -/
def LexLt3 (p q : ℝ × ℝ × ℝ) : Prop := LexPos3 (q.1 - p.1) (q.2.1 - p.2.1) (q.2.2 - p.2.2)

/-- Robust unimodality of a cycle of triples in the lexicographic order (ties allowed, except a
weak double peak): in every alternating quadruple one of the four comparisons is a strict
lexicographic inequality. -/
def RobUniLex {k : ℕ} (z : ZMod k → ℝ × ℝ × ℝ) : Prop :=
  ∀ (B : ZMod k) (b c d : ℕ), 0 < b → b < c → c < d → d < k →
    LexLt3 (z B) (z (B + b)) ∨ LexLt3 (z (B + c)) (z (B + b)) ∨
    LexLt3 (z B) (z (B + d)) ∨ LexLt3 (z (B + c)) (z (B + d))

theorem ev_lexPos3 {a b c : ℝ} (h : LexPos3 a b c) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < a + ε * b + ε ^ 2 * c := by
  rcases h with h | ⟨rfl, h | ⟨rfl, h⟩⟩
  · have hc : Continuous fun ε : ℝ => a + ε * b + ε ^ 2 * c := by fun_prop
    exact (hc.continuousAt.eventually (lt_mem_nhds (by simpa using h))).filter_mono
      nhdsWithin_le_nhds
  · filter_upwards [eventually_pos_affine (Or.inl h : 0 < b ∨ (b = 0 ∧ 0 < c)) |>.and
      self_mem_nhdsWithin] with ε ⟨h1, h2⟩
    have : (0 : ℝ) < ε := h2
    nlinarith [mul_pos this h1]
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have : (0 : ℝ) < ε := hε
    simpa using mul_pos (pow_pos this 2) h

/-- A strict lexicographic inequality of depth triples is a strict inequality at the lex point. -/
theorem ev_lexLt_inner (p q : ℝ³) (b d1 d2 : ℝ³)
    (h : LexLt3 (⟪p, b⟫, ⟪p, d1⟫, ⟪p, d2⟫) (⟪q, b⟫, ⟪q, d1⟫, ⟪q, d2⟫)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪p, b + ε • d1 + ε ^ 2 • d2⟫ < ⟪q, b + ε • d1 + ε ^ 2 • d2⟫ := by
  filter_upwards [ev_lexPos3 h] with ε hε
  simp only [inner_add_right, inner_smul_right] at hε ⊢
  nlinarith

/-- **Lemma LXC (lexicographic closed cell).**  Facet signs are decided lexicographically at the
point `b + ε d1 + ε² d2` (`ε → 0+`), and the rim depths are `RobUniLex` in the lexicographic
order on `(⟪·,b⟫, ⟪·,d1⟫, ⟪·,d2⟫)`. -/
theorem isRupert_of_lexCell {k : ℕ} [NeZero k] (hk : 4 ≤ k) (F : S0xFac m S x)
    (hx : Function.Injective x) {c : ZMod k → Fin n} (hc : Function.Injective c)
    {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn) (b d1 d2 : ℝ³)
    (hU : ∀ t ∈ U, LexPos3 ⟪F.N t, b⟫ ⟪F.N t, d1⟫ ⟪F.N t, d2⟫)
    (hD : ∀ t ∈ Dn, LexPos3 (-⟪F.N t, b⟫) (-⟪F.N t, d1⟫) (-⟪F.N t, d2⟫))
    (hR : RobUniLex (fun i => (⟪x (c i), b⟫, ⟪x (c i), d1⟫, ⟪x (c i), d2⟫))) :
    IsRupert (univ.image x) := by
  have e1 : ∀ (y : ℝ³) ε, ⟪y, b + ε • d1 + ε ^ 2 • d2⟫ = ⟪y, b⟫ + ε * ⟪y, d1⟫ + ε ^ 2 * ⟪y, d2⟫ := by
    intro y ε; simp only [inner_add_right, inner_smul_right]
  have hcell : ∀ᶠ ε in 𝓝[>] (0 : ℝ), CellAt F U Dn (b + ε • d1 + ε ^ 2 • d2) := by
    refine (Filter.eventually_all_finset U |>.2 fun t ht => ?_).and
      (Filter.eventually_all_finset Dn |>.2 fun t ht => ?_)
    · filter_upwards [ev_lexPos3 (hU t ht)] with ε h; rwa [e1]
    · filter_upwards [ev_lexPos3 (hD t ht)] with ε h; rw [e1]; linarith
  have hrob : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      RobUni (fun i => ⟪x (c i), b + ε • d1 + ε ^ 2 • d2⟫) := by
    have hall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ B : ZMod k, ∀ b' ∈ Finset.range k, ∀ c' ∈ Finset.range k,
        ∀ d' ∈ Finset.range k, 0 < b' → b' < c' → c' < d' → d' < k →
        ¬ (⟪x (c (B + b')), b + ε • d1 + ε ^ 2 • d2⟫ ≤ ⟪x (c B), b + ε • d1 + ε ^ 2 • d2⟫ ∧
           ⟪x (c (B + b')), b + ε • d1 + ε ^ 2 • d2⟫ ≤ ⟪x (c (B + c')), b + ε • d1 + ε ^ 2 • d2⟫ ∧
           ⟪x (c (B + d')), b + ε • d1 + ε ^ 2 • d2⟫ ≤ ⟪x (c B), b + ε • d1 + ε ^ 2 • d2⟫ ∧
           ⟪x (c (B + d')), b + ε • d1 + ε ^ 2 • d2⟫ ≤ ⟪x (c (B + c')), b + ε • d1 + ε ^ 2 • d2⟫) := by
      refine Filter.eventually_all.2 fun B => ?_
      refine Filter.eventually_all_finset _ |>.2 fun b' _ => ?_
      refine Filter.eventually_all_finset _ |>.2 fun c' _ => ?_
      refine Filter.eventually_all_finset _ |>.2 fun d' _ => ?_
      by_cases hp : 0 < b' ∧ b' < c' ∧ c' < d' ∧ d' < k
      · obtain ⟨h1, h2, h3, h4⟩ := hp
        rcases hR B b' c' d' h1 h2 h3 h4 with h | h | h | h
        · filter_upwards [ev_lexLt_inner _ _ b d1 d2 h] with ε hε
          intro _ _ _ _ ⟨a1, _⟩; exact absurd a1 (not_le.2 hε)
        · filter_upwards [ev_lexLt_inner _ _ b d1 d2 h] with ε hε
          intro _ _ _ _ ⟨_, a2, _⟩; exact absurd a2 (not_le.2 hε)
        · filter_upwards [ev_lexLt_inner _ _ b d1 d2 h] with ε hε
          intro _ _ _ _ ⟨_, _, a3, _⟩; exact absurd a3 (not_le.2 hε)
        · filter_upwards [ev_lexLt_inner _ _ b d1 d2 h] with ε hε
          intro _ _ _ _ ⟨_, _, _, a4⟩; exact absurd a4 (not_le.2 hε)
      · exact Filter.Eventually.of_forall fun ε h1 h2 h3 h4 =>
          absurd ⟨h1, h2, h3, h4⟩ hp
    filter_upwards [hall] with ε hε
    intro B b' c' d' h1 h2 h3 h4
    exact hε B b' (Finset.mem_range.2 (by omega)) c' (Finset.mem_range.2 (by omega)) d'
      (Finset.mem_range.2 h4) h1 h2 h3 h4
  obtain ⟨ε, h1, h2⟩ := (hcell.and hrob).exists
  exact isRupert_of_closedCell hk F hx hc hcyc h1 h1.cellLe h2

/-- Instance: `isRupert_of_closedCell` (`d1 = a - u₀`, `d2 = 0`; `RobUni` at `u₀` gives a strict
comparison at level 0). -/
theorem isRupert_of_closedCell_via_lex {k : ℕ} [NeZero k] (hk : 4 ≤ k) (F : S0xFac m S x)
    (hx : Function.Injective x) {c : ZMod k → Fin n} (hc : Function.Injective c)
    {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn) {a u₀ : ℝ³} (ha : CellAt F U Dn a)
    (hu : CellLe F U Dn u₀) (hR : RobUni (fun i => ⟪x (c i), u₀⟫)) :
    IsRupert (univ.image x) := by
  refine isRupert_of_lexCell hk F hx hc hcyc u₀ (a - u₀) 0 ?_ ?_ ?_
  · intro t ht
    rcases (hu.1 t ht).lt_or_eq with h | h
    · exact Or.inl h
    · refine Or.inr ⟨h.symm, Or.inl ?_⟩
      rw [inner_sub_right, ← h]; simpa using ha.1 t ht
  · intro t ht
    rcases (hu.2 t ht).lt_or_eq with h | h
    · exact Or.inl (by linarith)
    · refine Or.inr ⟨by rw [h]; simp, Or.inl ?_⟩
      rw [inner_sub_right, h]; have := ha.2 t ht; simp; linarith
  · intro B b c d h1 h2 h3 h4
    have := hR B b c d h1 h2 h3 h4
    by_contra hn
    push Not at hn
    have key : ∀ p q : ℝ³, ¬ LexLt3 (⟪p, u₀⟫, ⟪p, a - u₀⟫, ⟪p, (0 : ℝ³)⟫)
        (⟪q, u₀⟫, ⟪q, a - u₀⟫, ⟪q, (0 : ℝ³)⟫) → ⟪q, u₀⟫ ≤ ⟪p, u₀⟫ := by
      intro p q h
      by_contra h'
      exact h (Or.inl (by simp only; linarith [not_le.1 h']))
    exact this ⟨key _ _ hn.1, key _ _ hn.2.1, key _ _ hn.2.2.1, key _ _ hn.2.2.2⟩

end Minimality.LexCell
