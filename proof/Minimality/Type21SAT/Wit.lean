module

public import Minimality.Type21SAT.Geom
public import Minimality.Type21SAT.Par

@[expose] public section

/-!
# Type 21 three valued bridge (L3), part 1c: the tope variable `Tp` and its witnesses

`TpSem F u M sg` is the real meaning of the CNF variable `Tp(e, M, sg)` at the view `u = vv e`:
the view is zero, or some facet of `M` is not edge-on at `u`, or the tope exists.  The two escapes make
the witness clauses true without a hypothesis on the view, and cost nothing in a rule clause, whose state
says that every facet of `M` is edge-on and that some facet is strict, hence `u != 0`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace
open Finset

namespace Minimality.H21

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}

/-- The real meaning of `Tp(e, M, sg)` at the view `u`. -/
def TpSem (F : S0xFac m S x) (u : ℝ³) (M sg : Fin m → Bool) : Prop :=
  u = 0 ∨ (∃ t, M t = true ∧ ⟪F.N t, u⟫ ≠ 0) ∨ TopeEx F M sg

/-- In the state of a rule (all facets of `M` edge-on, one facet strict), `TpSem` is the tope. -/
theorem tope_of_tpSem (F : S0xFac m S x) {u : ℝ³} {M sg : Fin m → Bool}
    (hon : ∀ t, M t = true → ⟪F.N t, u⟫ = 0) (hu : u ≠ 0) (h : TpSem F u M sg) : TopeEx F M sg := by
  rcases h with h | ⟨t, ht, hne⟩ | h
  · exact absurd h hu
  · exact absurd (hon t ht) hne
  · exact h

/-- Witness kind 0 or a tope from a lex pair is a `TpSem`, whatever the view. -/
theorem tpSem_of_tope (F : S0xFac m S x) (u : ℝ³) {M sg : Fin m → Bool} (h : TopeEx F M sg) :
    TpSem F u M sg := Or.inr (Or.inr h)

/-- **Witness kind 2 as the clauses use it** (`d` zero on the facets `t0, t1` of `M`, with different
signs there, signed on the rest, and `k >= 3`): `TpSem` holds.  The proof: if all of `M` is edge-on at
`u != 0`, the third facet shows `d` is not parallel to `u`, so `N t0, N t1` are parallel, and distinct
facets cannot have normals pointing the same way. -/
theorem tpSem_witness2 (F : S0xFac m S x) (u d : ℝ³) (M sg : Fin m → Bool) (eps : ℝ)
    (t0 t1 s : Fin m) (h0 : M t0 = true) (h1 : M t1 = true) (hs3 : M s = true) (e0 : s ≠ t0)
    (e1 : s ≠ t1) (hne : t0 ≠ t1) (hsg : sg t0 ≠ sg t1)
    (hN0 : ⟪F.N t0, F.N t0⟫ ≠ 0) (hN1 : ⟪F.N t1, F.N t1⟫ ≠ 0) (hS0 : (S t0).Nonempty)
    (hsub : ¬ S t1 ⊆ S t0)
    (hz0 : ⟪F.N t0, d⟫ = 0) (hz1 : ⟪F.N t1, d⟫ = 0)
    (hs : ∀ t, M t = true → t ≠ t0 → t ≠ t1 →
      (sg t = true → 0 < eps * ⟪F.N t, d⟫) ∧ (sg t = false → eps * ⟪F.N t, d⟫ < 0)) :
    TpSem F u M sg := by
  by_cases hu : u = 0
  · exact Or.inl hu
  by_cases hon : ∀ t, M t = true → ⟪F.N t, u⟫ = 0
  · refine Or.inr (Or.inr ?_)
    have hsd : ⟪F.N s, d⟫ ≠ 0 := by
      intro h
      have := hs s hs3 e0 e1
      cases hsg' : sg s with
      | true => rw [h] at this; simpa [hsg'] using this.1 hsg'
      | false => rw [h] at this; simpa [hsg'] using this.2 hsg'
    have hN0' : F.N t0 ≠ 0 := fun h => hN0 (by rw [h]; simp)
    obtain ⟨r, hr⟩ := parallel_of_perp u d (F.N t0) (F.N t1) (F.N s) hu hN0'
      (hon t0 h0) hz0 (hon t1 h1) hz1
      (hon s hs3) hsd
    have hneg := neg_of_parallel F hr hN0 hN1 hS0 hsub
    have hpos : 0 < ⟪F.N t0, F.N t0⟫ := lt_of_le_of_ne real_inner_self_nonneg (Ne.symm hN0)
    exact witness2 F M sg d eps t0 t1 h0 h1 hne hsg hpos hneg hz0 hz1 hs
  · push Not at hon
    obtain ⟨t, ht, hne'⟩ := hon
    exact Or.inr (Or.inl ⟨t, ht, hne'⟩)

/-- Witness kind 1 as the clauses use it: zero on one facet of `M`, signed on the rest. -/
theorem tpSem_witness1 (F : S0xFac m S x) (u d : ℝ³) (M sg : Fin m → Bool) (eps : ℝ) (t0 : Fin m)
    (h0 : M t0 = true) (hN : ⟪F.N t0, F.N t0⟫ ≠ 0) (hz : ⟪F.N t0, d⟫ = 0)
    (hs : ∀ t, M t = true → t ≠ t0 →
      (sg t = true → 0 < eps * ⟪F.N t, d⟫) ∧ (sg t = false → eps * ⟪F.N t, d⟫ < 0)) :
    TpSem F u M sg := tpSem_of_tope F u (witness1 F M sg d eps t0 h0 hN hz hs)

/-- Witness kind 0 as the clauses use it: every facet of `M` signed at `d`. -/
theorem tpSem_witness0 (F : S0xFac m S x) (u d : ℝ³) (M sg : Fin m → Bool) (eps : ℝ)
    (hs : ∀ t, M t = true →
      (sg t = true → 0 < eps * ⟪F.N t, d⟫) ∧ (sg t = false → eps * ⟪F.N t, d⟫ < 0)) :
    TpSem F u M sg := tpSem_of_tope F u (witness0 F M sg d eps hs)


/-- Reversing the tilt complements the sign vector (the encoder stores `Tp` with the lowest facet down). -/
theorem TopeEx.compl (F : S0xFac m S x) {M sg : Fin m → Bool} (h : TopeEx F M sg) :
    TopeEx F M (fun t => !sg t) := by
  obtain ⟨v, hv⟩ := h
  refine ⟨-v, fun t ht => ?_⟩
  obtain ⟨h1, h2⟩ := hv t ht
  simp only [inner_neg_right]
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · have : sg t = false := by simpa using hp
    linarith [h2 this]
  · have : sg t = true := by simpa using hp
    linarith [h1 this]

/-- `TpSem` is invariant under complementing the sign vector. -/
theorem TpSem.compl (F : S0xFac m S x) {u : ℝ³} {M sg : Fin m → Bool} (h : TpSem F u M sg) :
    TpSem F u M (fun t => !sg t) := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h.compl)

/-- A mask with one facet always has a tope (`k = 1`: the encoder writes `Tp` as the constant true). -/
theorem tope_single (F : S0xFac m S x) (M sg : Fin m → Bool) (t0 : Fin m)
    (hM : ∀ t, M t = true → t = t0) (hN : ⟪F.N t0, F.N t0⟫ ≠ 0) : TopeEx F M sg := by
  have hpos : 0 < ⟪F.N t0, F.N t0⟫ := lt_of_le_of_ne real_inner_self_nonneg (Ne.symm hN)
  refine ⟨if sg t0 then F.N t0 else -F.N t0, fun t ht => ?_⟩
  have := hM t ht
  subst this
  cases hs : sg t
  · simp only [ite_false, Bool.false_eq_true, inner_neg_right]
    exact ⟨fun h => absurd h (by simp), fun _ => by linarith⟩
  · simp only [ite_true]
    exact ⟨fun _ => hpos, fun h => absurd h (by simp)⟩

/-- **The rule, ready for the row soundness.**  State, `TpSem` and a robust cycle give Rupert. -/
theorem rule_leaf' {k : ℕ} [NeZero k] (F : S0xFac m S x) (hx : Function.Injective x)
    {c : ZMod k → Fin n} {pp M sg : Fin m → Bool} {u : ℝ³} (hc : Function.Injective c)
    (hk : 3 ≤ k) (hcyc : S0xCycOK S c pp)
    (hoff : ∀ t, M t = false → (pp t = true → 0 < ⟪F.N t, u⟫) ∧ (pp t = false → ⟪F.N t, u⟫ < 0))
    (hon : ∀ t, M t = true → ⟪F.N t, u⟫ = 0 ∧ pp t = sg t)
    (hstrict : ∃ t, M t = false) (ht : TpSem F u M sg)
    (hU : RobUni (fun a : ZMod k => ⟪x (c a), u⟫)) : IsRupert (univ.image x) := by
  obtain ⟨t0, ht0⟩ := hstrict
  have hu : u ≠ 0 := by
    intro h0
    have := hoff t0 ht0
    cases hp : pp t0 <;> simp [hp, h0] at this
  exact rule_leaf F hx hc hk hcyc hoff hon ⟨t0, ht0⟩
    (tope_of_tpSem F (fun t h => (hon t h).1) hu ht) hU

end Minimality.H21

