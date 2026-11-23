module

public import Minimality.PSVC

@[expose] public section

/-!
# Conditional single view and pair + auxiliary vector (PA24)

Spec: nopert229 out/bottleneck/p4/sat/trigen-why/WHY.md (Finding 1, L1, L2).

`svc_cond` (L1): `single_view_closure` at a view `w` with extra *conditions* `(σ, E_u)`: `E_u`
is a list of decompositions of a vector `u`, and the Gram sign `σ ⟪u, w⟫ ≥ 0` is assumed
(σ = 0: no assumption, the decompositions of `u` are only read at the order of `w`, and an
order at which one decomposition reads positive and another negative is impossible).
An order is excluded by `condBad` when the evidence from `u` contradicts the assumed sign.

`pair_aux_closure` (L2): two views `w1`, `w2` and a list `A` of auxiliary vectors (each given by
its decompositions). `⟪w1, w2⟫ ≥ 0` is closed by `checkCond` at `w1` with the condition
`(+, E2)`, `⟪w1, w2⟫ ≤ 0` by `checkCond` at `w2` with `(-, E1)`; both also use the aux
conditions. No bad-order list and no order pair enters the kernel check.
-/

set_option autoImplicit false

open scoped RealInnerProductSpace
open Minimality Minimality.H21

namespace Minimality.PSVC

open Minimality.SVC

/-- The order `L` at the view contradicts the condition `(σ, E)`: `σ = +` and a decomposition
of `u` reads negative (but `0 ≤ ⟪u, w⟫`), `σ = -` and one reads positive (but `⟪u, w⟫ ≤ 0`),
`σ = 0` and one reads positive and another negative. -/
def condBad {p : ℕ} (σ : SignType) (E : List (List (Fin p × Fin p))) (L : List (Fin p)) : Bool :=
  match σ with
  | .pos => E.any (evNeg L)
  | .neg => E.any (evPos L)
  | .zero => E.any (evPos L) && E.any (evNeg L)

/-- The Gram sign assumption of a condition. -/
def CondSign (σ : SignType) (u w : ℝ³) : Prop :=
  match σ with
  | .pos => 0 ≤ ⟪u, w⟫
  | .neg => ⟪u, w⟫ ≤ 0
  | .zero => True

/-- Auxiliary conditions: no sign assumption. -/
def auxConds {p : ℕ} (A : List (List (List (Fin p × Fin p)))) :
    List (SignType × List (List (Fin p × Fin p))) :=
  A.map fun E => (0, E)

/-- Check at one view: rims valid, and every order is excluded, passes a rim, or contradicts a
condition. -/
def checkCond {m n p : ℕ} (S : Fin m → Finset (Fin n)) (P : Fin p → Fin n) (sw : Fin m → SignType)
    (forced : List (Fin p × Fin p)) (deps : List (Fin p → SignType))
    (E : List (List (Fin p × Fin p))) (R : List (Rim m p))
    (conds : List (SignType × List (List (Fin p × Fin p)))) : Bool :=
  R.all (rimValid S P sw) &&
    (List.finRange p).permutations'.all fun L =>
      exclOK forced deps E L || R.any (fun ρ => rimOK ρ L) ||
        conds.any (fun c => condBad c.1 c.2 L)

theorem condBad_false {n p : ℕ} {x : Fin n → ℝ³} {P : Fin p → Fin n} {w u : ℝ³}
    {σ : SignType} {E : List (List (Fin p × Fin p))} (hE : ∀ d ∈ E, DecOK x P u d)
    (hσ : CondSign σ u w) {L : List (Fin p)}
    (hrk : ∀ i j, rk L i < rk L j → ⟪x (P i), w⟫ < ⟪x (P j), w⟫)
    (h : condBad σ E L = true) : False := by
  cases σ with
  | zero =>
    simp only [condBad, Bool.and_eq_true, List.any_eq_true] at h
    obtain ⟨⟨d, hd, he⟩, ⟨d', hd', he'⟩⟩ := h
    have h1 := evPos_sound (hE d hd) hrk he
    have h2 := evNeg_sound (hE d' hd') hrk he'
    linarith
  | neg =>
    simp only [condBad, List.any_eq_true] at h
    obtain ⟨d, hd, he⟩ := h
    have h1 := evPos_sound (hE d hd) hrk he
    simp only [CondSign] at hσ
    linarith
  | pos =>
    simp only [condBad, List.any_eq_true] at h
    obtain ⟨d, hd, he⟩ := h
    have h1 := evNeg_sound (hE d hd) hrk he
    simp only [CondSign] at hσ
    linarith

/-- **Conditional single-view closure (L1).** `V` the view data (facings, tilts, forced pairs,
own decompositions, distinct depths); each condition `(σ, E)` comes from a vector `u` with
decompositions `E` and the Gram sign `σ ⟪u, w⟫ ≥ 0`. If `checkCond` passes, `Gen.LexAny F`. -/
theorem svc_cond {m n p : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (P : Fin p → Fin n) (w : ℝ³) (sw : Fin m → SignType)
    (R : List (Rim m p)) (forced : List (Fin p × Fin p)) (E : List (List (Fin p × Fin p)))
    (V : ViewData F P w sw R forced E)
    (deps : List (Fin p → SignType))
    (hdeps : ∀ s ∈ deps, ∃ mu : Fin p → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = s i)
    (conds : List (SignType × List (List (Fin p × Fin p))))
    (hconds : ∀ c ∈ conds, ∃ u : ℝ³, (∀ d ∈ c.2, DecOK x P u d) ∧ CondSign c.1 u w)
    (hcheck : checkCond S P sw forced deps E R conds = true) : Minimality.Gen.LexAny F := by
  classical
  obtain ⟨L, hL, hrk⟩ := V.order
  simp only [checkCond, Bool.and_eq_true, List.all_eq_true] at hcheck
  obtain ⟨hval, hperm⟩ := hcheck
  have h := hperm L hL
  simp only [Bool.or_eq_true, List.any_eq_true] at h
  rcases h with (hx | ⟨ρ, hρ, hok⟩) | ⟨c, hc, hb⟩
  · exact (exclOK_false V.hforced hdeps V.hE hrk hx).elim
  · exact lexAny_of_rimOK F P w sw ρ (V.hsw ρ hρ) (V.hR ρ hρ) (hval ρ hρ) hrk hok
  · obtain ⟨u, hu, hs⟩ := hconds c hc
    exact (condBad_false hu hs hrk hb).elim

/-- **Pair + auxiliary vectors (L2).** Two views `w1`, `w2` with `ViewData`, a list `A` of
auxiliary vectors (decomposition lists). If `⟪w1, w2⟫ ≥ 0` is closed at `w1` by the condition
`(+, E2)` and `⟪w1, w2⟫ ≤ 0` at `w2` by `(-, E1)` (both with the aux conditions), `Gen.LexAny F`. -/
theorem pair_aux_closure {m n p : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (P : Fin p → Fin n) (w1 w2 : ℝ³) (sw1 sw2 : Fin m → SignType)
    (R1 R2 : List (Rim m p)) (f1 f2 : List (Fin p × Fin p))
    (E1 E2 : List (List (Fin p × Fin p)))
    (V1 : ViewData F P w1 sw1 R1 f1 E1) (V2 : ViewData F P w2 sw2 R2 f2 E2)
    (deps : List (Fin p → SignType))
    (hdeps : ∀ s ∈ deps, ∃ mu : Fin p → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = s i)
    (A : List (List (List (Fin p × Fin p))))
    (hA : ∀ Ea ∈ A, ∃ u : ℝ³, ∀ d ∈ Ea, DecOK x P u d)
    (hc1 : checkCond S P sw1 f1 deps E1 R1 ((1, E2) :: auxConds A) = true)
    (hc2 : checkCond S P sw2 f2 deps E2 R2 ((-1, E1) :: auxConds A) = true) :
    Minimality.Gen.LexAny F := by
  have haux : ∀ c ∈ auxConds A, ∃ u : ℝ³, (∀ d ∈ c.2, DecOK x P u d) ∧ CondSign c.1 u w1 ∧
      CondSign c.1 u w2 := by
    intro c hc
    simp only [auxConds, List.mem_map] at hc
    obtain ⟨Ea, hEa, rfl⟩ := hc
    obtain ⟨u, hu⟩ := hA Ea hEa
    exact ⟨u, hu, trivial, trivial⟩
  rcases le_total 0 ⟪w1, w2⟫ with h | h
  · refine svc_cond F P w1 sw1 R1 f1 E1 V1 deps hdeps _ ?_ hc1
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨w2, V2.hE, by simpa [CondSign, real_inner_comm] using h⟩
    · obtain ⟨u, hu, h1, _⟩ := haux c hc
      exact ⟨u, hu, h1⟩
  · refine svc_cond F P w2 sw2 R2 f2 E2 V2 deps hdeps _ ?_ hc2
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨w1, V1.hE, by simpa [CondSign] using h⟩
    · obtain ⟨u, hu, _, h2⟩ := haux c hc
      exact ⟨u, hu, h2⟩

end Minimality.PSVC
