module

public import Minimality.Type29Sec

@[expose] public section

/-!
# Type 29: the automorphism `σ = (0 2)(4 5)` on the named views and the ties (§28)

The named views of `x ∘ σ` are `± ` the named views of `x` (`σV29`: the segments `ij ↦ σi σj`, the
vertex lines `0 ↦ 0`, `1 ↔ 2`, `3 ↦ 3`, `4 ↔ 5`, `6 ↦ 6`), so a tie of `x ∘ σ` at a named view
is a tie of `x` at the image view, and `OneTieGlobal29` is `σ`-invariant
(`OneTieGlobal29.sigma`).  This lets the classes K3b, K4b reuse the a forms.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- `σ` on the seven vertex lines of `vtxLines29`. -/
def sigmaL29 : Fin 7 → Fin 7 := ![0, 2, 1, 3, 5, 4, 6]

/-- `σ` on the named views. -/
def sigmaV29 : View29 → View29
  | .inl (i, j) => .inl (sigma29 i, sigma29 j)
  | .inr t => .inr (sigmaL29 t)

theorem sigmaV29_sigmaV29 (v : View29) : sigmaV29 (sigmaV29 v) = v := by
  rcases v with ⟨i, j⟩ | t
  · have h : ∀ j, sigma29 (sigma29 j) = j := by decide
    simp [sigmaV29, h]
  · have h : ∀ j, sigmaL29 (sigmaL29 j) = j := by decide
    simp [sigmaV29, h]

theorem sigma29_sigma29 (i : Fin 7) : sigma29 (sigma29 i) = i := by revert i; decide

theorem sigma29_inj' : Function.Injective sigma29 := sigma29_inj

variable (x : Fin 7 → ℝ³)

/-- The named views of `x ∘ σ` are `±` those of `x` at the image view. -/
theorem view29_sigma (v : View29) :
    ∃ c : ℝ, (c = 1 ∨ c = -1) ∧ view29 (x ∘ sigma29) v = c • view29 x (sigmaV29 v) := by
  rcases v with ⟨i, j⟩ | t
  · exact ⟨1, Or.inl rfl, by simp [view29, sigmaV29]⟩
  · fin_cases t
    · refine ⟨1, Or.inl rfl, ?_⟩
      show planeLine (x 2) (x 1) (x 0) (x 1) (x 5) (x 4) =
        (1 : ℝ) • planeLine (x 0) (x 1) (x 2) (x 1) (x 4) (x 5)
      rw [planeLine_eq_cross16, planeLine_eq_cross16]
      ext k
      fin_cases k <;> simp [cross] <;> ring
    · refine ⟨-1, Or.inr rfl, ?_⟩
      show planeLine (x 0) (x 3) (x 5) (x 1) (x 5) (x 4) =
        (-1 : ℝ) • planeLine (x 0) (x 3) (x 5) (x 1) (x 4) (x 5)
      rw [planeLine_eq_cross16, planeLine_eq_cross16]
      ext k
      fin_cases k <;> simp [cross] <;> ring
    · refine ⟨-1, Or.inr rfl, ?_⟩
      show planeLine (x 2) (x 3) (x 4) (x 1) (x 5) (x 4) =
        (-1 : ℝ) • planeLine (x 2) (x 3) (x 4) (x 1) (x 4) (x 5)
      rw [planeLine_eq_cross16, planeLine_eq_cross16]
      ext k
      fin_cases k <;> simp [cross] <;> ring
    · refine ⟨-1, Or.inr rfl, ?_⟩
      show planeLine (x 2) (x 1) (x 4) (x 1) (x 0) (x 5) =
        (-1 : ℝ) • planeLine (x 0) (x 1) (x 5) (x 1) (x 2) (x 4)
      rw [planeLine_eq_cross16, planeLine_eq_cross16]
      ext k
      fin_cases k <;> simp [cross] <;> ring
    · refine ⟨-1, Or.inr rfl, ?_⟩
      show planeLine (x 2) (x 1) (x 4) (x 3) (x 4) (x 6) =
        (-1 : ℝ) • planeLine (x 1) (x 2) (x 4) (x 3) (x 4) (x 6)
      rw [planeLine_eq_cross16, planeLine_eq_cross16]
      ext k
      fin_cases k <;> simp [cross] <;> ring
    · refine ⟨-1, Or.inr rfl, ?_⟩
      show planeLine (x 1) (x 0) (x 5) (x 3) (x 5) (x 6) =
        (-1 : ℝ) • planeLine (x 0) (x 1) (x 5) (x 3) (x 5) (x 6)
      rw [planeLine_eq_cross16, planeLine_eq_cross16]
      ext k
      fin_cases k <;> simp [cross] <;> ring
    · refine ⟨-1, Or.inr rfl, ?_⟩
      show planeLine (x 2) (x 3) (x 4) (x 0) (x 3) (x 5) =
        (-1 : ℝ) • planeLine (x 0) (x 3) (x 5) (x 2) (x 3) (x 4)
      rw [planeLine_eq_cross16, planeLine_eq_cross16]
      ext k
      fin_cases k <;> simp [cross] <;> ring

/-- A tie of `x ∘ σ` at a named view is a tie of `x` at the image view. -/
theorem TieInst29.sigma_iff (v : View29) (s t : Fin 7) :
    TieInst29 (x ∘ sigma29) v s t ↔ TieInst29 x (sigmaV29 v) (sigma29 s) (sigma29 t) := by
  obtain ⟨c, hc, hv⟩ := view29_sigma x v
  have hc0 : c ≠ 0 := by rcases hc with rfl | rfl <;> norm_num
  unfold TieInst29
  rw [hv, Function.comp_apply, Function.comp_apply, smul_ne_zero_iff, real_inner_smul_right,
    mul_eq_zero]
  constructor
  · rintro ⟨hst, ⟨-, h1⟩, h2⟩
    exact ⟨fun h => hst (sigma29_inj h), h1, h2.resolve_left hc0⟩
  · rintro ⟨hst, h1, h2⟩
    exact ⟨fun h => hst (by rw [h]), ⟨hc0, h1⟩, Or.inr h2⟩

/-- `SameTie29` pulls back along `σ`. -/
theorem SameTie29.of_sigma {v v' : View29} {s t s' t' : Fin 7}
    (h : SameTie29 (sigmaV29 v) (sigma29 s) (sigma29 t) (sigmaV29 v') (sigma29 s')
      (sigma29 t')) : SameTie29 v s t v' s' t' := by
  have hs := sigma29_sigma29
  have hinj := sigma29_inj
  have hV : ∀ {a b : View29}, sigmaV29 a = sigmaV29 b → a = b := fun {a b} e => by
    rw [← sigmaV29_sigmaV29 a, e, sigmaV29_sigmaV29]
  have hV' : ∀ {a : View29} {i j : Fin 7}, sigmaV29 a = .inl (i, j) →
      a = .inl (sigma29 i, sigma29 j) := fun {a i j} e => by
    rw [← sigmaV29_sigmaV29 a, e]; simp [sigmaV29]
  rcases h with ⟨hv, hp⟩ | ⟨i, j, hvij, hv', hp⟩
  · refine Or.inl ⟨?_, ?_⟩
    · rcases hv with e | ⟨i, j, e1, e2⟩
      · exact Or.inl (hV e)
      · exact Or.inr ⟨sigma29 i, sigma29 j, hV' e1, hV' e2⟩
    · rcases hp with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Or.inl ⟨hinj e1, hinj e2⟩
      · exact Or.inr ⟨hinj e1, hinj e2⟩
  · refine Or.inr ⟨sigma29 i, sigma29 j, hV' hvij, ?_, ?_⟩
    · rcases hv' with e | e
      · exact Or.inl (by rw [hV' e]; simp [hs])
      · exact Or.inr (by rw [hV' e]; simp [hs])
    · rcases hp with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Or.inl ⟨by rw [← e1, hs], by rw [← e2, hs]⟩
      · exact Or.inr ⟨by rw [← e1, hs], by rw [← e2, hs]⟩

/-- **The tie condition is `σ`-invariant.** -/
theorem OneTieGlobal29.sigma {x : Fin 7 → ℝ³} (h : OneTieGlobal29 x) :
    OneTieGlobal29 (x ∘ sigma29) := by
  intro v s t v' s' t' h1 h2
  exact SameTie29.of_sigma
    (h _ _ _ _ _ _ ((TieInst29.sigma_iff x v s t).mp h1) ((TieInst29.sigma_iff x v' s' t').mp h2))

end Minimality

end
