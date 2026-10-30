module

public import Minimality.Type08S.P2RKT7

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkR / K2 / R3: `lexCell_levTp` — the face cell at `T'` with a level `Q_ac` and `α4 > 1`.
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- **R3.**  Level face of `Q_ac` at `T'` with `α4 > 1`: the face cell (cycle `Q_ac = (d, a, b', c)`, `b` and `c'`
hidden behind `d` and `a`; lex-unimodal because the face is planar and level). -/
theorem lexCell_levTp {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hT' : IsT' a b c' d)
    (hlev : LevelQac a b c d) (hα : Al4Gt a b' c d) : HasLexCellAt (V8 a a' b b' c c' d) (b - d) := by
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hα4, hγ4, hαγ, hβ1, hβ6, hγ6, hγ61, hcv⟩ :=
    norm08_coordsTp' N hT'
  obtain ⟨α', γ', hb'', hα'⟩ := hα
  set p := a - d with hp
  set q := c - d with hq
  set r := b - d with hr
  have hΔ : det3 p q r ≠ 0 := by
    intro h; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = - det3 p q r := by
      simp only [hp, hq, hr, det3_expand]; ring
    rw [e, h, neg_zero]
  -- uniqueness of the representation of `b'`
  have huniq : α4 = α' := by
    have h0 : fcomb p q r (α4 - α') (γ4 - γ') 0 = 0 := by
      have : b' = b' := rfl
      have e : fcomb p q r (α4 - α') (γ4 - γ') 0 = (b' - d - α' • p - γ' • q) - (b' - d - α4 • p - γ4 • q) := by
        simp only [fcomb]; module
      rw [e]
      have e1 : b' - d - α' • p - γ' • q = 0 := by rw [hb'']; simp only [hp, hq]; module
      have e2 : b' - d - α4 • p - γ4 • q = 0 := by rw [hb']; simp only [hp, hq]; module
      rw [e1, e2, sub_zero]
    by_contra hne
    exact fcomb_ne_zero p q r hΔ (x := α4 - α') (y := γ4 - γ')
      (by intro h; apply hne; have := congrArg Prod.fst h; simpa [sub_eq_zero] using this) h0
  subst huniq
  have eO : fpoint p q r d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eA : fpoint p q r d (1, 0, 0) = a := by simp only [fpoint, fcomb, hp]; module
  have eB : fpoint p q r d (α4, γ4, 0) = b' := by rw [hb']; simp only [fpoint, fcomb, hp, hq]; module
  have eC : fpoint p q r d (0, 1, 0) = c := by simp only [fpoint, fcomb, hq]; module
  have eB1 : fpoint p q r d (0, 0, 1) = b := by simp only [fpoint, fcomb, hr]; module
  have eC' : fpoint p q r d (1, 0, β1) = c' := by rw [hc']; simp only [fpoint, fcomb, hp, hr]; module
  have eA' : fpoint p q r d (0, γ6, β6) = a' := by rw [ha']; simp only [fpoint, fcomb, hq, hr]; module
  refine face_hasLexCellAt (V8 a a' b b' c c' d) p q r d hΔ hlev.1 hlev.2 hα' hγ4 hβ1 hβ6 hγ6 hγ61 ?_ ?_ ?_ ?_ ?_
  · rw [eO]; simp [V8]
  · rw [eA]; simp [V8]
  · rw [eB]; simp [V8]
  · rw [eC]; simp [V8]
  · intro y hy
    rw [eO, eA, eB, eC, eB1, eC', eA']
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto

end Type08Sp
end Minimality

