module

public import Minimality.Type08S.P2H13

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# pkH H14: the final `close_hdn_pers'` — P2Pkg's statement plus the SC2 hypotheses for the chord end at `f`

`CEfN2`, `CEfKb`, `CEfK2`: what the SC2 package (SC2-S, SC2-S′, SC2-V; sp08f §2) must prove: a robust closing
whose persistent HDN has its foot at the chord end `f̄` (`CEf5`), in the canonical frame of the closing, is Rupert.
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- SC2 hypothesis for N2 `K_c` (`x' = a'`, `x = c`, `f = b`, `r = c'`, `g = b'`). -/
def CEfN2 (a a' b b' c c' d : ℝ³) : Prop :=
  ∀ (e1 e2 e3 : ℝ³) (κ : ℝ), Fr e1 e2 e3 → κ ≠ 0 → c - a' = κ • e3 → ⟪b - a', e2⟫ = 0 →
    0 < ⟪b - a', e1⟫ → 0 < ⟪c' - a', e2⟫ → Rob4 κ ⟪b - a', e3⟫ ⟪c' - a', e3⟫ ⟪b' - a', e3⟫ →
    CEf5 ⟪b - a', e1⟫ κ ⟪b - a', e3⟫ ⟪c' - a', e1⟫ ⟪c' - a', e2⟫ ⟪c' - a', e3⟫ ⟪b' - a', e1⟫ ⟪b' - a', e2⟫
      ⟪b' - a', e3⟫ → IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³))

/-- SC2 hypothesis for T4 `K_b` (`x' = d`, `x = b`, `f = c`, `r = b'`, `g = c'`). -/
def CEfKb (a a' b b' c c' d : ℝ³) : Prop :=
  ∀ (e1 e2 e3 : ℝ³) (κ : ℝ), Fr e1 e2 e3 → κ ≠ 0 → b - d = κ • e3 → ⟪c - d, e2⟫ = 0 →
    0 < ⟪c - d, e1⟫ → 0 < ⟪b' - d, e2⟫ → Rob4 κ ⟪c - d, e3⟫ ⟪b' - d, e3⟫ ⟪c' - d, e3⟫ →
    CEf5 ⟪c - d, e1⟫ κ ⟪c - d, e3⟫ ⟪b' - d, e1⟫ ⟪b' - d, e2⟫ ⟪b' - d, e3⟫ ⟪c' - d, e1⟫ ⟪c' - d, e2⟫
      ⟪c' - d, e3⟫ → IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³))

/-- SC2 hypothesis for T4 `K_2` (`x' = b`, `x = d`, `f = c'`, `r = b'`, `g = c`). -/
def CEfK2 (a a' b b' c c' d : ℝ³) : Prop :=
  ∀ (e1 e2 e3 : ℝ³) (κ : ℝ), Fr e1 e2 e3 → κ ≠ 0 → d - b = κ • e3 → ⟪c' - b, e2⟫ = 0 →
    0 < ⟪c' - b, e1⟫ → 0 < ⟪b' - b, e2⟫ → Rob4 κ ⟪c' - b, e3⟫ ⟪b' - b, e3⟫ ⟪c - b, e3⟫ →
    CEf5 ⟪c' - b, e1⟫ κ ⟪c' - b, e3⟫ ⟪b' - b, e1⟫ ⟪b' - b, e2⟫ ⟪b' - b, e3⟫ ⟪c - b, e1⟫ ⟪c - b, e2⟫
      ⟪c - b, e3⟫ → IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³))

theorem close_hdn_pers' {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (hT : ¬ IsT a' b c d) (hT' : ¬ IsT' a b c' d) {t : Fin 3 × Bool × Bool} (ht : t ∈ SC08)
    (hreg : (t.1 = 0 ∧ RegN2 N.F) ∨ (t.1 = 1 ∧ RegT4 N.F))
    {k' : ℕ} [NeZero k'] {σ : ZMod k' → ZMod (test08 t.1 t.2.1 t.2.2).k}
    (hrim : RimCertAt (pts08 a a' b b' c c' d) ((test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d))
      ((test08 t.1 t.2.1 t.2.2).lab ∘ σ))
    (hrob : IsRobustUnimodal (fun i => ⟪pts08 a a' b b' c c' d ((test08 t.1 t.2.1 t.2.2).lab (σ i)),
      (test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d)⟫))
    (hp : ¬ NoPersistHDN (fun i => pts08 a a' b b' c c' d ((test08 t.1 t.2.1 t.2.2).lab (σ i)))
        ((test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d)) (eF a a' b b' c c' d t))
    -- the SC2 package, chord end at `f` only (the parallel set is empty on `Norm08`, H13)
    (hfN2 : RegN2 N.F → CEfN2 a a' b b' c c' d) (hfT4 : RegT4 N.F → CEfKb a a' b b' c c' d ∧ CEfK2 a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) :=
  close_hdn_pers N hT hT' ht hreg hrim hrob hp (fun hr => SC2N2_of_CEf N (hfN2 hr))
    (fun hr => ⟨SC2Kb_of_CEf N (hfT4 hr).1, SC2K2_of_CEf N (hfT4 hr).2⟩)

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.close_hdn_pers'
