module

public import Minimality.Type08S.SCl

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true

set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

theorem rupert_of_SCcl2 {a a' b b' c c' d : ℝ³} {t : Fin 3 × Bool × Bool}
    (h : SCcl2 a a' b b' c c' d t) : IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  rcases h with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
  · exact rupert_SCfN2' h
  · have := rupert_SCfT4' h
    convert this using 1
    ext y; simp only [mem_insert, mem_singleton]; tauto
  · have := rupert_SCfT4' h
    convert this using 1
    ext y; simp only [mem_insert, mem_singleton]; tauto

/-- **Refined limit theorem.**  Rupert, or a single-circle closing `t` with certified limit rim and
an HDN at its view that does not satisfy the explicit class-(c) predicate `ClassCt`. -/
theorem isRupert_type08_limit_hdnC {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    {q : ℕ} (hq : q ≤ 2) (ties : Fin q → Fin 3 × Fin 7 × Fin 7)
    (hties : ∀ t, ⟪pts08 a a' b b' c c' d (ties t).2.1 - pts08 a a' b b' c c' d (ties t).2.2,
      (grp08 (ties t).1).view (pts08 a a' b b' c c' d)⟫ = 0)
    (hind : TieIndep (fun t => pts08 a a' b b' c c' d (ties t).2.1 - pts08 a a' b b' c c' d (ties t).2.2)
      (fun t => (grp08 (ties t).1).view (pts08 a a' b b' c c' d)))
    (hcover : ∀ i, ∀ T ∈ (grp08 i).tests, ∀ u v : ZMod T.k,
      T.depth (pts08 a a' b b' c c' d) u = T.depth (pts08 a a' b b' c c' d) v →
      Relation.EqvGen (fun p p' => ∃ t, (ties t).1 = i ∧ (ties t).2 = (p, p')) (T.lab u) (T.lab v))
    (hnt : ¬ Touch a a' b b' c c' d)
    (hTco : IsT a' b c d → ¬ CoT2 a a' b b' c c' d)
    (hT'co : IsT' a b c' d → ¬ CoT'2 a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨
      ∃ t ∈ SC08,
        (∃ (k' : ℕ) (_ : NeZero k') (σ : ZMod k' → ZMod (test08 t.1 t.2.1 t.2.2).k),
          RimCertAt (pts08 a a' b b' c c' d) ((test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d))
            ((test08 t.1 t.2.1 t.2.2).lab ∘ σ)) ∧
        ¬ NoHDNAt (insert d ({a, a', b, b', c, c'} : Finset ℝ³))
          ((test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d)) ∧
        ¬ ClassCt a a' b b' c c' d t := by
  classical
  rcases isRupert_type08_limit_hdn_rim N hq ties hties hind hcover hnt hTco hT'co with h | ⟨t, ht, hr, hn⟩
  · exact Or.inl h
  · by_cases hs : ClassCt a a' b b' c c' d t
    · exact Or.inl (rupert_of_SCcl2 (SCcl2_of_ClassCt N hs))
    · exact Or.inr ⟨t, ht, hr, hn, hs⟩

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.isRupert_type08_limit_hdnC
#print axioms Minimality.Type08Sp.SCcl2_of_ClassCt
