module


public import Mathlib

@[expose] public section

set_option autoImplicit true

/-!
# Lemma 08.2' (weak order from robustness), pure real-number form (sp08b/draft.md §4a)
-/

namespace Minimality
namespace Type08Sp

/-- A 4-cycle with diagonal depth pairs `{x,y}`, `{u,v}` has a two-peaked refinement iff the
pairs are weakly separated (so it is *not robust*). -/
def Sep (x y u v : ℝ) : Prop := max u v ≤ min x y ∨ max x y ≤ min u v

/-- `zs` lies strictly between `p` and `q`, or `p = q = zs`. -/
def Btw (p q zs : ℝ) : Prop := (p < zs ∧ zs < q) ∨ (q < zs ∧ zs < p) ∨ (p = q ∧ zs = p)

set_option maxHeartbeats 0 in
/-- **Lemma 08.2'.**  `R1 = (b,c',b',c)` robust with class-(d) HDN of foot depth `z*` (between
`C,B` and between `P,R`), `R2' = (2,c',b',c)` and `X_ba' = (b,c',b',a')` not robust: the weak
order `W ≤ C`, `P ≤ C < B ≤ R`, `B ≤ A`, `P < R`. -/
theorem lemma082p {W B C A P R zs : ℝ} (h1 : ¬ Sep B P C R) (h2 : Sep W P R C)
    (h3 : Sep B P R A) (hz1 : Btw C B zs) (hz2 : Btw P R zs) (hWB : W < B) :
    W ≤ C ∧ P ≤ C ∧ C < B ∧ B ≤ R ∧ B ≤ A ∧ P < R := by
  simp only [Sep, Btw, max_le_iff, le_min_iff, not_or, not_and_or, not_le] at h1 h2 h3 hz1 hz2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> by_contra hn <;> push Not at hn <;>
    casesm* _ ∨ _, _ ∧ _ <;> linarith

end Type08Sp
end Minimality
