module

public import Minimality.FaceCircleW
public import Minimality.DepthSeparated

@[expose] public section

/-!
# Four-rim split and triangle end condition (ARCH-IDEAS-FABLE 1.3, 1.1)

* `fourRim_unimodal_of_depthSeparated` (Lemma A): on a 4-rim with injective depths a
  depth-separated pair `(e, c)` with `c` not an end of `e` forces cyclic unimodality (leaf S never
  fires where leaf U fails); only the chain conditions are used.
* `triangle_end_condition`, `lemmaW'_triangle` (Lemma B): for a triangle face the end condition
  of Lemma W' is automatic.
-/

open scoped RealInnerProductSpace

namespace Minimality

theorem fourRim_unimodal_of_not_alt (z : ZMod 4 → ℝ) (hinj : Function.Injective z)
    (h1 : ¬ (z 1 < z 0 ∧ z 3 < z 0 ∧ z 1 < z 2 ∧ z 3 < z 2))
    (h2 : ¬ (z 0 < z 1 ∧ z 2 < z 1 ∧ z 0 < z 3 ∧ z 2 < z 3)) : IsCyclicUnimodal z := by
  refine ⟨hinj, ?_⟩
  have n01 : z 0 ≠ z 1 := fun h => by have := hinj h; revert this; decide
  have n02 : z 0 ≠ z 2 := fun h => by have := hinj h; revert this; decide
  have n03 : z 0 ≠ z 3 := fun h => by have := hinj h; revert this; decide
  have n12 : z 1 ≠ z 2 := fun h => by have := hinj h; revert this; decide
  have n13 : z 1 ≠ z 3 := fun h => by have := hinj h; revert this; decide
  have n23 : z 2 ≠ z 3 := fun h => by have := hinj h; revert this; decide
  rw [Finset.card_filter]
  have key : ∀ f : ZMod 4 → ℕ, ∑ i, f i = f 0 + f 1 + f 2 + f 3 := fun f => Fin.sum_univ_four f
  rw [key]
  have e0 : ((0 : ZMod 4) - 1) = 3 := by decide
  have e1 : ((1 : ZMod 4) - 1) = 0 := by decide
  have e2 : ((2 : ZMod 4) - 1) = 1 := by decide
  have e3 : ((3 : ZMod 4) - 1) = 2 := by decide
  have f0 : ((0 : ZMod 4) + 1) = 1 := by decide
  have f1 : ((1 : ZMod 4) + 1) = 2 := by decide
  have f2 : ((2 : ZMod 4) + 1) = 3 := by decide
  have f3 : ((3 : ZMod 4) + 1) = 0 := by decide
  simp only [e0, e1, e2, e3, f0, f1, f2, f3]
  rcases lt_or_gt_of_ne n01 with a | a <;> rcases lt_or_gt_of_ne n02 with b | b <;>
  rcases lt_or_gt_of_ne n03 with c | c <;> rcases lt_or_gt_of_ne n12 with d | d <;>
  rcases lt_or_gt_of_ne n13 with e | e <;> rcases lt_or_gt_of_ne n23 with f | f <;>
  simp_all [not_lt_of_gt, a.le, b.le, c.le, d.le, e.le, f.le] <;> (try (exfalso; linarith))


/-- **Lemma A (4-rim).** On a 4-rim with injective depths, a depth-separated pair whose
corner `c` is not an endpoint of the edge `[a, a+1]` forces cyclic unimodality: leaf S never
fires where leaf U fails.  Only the chain conditions are used. -/
theorem fourRim_unimodal_of_depthSeparated (p : ZMod 4 → ℝ²) (z : ZMod 4 → ℝ)
    (hinj : Function.Injective z) {a c : ZMod 4} (hca : c ≠ a) (hca1 : c ≠ a + 1)
    (h : IsDepthSeparatedPair p z a c) : IsCyclicUnimodal z := by
  obtain ⟨_, h⟩ := h
  have hcs : ∀ a : ZMod 4, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by decide
  apply fourRim_unimodal_of_not_alt z hinj <;> intro hh <;> obtain ⟨q1, q2, q3, q4⟩ := hh <;>
  revert hca hca1 h <;> (rcases hcs a with rfl | rfl | rfl | rfl) <;> (rcases hcs c with rfl | rfl | rfl | rfl) <;>
  first
  | (intro hca; exact absurd rfl hca)
  | (intro _ hca1; exact False.elim (hca1 (by decide)))
  | (intro _ _ h
     rcases h with ⟨hA, hB⟩ | ⟨hA, hB⟩ <;>
     (try have a1 := hA 1 (by decide) (by decide)) <;> (try have a2 := hA 2 (by decide) (by decide)) <;>
     (try have a3 := hA 3 (by decide) (by decide)) <;>
     (try have b1 := hB 1 (by decide) (by decide)) <;> (try have b2 := hB 2 (by decide) (by decide)) <;>
     (try have b3 := hB 3 (by decide) (by decide)) <;>
     simp only [Nat.cast_ofNat, Nat.cast_one, show ((0:ZMod 4)+1)=1 from by decide, show ((0:ZMod 4)+2)=2 from by decide, show ((0:ZMod 4)+3)=3 from by decide, show ((1:ZMod 4)+1)=2 from by decide, show ((1:ZMod 4)+2)=3 from by decide, show ((1:ZMod 4)+3)=0 from by decide, show ((2:ZMod 4)+1)=3 from by decide, show ((2:ZMod 4)+2)=0 from by decide, show ((2:ZMod 4)+3)=1 from by decide, show ((3:ZMod 4)+1)=0 from by decide, show ((3:ZMod 4)+2)=1 from by decide, show ((3:ZMod 4)+3)=2 from by decide] at * <;> linarith)


/-- **Lemma B (triangle face, end condition is automatic).**  A triangle face with chord ends of
depths `a`, `b` and middle vertex of depth `m` (pairwise distinct): its lowest depth `lo` and
highest depth `hi` are among `a, b, m` and bound them; then `lo` or `hi` is an end. -/
theorem triangle_end_condition {a b m lo hi : ℝ} (hab : a ≠ b) (ham : a ≠ m) (hbm : b ≠ m)
    (hlo : lo = a ∨ lo = b ∨ lo = m) (hhi : hi = a ∨ hi = b ∨ hi = m)
    (hla : lo ≤ a) (hlb : lo ≤ b) (hlm : lo ≤ m) (hha : a ≤ hi) (hhb : b ≤ hi) (hhm : m ≤ hi) :
    lo = a ∨ lo = b ∨ hi = a ∨ hi = b := by
  rcases hlo with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · rcases hhi with h' | h' | h'
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr h'))
    · exfalso; subst h; subst h'
      rcases lt_or_gt_of_ne ham with h1 | h1 <;> linarith

/-- Lemma W′ for a triangle face `(m, A, B)`: no end condition. -/
theorem lemmaW'_triangle {a b m lo hi : ℝ} {R : List ℝ} (hnd : (a :: b :: R).Nodup)
    (hab : a ≠ b) (ham : a ≠ m) (hbm : b ≠ m)
    (hlo : lo = a ∨ lo = b ∨ lo = m) (hhi : hi = a ∨ hi = b ∨ hi = m)
    (hla : lo ≤ a) (hlb : lo ≤ b) (hlm : lo ≤ m) (hha : a ≤ hi) (hhb : b ≤ hi) (hhm : m ≤ hi)
    (hloR : lo ∉ R) (hhiR : hi ∉ R) :
    (CU (skel1 a lo b ++ R) ∨ CU (skel1 a hi b ++ R)) ↔ CU (a :: b :: R) := by
  rw [lemmaW' hnd hla hlb hha hhb hloR hhiR]
  have := triangle_end_condition hab ham hbm hlo hhi hla hlb hlm hha hhb hhm
  tauto

end Minimality
