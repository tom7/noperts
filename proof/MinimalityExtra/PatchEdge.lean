module

public import Mathlib
public import MinimalityExtra
public import Minimality.RobustEdge

/-!
# The Patch-edge lemma
-/

@[expose] public section

open scoped Classical

local notation "E3" => EuclideanSpace ℝ (Fin 3)


namespace MinimalityExtra

/-- The tetrahedra `(a, b, c, v)` and `(v, a, c, b)` have the same orientation (an even permutation). -/
theorem det3_patch_identity (v a b c : E3) :
    det3 (b - a) (c - a) (v - a) = det3 (a - v) (c - v) (b - v) := by
  simp only [det3, PiLp.sub_apply]; ring

theorem det3_patch_shift (v w a b c : E3) :
    det3 (b - a) (c - a) (w - a) = det3 (b - a) (c - a) (v - a) - det3 (c - a) (b - a) (w - v) := by
  simp only [det3, PiLp.sub_apply]; ring

/-- Proof of `PatchEdgeBeyondPlane`: the sign of `v` against the plane `a b c` is the sign of `b`
against the plane `v a c`. -/
theorem patchEdgeBeyondPlane : PatchEdgeBeyondPlane := by
  intro V v w a b c hv hw ha hb hc q1 hface hcrease
  have hb0 : 0 ≤ det3 (a - v) (c - v) (b - v) := by
    rcases hface with h | h
    · exact h b hb
    · have := h w hw; linarith
  rw [det3_patch_identity]; exact lt_of_le_of_ne hb0 (Ne.symm hcrease)

end MinimalityExtra

namespace Minimality

open scoped RealInnerProductSpace

/-- **Patch-edge lemma with Lemma E.**  Faces `v a c`, `v c b` (a supporting plane `v a c`, with `b`
off it), the shadow along `v w` strictly convex `(q, a, c, b)` with every other point a middle or
hidden, and `w` weakly on the other side of the plane `a b c`: `V` is Rupert (Corollary 14.1 with
ties, `isRupert_edgePair_robust`, the hypothesis `hE` supplied by `PatchEdgeBeyondPlane`). -/
theorem patchEdge_isRupert {v w a b c : E3} (V : Finset E3)
    (hvV : v ∈ V) (hwV : w ∈ V) (haV : a ∈ V) (hbV : b ∈ V) (hcV : c ∈ V)
    (q₁ : 0 < det3 (a - v) (c - v) (w - v)) (q₂ : 0 < det3 (c - a) (b - a) (w - v))
    (q₃ : 0 < det3 (b - c) (v - c) (w - v)) (q₄ : 0 < det3 (v - b) (a - b) (w - v))
    (hface : (∀ z ∈ V, 0 ≤ det3 (a - v) (c - v) (z - v)) ∨
      (∀ z ∈ V, det3 (a - v) (c - v) (z - v) ≤ 0))
    (hcrease : det3 (a - v) (c - v) (b - v) ≠ 0)
    (hw : det3 (b - a) (c - a) (w - a) ≤ 0)
    (h3 : ¬ (⟪a, w - v⟫ = ⟪c, w - v⟫ ∧ ⟪c, w - v⟫ = ⟪b, w - v⟫))
    (hV : ∀ z ∈ V, z = v ∨ z = w ∨ z = a ∨ z = b ∨ z = c ∨ EdgeMid v w a b z ∨
      EdgeHidden (w - v) v a c b z)
    (hnd₁ : NoHDNAt (V.erase w) (w - v)) (hnd₂ : NoHDNAt (V.erase v) (w - v)) :
    IsRupert V := by
  have hb0 : 0 ≤ det3 (a - v) (c - v) (b - v) := by
    rcases hface with h | h
    · exact h b hbV
    · have := h w hwV; linarith
  have e : det3 (b - a) (c - a) (v - a) = det3 (a - v) (c - v) (b - v) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have hF : 0 < det3 (b - a) (c - a) (v - a) := by
    rw [e]; exact lt_of_le_of_ne hb0 (Ne.symm hcrease)
  exact isRupert_edgePair_robust V hvV hwV haV hbV hcV q₁ q₂ q₃ q₄
    (by nlinarith) h3 hV hnd₁ hnd₂

end Minimality
