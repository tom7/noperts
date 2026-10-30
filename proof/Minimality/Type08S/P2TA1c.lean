module

public import Minimality.Type08S.P2TA1b

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkP / A1c: `close_hdn_np_KbT`.
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

theorem close_hdn_np_KbT {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hT : IsT a' b c d) {s : Bool}
    {k' : ℕ} [NeZero k'] {σ : ZMod k' → ZMod (test08 1 s true).k}
    (hrim : RimCertAt (pts08 a a' b b' c c' d) ((test08 1 s true).view (pts08 a a' b b' c c' d))
      ((test08 1 s true).lab ∘ σ))
    (hrob : IsRobustUnimodal (fun i => ⟪pts08 a a' b b' c c' d ((test08 1 s true).lab (σ i)),
      (test08 1 s true).view (pts08 a a' b b' c c' d)⟫))
    (hnp : NoPersistHDN (fun i => pts08 a a' b b' c c' d ((test08 1 s true).lab (σ i)))
        ((test08 1 s true).view (pts08 a a' b b' c c' d)) (eF a a' b b' c c' d (1, s, true))) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨e1, e2, e3, κ, hF, hκ, hxe, hf2, hL, hr'⟩ := frame_Kb N
  have hκ0 : -κ ≠ 0 := neg_ne_zero.mpr hκ
  cases s
  · have hlab : ∀ j : ZMod 4, pts08 a a' b b' c c' d ((test08 1 false true).lab j) = quad b c' b' c j := by
      intro j; rcases zmod4_cases j with rfl | rfl | rfl | rfl <;> rfl
    have hu : (test08 1 false true).view (pts08 a a' b b' c c' d) = (-κ) • e3 := by
      show -(b - d) = (-κ) • e3
      rw [hxe, neg_smul]
    obtain ⟨hk3, hcyc, hleft, hz⟩ := rim_transfer (m := 4) (test08 1 false true).lab σ _
      (quad b c' b' c) hlab hrim hrob
    refine np_KbT N hT hF hκ (Or.inr rfl) hxe hf2 hL hr' hk3 σ _ (eF a a' b b' c c' d (1, false, true))
      hu ?_ hcyc hleft hz ?_
    · exact (show eF a a' b b' c c' d (1, false, true) = _ from rfl).trans
        (eF_of_view hF _ _ (-κ) hκ0 hu hf2)
    · have hfun : (fun i => pts08 a a' b b' c c' d ((test08 1 false true).lab (σ i))) =
          fun i => quad b c' b' c (σ i) := funext fun i => hlab (σ i)
      rw [hfun] at hnp; exact hnp
  · have hlab : ∀ j : ZMod 4, pts08 a a' b b' c c' d ((test08 1 true true).lab j) = quad b c' b' c j := by
      intro j; rcases zmod4_cases j with rfl | rfl | rfl | rfl <;> rfl
    have hu : (test08 1 true true).view (pts08 a a' b b' c c' d) = κ • e3 := hxe
    obtain ⟨hk3, hcyc, hleft, hz⟩ := rim_transfer (m := 4) (test08 1 true true).lab σ _
      (quad b c' b' c) hlab hrim hrob
    refine np_KbT N hT hF hκ (Or.inl rfl) hxe hf2 hL hr' hk3 σ _ (eF a a' b b' c c' d (1, true, true))
      hu ?_ hcyc hleft hz ?_
    · exact (show eF a a' b b' c c' d (1, true, true) = _ from rfl).trans
        (eF_of_view hF _ _ κ hκ hu hf2)
    · have hfun : (fun i => pts08 a a' b b' c c' d ((test08 1 true true).lab (σ i))) =
          fun i => quad b c' b' c (σ i) := funext fun i => hlab (σ i)
      rw [hfun] at hnp; exact hnp

end Type08Sp
end Minimality

