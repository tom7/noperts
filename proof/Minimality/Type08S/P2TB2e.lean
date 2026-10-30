module

public import Minimality.Type08S.P2TB2d

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkP / B2e: `K2_slide_angBig` (statement as PT0.lean).
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- **`K_2` on `Q_ab`'s circle with `∠q + ∠q' > π`** (29.12 B1, Theorem D): `a'` leaves `ḡ = c̄` into the interior
(SlideTest: zero at `ℓ`, positive derivative, by `AngBig`); otherwise the generic `np_K2` rows. -/
theorem K2_slide_angBig {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hT : IsT a' b c d)
    (hang : AngBig a b b' c d) {s : Bool}
    {k' : ℕ} [NeZero k'] {σ : ZMod k' → ZMod (test08 1 s false).k}
    (hrim : RimCertAt (pts08 a a' b b' c c' d) ((test08 1 s false).view (pts08 a a' b b' c c' d))
      ((test08 1 s false).lab ∘ σ))
    (hrob : IsRobustUnimodal (fun i => ⟪pts08 a a' b b' c c' d ((test08 1 s false).lab (σ i)),
      (test08 1 s false).view (pts08 a a' b b' c c' d)⟫))
    (hnp : NoPersistHDN (fun i => pts08 a a' b b' c c' d ((test08 1 s false).lab (σ i)))
        ((test08 1 s false).view (pts08 a a' b b' c c' d)) (eF a a' b b' c c' d (1, s, false))) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨e1, e2, e3, κ, hF, hκ, hxe, hf2, hL, hr'⟩ := frame_K2 N
  have hκ0 : -κ ≠ 0 := neg_ne_zero.mpr hκ
  cases s
  · have hlab : ∀ j : ZMod 4, pts08 a a' b b' c c' d ((test08 1 false false).lab j) = quad d c' b' c j := by
      intro j; rcases zmod4_cases j with rfl | rfl | rfl | rfl <;> rfl
    have hu : (test08 1 false false).view (pts08 a a' b b' c c' d) = κ • e3 := by
      show -(b - d) = κ • e3
      rw [neg_sub]; exact hxe
    obtain ⟨hk3, hcyc, hleft, hz⟩ := rim_transfer (m := 4) (test08 1 false false).lab σ _
      (quad d c' b' c) hlab hrim hrob
    refine np_K2T N hT hang hF hκ (Or.inl rfl) hxe hf2 hL hr' hk3 σ _ (eF a a' b b' c c' d (1, false, false))
      hu ?_ hcyc hleft hz ?_
    · exact (show eF a a' b b' c c' d (1, false, false) = _ from rfl).trans
        (eF_of_view hF _ _ κ hκ hu hf2)
    · have hfun : (fun i => pts08 a a' b b' c c' d ((test08 1 false false).lab (σ i))) =
          fun i => quad d c' b' c (σ i) := funext fun i => hlab (σ i)
      rw [hfun] at hnp; exact hnp
  · have hlab : ∀ j : ZMod 4, pts08 a a' b b' c c' d ((test08 1 true false).lab j) = quad d c' b' c j := by
      intro j; rcases zmod4_cases j with rfl | rfl | rfl | rfl <;> rfl
    have hu : (test08 1 true false).view (pts08 a a' b b' c c' d) = (-κ) • e3 := by
      show b - d = (-κ) • e3
      rw [neg_smul, ← hxe]; abel
    obtain ⟨hk3, hcyc, hleft, hz⟩ := rim_transfer (m := 4) (test08 1 true false).lab σ _
      (quad d c' b' c) hlab hrim hrob
    refine np_K2T N hT hang hF hκ (Or.inr rfl) hxe hf2 hL hr' hk3 σ _ (eF a a' b b' c c' d (1, true, false))
      hu ?_ hcyc hleft hz ?_
    · exact (show eF a a' b b' c c' d (1, true, false) = _ from rfl).trans
        (eF_of_view hF _ _ (-κ) hκ0 hu hf2)
    · have hfun : (fun i => pts08 a a' b b' c c' d ((test08 1 true false).lab (σ i))) =
          fun i => quad d c' b' c (σ i) := funext fun i => hlab (σ i)
      rw [hfun] at hnp; exact hnp

end Type08Sp
end Minimality

