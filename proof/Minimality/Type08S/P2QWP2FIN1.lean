module

public import Minimality.Type08S.P2QQ0c
public import Minimality.Type08S.P2QWSCl
public import Minimality.Type08S.P2QWP2PF0
public import Minimality.Type08S.P2QWP2PF1
public import Minimality.Type08S.P2QWP2PF2
public import Minimality.Type08S.P2QWP2PF3
public import Minimality.Type08S.P2QWP2NP1
public import Minimality.Type08S.P2QWP2NP2
public import Minimality.Type08S.P2QWP2NP3
public import Minimality.Type08S.P2QWP2NP5
public import Minimality.Type08S.P2QWP2NP6
public import Minimality.Type08S.P2FIN0

@[expose] public section

set_option relaxedAutoImplicit true
set_option relaxedAutoImplicit true

/-!
# P3a: `close_hdn_np` (statement identical to `P2Pkg.close_hdn_np`).
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace W5

/-- Screen direction of the face circle `F` of the closing `t` (identical to `P2Pkg.eF`). -/
noncomputable def eF (a a' b b' c c' d : ℝ³) (t : Fin 3 × Bool × Bool) : ℝ³ :=
  let u := (test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d)
  let v := if t.1 = 0 then b - a' else if t.2.2 then c - d else c' - b
  v - (⟪v, u⟫ / ⟪u, u⟫) • u

theorem eF_of_view {e1 e2 e3 : ℝ³} (hF : Fr e1 e2 e3) (u v : ℝ³) (κv : ℝ) (hκv : κv ≠ 0)
    (hu : u = κv • e3) (hv2 : ⟪v, e2⟫ = 0) :
    v - (⟪v, u⟫ / ⟪u, u⟫) • u = ⟪v, e1⟫ • e1 := by
  subst hu; exact eF_calc hF hκv v hv2

theorem close_hdn_np {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d)
    (hT : ¬ IsT a' b c d) (hT' : ¬ IsT' a b c' d) {t : Fin 3 × Bool × Bool} (ht : t ∈ SC08)
    (hreg : (t.1 = 0 ∧ RegN2 N.F) ∨ (t.1 = 1 ∧ RegT4 N.F))
    {k' : ℕ} [NeZero k'] {σ : ZMod k' → ZMod (test08 t.1 t.2.1 t.2.2).k}
    (hrim : RimCertAt (pts08 a a' b b' c c' d) ((test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d))
      ((test08 t.1 t.2.1 t.2.2).lab ∘ σ))
    (hrob : IsRobustUnimodal (fun i => ⟪pts08 a a' b b' c c' d ((test08 t.1 t.2.1 t.2.2).lab (σ i)),
      (test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d)⟫))
    (hnp : NoPersistHDN (fun i => pts08 a a' b b' c c' d ((test08 t.1 t.2.1 t.2.2).lab (σ i)))
        ((test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d)) (eF a a' b b' c c' d t)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨i, s, j⟩ := t
  simp only [SC08, Set.mem_setOf_eq] at ht
  dsimp only at ht hreg hrim hrob hnp
  rcases hreg with ⟨rfl, hr⟩ | ⟨rfl, hr⟩
  · -- N2 `K_c`
    have hj : j = true := by
      rcases ht with ⟨-, h⟩ | h
      · exact h
      · exact absurd h (by decide)
    subst hj
    obtain ⟨e1, e2, e3, κ, hF, hκ, hce, hb2, hL, hr'⟩ := frame_N2 N
    cases s
    · -- s = false: view = -(c - a')
      have hlab : ∀ j : ZMod 4, pts08 a a' b b' c c' d ((test08 0 false true).lab j) = quad c b c' b' j := by
        intro j; rcases zmod4_cases j with rfl | rfl | rfl | rfl <;> rfl
      have hκ0 : -κ ≠ 0 := neg_ne_zero.mpr hκ
      have hu : (test08 0 false true).view (pts08 a a' b b' c c' d) = (-κ) • e3 := by
        show -(c - a') = (-κ) • e3
        rw [hce, neg_smul]
      obtain ⟨hk3, hcyc, hleft, hz⟩ := rim_transfer (m := 4) (test08 0 false true).lab σ _
        (quad c b c' b') hlab hrim hrob
      refine np_N2 N hr hF hκ (Or.inr rfl) hce hb2 hL hr' hk3 σ _ (eF a a' b b' c c' d (0, false, true)) hu ?_ hcyc hleft hz ?_
      · exact (show eF a a' b b' c c' d (0, false, true) = _ from rfl).trans
          (eF_of_view hF _ _ (-κ) hκ0 hu hb2)
      · have hfun : (fun i => pts08 a a' b b' c c' d ((test08 0 false true).lab (σ i))) =
            fun i => quad c b c' b' (σ i) := funext fun i => hlab (σ i)
        rw [hfun] at hnp; exact hnp
    · have hlab : ∀ j : ZMod 4, pts08 a a' b b' c c' d ((test08 0 true true).lab j) = quad c b c' b' j := by
        intro j; rcases zmod4_cases j with rfl | rfl | rfl | rfl <;> rfl
      have hu : (test08 0 true true).view (pts08 a a' b b' c c' d) = κ • e3 := hce
      obtain ⟨hk3, hcyc, hleft, hz⟩ := rim_transfer (m := 4) (test08 0 true true).lab σ _
        (quad c b c' b') hlab hrim hrob
      refine np_N2 N hr hF hκ (Or.inl rfl) hce hb2 hL hr' hk3 σ _ (eF a a' b b' c c' d (0, true, true)) hu ?_ hcyc hleft hz ?_
      · exact (show eF a a' b b' c c' d (0, true, true) = _ from rfl).trans
          (eF_of_view hF _ _ κ hκ hu hb2)
      · have hfun : (fun i => pts08 a a' b b' c c' d ((test08 0 true true).lab (σ i))) =
            fun i => quad c b c' b' (σ i) := funext fun i => hlab (σ i)
        rw [hfun] at hnp; exact hnp
  · -- T4: `K_b` (`j = true`) or `K_2` (`j = false`)
    cases j
    · -- `K_2`
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
        refine np_K2 N hr hF hκ (Or.inl rfl) hxe hf2 hL hr' hk3 σ _ (eF a a' b b' c c' d (1, false, false))
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
        refine np_K2 N hr hF hκ (Or.inr rfl) hxe hf2 hL hr' hk3 σ _ (eF a a' b b' c c' d (1, true, false))
          hu ?_ hcyc hleft hz ?_
        · exact (show eF a a' b b' c c' d (1, true, false) = _ from rfl).trans
            (eF_of_view hF _ _ (-κ) hκ0 hu hf2)
        · have hfun : (fun i => pts08 a a' b b' c c' d ((test08 1 true false).lab (σ i))) =
              fun i => quad d c' b' c (σ i) := funext fun i => hlab (σ i)
          rw [hfun] at hnp; exact hnp
    · -- `K_b`
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
        refine np_Kb N hr hF hκ (Or.inr rfl) hxe hf2 hL hr' hk3 σ _ (eF a a' b b' c c' d (1, false, true))
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
        refine np_Kb N hr hF hκ (Or.inl rfl) hxe hf2 hL hr' hk3 σ _ (eF a a' b b' c c' d (1, true, true))
          hu ?_ hcyc hleft hz ?_
        · exact (show eF a a' b b' c c' d (1, true, true) = _ from rfl).trans
            (eF_of_view hF _ _ κ hκ hu hf2)
        · have hfun : (fun i => pts08 a a' b b' c c' d ((test08 1 true true).lab (σ i))) =
              fun i => quad b c' b' c (σ i) := funext fun i => hlab (σ i)
          rw [hfun] at hnp; exact hnp

end W5
end Type08Sp
end Minimality

