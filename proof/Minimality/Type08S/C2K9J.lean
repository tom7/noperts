module

public import Minimality.Type08S.C2K8J
public import Minimality.Type08S.C2K9I

@[expose] public section

/-!
# K9J: `tpA1iiK8_hasLexCell`: `TpA1iiK8` has a lex cell (no leftover).

L1 is empty (K9A); L2 (`C = 0`) is the cell `(b, d, c, b', c')` at `b - d` (K9F); L3 (`C > 0`) is the same cell
(L3a, K9G), and for `t = b` the cell `(b, d, c, b', c')` if `A > C` or `(a, d, c, b', c')` if `A < C` (K9H).
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

theorem k9_ip (P Q R : ℝ³) (x y z : ℝ) :
    ⟪x • P + y • Q + z • R, P⟫ = x * ⟪P, P⟫ + y * ⟪P, Q⟫ + z * ⟪P, R⟫ ∧
    ⟪x • P + y • Q + z • R, Q⟫ = x * ⟪P, Q⟫ + y * ⟪Q, Q⟫ + z * ⟪Q, R⟫ ∧
    ⟪x • P + y • Q + z • R, R⟫ = x * ⟪P, R⟫ + y * ⟪Q, R⟫ + z * ⟪R, R⟫ := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [inner_add_left, real_inner_smul_left, real_inner_comm P Q, real_inner_comm P R,
      real_inner_comm Q R]

set_option maxHeartbeats 6400000 in
theorem tpA1iiK8_hasLexCell {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (h : TpA1iiK8 a a' b b' c c' d) : HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hK, hnot⟩ := h
  have hT : TpA1ii a a' b b' c c' d := hK.1
  obtain ⟨β1, γ4, β6, γ6, hΔ, hγ4, hβ1, hγ6, hγ61, hβ6, hcv, hβγ, hc', hb', ha', htie⟩ := C2.k9_setup N hT
  obtain ⟨hm1, hv1, hm2, hv2⟩ := C2.k9_pts hc' hb' ha'
  have hCnn : 0 ≤ ⟪c - d, b - d⟫ := hT.2.2.2.1
  have hR0 : b - d ≠ 0 := by intro h0; rw [h0] at hΔ; simp [det3_expand] at hΔ
  have hA : 0 < ⟪b - d, b - d⟫ := real_inner_self_pos.2 hR0
  have hdone : HasLexCellAt (V8 a a' b b' c c' d) (b - d) → HasLexCell (V8 a a' b b' c c' d) :=
    fun hh => ⟨b - d, hR0, hh⟩
  set E := det3 (b - d) (c - d) (a - d) with hE
  have hE0 : E ≠ 0 := by
    intro h0; apply hΔ
    have e : det3 (c - d) (a - d) (b - d) = E := by simp only [hE, det3_expand]; ring
    rw [e, h0]
  have hEE : 0 < E * E := mul_self_pos.2 hE0
  have eX : det3 (a' - b) (c - d) (a - d) = (β6 - 1) * E := by
    rw [ha']; simp only [hE, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hXE : det3 (a' - b) (c - d) (a - d) * E = (β6 - 1) * (E * E) := by rw [eX]; ring
  -- inner products of `a' - c'` and `b - c'`
  have hva : a' - c' = γ6 • (c - d) + (-1 : ℝ) • (a - d) + (β6 - β1) • (b - d) := by
    rw [ha', hc']; module
  have hvb : b - c' = (0 : ℝ) • (c - d) + (-1 : ℝ) • (a - d) + (1 - β1) • (b - d) := by
    rw [hc']; module
  obtain ⟨ia1, ia2, ia3⟩ := k9_ip (c - d) (a - d) (b - d) γ6 (-1) (β6 - β1)
  obtain ⟨ib1, ib2, ib3⟩ := k9_ip (c - d) (a - d) (b - d) 0 (-1) (1 - β1)
  rw [← hva] at ia1 ia2 ia3
  rw [← hvb] at ib1 ib2 ib3
  have hGcd : ⟪c - d, a - d⟫ = ⟪c - d, a - d⟫ := rfl
  by_cases hC0 : ⟪c - d, b - d⟫ = 0
  · -- level face
    have hX : det3 (a' - b) (c - d) (a - d) ≠ 0 := fun hX0 => C2.k9_L1_false N hT hX0
    have hL2' : ¬ ((0 < det3 (a' - b) (c - d) (a - d) * det3 (b - d) (c - d) (a - d) →
          ⟪a' - c', c - d⟫ = 0 → 0 < ⟪a' - c', a - d⟫ ∨ 0 < ⟪a' - c', b - d⟫) ∧
        (det3 (a' - b) (c - d) (a - d) * det3 (b - d) (c - d) (a - d) < 0 → ⟪b - c', c - d⟫ = 0 →
          0 < ⟪b - c', a - d⟫ ∨ 0 < ⟪b - c', b - d⟫)) :=
      fun hh => hnot ⟨fun _ => hX, fun _ => hh, fun hp => absurd hC0 hp.ne'⟩
    have hB0 : ⟪a - d, b - d⟫ = 0 := by rw [htie, hC0]; ring
    rcases lt_trichotomy β6 1 with hlt | heq | hgt
    · -- L2b
      have hneg : det3 (a' - b) (c - d) (a - d) * det3 (b - d) (c - d) (a - d) < 0 := by
        rw [hXE]; nlinarith
      have hP1 : 0 < det3 (a' - b) (c - d) (a - d) * det3 (b - d) (c - d) (a - d) → ⟪a' - c', c - d⟫ = 0 →
          0 < ⟪a' - c', a - d⟫ ∨ 0 < ⟪a' - c', b - d⟫ := fun hp => absurd hp (not_lt.2 hneg.le)
      have hnP2 := fun hp2 => hL2' ⟨hP1, hp2⟩
      have hs : ⟪b - c', c - d⟫ = 0 := by
        by_contra hs; exact hnP2 (fun _ h => absurd h hs)
      have hxy : ¬ (0 < ⟪b - c', a - d⟫ ∨ 0 < ⟪b - c', b - d⟫) := fun hxy => hnP2 (fun _ _ => hxy)
      have hy : ⟪b - c', b - d⟫ ≤ 0 := by
        by_contra hy; exact hxy (Or.inr (not_le.1 hy))
      rw [ib1] at hs
      rw [ib3] at hy
      have hβ11 : 1 ≤ β1 := by
        by_contra hcon; push Not at hcon
        have : 0 < (1 - β1) * ⟪b - d, b - d⟫ := mul_pos (by linarith) hA
        nlinarith
      exact hdone (C2.k9_L2 (V8 a a' b b' c c' d) (c - d) (a - d) (b - d) d hΔ hγ4 hβ1 hγ6 hγ61 hβ6
        (σ := 0) le_rfl (by linarith) hC0 hB0 (by nlinarith) hm1 hv1)
    · exfalso; apply hX; rw [eX, heq]; ring
    · -- L2a
      have hpos : 0 < det3 (a' - b) (c - d) (a - d) * det3 (b - d) (c - d) (a - d) := by
        rw [hXE]; nlinarith
      have hP2 : det3 (a' - b) (c - d) (a - d) * det3 (b - d) (c - d) (a - d) < 0 → ⟪b - c', c - d⟫ = 0 →
          0 < ⟪b - c', a - d⟫ ∨ 0 < ⟪b - c', b - d⟫ := fun hp => absurd hp (not_lt.2 hpos.le)
      have hnP1 := fun hp1 => hL2' ⟨hp1, hP2⟩
      have hs : ⟪a' - c', c - d⟫ = 0 := by
        by_contra hs; exact hnP1 (fun _ h => absurd h hs)
      have hxy : ¬ (0 < ⟪a' - c', a - d⟫ ∨ 0 < ⟪a' - c', b - d⟫) := fun hxy => hnP1 (fun _ _ => hxy)
      have hy : ⟪a' - c', b - d⟫ ≤ 0 := by
        by_contra hy; exact hxy (Or.inr (not_le.1 hy))
      rw [ia1] at hs
      rw [ia3] at hy
      have hβ16 : β6 ≤ β1 := by
        by_contra hcon; push Not at hcon
        have : 0 < (β6 - β1) * ⟪b - d, b - d⟫ := mul_pos (by linarith) hA
        nlinarith
      exact hdone (C2.k9_L2 (V8 a a' b b' c c' d) (c - d) (a - d) (b - d) d hΔ hγ4 hβ1 hγ6 hγ61 hβ6
        (σ := γ6) hγ6.le (by linarith) hC0 hB0 (by nlinarith) hm1 hv1)
  · have hC : 0 < ⟪c - d, b - d⟫ := lt_of_le_of_ne hCnn (Ne.symm hC0)
    have hL3' : ¬ ((0 ≤ det3 (a' - b) (c - d) (a - d) * det3 (b - d) (c - d) (a - d) → ⟪a' - c', c - d⟫ = 0 →
          ⟪a' - c', b - d⟫ ≠ 0) ∧
        (det3 (a' - b) (c - d) (a - d) * det3 (b - d) (c - d) (a - d) < 0 → ⟪b - c', c - d⟫ = 0 →
          ⟪b - c', b - d⟫ ≠ 0)) :=
      fun hh => hnot ⟨fun hp => absurd hp hC0, fun hp => absurd hp hC0, fun _ => hh⟩
    rcases lt_trichotomy β6 1 with hlt | heq | hgt
    · -- L3b
      have hneg : det3 (a' - b) (c - d) (a - d) * det3 (b - d) (c - d) (a - d) < 0 := by
        rw [hXE]; nlinarith
      have hP1 : 0 ≤ det3 (a' - b) (c - d) (a - d) * det3 (b - d) (c - d) (a - d) → ⟪a' - c', c - d⟫ = 0 →
          ⟪a' - c', b - d⟫ ≠ 0 := fun hp => absurd hp (not_le.2 hneg)
      have hnP2 := fun hp2 => hL3' ⟨hP1, hp2⟩
      have hs : ⟪b - c', c - d⟫ = 0 := by
        by_contra hs; exact hnP2 (fun _ h => absurd h hs)
      have hy : ⟪b - c', b - d⟫ = 0 := by
        by_contra hy; exact hnP2 (fun _ _ => hy)
      rw [ib1] at hs
      rw [ib3] at hy
      exact hdone (C2.k9_L3b (V8 a a' b b' c c' d) (c - d) (a - d) (b - d) d hΔ hγ4 hβ1 hγ6 hγ61 hβ6 hβγ
        hC htie (by nlinarith) (by nlinarith) hm1 hv1 hm2 hv2)
    · exfalso
      have hX : det3 (a' - b) (c - d) (a - d) = 0 := by rw [eX, heq]; ring
      exact C2.k9_L1_false N hT hX
    · -- L3a
      have hpos : 0 ≤ det3 (a' - b) (c - d) (a - d) * det3 (b - d) (c - d) (a - d) := by
        rw [hXE]; nlinarith
      have hP2 : det3 (a' - b) (c - d) (a - d) * det3 (b - d) (c - d) (a - d) < 0 → ⟪b - c', c - d⟫ = 0 →
          ⟪b - c', b - d⟫ ≠ 0 := fun hp => absurd hp (not_lt.2 hpos)
      have hnP1 := fun hp1 => hL3' ⟨hp1, hP2⟩
      have hs : ⟪a' - c', c - d⟫ = 0 := by
        by_contra hs; exact hnP1 (fun _ h => absurd h hs)
      have hy : ⟪a' - c', b - d⟫ = 0 := by
        by_contra hy; exact hnP1 (fun _ _ => hy)
      rw [ia1] at hs
      rw [ia3] at hy
      exact hdone (C2.k9_L3a (V8 a a' b b' c c' d) (c - d) (a - d) (b - d) d hΔ hγ4 hβ1 hγ6 hγ61 hgt hβγ
        hC htie (by nlinarith) (by nlinarith) hm1 hv1)

end Type08Sp
end Minimality
