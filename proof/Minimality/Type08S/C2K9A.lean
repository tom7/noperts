module

public import Minimality.Type08S.C2K8J

@[expose] public section

/-!
# K9A: the L1 stratum (`C = 0`, `X = 0`) is empty: `α4 = 1` and `β6 = 1` contradict `κ_c ≠ 0`
(`a, a', b, b'` are coplanar because `a' - b ∥ b' - a ∥ c - d`).
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem k9_L1_false {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (h : TpA1ii a a' b b' c c' d) (hX : det3 (a' - b) (c - d) (a - d) = 0) : False := by
  obtain ⟨hT', -, hAl, -, -, -⟩ := h
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hα4, hγ4, hαγ, hβ1, hβ6p, hγ6, hγ61, hcv⟩ :=
    norm08_coordsTp' N hT'
  set D := det3 (a - d) (c - d) (b - d) with hD
  have hD0 : D ≠ 0 := by
    intro h0; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = -D := by simp only [hD, det3_expand]; ring
    rw [e, h0, neg_zero]
  have hα41 : α4 = 1 := by
    have e1 := det_alpha (b := b) hb'
    have : (α4 - 1) * D = 0 := by rw [hD]; rw [hAl] at e1; linarith
    have := (mul_eq_zero.mp this).resolve_right hD0
    linarith
  subst hα41
  set E := det3 (b - d) (c - d) (a - d) with hE
  have hE' : E = -D := by simp only [hE, hD, det3_expand]; ring
  have eB6 : det3 (a' - b) (c - d) (a - d) = (β6 - 1) * E := by
    rw [ha']; simp only [hE, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hE0 : E ≠ 0 := by rw [hE']; exact neg_ne_zero.2 hD0
  have hb61 : β6 = 1 := by
    rw [eB6] at hX
    have := (mul_eq_zero.mp hX).resolve_right hE0
    linarith
  subst hb61
  -- the affine function f x = det3 (b - a) (c - d) (x - a)
  set M := cross (b - a) (c - d) with hM
  have hf : ∀ y z : ℝ³, det3 (b - a) (c - d) (y - a) - det3 (b - a) (c - d) (z - a) = ⟪M, y - z⟫ := by
    intro y z
    simp only [det3, hM]
    rw [← inner_sub_right]
    congr 1
    abel
  have key := (N.G.hl).apply (f := fun x => det3 (b - a) (c - d) (x - a)) hf
  have key2 := (N.G.hm).apply (f := fun x => det3 (b - a) (c - d) (x - a)) hf
  have fa : det3 (b - a) (c - d) (a - a) = 0 := by simp [det3_expand]
  have fb : det3 (b - a) (c - d) (b - a) = 0 := by simp only [det3_expand]; ring
  have fa' : det3 (b - a) (c - d) (a' - a) = 0 := by
    rw [ha']; simp only [det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have fb' : det3 (b - a) (c - d) (b' - a) = 0 := by
    rw [hb']; simp only [det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have fc : det3 (b - a) (c - d) (c - a) = -det3 (a - d) (b - d) (c - d) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have fc' : det3 (b - a) (c - d) (c' - a) = β1 * det3 (b - a) (c - d) (b - d) := by
    rw [hc']; simp only [det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  simp only [fa, fb, fa', fb', mul_zero, zero_add] at key key2
  have hκ := N.hκc
  simp only [galeD] at hκ
  have e1 : (N.G.l c * N.G.m c' - N.G.m c * N.G.l c') * det3 (b - a) (c - d) (c - a) = 0 := by
    linear_combination N.G.m c' * key - N.G.l c' * key2
  have := (mul_eq_zero.mp e1).resolve_left hκ
  rw [fc] at this
  exact hdet (neg_eq_zero.mp this)

end C2
end Type08Sp
end Minimality
