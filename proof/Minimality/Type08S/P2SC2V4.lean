module

public import Minimality.Type08S.P2SC2V2
public import Minimality.Type08S.P2SC2V3

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# Corollary SC2-V (package G): top vertex over `f̄` (`t = r`, `t = g`) and the near end `f̄ = ḡ`, frame form

`ClassV2` is the frame form of: (`h_{x'} ≤ h_f`, i.e. `σ(zf - zp) ≥ 0`) and a top vertex `r` over `f̄` (`x`, `g` strictly on one
side of `z_f`), or a top vertex `g` over `f̄` (`x`, `r` strictly on opposite sides), or `f̄ = ḡ` the near end of a top side
(`x`, `r` strictly on opposite sides).  (HDN classification taken as this hypothesis.)  The case `h_{x'} > h_f` is Lemma
LX (ii), not covered.
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

def ClassV2 (σ zp L zx zf Xr Yr zr Xg Yg zg : ℝ) : Prop :=
  0 ≤ σ * (zf - zp) ∧
  ((Xr = L ∧ zr = zf ∧ Yg < Yr ∧ 0 < (zg - zf) * (zx - zf)) ∨
   (Xg = L ∧ zg = zf ∧ Yr < Yg ∧ (zr - zf) * (zx - zf) < 0) ∨
   (Yg = Yr ∧ Xg = L ∧ zg = zf ∧ L < Xr ∧ (zr - zf) * (zx - zf) < 0))

theorem exists_b {L c1 c2 c3 d : ℝ} (hL : 0 < L) (hd : 0 < d) :
    ∃ b : ℝ, 0 < b ∧ 0 < L + b * c1 ∧ 0 < L + b * c2 ∧ b * |c3| < d := by
  refine ⟨min (L / (2 * (|c1| + |c2| + 1))) (d / (2 * (|c3| + 1))), lt_min (by positivity) (by positivity), ?_, ?_, ?_⟩
  all_goals
    set b := min (L / (2 * (|c1| + |c2| + 1))) (d / (2 * (|c3| + 1))) with hb
    have hb0 : 0 < b := lt_min (by positivity) (by positivity)
    have h1 : b ≤ L / (2 * (|c1| + |c2| + 1)) := min_le_left _ _
    have h2 : b ≤ d / (2 * (|c3| + 1)) := min_le_right _ _
    have h1' : b * (2 * (|c1| + |c2| + 1)) ≤ L := (le_div_iff₀ (by positivity)).1 h1
    have h2' : b * (2 * (|c3| + 1)) ≤ d := (le_div_iff₀ (by positivity)).1 h2
  · nlinarith [neg_abs_le c1, abs_nonneg c2, mul_nonneg hb0.le (abs_nonneg c1), mul_nonneg hb0.le (abs_nonneg c2),
      mul_le_mul_of_nonneg_left (neg_abs_le c1) hb0.le]
  · nlinarith [neg_abs_le c2, abs_nonneg c1, mul_nonneg hb0.le (abs_nonneg c1), mul_nonneg hb0.le (abs_nonneg c2),
      mul_le_mul_of_nonneg_left (neg_abs_le c2) hb0.le]
  · nlinarith [mul_nonneg hb0.le (abs_nonneg c3)]

/-- **Corollary SC2-V**, frame form. -/
theorem lemmaSC2V (hF : Fr e1 e2 e3) (o : ℝ³) (E : Finset ℝ³)
    {σ L zp zx zf Xr Yr zr Xg Yg zg : ℝ}
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp))
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcg : 0 < Yg * Xr - Xg * Yr) (hc : ClassV2 σ zp L zx zf Xr Yr zr Xg Yg zg)
    (hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E)
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0) y) :
    IsRupert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E) := by
  obtain ⟨hzf, h | h | h⟩ := hc
  · obtain ⟨hXr, hzr, hYgr, hsep⟩ := h
    subst hXr; subst hzr
    have hXg : Xg < Xr := by nlinarith
    obtain ⟨b, hb, hb1, hb2, -⟩ := exists_b (L := Xr) (c1 := σ * (zp - zr)) (c2 := σ * (zx - zr))
      (c3 := 0) (d := 1) hL one_pos
    have hgz : zg - zr ≠ 0 := fun h0 => by rw [h0] at hsep; simp at hsep
    refine sc2V_core_r hF o E hL hzx hYg hYgr hXg hcg hb (by linarith) (by linarith) hzf
      (κ := zg - zr) (by nlinarith [sq_pos_of_ne_zero hgz]) (by nlinarith) hE
  · obtain ⟨hXg, hzg, hYrg, hsep⟩ := h
    subst hXg; subst hzg
    have hXr : Xg < Xr := by nlinarith
    obtain ⟨b, hb, hb1, hb2, -⟩ := exists_b (L := Xg) (c1 := σ * (zp - zg)) (c2 := σ * (zx - zg))
      (c3 := 0) (d := 1) hL one_pos
    have hxz : zx - zg ≠ 0 := fun h0 => by rw [h0] at hsep; simp at hsep
    refine sc2V_core_g hF o E hL hzx hYr hYrg hXr hcg hb (by linarith) (by linarith) hzf
      (κ := zx - zg) (by nlinarith) (by nlinarith [sq_pos_of_ne_zero hxz]) hE
  · obtain ⟨hYY, hXg, hzg, hXr, hsep⟩ := h
    subst hYY; subst hXg; subst hzg
    obtain ⟨b, hb, hb1, hb2, hb3'⟩ := exists_b (L := Xg) (c1 := σ * (zp - zg)) (c2 := σ * (zx - zg))
      (c3 := σ * (zr - zg)) (d := Xr - Xg) hL (sub_pos.2 hXr)
    have hxz : zx - zg ≠ 0 := fun h0 => by rw [h0] at hsep; simp at hsep
    have hb3 : 0 < (Xg - Xr) * (Xg - Xr + σ * b * (zr - zg)) := by
      have h1 : b * (σ * (zr - zg)) ≤ b * |σ * (zr - zg)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hb.le
      have h2 : 0 < Xr - Xg - σ * b * (zr - zg) := by linarith
      nlinarith [mul_pos (sub_pos.2 hXr) h2]
    refine sc2V_core_end hF o E hL hzx hYr hXr hb (by linarith) (by linarith) hb3 hzf
      (κ := zx - zg) (by nlinarith) (by nlinarith [sq_pos_of_ne_zero hxz]) hE

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.lemmaSC2V
