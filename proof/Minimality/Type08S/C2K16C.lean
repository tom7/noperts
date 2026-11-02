module

public import Minimality.Type08S.C2K16B

@[expose] public section


/-!
# K16 / C: the region data `RegN2` (`γ6 > 1`) and `RegT4` (`α1 > 1`, `γ6 < 1`) in the K6M coordinates.
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
namespace C2

theorem k16_reg_raw {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) :
    ∃ α1 β1 β6 γ6 : ℝ, c' = d + α1 • (a - d) + β1 • (b - d) ∧ a' = d + β6 • (b - d) + γ6 • (c - d) ∧
      (RegN2 W.F → 1 < γ6) ∧ (RegT4 W.F → 1 < α1 ∧ γ6 < 1) := by
  obtain ⟨F, hd, G, hκa, hκb, hU⟩ := W
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  obtain ⟨p1, p2, p3, hc'⟩ : 0 < F.a'bc.f c' / F.a'bc.f a ∧ 0 < F.ab'c.f c' / F.ab'c.f b ∧
      1 < F.a'bc.f c' / F.a'bc.f a + F.ab'c.f c' / F.ab'c.f b ∧
      c' = d + (F.a'bc.f c' / F.a'bc.f a) • (a - d) + (F.ab'c.f c' / F.ab'c.f b) • (b - d) :=
    hd.perm₂₃.Qac_coords'
  obtain ⟨hβ6, hγ6, hcv6, ha'⟩ : 0 < F.ab'c.f a' / F.ab'c.f b ∧ 0 < F.abc'.f a' / F.abc'.f c ∧
      1 < F.ab'c.f a' / F.ab'c.f b + F.abc'.f a' / F.abc'.f c ∧
      a' = d + (F.ab'c.f a' / F.ab'c.f b) • (b - d) + (F.abc'.f a' / F.abc'.f c) • (c - d) :=
    hd.perm₁₂.Qac_coords'
  have hFc := F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc'
  have hFa := F.a'bc.neg a (by simp) haa' hab hac
  refine ⟨_, _, _, _, hc', ha', ?_, ?_⟩
  · intro h; exact (one_lt_div_of_neg hFc).mpr h
  · rintro ⟨h1, h2⟩
    exact ⟨(one_lt_div_of_neg hFa).mpr h2, (div_lt_one_of_neg hFc).mpr h1⟩

theorem k16_reg_coords {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    {α1 β1 β6 γ6 : ℝ} (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) :
    (RegN2 W.F → 1 < γ6) ∧ (RegT4 W.F → 1 < α1 ∧ γ6 < 1) := by
  obtain ⟨hdet, hc', hb', ha', -⟩ := hC
  obtain ⟨α1', β1', β6', γ6', hc'2, ha'2, hN, hT⟩ := k16_reg_raw W
  have e1 := k5b_coeff3 hdet (x := α1) (y := β1) (z := 0) (x' := α1') (y' := β1') (z' := 0)
    (by have := hc'.symm.trans hc'2; simpa [add_assoc] using this)
  have e2 := k5b_coeff3 (p := b - d) (q := c - d) (r := a - d)
    (by intro h; apply hdet; simp only [det3_expand] at h ⊢; linarith) (x := β6) (y := γ6) (z := 0)
    (x' := β6') (y' := γ6') (z' := 0)
    (by have := ha'.symm.trans ha'2; simpa [add_assoc] using this)
  obtain ⟨rfl, -, -⟩ := e1
  obtain ⟨-, rfl, -⟩ := e2
  exact ⟨hN, hT⟩

end C2
end Type08Sp
end Minimality
