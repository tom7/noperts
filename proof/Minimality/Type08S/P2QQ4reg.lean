module

public import Minimality.Type08S.P2QQ0c
public import Minimality.Type08S.P2QQ2b

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkQ / Q4reg: W copies (on `Norm08w`) of the region and frame helpers used by Q4.
Namespace `Minimality.Type08Sp.W`.  Possible name clashes with Q3's copies (`W4.region_gamma6`, `W4.region_alpha1`).
-/

set_option autoImplicit true
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace W4

theorem det_nf08 {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d) :
    det3 (a - d) (b - d) (c - d) ≠ 0 := by
  have := N.hd.det_Qac_ne
  intro h; apply this
  simp only [det3_expand, PiLp.sub_apply] at h ⊢
  linarith

set_option maxHeartbeats 4000000 in
theorem seg08 {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d) :
    let x := pts08 a a' b b' c c' d
    (∀ i j m : Fin 7, x m ≠ x i → x m ≠ x j → ∀ s : ℝ, 0 < s → s < 1 → x m ≠ x i + s • (x j - x i)) ∧
    ∃ i j l m : Fin 7, det3 (x j - x i) (x l - x i) (x m - x i) ≠ 0 := by
  intro x
  refine ⟨?_, 6, 0, 2, 4, by simpa [x, pts08] using det_nf08 N⟩
  have hd := N.hd
  have hnd := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have f1_0 : N.F.abc'.f a = 0 := N.F.abc'.hP
  have f1_1 : N.F.abc'.f a' < 0 := N.F.abc'.neg a' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f1_2 : N.F.abc'.f b = 0 := N.F.abc'.hQ
  have f1_3 : N.F.abc'.f b' < 0 := N.F.abc'.neg b' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f1_4 : N.F.abc'.f c < 0 := N.F.abc'.neg c (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f1_5 : N.F.abc'.f c' = 0 := N.F.abc'.hR
  have f1_6 : N.F.abc'.f d = 0 := hd.abc'
  have f2_0 : N.F.ab'c.f a = 0 := N.F.ab'c.hP
  have f2_1 : N.F.ab'c.f a' < 0 := N.F.ab'c.neg a' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f2_2 : N.F.ab'c.f b < 0 := N.F.ab'c.neg b (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f2_3 : N.F.ab'c.f b' = 0 := N.F.ab'c.hQ
  have f2_4 : N.F.ab'c.f c = 0 := N.F.ab'c.hR
  have f2_5 : N.F.ab'c.f c' < 0 := N.F.ab'c.neg c' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f2_6 : N.F.ab'c.f d = 0 := hd.ab'c
  have f3_0 : N.F.a'bc.f a < 0 := N.F.a'bc.neg a (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f3_1 : N.F.a'bc.f a' = 0 := N.F.a'bc.hP
  have f3_2 : N.F.a'bc.f b = 0 := N.F.a'bc.hQ
  have f3_3 : N.F.a'bc.f b' < 0 := N.F.a'bc.neg b' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f3_4 : N.F.a'bc.f c = 0 := N.F.a'bc.hR
  have f3_5 : N.F.a'bc.f c' < 0 := N.F.a'bc.neg c' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f3_6 : N.F.a'bc.f d = 0 := hd.a'bc
  have f4_0 : N.F.ab'c'.f a = 0 := N.F.ab'c'.hP
  have f4_1 : N.F.ab'c'.f a' < 0 := N.F.ab'c'.neg a' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f4_2 : N.F.ab'c'.f b < 0 := N.F.ab'c'.neg b (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f4_3 : N.F.ab'c'.f b' = 0 := N.F.ab'c'.hQ
  have f4_4 : N.F.ab'c'.f c < 0 := N.F.ab'c'.neg c (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f4_5 : N.F.ab'c'.f c' = 0 := N.F.ab'c'.hR
  have f4_6 : N.F.ab'c'.f d < 0 := hd.ab'c'
  have f5_0 : N.F.a'bc'.f a < 0 := N.F.a'bc'.neg a (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f5_1 : N.F.a'bc'.f a' = 0 := N.F.a'bc'.hP
  have f5_2 : N.F.a'bc'.f b = 0 := N.F.a'bc'.hQ
  have f5_3 : N.F.a'bc'.f b' < 0 := N.F.a'bc'.neg b' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f5_4 : N.F.a'bc'.f c < 0 := N.F.a'bc'.neg c (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f5_5 : N.F.a'bc'.f c' = 0 := N.F.a'bc'.hR
  have f5_6 : N.F.a'bc'.f d < 0 := hd.a'bc'
  have f6_0 : N.F.a'b'c.f a < 0 := N.F.a'b'c.neg a (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f6_1 : N.F.a'b'c.f a' = 0 := N.F.a'b'c.hP
  have f6_2 : N.F.a'b'c.f b < 0 := N.F.a'b'c.neg b (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f6_3 : N.F.a'b'c.f b' = 0 := N.F.a'b'c.hQ
  have f6_4 : N.F.a'b'c.f c = 0 := N.F.a'b'c.hR
  have f6_5 : N.F.a'b'c.f c' < 0 := N.F.a'b'c.neg c' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f6_6 : N.F.a'b'c.f d < 0 := hd.a'b'c
  have f7_0 : N.F.a'b'c'.f a < 0 := N.F.a'b'c'.neg a (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f7_1 : N.F.a'b'c'.f a' = 0 := N.F.a'b'c'.hP
  have f7_2 : N.F.a'b'c'.f b < 0 := N.F.a'b'c'.neg b (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f7_3 : N.F.a'b'c'.f b' = 0 := N.F.a'b'c'.hQ
  have f7_4 : N.F.a'b'c'.f c < 0 := N.F.a'b'c'.neg c (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f7_5 : N.F.a'b'c'.f c' = 0 := N.F.a'b'c'.hR
  have f7_6 : N.F.a'b'c'.f d < 0 := hd.a'b'c'
  refine noSeg_of_aff08 (![fun y => N.F.abc'.f y + N.F.ab'c.f y + N.F.ab'c'.f y, fun y => N.F.a'bc.f y + N.F.a'bc'.f y + N.F.a'b'c.f y + N.F.a'b'c'.f y, fun y => N.F.abc'.f y + N.F.a'bc.f y + N.F.a'bc'.f y, fun y => N.F.ab'c.f y + N.F.ab'c'.f y + N.F.a'b'c.f y + N.F.a'b'c'.f y, fun y => N.F.ab'c.f y + N.F.a'bc.f y + N.F.a'b'c.f y, fun y => N.F.abc'.f y + N.F.ab'c'.f y + N.F.a'bc'.f y + N.F.a'b'c'.f y, fun y => N.F.abc'.f y + N.F.ab'c.f y + N.F.a'bc.f y]) ?_ ?_
  · intro m y z s
    fin_cases m <;> simp [facet_aff08] <;> ring
  · intro m w hw
    fin_cases m <;> fin_cases w <;> first | exact absurd rfl hw | (simp only [x, pts08]; simp; linarith)
theorem region_gamma6 {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d) {o E₁ E₂ E₃ : ℝ³}
    {θ : Fin 6 → ℝ} (hE : det3 E₁ E₂ E₃ ≠ 0) (hθ : Ineq08w θ)
    (hpts : pts08 a a' b b' c c' d = nfShape08 o E₁ E₂ E₃ θ) :
    N.F.abc'.f a' = θ 5 * N.F.abc'.f c := by
  have hnd := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have hp := facet_prop08 N.F.abc' c a'
  have d1 : det3 (b - a) (c' - a) (c - a) = det3 E₁ E₂ E₃ * fc08 θ 0 2 5 4 := by
    have := det3_nf08 o E₁ E₂ E₃ θ 0 2 5 4; rw [← hpts] at this; exact this
  have d2 : det3 (b - a) (c' - a) (a' - a) = det3 E₁ E₂ E₃ * fc08 θ 0 2 5 1 := by
    have := det3_nf08 o E₁ E₂ E₃ θ 0 2 5 1; rw [← hpts] at this; exact this
  rw [d1, d2] at hp
  have hA : fc08 θ 0 2 5 4 = 1 - θ 0 - θ 1 := by simp only [fc08, cdet, cp08]; simp; ring
  have hB : fc08 θ 0 2 5 1 = θ 5 * (1 - θ 0 - θ 1) := by simp only [fc08, cdet, cp08]; simp; ring
  have e1 : 0 < θ 0 + θ 1 - 1 := hθ.pos 6 (by decide) (by decide) (by decide)
  have hD : det3 E₁ E₂ E₃ * (1 - θ 0 - θ 1) ≠ 0 := mul_ne_zero hE (by linarith)
  rw [hA, hB] at hp
  apply mul_right_cancel₀ hD; linear_combination hp

theorem region_alpha1 {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d) {o E₁ E₂ E₃ : ℝ³}
    {θ : Fin 6 → ℝ} (hE : det3 E₁ E₂ E₃ ≠ 0) (hθ : Ineq08w θ)
    (hpts : pts08 a a' b b' c c' d = nfShape08 o E₁ E₂ E₃ θ) :
    N.F.a'bc.f c' = θ 0 * N.F.a'bc.f a := by
  have hp := facet_prop08 N.F.a'bc a c'
  have d1 : det3 (b - a') (c - a') (a - a') = det3 E₁ E₂ E₃ * fc08 θ 1 2 4 0 := by
    have := det3_nf08 o E₁ E₂ E₃ θ 1 2 4 0; rw [← hpts] at this; exact this
  have d2 : det3 (b - a') (c - a') (c' - a') = det3 E₁ E₂ E₃ * fc08 θ 1 2 4 5 := by
    have := det3_nf08 o E₁ E₂ E₃ θ 1 2 4 5; rw [← hpts] at this; exact this
  rw [d1, d2] at hp
  have hA : fc08 θ 1 2 4 0 = 1 - θ 4 - θ 5 := by simp only [fc08, cdet, cp08]; simp; ring
  have hB : fc08 θ 1 2 4 5 = θ 0 * (1 - θ 4 - θ 5) := by simp only [fc08, cdet, cp08]; simp; ring
  have e1 : 0 < θ 4 + θ 5 - 1 := hθ.pos 8 (by decide) (by decide) (by decide)
  have hD : det3 E₁ E₂ E₃ * (1 - θ 4 - θ 5) ≠ 0 := mul_ne_zero hE (by linarith)
  rw [hA, hB] at hp
  apply mul_right_cancel₀ hD; linear_combination hp

theorem grp_view_ne {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d) (i : Fin 3) :
    (grp08 i).view (pts08 a a' b b' c c' d) ≠ 0 := by
  have hnd := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := N.hd.ne
  fin_cases i <;> simp [grp08, ViewGroup.view, LabTest.quad, pts08, sub_eq_zero]
  · exact Ne.symm ha'c
  · exact hdb.symm
  · exact hdb.symm

theorem view0_test08 {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d) (c0 : Fin 3 × Bool × Bool) :
    (test08 c0.1 c0.2.1 c0.2.2).view (pts08 a a' b b' c c' d) ≠ 0 := by
  obtain ⟨T, hT, h | h⟩ := test08_eq c0.1 c0.2.1 c0.2.2
  · rw [h, grp_tests_view _ T hT]; exact grp_view_ne N _
  · rw [h]; simp only [LabTest.neg, grp_tests_view _ T hT, neg_ne_zero]; exact grp_view_ne N _

theorem pts08_inj {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d) :
    Function.Injective (pts08 a a' b b' c c' d) := by
  have hnd := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := N.hd.ne
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [pts08]

end W4
end Type08Sp
end Minimality
