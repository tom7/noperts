module

public import Minimality.Type08S.P2H14
public import Minimality.Type08S.P2CE1

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# pkL CE2: `CEfN2`, `CEfKb`, `CEfK2` (chord end at `f`) on `Norm08`

Each is proved as `pers_N2/Kb/K2` up to the extra-vertex TriCert block `hE` (lines copied from pkH H8/H9), then
`ce_frame` (CE1) with strict Lemma E (`lemE_strict`, H13).
-/

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

set_option maxHeartbeats 4000000 in
theorem cef_N2 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hreg : RegN2 N.F) :
    CEfN2 a a' b b' c c' d := by
  intro e1 e2 e3 κ hF hκ hce hb2 hL hr hrob hce5
  have hnd := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  obtain ⟨hcr, hcg, hXd0, hXdL, hYa, hfr, hrg, hgx⟩ := pic_N2 N hreg hF hκ hce hb2 hL hr
  obtain ⟨hYg, hYd, hDp⟩ := extra_N2 N hreg hF hκ hce hb2 hL hr
  have hside := side_pos hF N.F.a'bc'.hN (xp := a') (x := c) (fp := b) (p := d) (κ := κ)
    N.F.a'bc'.hP N.F.a'bc'.hQ (N.F.a'bc'.neg c (by simp) (by ne_tac) (by ne_tac) (by ne_tac)) N.hd.a'bc'
    hce hb2 hYd hL
  have hxx : c = a' + pc e1 e2 e3 0 0 κ := by
    rw [← pc_smul_e3 hF, ← hce]; abel
  have hxf : b = a' + pc e1 e2 e3 ⟪b - a', e1⟫ 0 ⟪b - a', e3⟫ := by
    have := pc_coords hF a' b; rw [hb2] at this; exact this
  have hxr : c' = a' + pc e1 e2 e3 ⟪c' - a', e1⟫ ⟪c' - a', e2⟫ ⟪c' - a', e3⟫ := pc_coords hF a' c'
  have hxg : b' = a' + pc e1 e2 e3 ⟪b' - a', e1⟫ ⟪b' - a', e2⟫ ⟪b' - a', e3⟫ := pc_coords hF a' b'
  have hxp : d = a' + pc e1 e2 e3 ⟪d - a', e1⟫ 0 ⟪d - a', e3⟫ := by
    have := pc_coords hF a' d; rw [hYd] at this; exact this
  have hxw : a = a' + pc e1 e2 e3 ⟪a - a', e1⟫ ⟪a - a', e2⟫ ⟪a - a', e3⟫ := pc_coords hF a' a
  -- `a` is not on the 3-D line `b b'`
  have hnc : ¬ ((⟪b' - a', e1⟫ - ⟪b - a', e1⟫) * ⟪a - a', e2⟫ - ⟪b' - a', e2⟫ * (⟪a - a', e1⟫ - ⟪b - a', e1⟫) = 0 ∧
      ⟪b' - a', e2⟫ * (⟪a - a', e3⟫ - ⟪b - a', e3⟫) - (⟪b' - a', e3⟫ - ⟪b - a', e3⟫) * ⟪a - a', e2⟫ = 0) := by
    rintro ⟨hD0, hW0⟩
    have iexp : ∀ v : ℝ³, ⟪N.F.abc'.N, v⟫ = ⟪v, e1⟫ * ⟪N.F.abc'.N, e1⟫ + ⟪v, e2⟫ * ⟪N.F.abc'.N, e2⟫ +
        ⟪v, e3⟫ * ⟪N.F.abc'.N, e3⟫ := by
      intro v
      conv_lhs => rw [hF.expand v]
      simp only [inner_add_right, real_inner_smul_right]
    have k1 := N.F.abc'.hN a b
    have k2 := N.F.abc'.hN b' b
    rw [N.F.abc'.hP, N.F.abc'.hQ] at k1
    rw [N.F.abc'.hQ] at k2
    have k3 := N.F.abc'.neg b' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
    rw [iexp, inner_diff a b a', inner_diff a b a', inner_diff a b a'] at k1
    rw [iexp, inner_diff b' b a', inner_diff b' b a', inner_diff b' b a'] at k2
    rw [hb2] at k1 k2
    have k4 : ⟪b' - a', e2⟫ * (0 - 0) = ⟪a - a', e2⟫ * (N.F.abc'.f b' - 0) := by
      rw [k1, k2]
      linear_combination (-⟪N.F.abc'.N, e1⟫) * hD0 + ⟪N.F.abc'.N, e3⟫ * hW0
    nlinarith [mul_pos hYa (neg_pos.2 k3)]
  set E : Finset ℝ³ := {a' + pc e1 e2 e3 ⟪d - a', e1⟫ 0 ⟪d - a', e3⟫,
    a' + pc e1 e2 e3 ⟪a - a', e1⟫ ⟪a - a', e2⟫ ⟪a - a', e3⟫} with hEdef
  set V5 := rim5 e1 e2 e3 a' ⟪b - a', e1⟫ 0 κ ⟪b - a', e3⟫ ⟪c' - a', e1⟫ ⟪c' - a', e2⟫ ⟪c' - a', e3⟫
    ⟪b' - a', e1⟫ ⟪b' - a', e2⟫ ⟪b' - a', e3⟫ E with hV5
  have m1 : a' + pc e1 e2 e3 0 0 0 ∈ V5 := by simp [hV5, rim5]
  have m2 : a' + pc e1 e2 e3 ⟪b - a', e1⟫ 0 ⟪b - a', e3⟫ ∈ V5 := by simp [hV5, rim5]
  have m3 : a' + pc e1 e2 e3 ⟪c' - a', e1⟫ ⟪c' - a', e2⟫ ⟪c' - a', e3⟫ ∈ V5 := by simp [hV5, rim5]
  have m4 : a' + pc e1 e2 e3 ⟪b' - a', e1⟫ ⟪b' - a', e2⟫ ⟪b' - a', e3⟫ ∈ V5 := by simp [hV5, rim5]
  have hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert V5 (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (κ * s) (-κ) 0) y := by
    filter_upwards [triCert_quad hF a' V5 (σ := κ) hκ m1 m2 m3 m4 hL hYg hcr hYa hfr hrg hgx hnc]
      with s hs y hy
    rw [hEdef, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · refine triCert_midF hF a' V5 hL hYg hXd0 hXdL m1 m2 m4 ?_
      nlinarith [hside]
    · exact hs
  have hR := ce_frame hF a' E hκ hL hr hYg hcr hcg hE hrob
    (fun hY => lemEs_frame hF a' hr hY (by rw [← hxx, ← hxf, ← hxr, ← hxg]; exact (lemE_strict N).1)) hce5
  simp only [rim5, hEdef] at hR
  rw [show a' + pc e1 e2 e3 0 0 0 = a' by simp [pc], ← hxx, ← hxf, ← hxr, ← hxg, ← hxp, ← hxw] at hR
  have hset : insert d ({a, a', b, b', c, c'} : Finset ℝ³) = ({a', c, b, c', b'} : Finset ℝ³) ∪ {d, a} := by
    ext y; simp only [mem_insert, mem_singleton, mem_union]
    constructor
    · rintro (h | h | h | h | h | h | h) <;> subst h <;> simp only [true_or, or_true]
    · rintro ((h | h | h | h | h) | (h | h)) <;> subst h <;> simp only [true_or, or_true]
  rw [hset]; exact hR

set_option maxHeartbeats 4000000 in
theorem cef_Kb {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hreg : RegT4 N.F) :
    CEfKb a a' b b' c c' d := by
  intro e1 e2 e3 κ hF hκ hxe hf2 hL hr hrob hce5
  have hnd := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  obtain ⟨hcr, hcg, hXd0, hXdL, hlam⟩ := pic_Kb N hreg hF hκ hxe hf2 hL hr
  obtain ⟨hYg, hYp, hDp, hYq, hYlt, hcop, hchord⟩ := extra_Kb N hreg hF hκ hxe hf2 hL hr hcg hlam
  have hside := side_pos hF N.F.ab'c.hN (xp := d) (x := b) (fp := c) (p := a') (κ := κ)
    N.hd.ab'c N.F.ab'c.hR (N.F.ab'c.neg b (by simp) (by ne_tac) (by ne_tac) (by ne_tac))
    (N.F.ab'c.neg a' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)) hxe hf2 hYp hL
  have hxx : b = d + pc e1 e2 e3 0 0 κ := by
    rw [← pc_smul_e3 hF, ← hxe]; abel
  have hxf : c = d + pc e1 e2 e3 ⟪c - d, e1⟫ 0 ⟪c - d, e3⟫ := by
    have := pc_coords hF d c; rw [hf2] at this; exact this
  have hxr : b' = d + pc e1 e2 e3 ⟪b' - d, e1⟫ ⟪b' - d, e2⟫ ⟪b' - d, e3⟫ := pc_coords hF d b'
  have hxg : c' = d + pc e1 e2 e3 ⟪c' - d, e1⟫ ⟪c' - d, e2⟫ ⟪c' - d, e3⟫ := pc_coords hF d c'
  have hxp : a' = d + pc e1 e2 e3 ⟪a' - d, e1⟫ 0 ⟪a' - d, e3⟫ := by
    have := pc_coords hF d a'; rw [hYp] at this; exact this
  have hxw : a = d + pc e1 e2 e3 ⟪a - d, e1⟫ ⟪a - d, e2⟫ ⟪a - d, e3⟫ := pc_coords hF d a
  set E : Finset ℝ³ := {d + pc e1 e2 e3 ⟪a' - d, e1⟫ 0 ⟪a' - d, e3⟫,
    d + pc e1 e2 e3 ⟪a - d, e1⟫ ⟪a - d, e2⟫ ⟪a - d, e3⟫} with hEdef
  set V5 := rim5 e1 e2 e3 d ⟪c - d, e1⟫ 0 κ ⟪c - d, e3⟫ ⟪b' - d, e1⟫ ⟪b' - d, e2⟫ ⟪b' - d, e3⟫
    ⟪c' - d, e1⟫ ⟪c' - d, e2⟫ ⟪c' - d, e3⟫ E with hV5
  have m1 : d + pc e1 e2 e3 0 0 0 ∈ V5 := by simp [hV5, rim5]
  have m0 : d + pc e1 e2 e3 0 0 κ ∈ V5 := by simp [hV5, rim5]
  have m2 : d + pc e1 e2 e3 ⟪c - d, e1⟫ 0 ⟪c - d, e3⟫ ∈ V5 := by simp [hV5, rim5]
  have m4 : d + pc e1 e2 e3 ⟪c' - d, e1⟫ ⟪c' - d, e2⟫ ⟪c' - d, e3⟫ ∈ V5 := by simp [hV5, rim5]
  have hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert V5 (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (κ * s) (-κ) 0) y := by
    filter_upwards [triCert_midG' hF d V5 hL hYg hYq hYlt hcop hchord m4 m0 m2] with s hs y hy
    rw [hEdef, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · refine triCert_midF hF d V5 hL hYg hXd0 hXdL m1 m2 m4 ?_
      nlinarith [hside]
    · exact hs
  have hR := ce_frame hF d E hκ hL hr hYg hcr hcg hE hrob
    (fun hY => lemEs_frame hF d hr hY (by rw [← hxx, ← hxf, ← hxr, ← hxg]; exact (lemE_strict N).2.1)) hce5
  simp only [rim5, hEdef] at hR
  rw [show d + pc e1 e2 e3 0 0 0 = d by simp [pc], ← hxx, ← hxf, ← hxr, ← hxg, ← hxp, ← hxw] at hR
  have hset : insert d ({a, a', b, b', c, c'} : Finset ℝ³) = ({d, b, c, b', c'} : Finset ℝ³) ∪ {a', a} := by
    ext y; simp only [mem_insert, mem_singleton, mem_union]
    constructor
    · rintro (h | h | h | h | h | h | h) <;> subst h <;> simp only [true_or, or_true]
    · rintro ((h | h | h | h | h) | (h | h)) <;> subst h <;> simp only [true_or, or_true]
  rw [hset]; exact hR

set_option maxHeartbeats 4000000 in
theorem cef_K2 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hreg : RegT4 N.F) :
    CEfK2 a a' b b' c c' d := by
  intro e1 e2 e3 κ hF hκ hxe hf2 hL hr hrob hce5
  have hnd := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  obtain ⟨hcr, hcg, hXd0, hXdL, hlam⟩ := pic_K2 N hreg hF hκ hxe hf2 hL hr
  obtain ⟨hYg, hYp, hDp, hYq, hYlt, hcop, hchord⟩ := extra_K2 N hreg hF hκ hxe hf2 hL hr hcg hlam
  have hside := side_pos hF N.F.a'bc'.hN (xp := b) (x := d) (fp := c') (p := a) (κ := κ)
    N.F.a'bc'.hQ N.F.a'bc'.hR N.hd.a'bc'
    (N.F.a'bc'.neg a (by simp) (by ne_tac) (by ne_tac) (by ne_tac)) hxe hf2 hYp hL
  have hxx : d = b + pc e1 e2 e3 0 0 κ := by
    rw [← pc_smul_e3 hF, ← hxe]; abel
  have hxf : c' = b + pc e1 e2 e3 ⟪c' - b, e1⟫ 0 ⟪c' - b, e3⟫ := by
    have := pc_coords hF b c'; rw [hf2] at this; exact this
  have hxr : b' = b + pc e1 e2 e3 ⟪b' - b, e1⟫ ⟪b' - b, e2⟫ ⟪b' - b, e3⟫ := pc_coords hF b b'
  have hxg : c = b + pc e1 e2 e3 ⟪c - b, e1⟫ ⟪c - b, e2⟫ ⟪c - b, e3⟫ := pc_coords hF b c
  have hxp : a = b + pc e1 e2 e3 ⟪a - b, e1⟫ 0 ⟪a - b, e3⟫ := by
    have := pc_coords hF b a; rw [hYp] at this; exact this
  have hxw : a' = b + pc e1 e2 e3 ⟪a' - b, e1⟫ ⟪a' - b, e2⟫ ⟪a' - b, e3⟫ := pc_coords hF b a'
  set E : Finset ℝ³ := {b + pc e1 e2 e3 ⟪a - b, e1⟫ 0 ⟪a - b, e3⟫,
    b + pc e1 e2 e3 ⟪a' - b, e1⟫ ⟪a' - b, e2⟫ ⟪a' - b, e3⟫} with hEdef
  set V5 := rim5 e1 e2 e3 b ⟪c' - b, e1⟫ 0 κ ⟪c' - b, e3⟫ ⟪b' - b, e1⟫ ⟪b' - b, e2⟫ ⟪b' - b, e3⟫
    ⟪c - b, e1⟫ ⟪c - b, e2⟫ ⟪c - b, e3⟫ E with hV5
  have m1 : b + pc e1 e2 e3 0 0 0 ∈ V5 := by simp [hV5, rim5]
  have m0 : b + pc e1 e2 e3 0 0 κ ∈ V5 := by simp [hV5, rim5]
  have m2 : b + pc e1 e2 e3 ⟪c' - b, e1⟫ 0 ⟪c' - b, e3⟫ ∈ V5 := by simp [hV5, rim5]
  have m4 : b + pc e1 e2 e3 ⟪c - b, e1⟫ ⟪c - b, e2⟫ ⟪c - b, e3⟫ ∈ V5 := by simp [hV5, rim5]
  have hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert V5 (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (κ * s) (-κ) 0) y := by
    filter_upwards [triCert_midG' hF b V5 hL hYg hYq hYlt hcop hchord m4 m0 m2] with s hs y hy
    rw [hEdef, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · refine triCert_midF hF b V5 hL hYg hXd0 hXdL m1 m2 m4 ?_
      nlinarith [hside]
    · exact hs
  have hR := ce_frame hF b E hκ hL hr hYg hcr hcg hE hrob
    (fun hY => lemEs_frame hF b hr hY (by rw [← hxx, ← hxf, ← hxr, ← hxg]; exact (lemE_strict N).2.2)) hce5
  simp only [rim5, hEdef] at hR
  rw [show b + pc e1 e2 e3 0 0 0 = b by simp [pc], ← hxx, ← hxf, ← hxr, ← hxg, ← hxp, ← hxw] at hR
  have hset : insert d ({a, a', b, b', c, c'} : Finset ℝ³) = ({b, d, c', b', c} : Finset ℝ³) ∪ {a, a'} := by
    ext y; simp only [mem_insert, mem_singleton, mem_union]
    constructor
    · rintro (h | h | h | h | h | h | h) <;> subst h <;> simp only [true_or, or_true]
    · rintro ((h | h | h | h | h) | (h | h)) <;> subst h <;> simp only [true_or, or_true]
  rw [hset]; exact hR

end Type08Sp
end Minimality
