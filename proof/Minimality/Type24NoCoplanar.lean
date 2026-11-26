module

public import Minimality.EdgePlaneRim4Level
public import Minimality.EdgeViewLink
public import Minimality.SplitLeaf
public import Minimality.Type24SAT.K24.Wire24

/-!
# No five vertices of a type-24 solid are coplanar

Carbon A76 Lemma 1.0 (referee's short proof) and A77 Lemma 1.1.  Every 5-subset of the seven vertices contains the
vertex set of one of the nine facets (the eight triangles and `{0,3,4,5}`), and a vertex off a facet is not in its
plane (`fne24`).  Consequence: the hypothesis `hdiag` of `Split.Rim4.edgePlaneAny_of_strictRim4_level` holds for
every strict 4-rim of a type-24 solid.
-/

@[expose] public section

set_option autoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT

namespace Minimality.T24.NC

theorem cover5 : ∀ S : Finset (Fin 7), S.card = 5 → ∃ t : Fin 9, s0x_S24 t ⊆ S := by decide +kernel

theorem card_facet_le : ∀ t : Fin 9, (s0x_S24 t).card ≤ 4 := by decide +kernel

/-- Among any five vertices four have a nonzero bracket. -/
theorem exists_bracket_ne {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (S : Finset (Fin 7)) (hS : S.card = 5) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S, T24.Bk x a b c d ≠ 0 := by
  obtain ⟨t, ht⟩ := cover5 S hS
  have hlt : (s0x_S24 t).card < S.card := by have := card_facet_le t; omega
  obtain ⟨v, hvS, hvt⟩ := Finset.exists_of_ssubset
    (Finset.ssubset_iff_subset_ne.2 ⟨ht, fun h => by rw [h] at hlt; exact lt_irrefl _ hlt⟩)
  obtain ⟨hA, hB, hC⟩ := fABC_mem t
  exact ⟨_, ht hA, _, ht hB, _, ht hC, v, hvS, T24.fne24 F t v _ _ _ hvt rfl rfl rfl⟩

/-- No five distinct vertices are coplanar (all brackets of four of them vanish is impossible). -/
theorem not_coplanar5 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {i j k l m : Fin 7}
    (h : [i, j, k, l, m].Nodup) :
    ¬ ∀ a ∈ ({i, j, k, l, m} : Finset (Fin 7)), ∀ b ∈ ({i, j, k, l, m} : Finset (Fin 7)),
      ∀ c ∈ ({i, j, k, l, m} : Finset (Fin 7)), ∀ d ∈ ({i, j, k, l, m} : Finset (Fin 7)),
        T24.Bk x a b c d = 0 := by
  intro hz
  have hc : ({i, j, k, l, m} : Finset (Fin 7)).card = 5 := by
    have e : ({i, j, k, l, m} : Finset (Fin 7)) = [i, j, k, l, m].toFinset := by ext; simp
    rw [e, List.toFinset_card_of_nodup h]; rfl
  obtain ⟨a, ha, b, hb, c, hc', d, hd, hne⟩ := exists_bracket_ne F _ hc
  exact hne (hz a ha b hb c hc' d hd)

/-- Normal-vector form: no nonzero `n` and `c` with all five points on `⟪n, ·⟫ = c`. -/
theorem not_coplanar5_normal {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {i j k l m : Fin 7}
    (h : [i, j, k, l, m].Nodup) :
    ¬ ∃ (n : ℝ³) (c : ℝ), n ≠ 0 ∧ ∀ p ∈ ({i, j, k, l, m} : Finset (Fin 7)), ⟪n, x p⟫ = c := by
  rintro ⟨n, c, hn, hp⟩
  refine not_coplanar5 F h (fun a ha b hb c' hc' d hd => ?_)
  refine T24.det3_zero_of_inner n _ _ _ hn ?_ ?_ ?_ <;>
    simp only [inner_sub_right, hp a ha, hp b hb, hp c' hc', hp d hd, sub_self]

theorem hdiag {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (lab : ZMod 4 → Fin 7)
    (hinj : Function.Injective lab) :
    ∀ m, (∀ i, m ≠ lab i) → ∃ i : ZMod 4, cross (x (lab (i + 2)) - x (lab i)) (x m - x (lab i)) ≠ 0 := by
  intro m hm
  by_contra hcon
  push Not at hcon
  have h0 := hcon 0
  have h1 := hcon 1
  have e2 : (0 : ZMod 4) + 2 = 2 := by decide
  have e3 : (1 : ZMod 4) + 2 = 3 := by decide
  rw [e2] at h0; rw [e3] at h1
  have hx := EdgeViewLink.inj_of_fac24 F
  have n02 : x (lab 2) - x (lab 0) ≠ 0 := by
    rw [sub_ne_zero]; intro h; have := hinj (hx h); revert this; decide
  have n13 : x (lab 3) - x (lab 1) ≠ 0 := by
    rw [sub_ne_zero]; intro h; have := hinj (hx h); revert this; decide
  obtain ⟨s, hs⟩ := Split.cross_eq_zero_imp h0 n02
  obtain ⟨t, ht⟩ := Split.cross_eq_zero_imp h1 n13
  set u := x (lab 2) - x (lab 0) with hu
  set v := x (lab 3) - x (lab 1) with hv
  -- m = x0 + s u = x1 + t v
  have hm0 : x m - x (lab 0) = s • u := hs
  have hm1 : x m - x (lab 1) = t • v := ht
  have hsp : ∀ a ∈ ({lab 0, lab 1, lab 2, lab 3, m} : Finset (Fin 7)),
      ∃ α β : ℝ, x a - x (lab 0) = α • u + β • v := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, 0, by simp⟩
    · refine ⟨s, -t, ?_⟩
      have : x (lab 1) - x (lab 0) = (x m - x (lab 0)) - (x m - x (lab 1)) := by abel
      rw [this, hm0, hm1]; module
    · exact ⟨1, 0, by simp [hu]⟩
    · refine ⟨s, 1 - t, ?_⟩
      have : x (lab 3) - x (lab 0) = (x m - x (lab 0)) - (x m - x (lab 1)) + v := by rw [hv]; abel
      rw [this, hm0, hm1]; module
    · exact ⟨s, 0, by rw [hm0]; simp⟩
  have hnd : [lab 0, lab 1, lab 2, lab 3, m].Nodup := by
    have d01 : lab 0 ≠ lab 1 := hinj.ne (by decide)
    have d02 : lab 0 ≠ lab 2 := hinj.ne (by decide)
    have d03 : lab 0 ≠ lab 3 := hinj.ne (by decide)
    have d12 : lab 1 ≠ lab 2 := hinj.ne (by decide)
    have d13 : lab 1 ≠ lab 3 := hinj.ne (by decide)
    have d23 : lab 2 ≠ lab 3 := hinj.ne (by decide)
    simp [List.nodup_cons, d01, d02, d03, d12, d13, d23, (hm 0).symm, (hm 1).symm,
      (hm 2).symm, (hm 3).symm]
  refine not_coplanar5 F hnd (fun a ha b hb c hc d hd => ?_)
  obtain ⟨αa, βa, ea⟩ := hsp a ha
  obtain ⟨αb, βb, eb⟩ := hsp b hb
  obtain ⟨αc, βc, ec⟩ := hsp c hc
  obtain ⟨αd, βd, ed⟩ := hsp d hd
  have key : ∀ (p q : Fin 7) (αp βp αq βq : ℝ), x p - x (lab 0) = αp • u + βp • v →
      x q - x (lab 0) = αq • u + βq • v →
      x q - x p = (αq - αp) • u + (βq - βp) • v := by
    intro p q αp βp αq βq hp hq
    rw [← sub_sub_sub_cancel_right (x q) (x p) (x (lab 0)), hp, hq]; module
  unfold T24.Bk
  rw [key a b _ _ _ _ ea eb, key a c _ _ _ _ ea ec, key a d _ _ _ _ ea ed]
  simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- `Split.Rim4.edgePlaneAny_of_strictRim4_level` for a type-24 solid, without `hdiag`.  `hnp` (no two opposite
rim edges parallel) stays a hypothesis: for type 24 it is a genuine special-position stratum. -/
theorem edgePlaneAny_of_strictRim4_level {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (lab : ZMod 4 → Fin 7)
    (hinj : Function.Injective lab) (w₀ : ℝ³) (hR : Split.StrictRimN x w₀ lab)
    (hnp : ∀ r : ZMod 4,
      cross (x (lab (2 + r)) - x (lab (1 + r))) (x (lab (0 + r)) - x (lab (3 + r))) ≠ 0)
    (a : ZMod 4) (hlev : ⟪x (lab (a + 1)) - x (lab a), w₀⟫ = 0) : Gen.EdgePlaneAny x :=
  Split.Rim4.edgePlaneAny_of_strictRim4_level x lab hinj w₀ hR hnp (hdiag F lab hinj) a hlev

end Minimality.T24.NC
