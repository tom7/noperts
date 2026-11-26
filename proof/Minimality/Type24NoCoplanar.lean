module

public import Minimality.EdgePlaneRim4Level
public import Minimality.EdgeViewLink
public import Minimality.LinkRim24
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

/-- The 4-subsets for which the argument fails: `{0,3,4,5}` (the quad facet) and the five sets that contain
neither a triangle facet nor three vertices of the quad facet. -/
def badRims : List (Finset (Fin 7)) :=
  [{0, 3, 4, 5}, {1, 2, 3, 4}, {1, 2, 4, 5}, {1, 3, 5, 6}, {1, 4, 5, 6}, {2, 4, 5, 6}]

set_option synthInstance.maxSize 1024 in
/-- Every other 4-subset contains the reference triple of a facet (a triangle, or `0 3 4` of the quad) and a vertex
off it, or `0 3 5`, `0 4 5`, `3 4 5` and a vertex off the quad. -/
theorem cover4 : ∀ a b c d : Fin 7, [a, b, c, d].Nodup → ({a, b, c, d} : Finset (Fin 7)) ∉ badRims →
    (∃ t : Fin 9, ∃ v : Fin 7, v ∉ s0x_S24 t ∧
      fA t ∈ ({a, b, c, d} : Finset (Fin 7)) ∧ fB t ∈ ({a, b, c, d} : Finset (Fin 7)) ∧
        fC t ∈ ({a, b, c, d} : Finset (Fin 7)) ∧ v ∈ ({a, b, c, d} : Finset (Fin 7))) ∨
    (∃ v : Fin 7, v ∉ s0x_S24 3 ∧ v ∈ ({a, b, c, d} : Finset (Fin 7)) ∧
      (({0, 3, 5} : Finset (Fin 7)) ⊆ {a, b, c, d} ∨ ({0, 4, 5} : Finset (Fin 7)) ⊆ {a, b, c, d} ∨
        ({3, 4, 5} : Finset (Fin 7)) ⊆ {a, b, c, d})) := by
  decide +kernel

theorem cross_ne_of_det3_ne {a b c : ℝ³} (h : det3 a b c ≠ 0) :
    cross a b ≠ 0 ∧ cross b c ≠ 0 ∧ cross c a ≠ 0 := by
  refine ⟨fun e => h ?_, fun e => h ?_, fun e => h ?_⟩
  · simp [det3, e]
  · simp only [det3_expand]
    have h0 := congrFun (congrArg (fun v : ℝ³ => (v : Fin 3 → ℝ)) e) 0
    have h1 := congrFun (congrArg (fun v : ℝ³ => (v : Fin 3 → ℝ)) e) 1
    have h2 := congrFun (congrArg (fun v : ℝ³ => (v : Fin 3 → ℝ)) e) 2
    simp [cross] at h0 h1 h2
    linear_combination a 0 * h0 + a 1 * h1 + a 2 * h2
  · simp only [det3_expand]
    have h0 := congrFun (congrArg (fun v : ℝ³ => (v : Fin 3 → ℝ)) e) 0
    have h1 := congrFun (congrArg (fun v : ℝ³ => (v : Fin 3 → ℝ)) e) 1
    have h2 := congrFun (congrArg (fun v : ℝ³ => (v : Fin 3 → ℝ)) e) 2
    simp [cross] at h0 h1 h2
    linear_combination b 0 * h0 + b 1 * h1 + b 2 * h2

/-- Three non-collinear vertices of the quad facet and a vertex off it are not coplanar. -/
theorem quad_bk_ne {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {p q r v : Fin 7}
    (hp : p ∈ s0x_S24 3) (hq : q ∈ s0x_S24 3) (hr : r ∈ s0x_S24 3) (hv : v ∉ s0x_S24 3)
    (hc : cross (x q - x p) (x r - x p) ≠ 0) : T24.Bk x p q r v ≠ 0 := by
  have z : ∀ a : Fin 7, a ∈ s0x_S24 3 → ⟪F.N 3, x a - x p⟫ = 0 := by
    intro a ha; rw [F.inner_sub, F.zero 3 a ha, F.zero 3 p hp, sub_self]
  have off : ⟪F.N 3, x v - x p⟫ < 0 := by
    rw [F.inner_sub, F.zero 3 p hp, sub_zero]; exact F.neg 3 v hv
  have hN : F.N 3 ≠ 0 := by
    intro h; rw [h] at off; simp at off
  obtain ⟨κ, hκ⟩ := Link24R.cross_par_of_orth _ _ _ hN (by rw [real_inner_comm]; exact z q hq)
    (by rw [real_inner_comm]; exact z r hr)
  have hκ0 : κ ≠ 0 := by rintro rfl; apply hc; rw [hκ]; simp
  intro h
  unfold T24.Bk det3 at h
  rw [hκ, real_inner_smul_left] at h
  have := mul_eq_zero.1 h
  rcases this with h | h
  · exact hκ0 h
  · linarith

/-- Two parallel segments `ab`, `cd` of a type-24 solid with four distinct endpoints, not among `badRims`, are
impossible (the four points would be coplanar). -/
theorem not_parallel4 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {a b c d : Fin 7}
    (hnd : [a, b, c, d].Nodup) (hS : ({a, b, c, d} : Finset (Fin 7)) ∉ badRims)
    (hcr : cross (x a - x b) (x c - x d) = 0) : False := by
  have hx := EdgeViewLink.inj_of_fac24 F
  have hab : a ≠ b := by
    intro h; subst h; simp at hnd
  have nab : x a - x b ≠ 0 := by
    rw [sub_ne_zero]; intro h; exact hab (hx h)
  obtain ⟨s, hs⟩ := Split.cross_eq_zero_imp hcr nab
  set u := x a - x b with hu
  set e := x d - x b with he
  have hsp : ∀ p ∈ ({a, b, c, d} : Finset (Fin 7)), ∃ α β : ℝ, x p - x b = α • u + β • e := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact ⟨1, 0, by simp [hu]⟩
    · exact ⟨0, 0, by simp⟩
    · refine ⟨s, 1, ?_⟩
      have : x p - x b = (x p - x d) + (x d - x b) := by abel
      rw [this, hs, he]; module
    · exact ⟨0, 1, by simp [he]⟩
  have hz : ∀ p ∈ ({a, b, c, d} : Finset (Fin 7)), ∀ q ∈ ({a, b, c, d} : Finset (Fin 7)),
      ∀ r ∈ ({a, b, c, d} : Finset (Fin 7)), ∀ w ∈ ({a, b, c, d} : Finset (Fin 7)),
      T24.Bk x p q r w = 0 := by
    intro p hp q hq r hr w hw
    obtain ⟨α1, β1, e1⟩ := hsp _ hp
    obtain ⟨α2, β2, e2⟩ := hsp _ hq
    obtain ⟨α3, β3, e3⟩ := hsp _ hr
    obtain ⟨α4, β4, e4⟩ := hsp _ hw
    have key : ∀ (p q : Fin 7) (αp βp αq βq : ℝ), x p - x b = αp • u + βp • e →
        x q - x b = αq • u + βq • e → x q - x p = (αq - αp) • u + (βq - βp) • e := by
      intro p q αp βp αq βq hp hq
      rw [← sub_sub_sub_cancel_right (x q) (x p) (x b), hp, hq]; module
    unfold T24.Bk
    rw [key _ _ _ _ _ _ e1 e2, key _ _ _ _ _ _ e1 e3, key _ _ _ _ _ _ e1 e4]
    simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rcases cover4 a b c d hnd hS with ⟨t, v, hv, h1, h2, h3, h4⟩ | ⟨v, hv, h4, hsub⟩
  · exact T24.fne24 F t v _ _ _ hv rfl rfl rfl (hz _ h1 _ h2 _ h3 _ h4)
  · have hq : ∀ p q r : Fin 7, p ∈ s0x_S24 3 → q ∈ s0x_S24 3 → r ∈ s0x_S24 3 → p ∈ ({a, b, c, d} : Finset (Fin 7)) →
        q ∈ ({a, b, c, d} : Finset (Fin 7)) → r ∈ ({a, b, c, d} : Finset (Fin 7)) →
        cross (x q - x p) (x r - x p) ≠ 0 → False := fun p q r hp hq hr mp mq mr hc =>
      quad_bk_ne F hp hq hr hv hc (hz _ mp _ mq _ mr _ h4)
    rcases hsub with hsub | hsub | hsub
    · have m0 : (0 : Fin 7) ∈ ({a, b, c, d} : Finset (Fin 7)) := hsub (by decide)
      have m3 : (3 : Fin 7) ∈ ({a, b, c, d} : Finset (Fin 7)) := hsub (by decide)
      have m5 : (5 : Fin 7) ∈ ({a, b, c, d} : Finset (Fin 7)) := hsub (by decide)
      have := (cross_ne_of_det3_ne (T24.fne24 F 2 3 0 2 5 (by decide) rfl rfl rfl)).2.1
      exact hq 0 5 3 (by decide) (by decide) (by decide) m0 m5 m3 this
    · have m0 : (0 : Fin 7) ∈ ({a, b, c, d} : Finset (Fin 7)) := hsub (by decide)
      have m4 : (4 : Fin 7) ∈ ({a, b, c, d} : Finset (Fin 7)) := hsub (by decide)
      have m5 : (5 : Fin 7) ∈ ({a, b, c, d} : Finset (Fin 7)) := hsub (by decide)
      have := (cross_ne_of_det3_ne (T24.fne24 F 4 5 0 4 6 (by decide) rfl rfl rfl)).2.2
      exact hq 0 5 4 (by decide) (by decide) (by decide) m0 m5 m4 this
    · have m3 : (3 : Fin 7) ∈ ({a, b, c, d} : Finset (Fin 7)) := hsub (by decide)
      have m4 : (4 : Fin 7) ∈ ({a, b, c, d} : Finset (Fin 7)) := hsub (by decide)
      have m5 : (5 : Fin 7) ∈ ({a, b, c, d} : Finset (Fin 7)) := hsub (by decide)
      have := (cross_ne_of_det3_ne (T24.fne24 F 8 5 3 4 6 (by decide) rfl rfl rfl)).2.2
      exact hq 3 5 4 (by decide) (by decide) (by decide) m3 m5 m4 this

/-- Carbon A78 Lemma 1.2 (restricted to rims outside `badRims`): no two opposite rim edges are parallel. -/
theorem hnp_of_img {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (lab : ZMod 4 → Fin 7)
    (hinj : Function.Injective lab) (himg : Finset.univ.image lab ∉ badRims) :
    ∀ r : ZMod 4,
      cross (x (lab (2 + r)) - x (lab (1 + r))) (x (lab (0 + r)) - x (lab (3 + r))) ≠ 0 := by
  intro r hcr
  have hS : ({lab (2 + r), lab (1 + r), lab (0 + r), lab (3 + r)} : Finset (Fin 7)) =
      Finset.univ.image lab := by
    ext y
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro (h | h | h | h) <;> exact ⟨_, h.symm⟩
    · rintro ⟨i, rfl⟩
      have hi : ∀ r i : ZMod 4, i = 2 + r ∨ i = 1 + r ∨ i = 0 + r ∨ i = 3 + r := by decide
      rcases hi r i with h | h | h | h <;> rw [h] <;> simp
  have hnd : [lab (2 + r), lab (1 + r), lab (0 + r), lab (3 + r)].Nodup := by
    have : ∀ r : ZMod 4, [2 + r, 1 + r, 0 + r, 3 + r].Nodup := by decide
    simpa using (List.Nodup.map hinj (this r))
  exact not_parallel4 F hnd (by rw [hS]; exact himg) hcr

/-- `edgePlaneAny_of_strictRim4_level` with `hnp` discharged: the rim is not `{0,3,4,5}` (that case is the quad
facet, `T24.EPQ`). -/
theorem edgePlaneAny_of_strictRim4_level' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (lab : ZMod 4 → Fin 7)
    (hinj : Function.Injective lab) (himg : Finset.univ.image lab ∉ badRims)
    (w₀ : ℝ³) (hR : Split.StrictRimN x w₀ lab) (a : ZMod 4) (hlev : ⟪x (lab (a + 1)) - x (lab a), w₀⟫ = 0) :
    Gen.EdgePlaneAny x :=
  edgePlaneAny_of_strictRim4_level F lab hinj w₀ hR (hnp_of_img F lab hinj himg) a hlev

end Minimality.T24.NC
