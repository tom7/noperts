module

public import Minimality.Type21F2Case

@[expose] public section

/-!
# Type 21: the normal form `(+, −, +)` (`FEWER-FACES-PROOFS.md` §16 addendum, Theorems 16.18,
16.20, 16.23)

Labels as in `Type21Lemmas.lean`: `a, a', b, b', c, c', d = 0, 3, 4, 5, 1, 6, 2`.

* `galeD_pair_ne_zero` — `[x x'] ≠ 0` for an antipodal pair when the opposite equator is not
  planar.
* `cert_type21_pattern` — `K − 2` in the pattern `(+, −, +)` (`CrossNorm G`, `[4 5] > 0`):
  off the special positions, `K` has a rim certificate (`CertV`).  With `τ` from the cap, the classes are decided by
  the signs of `{5 4}` and `{0 3}`, the pair brackets of `K − 6` (`2` beyond `013`, `145`); they
  vanish exactly on the planar equators `{0, 1, 2, 3}`, `{1, 2, 4, 5}` of `K − 6`, which are
  excluded.  Class (b) (`{0 3} > 0`): 16.20; class (a) (`{5 4}, {0 3} < 0`): 16.18; class (c):
  16.23 with 16.24; on the switch surface `H⁻_c` (`δ_014(2) = δ_014(5)`, `δ_056(4) < δ_056(1)`)
  Theorem 16.30 (`cert_type21_switch`).  Every tie of a Gale comparison used is a segment
  parallel to a face plane (`NoPlaneParallel`), as is `f ≠ 0` for `K − 2` and `K − 6`.

**Certificate form** (§18.2, §18.6 step 2): every theorem of the tier cover concludes a rim
certificate at a named view (`CertV`: a segment view or a view satisfying `L`, the named vertex
crossings) instead of Rupertness; no horizontal double normal is assumed.  The old statement
`isRupert_type21_facets` and the limit theorem are in `Type21Limit.lean`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

variable {L : ℝ³ → Prop}

/-- **A pair bracket is nonzero off planar equators**: if the equator `b b' c c'` is not planar,
`[a a'] ≠ 0` (else the dependency `[a ·]` is an affine dependency of `b, b', c, c'` with
`[a c] ≠ 0`). -/
theorem galeD_pair_ne_zero {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') (h : det3 (b' - b) (c - b) (c' - b) ≠ 0) :
    galeD G.l G.m a a' ≠ 0 := by
  intro h0
  have hs := galeD_sum G.hl G.hm a
  have hv := (G.hl.galeD G.hm a).vsum
  rw [galeD_self] at hs hv
  rw [h0] at hs hv
  have hc : galeD G.l G.m a c ≠ 0 := galeD_ne_zero F.perm₂₃ G.perm₂₃
  have key : galeD G.l G.m a c • (c - b) =
      -(galeD G.l G.m a b' • (b' - b) + galeD G.l G.m a c' • (c' - b)) := by
    linear_combination (norm := module) hv - hs • b
  apply h
  have e : galeD G.l G.m a c * det3 (b' - b) (c - b) (c' - b) =
      det3 (b' - b) (galeD G.l G.m a c • (c - b)) (c' - b) := by
    simp only [det3_expand, PiLp.smul_apply, smul_eq_mul]; ring
  have : galeD G.l G.m a c * det3 (b' - b) (c - b) (c' - b) = 0 := by
    rw [e, key]
    simp only [det3_expand, PiLp.neg_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
      smul_eq_mul]
    ring
  exact (mul_eq_zero.mp this).resolve_left hc

/-- **The normal form `(+, −, +)`** (Theorems 16.18, 16.20, 16.23 with Lemma 16.24).  `K − 2`
in the pattern `(+, −, +)` (`CrossNorm G` and `[4 5] > 0`).  Off the special positions — no
segment of `K` parallel to a plane through three other points (`NoPlaneParallel`, which
contains every tie of a Gale comparison used and `f ≠ 0`), `GenPosTie`, no horizontal double
normal at the edge views (`NoHDNEdges`), `2` off the planes `013` and `145` (the planar
equators of `K − 6`), and the special positions of `T1` and of the two vertex tests of F2 — `K`
has a rim certificate: one of the tiers Q (of `K − 2` or `K − 6`), H, R, F1, F2 holds, or `K` is on the
switch surface `H⁻_c` (`δ_014(2) = δ_014(5)` with `|[3 1]| > |[3 4]|`, here
`δ_056(4) < δ_056(1)`) and Theorem 16.30 applies. -/
theorem cert_type21_pattern {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap21 F d) (G : GaleData a a' b b' c c') (hN : CrossNorm G)
    (h45 : 0 < galeD G.l G.m b b')
    (hpp : NoPlaneParallel (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hgen : GenPosTie (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (h013 : det3 (a - a') (c - a') (d - a') ≠ 0) (h145 : det3 (b - b') (c - b') (d - b') ≠ 0)
    (hT1 : ∀ u : ℝ³, u ≠ 0 → ⟪F.abc.N, u⟫ = 0 → ⟪F.ab'c'.N, u⟫ = 0 →
      T1Gen (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L a a' b b' u)
    (hF2 : F2ViewsL (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L a a' b b' c c' d) :
    CertV (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L := by
  -- the switch surface `H⁻_c`: Theorem 16.30
  by_cases hHc : F.abc.f d = F.abc.f b' ∧ F.ab'c'.f b < F.ab'c'.f c
  · exact cert_type21_switch F hd G hN hHc.1 hHc.2 hpp hgen
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd'
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := hd.ne
  obtain ⟨s34, s05, s04, s56, s51, s46, s41, s63, s60, s13, s10⟩ := hN.signs F
  have s30 := hN.h30; have s61 := hN.h61; have s35 := hN.h35
  have anti := galeD_anti G.l G.m
  set K := insert d ({a, a', b, b', c, c'} : Finset ℝ³) with hK
  have hKa : a ∈ K := by simp [hK]
  have hKa' : a' ∈ K := by simp [hK]
  have hKb : b ∈ K := by simp [hK]
  have hKb' : b' ∈ K := by simp [hK]
  have hKc : c ∈ K := by simp [hK]
  have hKc' : c' ∈ K := by simp [hK]
  have hKd : d ∈ K := by simp [hK]
  -- the ties excluded by `NoPlaneParallel`
  have tie : ∀ {P Q R : ℝ³} (Fc : FacetFn {a, a', b, b', c, c'} P Q R) {x y : ℝ³},
      [P, Q, R, x, y].Nodup → P ∈ K → Q ∈ K → R ∈ K → x ∈ K → y ∈ K → Fc.f x ≠ 0 →
      Fc.f x ≠ Fc.f y := by
    intro P Q R Fc x y hnd5 hP hQ hR hx hy hx0 heq
    exact hpp P hP Q hQ R hR x hx y hy hnd5 (facet_tie_det Fc hx0 heq)
  have nd5 : ∀ {x₁ x₂ x₃ x₄ x₅ : ℝ³}, x₁ ≠ x₂ → x₁ ≠ x₃ → x₁ ≠ x₄ → x₁ ≠ x₅ → x₂ ≠ x₃ →
      x₂ ≠ x₄ → x₂ ≠ x₅ → x₃ ≠ x₄ → x₃ ≠ x₅ → x₄ ≠ x₅ → [x₁, x₂, x₃, x₄, x₅].Nodup := by
    intro x₁ x₂ x₃ x₄ x₅ h12 h13 h14 h15 h23 h24 h25 h34 h35 h45
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    exact ⟨⟨h12, h13, h14, h15⟩, ⟨h23, h24, h25⟩, ⟨h34, h35⟩, h45, not_false⟩
  -- `[1 0] ≠ [5 1]`: the face `346` and `[1 ·]`
  have t10 : galeD G.l G.m c a ≠ galeD G.l G.m b' c := by
    intro h
    have r := (G.hl.galeD G.hm c).apply F.a'bc'.hN
    rw [F.a'bc'.hP, F.a'bc'.hQ, F.a'bc'.hR, galeD_self, anti b' c] at r
    refine tie F.a'bc' (x := a) (y := b') (nd5 ha'b ha'c' (Ne.symm haa') ha'b' hbc'
      (Ne.symm hab) hbb' (Ne.symm hac') (Ne.symm hb'c') hab') hKa' hKb hKc' hKa hKb'
      (F.a'bc'.neg a (by simp) haa' hab hac').ne ?_
    have : galeD G.l G.m c a * (F.a'bc'.f a - F.a'bc'.f b') = 0 := by
      linear_combination r - F.a'bc'.f b' * h
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left s10.ne')
  -- `[6 0] ≠ [5 6]`: the face `134` and `[6 ·]`
  have t56 : galeD G.l G.m b' c' ≠ galeD G.l G.m c' a := by
    intro h
    have r := (G.hl.galeD G.hm c').apply F.a'bc.hN
    rw [F.a'bc.hP, F.a'bc.hQ, F.a'bc.hR, galeD_self, anti b' c'] at r
    refine tie F.a'bc (x := a) (y := b') (nd5 ha'b ha'c (Ne.symm haa') ha'b' hbc (Ne.symm hab)
      hbb' (Ne.symm hac) (Ne.symm hb'c) hab') hKa' hKb hKc hKa hKb'
      (F.a'bc.neg a (by simp) haa' hab hac).ne ?_
    have : galeD G.l G.m c' a * (F.a'bc.f a - F.a'bc.f b') = 0 := by
      linear_combination r - F.a'bc.f b' * h.symm
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left s60.ne')
  -- `[5 1] ≠ [3 5]`: the face `046` and `[5 ·]`
  have t51 : galeD G.l G.m b' c ≠ galeD G.l G.m a' b' := by
    intro h
    have r := (G.hl.galeD G.hm b').apply F.abc'.hN
    rw [F.abc'.hP, F.abc'.hQ, F.abc'.hR, galeD_self, anti a' b'] at r
    refine tie F.abc' (x := c) (y := a') (nd5 hab hac' hac haa' hbc' hbc (Ne.symm ha'b)
      (Ne.symm hcc') (Ne.symm ha'c') (Ne.symm ha'c)) hKa hKb hKc' hKc hKa'
      (F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc').ne ?_
    have : galeD G.l G.m b' c * (F.abc'.f c - F.abc'.f a') = 0 := by
      linear_combination r - F.abc'.f a' * h
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left s51.ne')
  -- the face `056` and the dependencies `[1 ·]`, `[3 ·]`
  have r1 := (G.hl.galeD G.hm c).apply F.ab'c'.hN
  rw [F.ab'c'.hP, F.ab'c'.hQ, F.ab'c'.hR, galeD_self, anti b c] at r1
  have r3 := (G.hl.galeD G.hm a').apply F.ab'c'.hN
  rw [F.ab'c'.hP, F.ab'c'.hQ, F.ab'c'.hR, galeD_self, anti c a'] at r3
  have f3 := F.ab'c'.neg a' (by simp) (Ne.symm haa') ha'b' ha'c'
  have f4 := F.ab'c'.neg b (by simp) (Ne.symm hab) hbb' hbc'
  have f1 := F.ab'c'.neg c (by simp) (Ne.symm hac) (Ne.symm hb'c) hcc'
  -- `[4 1] ≠ [1 3]`
  have t13 : galeD G.l G.m b c ≠ galeD G.l G.m c a' := by
    intro h
    refine tie F.ab'c' (x := a') (y := b) (nd5 hab' hac' haa' hab hb'c' (Ne.symm ha'b')
      (Ne.symm hbb') (Ne.symm ha'c') (Ne.symm hbc') ha'b) hKa hKb' hKc' hKa' hKb f3.ne ?_
    have : galeD G.l G.m c a' * (F.ab'c'.f a' - F.ab'c'.f b) = 0 := by
      linear_combination r1 + F.ab'c'.f b * h
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left s13.ne')
  -- `[3 4] ≠ [1 3]`
  have t34 : galeD G.l G.m a' b ≠ galeD G.l G.m c a' := by
    intro h
    refine tie F.ab'c' (x := b) (y := c) (nd5 hab' hac' hab hac hb'c' (Ne.symm hbb') hb'c
      (Ne.symm hbc') (Ne.symm hcc') hbc) hKa hKb' hKc' hKb hKc f4.ne ?_
    have : galeD G.l G.m a' b * (F.ab'c'.f b - F.ab'c'.f c) = 0 := by
      linear_combination r3 - F.ab'c'.f c * h
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left s34.ne')
  -- `H⁻_c` in brackets
  have hHc' : ¬ (F.abc.f d = F.abc.f b' ∧ galeD G.l G.m a' b < galeD G.l G.m c a') := by
    rintro ⟨h1, h2⟩
    refine hHc ⟨h1, ?_⟩
    have e1 : galeD G.l G.m c a' * F.ab'c'.f c < galeD G.l G.m a' b * F.ab'c'.f c :=
      mul_lt_mul_of_neg_right h2 f1
    have e2 : galeD G.l G.m a' b * F.ab'c'.f b < galeD G.l G.m a' b * F.ab'c'.f c := by
      linarith
    exact lt_of_mul_lt_mul_left e2 s34.le
  have t23 : F.abc.f a' ≠ F.abc.f d :=
    tie F.abc (x := a') (y := d) (nd5 hab hac haa' (Ne.symm hda) hbc (Ne.symm ha'b)
      (Ne.symm hdb) (Ne.symm ha'c) (Ne.symm hdc) (Ne.symm hda')) hKa hKb hKc hKa' hKd
      (F.abc.neg a' (by simp) (Ne.symm haa') ha'b ha'c).ne
  have hRid : det3 (b - b') (c - b') (d - c') ≠ 0 :=
    hpp b' hKb' b hKb c hKc c' hKc' d hKd (nd5 (Ne.symm hbb') hb'c hb'c' (Ne.symm hdb') hbc hbc'
      (Ne.symm hdb) hcc' (Ne.symm hdc) (Ne.symm hdc'))
  have hpp2 : det3 (a - b) (c - b) (a' - b') ≠ 0 :=
    hpp b hKb a hKa c hKc b' hKb' a' hKa' (nd5 (Ne.symm hab) hbc hbb' (Ne.symm ha'b) hac hab'
      haa' (Ne.symm hb'c) (Ne.symm ha'c) (Ne.symm ha'b'))
  have hf : ¬(G.l a' + G.l b + G.l c' = 0 ∧ G.m a' + G.m b + G.m c' = 0) :=
    gale_f_ne F.swap₁.swap₃ G.swap₁.swap₃ (hpp a hKa b' hKb' c hKc a' hKa' b hKb
      (nd5 hab' hac haa' hab hb'c (Ne.symm ha'b') (Ne.symm hbb') (Ne.symm ha'c)
        (Ne.symm hbc) ha'b))
  -- tier `Q` of `K − 2`, else Lemma 16.16
  by_cases hQ : Type21Q G.l G.m a a' b b' c c'
  · exact cert_type21_Q F hd G hgen hQ
  obtain ⟨hq36, hq10⟩ := type21_O_quad36 F G hN h45 hf hQ
  -- the cap and the pair brackets of `K − 6`
  obtain ⟨α, β, τ, -, hβ, -, hτ, hco, hα, ht⟩ := hd.tau hN
  obtain ⟨hr, -, -⟩ := type21_r_pos hd hN hco hα ht
  obtain ⟨G2, l5, l4, l3, l0, l1, l2, m5, m4, m3, m0, m1, m2⟩ :=
    type21_galeO2 hd G hco hα ht hr.ne' s10.ne'
  obtain ⟨k1, k2, -, -⟩ := type21_galeO2_kappa (F := F) G hN hα ht hr G2 l5 l4 l3 l0 l1 l2 m5
    m4 m3 m0 m1 m2
  have n1 : galeD G2.l G2.m b' b ≠ 0 := galeD_pair_ne_zero hd.O2 G2 h013
  have n2 : galeD G2.l G2.m a' a ≠ 0 := galeD_pair_ne_zero hd.O2.perm₁₂ G2.perm₁₂ h145
  rcases lt_trichotomy ((β + τ * galeD G.l G.m c c') * galeD G.l G.m a' a)
    (τ * galeD G.l G.m c a' * galeD G.l G.m c' a) with hc145 | h0 | hn145
  · -- class (b)
    exact cert_type21_classB F hd G hN hτ hco hα ht hc145 t10 t13 hRid hgen
  · exfalso
    apply n2
    rw [k2, anti a' a]
    linear_combination (β + τ * galeD G.l G.m c c') * galeD G.l G.m c a * h0
  rcases lt_trichotomy ((β + τ * galeD G.l G.m c c') * galeD G.l G.m b' b +
    τ * galeD G.l G.m b c * galeD G.l G.m b' c') 0 with hn013 | h0 | hc013
  · -- class (a)
    exact cert_type21_classA F hd G hN h45 hτ hco hα ht hq36 hq10 hn013 hn145 hgen
  · exfalso
    apply n1
    rw [k1, h0, mul_zero]
  · -- class (c)
    exact cert_type21_classC F hd G hN h45 hβ hτ hco hα ht hc013 hn145 hq10 hpp2 t34 t10 t51
      t56 t23 hHc' hT1 hF2 hgen

/-! ### The normal forms (Lemma 16.15) -/

/-- **The signs of `K − 6`** (Lemmas 16.2, 16.3, 16.14), for any Gale data of `K − 2` with
`[3 5] > 0`: Gale data `G2` of `K − 6` (labels `5, 4, 3, 0, 1, 2`) with `[5 4]₂ = r [1 0] {5 4}`,
`[3 0]₂ = −r [1 0] {0 3}`, `[2 1]₂ = r [1 0] [6 1]`, so `[5 4]₂ > 0` if `[5 4] > 0` (`2` cannot be
beyond `013` then) and `[3 0]₂ < 0` if `[3 0] < 0` (nor beyond `145`); and `[4 0]₂ < 0`
(Lemma 13.4 for `K − 6`, from `[4 1]₂ > 0`). -/
theorem type21_O2_signs {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap21 F d) (G : GaleData a a' b b' c c') (h35 : 0 < galeD G.l G.m a' b') :
    ∃ G2 : GaleData b' b a' a c d,
      (0 < galeD G.l G.m b' b → 0 < galeD G2.l G2.m b' b) ∧
      (galeD G.l G.m a' a < 0 → galeD G2.l G2.m a' a < 0) ∧
      (0 < galeD G.l G.m c' c → 0 < galeD G2.l G2.m d c) ∧
      (galeD G.l G.m c' c < 0 → galeD G2.l G2.m d c < 0) ∧
      galeD G2.l G2.m b a < 0 := by
  obtain ⟨s34, s05, s04, s56, s51, s46, s41, s63, s60, s13, s10⟩ := type21_cross_signs F h35
  have anti := galeD_anti G.l G.m
  obtain ⟨α, β, τ, -, hβ, -, hτ, hco, hα, ht⟩ := hd.tau' h35
  obtain ⟨hr, -, -⟩ := type21_r_pos' hd h35 hco hα ht
  obtain ⟨G2, l5, l4, l3, l0, l1, l2, m5, m4, m3, m0, m1, m2⟩ :=
    type21_galeO2 hd G hco hα ht hr.ne' s10.ne'
  have hβ' : β = 1 + τ * galeD G.l G.m c a - τ * galeD G.l G.m b' c := by linarith
  have k1 : galeD G2.l G2.m b' b = (β + τ * galeD G.l G.m c c') * galeD G.l G.m c a *
      ((β + τ * galeD G.l G.m c c') * galeD G.l G.m b' b +
        τ * galeD G.l G.m b c * galeD G.l G.m b' c') := by
    show G2.l b' * G2.m b - G2.m b' * G2.l b = _
    rw [l5, m4, m5, l4, hβ']
    simp only [galeD, IsDep.l_last G.hl, IsDep.l_last G.hm]; ring
  have k2 : galeD G2.l G2.m a' a = -((β + τ * galeD G.l G.m c c') * galeD G.l G.m c a *
      ((β + τ * galeD G.l G.m c c') * galeD G.l G.m a a' +
        τ * galeD G.l G.m c a' * galeD G.l G.m c' a)) := by
    show G2.l a' * G2.m a - G2.m a' * G2.l a = _
    rw [l3, m0, m3, l0]; ring
  have k3 : galeD G2.l G2.m d c =
      (β + τ * galeD G.l G.m c c') * galeD G.l G.m c a * galeD G.l G.m c' c := by
    show G2.l d * G2.m c - G2.m d * G2.l c = _
    rw [l2, m1, m2, l1, anti c' c, anti c a]; ring
  have hbc2 : 0 < galeD G2.l G2.m b c := by
    show 0 < G2.l b * G2.m c - G2.m b * G2.l c
    rw [l4, m1, l1, anti b c, anti c a]
    have := mul_pos (mul_pos hβ s41) (mul_pos hr s10)
    linarith
  obtain ⟨-, ⟨B1, -, B3⟩, -, -⟩ := cluster_signs hd.O2 G2
  have hba'2 : galeD G2.l G2.m b a' < 0 := neg_of_mul_neg_left B3 hbc2.le
  refine ⟨G2, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    neg_of_mul_pos_right B1 hba'2.le⟩
  · rw [k1]
    refine mul_pos (mul_pos hr s10) ?_
    have := mul_pos hr h
    have := mul_pos (mul_pos hτ s41) s56
    linarith
  · rw [k2, anti a' a]
    have i1 : 0 < (β + τ * galeD G.l G.m c c') * -galeD G.l G.m a' a +
        τ * galeD G.l G.m c a' * galeD G.l G.m c' a := by
      have := mul_pos hr (neg_pos.mpr h)
      have := mul_pos (mul_pos hτ s13) s60
      linarith
    have := mul_pos (mul_pos hr s10) i1
    linarith
  · rw [k3]; exact mul_pos (mul_pos hr s10) h
  · rw [k3]; exact mul_neg_of_pos_of_neg (mul_pos hr s10) h

theorem type21_set_O21 (a a' b b' c c' d : ℝ³) :
    insert c' ({a', a, b', b, c, d} : Finset ℝ³) = insert d {a, a', b, b', c, c'} := by
  ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

/-- **The special positions of the two vertex tests of F2** in one labelling (vertex `b`), with
the ties of `QuadTie` and no horizontal double normal of `V`: at every direction `u ≠ 0` of the
line `abc ∩ a'bc'` (`V = 014/2346`, rim `b, d, b', c`) and of `abc' ∩ a'bc` (`V′ = 046/134`, rim
`b, a', b', a`).  The planes are given by determinants. -/
def F2Views (V : Finset ℝ³) (a a' b b' c c' d : ℝ³) : Prop :=
  (∀ u : ℝ³, u ≠ 0 → det3 (a - b) (c - b) u = 0 → det3 (a' - b) (c' - b) u = 0 →
    det3 (c - d) (b' - d) u ≠ 0 ∧ QuadTie ⟪b, u⟫ ⟪d, u⟫ ⟪b', u⟫ ⟪c, u⟫ ∧ NoHDNAt V u) ∧
  (∀ u : ℝ³, u ≠ 0 → det3 (a - b) (c' - b) u = 0 → det3 (a' - b) (c - b) u = 0 →
    det3 (a - a') (b' - a') u ≠ 0 ∧ QuadTie ⟪b, u⟫ ⟪a', u⟫ ⟪b', u⟫ ⟪a, u⟫ ∧ NoHDNAt V u)

theorem F2Views.toL {V : Finset ℝ³} {a a' b b' c c' d : ℝ³} (h : F2Views V a a' b b' c c' d) :
    F2ViewsL V (NoHDNAt V) a a' b b' c c' d :=
  ⟨fun u hu h1 h2 => ⟨(h.1 u hu h1 h2).1, (h.1 u hu h1 h2).2.2⟩,
    fun v hv h1 h2 => ⟨(h.2 v hv h1 h2).1, (h.2 v hv h1 h2).2.2⟩,
    fun u v hu h1 h2 hv h3 h4 => Or.inl ⟨(h.1 u hu h1 h2).2.1, (h.2 v hv h3 h4).2.1⟩⟩

/-- The special positions of the other classes for one labelling `F` of `K − 2` with the cap
`d`: those of the two vertex tests of F2 (`F2Views`).  (The switch surface `H⁻_c` of class (c) is
no longer excluded: Theorem 16.30.) -/
def Type21OtherGen (K : Finset ℝ³) (L : ℝ³ → Prop) {a a' b b' c c' : ℝ³}
    (_F : OctFacets a a' b b' c c') (d : ℝ³) : Prop :=
  F2ViewsL K L a a' b b' c c' d

/-- **Theorem 16.26 (type 21).**  Let `K = O ∪ {2}` be of type 21 (`IsCap21`).  Off the special
positions — `NoPlaneParallel` (every tie of a Gale comparison used, and `f ≠ 0` for `K − 2` and
`K − 6`), `GenPosTie`, no horizontal double normal at the edge views (`NoHDNEdges`), the five planar
equators of `K − 2` and `K − 6` (`{4, 5, 1, 6}`, `{0, 3, 1, 6}`, `{0, 3, 4, 5}`, `{0, 3, 1, 2}`,
`{4, 5, 1, 2}`), and, for each of the four labellings `id, σ1, σ2, σ2σ1`, the special positions
of `T1` (`Type21CapGen`) and of F2 (`Type21OtherGen`) — `K` has a rim certificate (`CertV`): one of the tiers Q (of
`K − 2` or `K − 6`), H, R, F1, F2 holds, or, on the switch surface, the certificate of
Theorem 16.30 at the edge `25`.
*Proof.* The cap-face class is Theorem 16.13.  Otherwise reflect the Gale diagram so that
`[3 5] > 0`; the pattern `(s_A, s_B, s_C)` of `K − 2` is not `±(+, +, +)`.  `(+, −, +)` is the
normal form; `(+, −, −)` is mapped to it by `σ1`.  For the others `K − 6` is used
(`type21_O2_signs`): `(−, +, −)` and, with `2` beyond `145`, `(+, +, −)` by `σ2`; `(−, +, +)` and,
with `2` beyond `013`, `(−, −, +)` by `σ2σ1`; in the remaining two states `K − 6` is in its
cap-face class. -/
theorem cert_type21_all {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap21 F d)
    (hpp : NoPlaneParallel (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hgen : GenPosTie (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hE : det3 (b' - b) (c - b) (c' - b) ≠ 0 ∧ det3 (a' - a) (c - a) (c' - a) ≠ 0 ∧
      det3 (a' - a) (b - a) (b' - a) ≠ 0 ∧ det3 (a - a') (c - a') (d - a') ≠ 0 ∧
      det3 (b - b') (c - b') (d - b') ≠ 0)
    (hG : Type21CapGen (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L F d ∧
      Type21CapGen (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L F.perm₁₂ d ∧
      Type21CapGen (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L hd.O2 c' ∧
      Type21CapGen (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L hd.O2.perm₁₂ c')
    (hG' : Type21OtherGen (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L F d ∧
      Type21OtherGen (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L F.perm₁₂ d ∧
      Type21OtherGen (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L hd.O2 c' ∧
      Type21OtherGen (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L hd.O2.perm₁₂ c') :
    CertV (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L := by
  by_cases hcl : (∃ G : GaleData a a' b b' c c', CapFace G) ∨
      (∃ G : GaleData b' b a' a c d, CapFace G)
  · exact cert_type21_capFace F hd hpp hgen hG hcl
  push Not at hcl
  obtain ⟨hcl1, hcl2⟩ := hcl
  obtain ⟨hE1, hE2, hE3, hE4, hE5⟩ := hE
  obtain ⟨g1, g2, g3, g4⟩ := hG
  obtain ⟨v1, v2, v3, v4⟩ := hG'
  obtain ⟨G0⟩ := F.nonempty_galeData
  obtain ⟨G, h35⟩ : ∃ G : GaleData a a' b b' c c', 0 < galeD G.l G.m a' b' := by
    have hε : galeD G0.l G0.m a' b' ≠ 0 := galeD_ne_zero F.swap₁.swap₂ G0.swap₁.swap₂
    rcases lt_or_gt_of_ne hε with h | h
    · exact ⟨G0.flip, by rw [galeD_flip]; linarith⟩
    · exact ⟨G0, h⟩
  have anti := galeD_anti G.l G.m
  have n30 : galeD G.l G.m a' a ≠ 0 := by
    rw [anti]; exact neg_ne_zero.mpr (galeD_pair_ne_zero F G hE1)
  have n54 : galeD G.l G.m b' b ≠ 0 := by
    rw [anti]; exact neg_ne_zero.mpr (galeD_pair_ne_zero F.perm₁₂ G.perm₁₂ hE2)
  have n61 : galeD G.l G.m c' c ≠ 0 := by
    rw [anti]; exact neg_ne_zero.mpr (galeD_pair_ne_zero F.perm₂₃.perm₁₂ G.perm₂₃.perm₁₂ hE3)
  have eO2 := type21_set_O2 a a' b b' c c' d
  have eO21 := type21_set_O21 a a' b b' c c' d
  have e1 := (type21_set a a' b b' c c' d).2.2.2.2
  -- the core for each labelling
  have coreO : 0 < galeD G.l G.m a' a → 0 < galeD G.l G.m c' c → 0 < galeD G.l G.m b b' →
      CertV (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L := fun s30 s61 s45 =>
    cert_type21_pattern F hd G ⟨s30, s61, h35⟩ s45 hpp hgen hE4 hE5 g1 v1
  have coreS1 : galeD G.l G.m b' b < 0 → galeD G.l G.m c' c < 0 → galeD G.l G.m a a' < 0 →
      CertV (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L := by
    intro s54 s61 s03
    rw [← e1] at hpp hgen g2 v2 ⊢
    refine cert_type21_pattern F.perm₁₂ hd.sigma1 G.perm₁₂.flip ⟨?_, ?_, ?_⟩ ?_ hpp hgen
      hE5 hE4 g2 v2
    · show 0 < galeD G.flip.l G.flip.m b' b
      rw [galeD_flip]; linarith
    · show 0 < galeD G.flip.l G.flip.m c' c
      rw [galeD_flip]; linarith
    · show 0 < galeD G.flip.l G.flip.m b' a'
      rw [galeD_flip, anti]; linarith
    · show 0 < galeD G.flip.l G.flip.m a a'
      rw [galeD_flip]; linarith
  obtain ⟨G2, i1, i2, i3, i4, i5⟩ := type21_O2_signs F hd G h35
  have anti2 := galeD_anti G2.l G2.m
  have m54 : galeD G2.l G2.m b' b ≠ 0 := galeD_pair_ne_zero hd.O2 G2 hE4
  have m30 : galeD G2.l G2.m a' a ≠ 0 := galeD_pair_ne_zero hd.O2.perm₁₂ G2.perm₁₂ hE5
  have coreS2 : 0 < galeD G2.l G2.m b' b → galeD G2.l G2.m d c < 0 →
      galeD G2.l G2.m a' a < 0 → CertV (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L := by
    intro t54 t21 t30
    rw [← eO2] at hpp hgen g3 v3 ⊢
    refine cert_type21_pattern hd.O2 hd.sigma2 G2.flip ⟨?_, ?_, ?_⟩ ?_ hpp hgen
      hE1 hE2 g3 v3
    · show 0 < galeD G2.flip.l G2.flip.m b b'
      rw [galeD_flip, anti2]; linarith
    · show 0 < galeD G2.flip.l G2.flip.m d c
      rw [galeD_flip]; linarith
    · show 0 < galeD G2.flip.l G2.flip.m b a
      rw [galeD_flip]; linarith
    · show 0 < galeD G2.flip.l G2.flip.m a' a
      rw [galeD_flip]; linarith
  have coreS21 : 0 < galeD G2.l G2.m b' b → 0 < galeD G2.l G2.m d c →
      galeD G2.l G2.m a' a < 0 → CertV (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L := by
    intro t54 t21 t30
    rw [← eO21] at hpp hgen g4 v4 ⊢
    refine cert_type21_pattern hd.O2.perm₁₂ hd.sigma2.sigma1 G2.perm₁₂ ⟨?_, ?_, ?_⟩ ?_ hpp
      hgen hE2 hE1 g4 v4
    · show 0 < galeD G2.l G2.m a a'
      rw [anti2]; linarith
    · exact t21
    · show 0 < galeD G2.l G2.m a b
      rw [anti2]; linarith
    · exact t54
  have capO2 : galeD G2.l G2.m b' b * galeD G2.l G2.m a' a > 0 →
      galeD G2.l G2.m b' b * galeD G2.l G2.m d c < 0 → False := by
    intro p1 p2
    refine hcl2 G2 ⟨?_, ?_⟩
    · rw [anti2 b' b, anti2 a' a]; linarith
    · rw [anti2 b' b]; linarith
  rcases lt_or_gt_of_ne n30 with s30 | s30 <;> rcases lt_or_gt_of_ne n54 with s54 | s54 <;>
    rcases lt_or_gt_of_ne n61 with s61 | s61
  · exact absurd ⟨mul_pos_of_neg_of_neg s30 s54, mul_pos_of_neg_of_neg s30 s61⟩ (hcl1 G)
  · -- `(−, −, +)`: `σ2σ1`, else `K − 6` is cap-face
    have t30 := i2 s30
    have t21 := i3 s61
    rcases lt_or_gt_of_ne m54 with t54 | t54
    · exact (capO2 (mul_pos_of_neg_of_neg t54 t30) (mul_neg_of_neg_of_pos t54 t21)).elim
    · exact coreS21 t54 t21 t30
  · -- `(−, +, −)`: `σ2`
    exact coreS2 (i1 s54) (i4 s61) (i2 s30)
  · -- `(−, +, +)`: `σ2σ1`
    exact coreS21 (i1 s54) (i3 s61) (i2 s30)
  · -- `(+, −, −)`: `σ1`
    exact coreS1 s54 s61 (by rw [anti]; linarith)
  · -- `(+, −, +)`: the normal form
    exact coreO s30 s61 (by rw [anti]; linarith)
  · -- `(+, +, −)`: `σ2`, else `K − 6` is cap-face
    have t54 := i1 s54
    have t21 := i4 s61
    rcases lt_or_gt_of_ne m30 with t30 | t30
    · exact coreS2 t54 t21 t30
    · exact (capO2 (mul_pos t54 t30) (mul_neg_of_pos_of_neg t54 t21)).elim
  · exact absurd ⟨mul_pos s30 s54, mul_pos s30 s61⟩ (hcl1 G)

end Minimality

end
