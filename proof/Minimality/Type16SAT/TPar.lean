module

public import Minimality.Type16SAT.WitRow
public import Minimality.Type21SAT.Geom
public import Minimality.Type21SAT.Par

@[expose] public section

/-!
# L16T (copy of L29T piece T5): edge-on facets at a tie view, and the facing exclusions (family 36)

The tie view of `(t, f)` is `u'(eps) = w + eps sigma d` with `w = N_t x D_f` and `d = dpl N_t D_f =
|N_t|^2 D_f - <N_t, D_f> N_t` (DESIGN 2.1).  The facing of a facet `s` there has the two levels
`<N_s, w> = - Lf N_t N_s D_f` and `<N_s, d> = Kf N_t N_s D_f` (`Lf` = the encoder's lineS, `Kf` = its `K`).

* Geometry, free of the CNF: both levels zero means `N_s // N_t` (`tie_par`); a facet of type 16 parallel to
  another one is antiparallel (`antipar_neg`), vertex disjoint from it (`antipar_disjoint`), and unique
  (`at_most_one_antipar`); together `zero_facet_antipar` (what the tie rule, T6, needs for its facet `zi`).
  The vertex-disjoint pairs of type 16 are AG, BC, DF, DH (`disjPairs`, `antipar_pairs`, `zero_facet_pair`).
* Family 36 (DESIGN 4.7): `t36a_geom`, `t36b_geom` (off Z0), then `fam36a_sound`, `fam36b_sound`, `fam36_sound`
  against explicit lex sign hypotheses `Lex2Sg` on the two literals of `Fp(s)`, with the KA real `k` given by
  `KAsem` (`k = 1` under Z0, `k = Kf` off Z0; the convention of TIE-REVIEW 1.4 / DESIGN 3).  The glue to `rhoW`
  is to prove `Lex2Sg (evalW (rhoW g) (Fp s).1) (evalW (rhoW g) (Fp s).2) (-Lf ..) (sigma * k)` (T4's lexS_sound).
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.H29.SAT Minimality.H16.SAT

namespace Minimality.H16T.SAT

/-! ### The vectors of the tie view -/

/-- The plane direction of the tie view: `d_+ = |n|^2 D - <n, D> n` (DESIGN 2.1, `= - n x (n x D)`). -/
noncomputable def dpl (n D : ℝ³) : ℝ³ := ⟪n, n⟫ • D - ⟪n, D⟫ • n

/-- The encoder's line functional `L(s, x) = det3 (N_t, N_s, D_x)` (lineS). -/
noncomputable def Lf (n a D : ℝ³) : ℝ := det3 n a D

/-- The second level of a facing at the tie view: `K(s) = |N_t|^2 <D_f, N_s> - <N_t, D_f> <N_t, N_s>`. -/
noncomputable def Kf (n a D : ℝ³) : ℝ := ⟪n, n⟫ * ⟪D, a⟫ - ⟪n, D⟫ * ⟪n, a⟫

theorem dpl_eq_cross (n D : ℝ³) : dpl n D = cross (cross n D) n := by
  ext i
  fin_cases i <;>
    simp only [dpl, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul, cross_apply_zero, cross_apply_one, cross_apply_two, inn3] <;> ring

/-- First level: `<a, n x D> = - L`. -/
theorem inner_cross_eq_Lf (n a D : ℝ³) : ⟪a, cross n D⟫ = - Lf n a D := by
  simp only [Lf, det3_expand, inn3, cross_apply_zero, cross_apply_one, cross_apply_two]; ring

/-- Second level: `<a, d_+> = K`. -/
theorem inner_dpl_eq_Kf (n a D : ℝ³) : ⟪a, dpl n D⟫ = Kf n a D := by
  simp only [dpl, Kf, inner_sub_right, inner_smul_right, real_inner_comm a D, real_inner_comm a n]

theorem inner_n_cross (n D : ℝ³) : ⟪n, cross n D⟫ = 0 := by
  rw [real_inner_comm]; exact inner_cross_left n D

theorem inner_n_dpl (n D : ℝ³) : ⟪n, dpl n D⟫ = 0 := by
  simp only [dpl, inner_sub_right, inner_smul_right]; ring

theorem inner_cross_dpl (n D : ℝ³) : ⟪cross n D, dpl n D⟫ = 0 := by
  simp only [dpl, inner_sub_right, inner_smul_right, inner_cross_left, inner_cross_right, mul_zero, sub_zero]

/-- Lagrange: `<d_+, D> = |n x D|^2`. -/
theorem inner_dpl_D (n D : ℝ³) : ⟪dpl n D, D⟫ = ⟪cross n D, cross n D⟫ := by
  simp only [dpl, inner_sub_left, inner_smul_left, conj_trivial, inn3, cross_apply_zero, cross_apply_one,
    cross_apply_two]; ring

theorem dpl_ne {n D : ℝ³} (hZ : cross n D ≠ 0) : dpl n D ≠ 0 := by
  intro h
  have := inner_dpl_D n D
  rw [h, inner_zero_left] at this
  exact hZ (inner_self_eq_zero.mp this.symm)

theorem ne_of_cross_ne {n D : ℝ³} (hZ : cross n D ≠ 0) : n ≠ 0 := by
  intro h; apply hZ; subst h
  ext i; fin_cases i <;> simp [cross_apply_zero, cross_apply_one, cross_apply_two]

/-- **Parallel of two zero levels** (general form): `a` and the nonzero `n` both orthogonal to the orthogonal
nonzero vectors `w`, `d`: `a` is a multiple of `n`. -/
theorem par_of_perp2 {n w d a : ℝ³} (hn : n ≠ 0) (hw : w ≠ 0) (hd : d ≠ 0) (hnw : ⟪n, w⟫ = 0)
    (hnd : ⟪n, d⟫ = 0) (hwd : ⟪w, d⟫ = 0) (haw : ⟪a, w⟫ = 0) (had : ⟪a, d⟫ = 0) : ∃ r : ℝ, a = r • n :=
  parallel_of_perp w d n a d hw hn hnw hnd haw had (by rw [real_inner_comm]; exact hwd)
    (fun h => hd (inner_self_eq_zero.mp h))

/-- **parallel_of_two_level_zero**: off Z0 (`n x D != 0`), a vector with both levels of the tie view zero is a
multiple of `n`. -/
theorem tie_par {n D a : ℝ³} (hZ : cross n D ≠ 0) (h1 : Lf n a D = 0) (h2 : Kf n a D = 0) :
    ∃ r : ℝ, a = r • n :=
  par_of_perp2 (ne_of_cross_ne hZ) hZ (dpl_ne hZ) (inner_n_cross n D) (inner_n_dpl n D) (inner_cross_dpl n D)
    (by rw [inner_cross_eq_Lf, h1, neg_zero]) (by rw [inner_dpl_eq_Kf, h2])

/-! ### Parallel facets of type 16 -/

variable {x : Fin 7 → ℝ³}

/-- The normal of a facet of type 16 is not zero. -/
theorem N_ne16 (F : S0xFac 8 V2.fIdx x) (t : Fin 8) : F.N t ≠ 0 := by
  have key : ∀ t : Fin 8, ∃ j i : Fin 7, j ∈ V2.fIdx t ∧ i ∉ V2.fIdx t := by decide +kernel
  obtain ⟨j, i, hj, hi⟩ := key t
  intro h0
  have h1 := F.hN t (x i) (x j)
  rw [h0] at h1
  simp only [inner_zero_left] at h1
  have := F.zero t j hj
  have := F.neg t i hi
  linarith

theorem nn16 (F : S0xFac 8 V2.fIdx x) (t : Fin 8) : 0 < ⟪F.N t, F.N t⟫ := real_inner_self_pos.2 (N_ne16 F t)

/-- **antipar_neg**: two distinct facets with `N_s = r N_t` have `r < 0`. -/
theorem antipar_neg (F : S0xFac 8 V2.fIdx x) {t s : Fin 8} {r : ℝ} (hne : t ≠ s)
    (hN : F.N s = r • F.N t) : r < 0 := by
  obtain ⟨hS, hsub⟩ := facet_pair t s hne
  have h := neg_of_parallel F hN (nn16 F t).ne' (nn16 F s).ne' hS hsub
  rw [hN, inner_smul_left] at h
  simp only [conj_trivial] at h
  have hp := nn16 F t
  by_contra hc
  nlinarith [mul_nonneg (not_lt.mp hc) hp.le]

/-- **antipar_disjoint**: two distinct facets with proportional normals share no vertex. -/
theorem antipar_disjoint (F : S0xFac 8 V2.fIdx x) {t s : Fin 8} {r : ℝ} (hne : t ≠ s)
    (hN : F.N s = r • F.N t) (v : Fin 7) (hvt : v ∈ V2.fIdx t) (hvs : v ∈ V2.fIdx s) : False := by
  apply (facet_pair s t (Ne.symm hne)).2
  intro q hq
  by_contra hqs
  have e1 := F.hN s (x q) (x v)
  rw [hN, inner_smul_left, ← F.hN t] at e1
  simp only [conj_trivial] at e1
  rw [F.zero t q hq, F.zero t v hvt, F.zero s v hvs] at e1
  have := F.neg s q hqs
  linarith

/-- **at_most_one_antipar**: a facet has at most one parallel partner. -/
theorem at_most_one_antipar (F : S0xFac 8 V2.fIdx x) {t s s2 : Fin 8} {r r2 : ℝ} (h1 : t ≠ s) (h2 : t ≠ s2)
    (h3 : s ≠ s2) (hN1 : F.N s = r • F.N t) (hN2 : F.N s2 = r2 • F.N t) : False := by
  have hr := antipar_neg F h1 hN1
  have hr2 := antipar_neg F h2 hN2
  have hc : 0 < r2 / r := div_pos_of_neg_of_neg hr2 hr
  have hN : F.N s2 = (r2 / r) • F.N s := by
    rw [hN1, hN2, smul_smul, div_mul_cancel₀ _ hr.ne]
  obtain ⟨hS, hsub⟩ := facet_pair s s2 h3
  exact no_same_dir F hc hN hS hsub

/-- **The zero facet of a tie view** (DESIGN 2.2, for T6's `tie_hfac`): off Z0, a facet `s != t` with both levels
zero is antiparallel to `t`. -/
theorem zero_facet_antipar (F : S0xFac 8 V2.fIdx x) {t s : Fin 8} {D : ℝ³} (hZ : cross (F.N t) D ≠ 0)
    (hne : t ≠ s) (h1 : Lf (F.N t) (F.N s) D = 0) (h2 : Kf (F.N t) (F.N s) D = 0) :
    ∃ r : ℝ, r < 0 ∧ F.N s = r • F.N t := by
  obtain ⟨r, hr⟩ := tie_par hZ h1 h2
  exact ⟨r, antipar_neg F hne hr, hr⟩

/-! ### The vertex-disjoint facet pairs of type 16: AG, BC, DF, DH -/

/-- The vertex-disjoint facet pairs of type 16 (`V2.fIdx`: A 0235, B 1356, C 024, D 036, E 046, F 145, G 146, H 245),
as encoder indices `t < s`: A-G, B-C, D-F, D-H (type 29 has seven).  On the PL/Z strata D and F are parallel. -/
def disjPairs : List (Nat × Nat) := [(0, 6), (1, 2), (3, 5), (3, 7)]

/-- Two distinct facets share no vertex iff they are one of the pairs of `disjPairs`. -/
theorem disj_iff : ∀ t s : Fin 8, t ≠ s →
    (Disjoint (V2.fIdx t) (V2.fIdx s) ↔ ((t.val, s.val) ∈ disjPairs ∨ (s.val, t.val) ∈ disjPairs)) := by
  decide +kernel

/-- **antipar_pairs**: two distinct facets of type 16 with proportional normals are one of the pairs AG, BC, DF, DH. -/
theorem antipar_pairs (F : S0xFac 8 V2.fIdx x) {t s : Fin 8} {r : ℝ} (hne : t ≠ s) (hN : F.N s = r • F.N t) :
    (t.val, s.val) ∈ disjPairs ∨ (s.val, t.val) ∈ disjPairs := by
  refine (disj_iff t s hne).mp ?_
  rw [Finset.disjoint_left]
  intro v hvt hvs
  exact antipar_disjoint F hne hN v hvt hvs

/-- Off Z0, the zero facet of a tie view at `t` is a disjoint partner of `t` (AG, BC, DF or DH). -/
theorem zero_facet_pair (F : S0xFac 8 V2.fIdx x) {t s : Fin 8} {D : ℝ³} (hZ : cross (F.N t) D ≠ 0)
    (hne : t ≠ s) (h1 : Lf (F.N t) (F.N s) D = 0) (h2 : Kf (F.N t) (F.N s) D = 0) :
    (t.val, s.val) ∈ disjPairs ∨ (s.val, t.val) ∈ disjPairs := by
  obtain ⟨r, -, hr⟩ := zero_facet_antipar F hZ hne h1 h2
  exact antipar_pairs F hne hr

/-! ### Family 36, geometric core (off Z0) -/

/-- (a): a facet `s != t` with a vertex of `t` is not edge-on at the tie view. -/
theorem t36a_geom (F : S0xFac 8 V2.fIdx x) {t s : Fin 8} {D : ℝ³} (hZ : cross (F.N t) D ≠ 0)
    (hne : t ≠ s) (hv : ∃ v : Fin 7, v ∈ V2.fIdx t ∧ v ∈ V2.fIdx s) :
    ¬ (Lf (F.N t) (F.N s) D = 0 ∧ Kf (F.N t) (F.N s) D = 0) := by
  rintro ⟨h1, h2⟩
  obtain ⟨r, -, hr⟩ := zero_facet_antipar F hZ hne h1 h2
  obtain ⟨v, hvt, hvs⟩ := hv
  exact antipar_disjoint F hne hr v hvt hvs

/-- (b): two distinct facets `s, s2`, both `!= t`, are not both edge-on at the tie view. -/
theorem t36b_geom (F : S0xFac 8 V2.fIdx x) {t s s2 : Fin 8} {D : ℝ³} (hZ : cross (F.N t) D ≠ 0)
    (h1 : t ≠ s) (h2 : t ≠ s2) (h3 : s ≠ s2) :
    ¬ ((Lf (F.N t) (F.N s) D = 0 ∧ Kf (F.N t) (F.N s) D = 0) ∧
       (Lf (F.N t) (F.N s2) D = 0 ∧ Kf (F.N t) (F.N s2) D = 0)) := by
  rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩
  obtain ⟨r, hr⟩ := tie_par hZ a1 a2
  obtain ⟨r2, hr2⟩ := tie_par hZ b1 b2
  exact at_most_one_antipar F h1 h2 h3 hr hr2

/-! ### Family 36 against lex signs -/

/-- The two literals `(p, q)` of a two-level lex sign say exactly "`(a, b)` lex positive", "lex negative". -/
def Lex2Sg (bp bq : Bool) (a b : ℝ) : Prop :=
  (bp = true ↔ h21b_LP a b) ∧ (bq = true ↔ h21b_LP (-a) (-b))

/-- A lex sign of a pair that is not `(0, 0)` has one of its two literals true. -/
theorem lex2_nz {bp bq : Bool} {a b : ℝ} (h : Lex2Sg bp bq a b) (hnz : ¬ (a = 0 ∧ b = 0)) :
    bp = true ∨ bq = true := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · exact Or.inr (h.2.2 (Or.inl (by linarith)))
  · have hb : b ≠ 0 := fun hb => hnz ⟨ha, hb⟩
    rcases lt_or_gt_of_ne hb with hb | hb
    · exact Or.inr (h.2.2 (Or.inr ⟨by rw [ha, neg_zero], by linarith⟩))
    · exact Or.inl (h.1.2 (Or.inr ⟨ha, hb⟩))
  · exact Or.inl (h.1.2 (Or.inl ha))

/-- The KA real of `(t, f, s)` (DESIGN 3, TIE-REVIEW 1.4): `1` under Z0 (`n x D = 0`), `K` off Z0. -/
def KAsem (n a D : ℝ³) (k : ℝ) : Prop := (cross n D = 0 → k = 1) ∧ (cross n D ≠ 0 → k = Kf n a D)

/-- The pair of levels of `Fp(s)` is `(0, 0)` only off Z0 with both levels of the facing zero. -/
theorem fp_zero {n a D : ℝ³} {σ k : ℝ} (hσ : σ = 1 ∨ σ = -1) (hk : KAsem n a D k)
    (h : -Lf n a D = 0 ∧ σ * k = 0) : cross n D ≠ 0 ∧ Lf n a D = 0 ∧ Kf n a D = 0 := by
  have hσ0 : σ ≠ 0 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hk0 : k = 0 := (mul_eq_zero.mp h.2).resolve_left hσ0
  by_cases hZ : cross n D = 0
  · have := hk.1 hZ; rw [hk0] at this; norm_num at this
  · exact ⟨hZ, by linarith [h.1], by rw [← hk.2 hZ, hk0]⟩

/-- **Schema 36 (a), real form.**  `s != t` with a vertex of `t`: one literal of `Fp(s)` is true. -/
theorem fam36a_core (F : S0xFac 8 V2.fIdx x) {t s : Fin 8} {D : ℝ³} {σ k : ℝ} {bp bq : Bool}
    (hσ : σ = 1 ∨ σ = -1) (hne : t ≠ s) (hv : ∃ v : Fin 7, v ∈ V2.fIdx t ∧ v ∈ V2.fIdx s)
    (hk : KAsem (F.N t) (F.N s) D k) (hs : Lex2Sg bp bq (-Lf (F.N t) (F.N s) D) (σ * k)) :
    bp = true ∨ bq = true := by
  refine lex2_nz hs fun h => ?_
  obtain ⟨hZ, h1, h2⟩ := fp_zero hσ hk h
  exact t36a_geom F hZ hne hv ⟨h1, h2⟩

/-- **Schema 36 (b), real form.**  Distinct `s, s2`, both `!= t`: one of the four literals is true. -/
theorem fam36b_core (F : S0xFac 8 V2.fIdx x) {t s s2 : Fin 8} {D : ℝ³} {σ k k2 : ℝ}
    {bp bq bp2 bq2 : Bool} (hσ : σ = 1 ∨ σ = -1) (h1 : t ≠ s) (h2 : t ≠ s2) (h3 : s ≠ s2)
    (hk : KAsem (F.N t) (F.N s) D k) (hk2 : KAsem (F.N t) (F.N s2) D k2)
    (hs : Lex2Sg bp bq (-Lf (F.N t) (F.N s) D) (σ * k))
    (hs2 : Lex2Sg bp2 bq2 (-Lf (F.N t) (F.N s2) D) (σ * k2)) :
    bp = true ∨ bq = true ∨ bp2 = true ∨ bq2 = true := by
  by_cases ha : -Lf (F.N t) (F.N s) D = 0 ∧ σ * k = 0
  · by_cases hb : -Lf (F.N t) (F.N s2) D = 0 ∧ σ * k2 = 0
    · obtain ⟨hZ, a1, a2⟩ := fp_zero hσ hk ha
      obtain ⟨-, b1, b2⟩ := fp_zero hσ hk2 hb
      exact absurd ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ (t36b_geom F hZ h1 h2 h3)
    · rcases lex2_nz hs2 hb with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  · rcases lex2_nz hs ha with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

/-! ### Family 36 rows: tag check and soundness on the real data `geoF F` -/

/-- Facets `t` and `s` (encoder indices) share a vertex. -/
def shareV (t s : Nat) : Bool := (List.range 7).any fun i => inF t i && inF s i

/-- The parameter check of a family 36 row `36 t f sd kind s s2` (FORMAT.md).  Kind 0: `s != t` shares a vertex
with `t`.  Kind 1: `t, s, s2` distinct (the encoder emits only facets disjoint from `t`; not needed). -/
def p36OK (t kind s s2 : Nat) : Bool :=
  decide (t < 8 ∧ s < 8 ∧ s ≠ t) &&
  ((kind == 0 && shareV t s) || (kind == 1 && decide (s2 < 8 ∧ s2 ≠ t ∧ s2 ≠ s)))

/-- The clause of a family 36 row from the two literal values `fp r = (Fp(r).p, Fp(r).q)`. -/
def cl36 (kind s s2 : Nat) (fp : Nat → Bool × Bool) : Bool :=
  (fp s).1 || (fp s).2 || (kind == 1 && ((fp s2).1 || (fp s2).2))

theorem shareV_sound {t s : Nat} (ht : t < 8) (hs : s < 8) (h : shareV t s = true) :
    ∃ v : Fin 7, v ∈ V2.fIdx ⟨t, ht⟩ ∧ v ∈ V2.fIdx ⟨s, hs⟩ := by
  simp only [shareV, List.any_eq_true, List.mem_range, Bool.and_eq_true] at h
  obtain ⟨i, hi, h1, h2⟩ := h
  exact ⟨⟨i, hi⟩, (mem_S16 ⟨t, ht⟩ ⟨i, hi⟩).mpr h1, (mem_S16 ⟨s, hs⟩ ⟨i, hi⟩).mpr h2⟩

/-- **Soundness of family 36 (a and b)** on the real data `g = geoF F`, at the tie leaf `(t, f, sd)` with the side
`σ = ±1`.  Hypothesis `hfp`: for every facet `r != t`, the two literal values `fp r` are the lex sign of
`(-L(r, f), σ k)` with the KA real `k` of DESIGN 3 (this is what `rhoW` and T4's lexS_sound must give). -/
theorem fam36_sound (F : S0xFac 8 V2.fIdx x) {t f kind s s2 : Nat} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hok : p36OK t kind s s2 = true) (fp : Nat → Bool × Bool)
    (hfp : ∀ r, r < 8 → r ≠ t → ∃ k : ℝ, KAsem ((geoF F).N t) ((geoF F).N r) ((geoF F).dv f) k ∧
      Lex2Sg (fp r).1 (fp r).2 (-Lf ((geoF F).N t) ((geoF F).N r) ((geoF F).dv f)) (σ * k)) :
    cl36 kind s s2 fp = true := by
  simp only [p36OK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨⟨ht, hs, hst⟩, hk⟩ := hok
  have eN : ∀ r (hr : r < 8), (geoF F).N r = F.N ⟨r, hr⟩ := fun r hr => geoF_N F ⟨r, hr⟩
  have fne : ∀ {a b : Nat} (ha : a < 8) (hb : b < 8), a ≠ b → (⟨a, ha⟩ : Fin 8) ≠ ⟨b, hb⟩ :=
    fun ha hb h e => h (congrArg Fin.val e)
  obtain ⟨k, hkS, hlS⟩ := hfp s hs hst
  rw [eN t ht, eN s hs] at hkS hlS
  simp only [cl36, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  rcases hk with ⟨-, hsh⟩ | ⟨hk1, hs2, hs2t, hs2s⟩
  · rcases fam36a_core F hσ (fne ht hs (Ne.symm hst)) (shareV_sound ht hs hsh) hkS hlS with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
  · obtain ⟨k2, hkS2, hlS2⟩ := hfp s2 hs2 hs2t
    rw [eN t ht, eN s2 hs2] at hkS2 hlS2
    rcases fam36b_core F hσ (fne ht hs (Ne.symm hst)) (fne ht hs2 (Ne.symm hs2t))
        (fne hs hs2 (Ne.symm hs2s)) hkS hkS2 hlS hlS2 with h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨hk1, Or.inl h⟩
    · exact Or.inr ⟨hk1, Or.inr h⟩

/-! ### For T6: the tie view at the real data -/

/-- Off Z0 the first level of the tie view is not zero (`u = w_f != 0`), and the facing levels of a facet are
`<N_s, w> = -L` and `<N_s, d_+> = K`: restated for `s0x_lex2_rupert`'s `hfac`. -/
theorem tie_levels (n a D : ℝ³) : ⟪a, cross n D⟫ = - Lf n a D ∧ ⟪a, dpl n D⟫ = Kf n a D :=
  ⟨inner_cross_eq_Lf n a D, inner_dpl_eq_Kf n a D⟩

/-- `t` itself is edge-on at every point of the tie view. -/
theorem tie_t_levels (n D : ℝ³) : Lf n n D = 0 ∧ Kf n n D = 0 := by
  refine ⟨?_, ?_⟩
  · have := inner_cross_eq_Lf n n D; rw [inner_n_cross] at this; linarith
  · rw [← inner_dpl_eq_Kf, inner_n_dpl]

end Minimality.H16T.SAT

end

#print axioms Minimality.H16T.SAT.fam36_sound
#print axioms Minimality.H16T.SAT.zero_facet_antipar
#print axioms Minimality.H16T.SAT.at_most_one_antipar
#print axioms Minimality.H16T.SAT.antipar_disjoint
#print axioms Minimality.H16T.SAT.antipar_pairs
#print axioms Minimality.H16T.SAT.zero_facet_pair
