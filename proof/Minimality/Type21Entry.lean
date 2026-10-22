module

public import Minimality.Type21Cap
public import Minimality.Type21R
public import Minimality.Type08

@[expose] public section

/-!
# Type 21 from its facets (`FEWER-FACES-PROOFS.md` §9.0, §16)

Seven points `x 0, …, x 6` whose facets are `014, 015, 0256, 046, 134, 135, 2346, 235`
(given by affine functions vanishing exactly there): `exists_type21_cap` builds the octahedron
`O = K − 2` (labels `a, a', b, b', c, c' = x 0, x 3, x 4, x 5, x 1, x 6`) with its eighth face
`356` (the pencil of `135` and `235` through `6`; `0` and `4` are beneath it by the convexity of
the quadrilaterals `0256` and `2346`), and the cap `x 2` (`IsCap21`).
`T1View`: the special positions of `T1` along a line of two faces.  The theorem from the facets
is `cert_type21_facets` (`Type21Facets.lean`).

**Certificate form** (§18.2, §18.6 step 2): every theorem of the tier cover concludes a rim
certificate at a named view (`CertV`: a segment view or a view satisfying `L`, the named vertex
crossings) instead of Rupertness; no horizontal double normal is assumed.  The old statement
`isRupert_type21_facets` and the limit theorem are in `Type21Limit.lean`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

variable {L : ℝ³ → Prop}

theorem image_seven21 (x : Fin 7 → ℝ³) :
    (({0, 3, 4, 5, 1, 6} : Finset (Fin 7)).image x) = {x 0, x 3, x 4, x 5, x 1, x 6} ∧
    univ.image x = insert (x 2) ({x 0, x 3, x 4, x 5, x 1, x 6} : Finset ℝ³) := by
  constructor
  · simp [Finset.image_insert]
  · ext z
    simp only [mem_image, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      exacts [⟨2, rfl⟩, ⟨0, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩, ⟨1, rfl⟩, ⟨6, rfl⟩]

set_option maxHeartbeats 400000 in
/-- **The facet data of type 21 make `x 2` a type-21 cap** (`IsCap21`) over the octahedron
`O = K − 2` with opposite pairs `(0, 3)`, `(4, 5)`, `(1, 6)`; its face `356` is constructed. -/
theorem exists_type21_cap (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (fA fB fC fD fE fF fG fH : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 4} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 4} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({0, 1, 5} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({0, 1, 5} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({0, 2, 5, 6} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({0, 2, 5, 6} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({1, 3, 4} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({1, 3, 4} : Finset (Fin 7)) → fE (x i) < 0))
    (hF : ∀ i, (i ∈ ({1, 3, 5} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({1, 3, 5} : Finset (Fin 7)) → fF (x i) < 0))
    (hG : ∀ i, (i ∈ ({2, 3, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({2, 3, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hH : ∀ i, (i ∈ ({2, 3, 5} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({2, 3, 5} : Finset (Fin 7)) → fH (x i) < 0)) :
    ∃ F : OctFacets (x 0) (x 3) (x 4) (x 5) (x 1) (x 6), IsCap21 F (x 2) ∧
      F.abc.f = fA ∧ F.abc'.f = fD ∧ F.ab'c.f = fB ∧ F.ab'c'.f = fC ∧ F.a'bc.f = fE ∧
      F.a'bc'.f = fG ∧ F.a'b'c.f = fF := by
  classical
  obtain ⟨eI, -⟩ := image_seven21 x
  obtain ⟨NB, hNB⟩ := exists_normal_of_affine fB
  obtain ⟨NC, hNC⟩ := exists_normal_of_affine fC
  obtain ⟨ND, hND⟩ := exists_normal_of_affine fD
  obtain ⟨NE, hNE⟩ := exists_normal_of_affine fE
  obtain ⟨NF, hNF⟩ := exists_normal_of_affine fF
  obtain ⟨NG, hNG⟩ := exists_normal_of_affine fG
  obtain ⟨NH, hNH⟩ := exists_normal_of_affine fH
  have hN : ∀ {f : ℝ³ →ᵃ[ℝ] ℝ} {N : ℝ³}, (∀ y z, f y - f z = ⟪N, y - z⟫) →
      ∀ y z, (f : ℝ³ → ℝ) y - f z = ⟪N, y - z⟫ := fun h => h
  have B0 := (hB 0).1 (by decide); have B5 := (hB 5).1 (by decide)
  have B2 := (hB 2).2 (by decide); have B6 := (hB 6).2 (by decide)
  have C0 := (hC 0).1 (by decide); have C2 := (hC 2).1 (by decide)
  have C5 := (hC 5).1 (by decide); have C6 := (hC 6).1 (by decide)
  have C1 := (hC 1).2 (by decide)
  have D0 := (hD 0).1 (by decide); have D4 := (hD 4).1 (by decide)
  have D6 := (hD 6).1 (by decide); have D2 := (hD 2).2 (by decide)
  have D3 := (hD 3).2 (by decide); have D5 := (hD 5).2 (by decide)
  have E3 := (hE 3).1 (by decide); have E4 := (hE 4).1 (by decide)
  have E2 := (hE 2).2 (by decide); have E6 := (hE 6).2 (by decide)
  have F1 := (hF 1).1 (by decide); have F3 := (hF 3).1 (by decide)
  have F5 := (hF 5).1 (by decide); have F2 := (hF 2).2 (by decide)
  have F6 := (hF 6).2 (by decide)
  have G2 := (hG 2).1 (by decide); have G3 := (hG 3).1 (by decide)
  have G4 := (hG 4).1 (by decide); have G6 := (hG 6).1 (by decide)
  have G1 := (hG 1).2 (by decide)
  have H2 := (hH 2).1 (by decide); have H3 := (hH 3).1 (by decide)
  have H5 := (hH 5).1 (by decide); have H0 := (hH 0).2 (by decide)
  have H1 := (hH 1).2 (by decide); have H4 := (hH 4).2 (by decide)
  have H6 := (hH 6).2 (by decide)
  -- the face `356`: the pencil of `135` and `235` through `6`
  set h : ℝ³ → ℝ := fun X => fH (x 6) * fF X - fF (x 6) * fH X with hh_def
  have hhN : ∀ y z, h y - h z = ⟪fH (x 6) • NF - fF (x 6) • NH, y - z⟫ :=
    pencil_hN (hN hNF) (hN hNH) _ _
  have h3 : h (x 3) = 0 := by simp only [h, F3, H3]; ring
  have h5 : h (x 5) = 0 := by simp only [h, F5, H5]; ring
  have h6 : h (x 6) = 0 := by simp only [h]; ring
  have h1 : h (x 1) < 0 := by
    simp only [h, F1]; have := mul_pos_of_neg_of_neg F6 H1; linarith
  have h2 : 0 < h (x 2) := by
    simp only [h, H2]; have := mul_pos_of_neg_of_neg H6 F2; linarith
  -- the quadrilateral `0256`: `2 = 0 + α (5 − 0) + β (6 − 0)`, `α + β > 1`
  have q1 := coords_of_affine3 (hN hNC) (hN hND) (hN hNB) (o := x 0) (p := x 5) (q := x 6)
    (w := x 2) (Z := x 1) C0 C5 C6 C2 C1.ne D0 D6 D5.ne B0 B5 B6.ne
  set α := fD (x 2) / fD (x 5)
  set β := fB (x 2) / fB (x 6)
  have hβ : 0 < β := div_pos_of_neg_of_neg B2 B6
  have k1 : 1 - α - β < 0 := by
    have hf := affine_frame (hN hNH) (x 0) (x 5) (x 6) α β
    rw [← q1, H2, H5] at hf
    have := mul_neg_of_pos_of_neg hβ H6
    by_contra hc; push Not at hc
    have := mul_nonpos_of_nonneg_of_nonpos hc H0.le
    linarith
  have g0 : h (x 2) = (1 - α - β) * h (x 0) := by
    have hf := affine_frame hhN (x 0) (x 5) (x 6) α β
    rw [← q1, h5, h6] at hf; linarith
  have h0 : h (x 0) < 0 := by
    by_contra hc; push Not at hc
    have := mul_nonpos_of_nonpos_of_nonneg k1.le hc; linarith
  -- the quadrilateral `2346`: `2 = 4 + α' (3 − 4) + β' (6 − 4)`, `α' + β' > 1`
  have q2 := coords_of_affine3 (hN hNG) (hN hND) (hN hNE) (o := x 4) (p := x 3) (q := x 6)
    (w := x 2) (Z := x 1) G4 G3 G6 G2 G1.ne D4 D6 D3.ne E4 E3 E6.ne
  set α' := fD (x 2) / fD (x 3)
  set β' := fE (x 2) / fE (x 6)
  have hβ' : 0 < β' := div_pos_of_neg_of_neg E2 E6
  have k2 : 1 - α' - β' < 0 := by
    have hf := affine_frame (hN hNH) (x 4) (x 3) (x 6) α' β'
    rw [← q2, H2, H3] at hf
    have := mul_neg_of_pos_of_neg hβ' H6
    by_contra hc; push Not at hc
    have := mul_nonpos_of_nonneg_of_nonpos hc H4.le
    linarith
  have g4 : h (x 2) = (1 - α' - β') * h (x 4) := by
    have hf := affine_frame hhN (x 4) (x 3) (x 6) α' β'
    rw [← q2, h3, h6] at hf; linarith
  have h4 : h (x 4) < 0 := by
    by_contra hc; push Not at hc
    have := mul_nonpos_of_nonpos_of_nonneg k2.le hc; linarith
  let Fh : FacetFn {x 0, x 3, x 4, x 5, x 1, x 6} (x 3) (x 5) (x 6) :=
    ⟨h, _, hhN, h3, h5, h6, fun w hw e1 e2 e3 => by
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
      · exact h0
      · exact absurd rfl e1
      · exact h4
      · exact absurd rfl e2
      · exact h1
      · exact absurd rfl e3⟩
  have hnodup : [x 0, x 3, x 4, x 5, x 1, x 6].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    refine ⟨⟨hx.ne (by decide), hx.ne (by decide), hx.ne (by decide), hx.ne (by decide),
      hx.ne (by decide)⟩, ⟨hx.ne (by decide), hx.ne (by decide), hx.ne (by decide),
      hx.ne (by decide)⟩, ⟨hx.ne (by decide), hx.ne (by decide), hx.ne (by decide)⟩,
      ⟨hx.ne (by decide), hx.ne (by decide)⟩, hx.ne (by decide), not_false⟩
  let F : OctFacets (x 0) (x 3) (x 4) (x 5) (x 1) (x 6) :=
    ⟨hnodup,
      (facetFn_of_index x fA _ hA {0, 3, 4, 5, 1, 6} (i := 0) (j := 4) (k := 1)
        (by decide) (by decide) (by decide) (by decide)).congr eI,
      (facetFn_of_index x fD _ hD {0, 3, 4, 5, 1, 6} (i := 0) (j := 4) (k := 6)
        (by decide) (by decide) (by decide) (by decide)).congr eI,
      (facetFn_of_index x fB _ hB {0, 3, 4, 5, 1, 6} (i := 0) (j := 5) (k := 1)
        (by decide) (by decide) (by decide) (by decide)).congr eI,
      (facetFn_of_index x fC _ hC {0, 3, 4, 5, 1, 6} (i := 0) (j := 5) (k := 6)
        (by decide) (by decide) (by decide) (by decide)).congr eI,
      (facetFn_of_index x fE _ hE {0, 3, 4, 5, 1, 6} (i := 3) (j := 4) (k := 1)
        (by decide) (by decide) (by decide) (by decide)).congr eI,
      (facetFn_of_index x fG _ hG {0, 3, 4, 5, 1, 6} (i := 3) (j := 4) (k := 6)
        (by decide) (by decide) (by decide) (by decide)).congr eI,
      (facetFn_of_index x fF _ hF {0, 3, 4, 5, 1, 6} (i := 3) (j := 5) (k := 1)
        (by decide) (by decide) (by decide) (by decide)).congr eI,
      Fh⟩
  refine ⟨F, ⟨C2, G2, h2, (hA 2).2 (by decide), D2, B2, E2, F2⟩, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl⟩

/-- The linear part of an affine function, read off a facet function with the same values. -/
theorem affine_linear_eq (f : ℝ³ →ᵃ[ℝ] ℝ) {g : ℝ³ → ℝ} {N : ℝ³} (hg : g = f)
    (hN : ∀ y z, g y - g z = ⟪N, y - z⟫) (u : ℝ³) : f.linear u = ⟪N, u⟫ := by
  have e := f.map_vadd 0 u
  rw [vadd_eq_add, vadd_eq_add, add_zero] at e
  have k := hN u 0
  rw [hg, sub_zero, e] at k
  linarith

/-- **The special positions of `T1` along a vertex crossing** given by two faces `fP`, `fQ`
through the apex: at every direction `u ≠ 0` of their line, `T1Gen` (the antipode off the far
side, only the ties of `QuadTie` among the depths of the rim corners, no horizontal double
normal). -/
def T1View (V : Finset ℝ³) (fP fQ : ℝ³ →ᵃ[ℝ] ℝ) (a a' b b' : ℝ³) : Prop :=
  ∀ u : ℝ³, u ≠ 0 → fP.linear u = 0 → fQ.linear u = 0 →
    det3 (b - b') (a' - b') u ≠ 0 ∧ QuadTie ⟪a, u⟫ ⟪b', u⟫ ⟪a', u⟫ ⟪b, u⟫ ∧ NoHDNAt V u

/-- **`T1View` with any condition `L` on the views** in place of "no horizontal double normal"
(for the certificate form: `L` names the view). -/
def T1ViewL (K : Finset ℝ³) (L : ℝ³ → Prop) (fP fQ : ℝ³ →ᵃ[ℝ] ℝ) (a a' b b' : ℝ³) : Prop :=
  ∀ u : ℝ³, u ≠ 0 → fP.linear u = 0 → fQ.linear u = 0 → T1Gen K L a a' b b' u

theorem T1View.toL {V : Finset ℝ³} {fP fQ : ℝ³ →ᵃ[ℝ] ℝ} {a a' b b' : ℝ³}
    (h : T1View V fP fQ a a' b b') : T1ViewL V (NoHDNAt V) fP fQ a a' b b' :=
  fun u hu h1 h2 => ⟨(h u hu h1 h2).1, Or.inl (h u hu h1 h2).2.1, fun _ => (h u hu h1 h2).2.2⟩

end Minimality

end
