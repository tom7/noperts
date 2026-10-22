module

public import Minimality.Type21QEdge

@[expose] public section

/-!
# Type 21: no horizontal-double-normal exception at `05`, `34` and the ridge `26` (§22)

The certificates of the tier cover at the views along `05` and its image `34` (under `σ1`) are
edge pairs of tier Q (Lemma 3 of §9 at `0 → 5`, `5 → 0` in `K − 2` and in `K − 6`), with Lemma E:
in case (a) from the dependency of the E-good edge (16.1 (ii)), in case (b) from the dependency
of `O` with `6` replaced by the cap (`lemmaE_far21`, Proposition 14.2 by a direct argument).  The
certificates at the ridge `26` are those of tier R (Lemma 16.5): an edge pair with Lemma E, or,
with `1` hidden, the two triangle closings.  The records of the cover carry them (`QEdge5`,
`REdge21`, `CertW21`).

At the ridge a triangle closing is realized on one face circle (quadrants `(5, 4)`, `(0, 3)`) or
on both (`(0, 4)`, `(5, 3)`).  Lemma 22.3 for a three-corner rim (`triSlide_or`): the slide on a
realizing circle fails only with a double normal of the rim perpendicular to that face, which is
a horizontal double normal of the shape (`hdnDir_of_rim`).  `K_6` and `K_2` (or one of them on
both circles) give two such slides on the two circles, and the two double normals would have two
directions, against `OneHDNDir` (`isRupert_ridgeTri`); Lemma 22.4 is not needed.

* `isRupert_qPair21`: an edge pair at a triangle–quadrilateral edge at the limit (§22.3–22.8,
  `isRupert_ePair_limit_facts`).
* `Q5Gen21`, `isRupert_q5Edge21`: the edges `05`, `34`.
* `triSlide_or`, `isRupert_ridgeTri`: triangle closings at a ridge view.
* `R26Gen21`, `isRupert_ridge21`: the ridge `26`.
* `isRupert_type21_limit_facets_codim2`: type 21 with every edge closed.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### An edge pair at a triangle–quadrilateral edge -/

set_option maxHeartbeats 1000000 in
/-- **An edge pair at the edge `P C'` at the limit** (§22, generic in the labels).  The edge `P C'`
of type 21 lies on the triangle `S_T = {P, C', R}` and on the facet `S_Q ∋ P, C', Y` with at most
one more vertex; the closings at `P C'` have the far corners `R, Z, Y` (`Z` off both facets).  If
shapes `K_n → x` frequently carry such an edge pair with Lemma E (`QAData`, in either direction
and orientation), then under §22.4's conditions at the view (`EdgeGen`) and with `P`, `C'` off
the plane `R Y Z`, `x` is Rupert (`isRupert_ePair_limit_facts`). -/
theorem isRupert_qPair21 {x : Fin 7 → ℝ³} (T : Facets21 x) {P C' R Y Z : Fin 7}
    {ST SQ : Finset (Fin 7)} (FT : Face16 x ST) (FQ : Face16 x SQ) (hPC' : P ≠ C')
    (hT : P ∈ ST ∧ C' ∈ ST ∧ R ∈ ST ∧ Y ∉ ST ∧ Z ∉ ST ∧ ∀ i ∈ ST, i = P ∨ i = C' ∨ i = R)
    (hQ : P ∈ SQ ∧ C' ∈ SQ ∧ Y ∈ SQ ∧ R ∉ SQ ∧ Z ∉ SQ ∧ ∀ i ∈ SQ, ∀ j ∈ SQ,
      i ≠ P → i ≠ C' → i ≠ Y → j ≠ P → j ≠ C' → j ≠ Y → i = j)
    (K : ℕ → Fin 7 → ℝ³) (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)))
    (hfreq : ∃ᶠ n in atTop,
      (QAData (univ.image (K n)) (K n P) (K n C') (K n R) (K n Y) (K n Z) ∨
        QAData (univ.image (K n)) (K n P) (K n C') (K n Y) (K n R) (K n Z)) ∨
      (QAData (univ.image (K n)) (K n C') (K n P) (K n R) (K n Y) (K n Z) ∨
        QAData (univ.image (K n)) (K n C') (K n P) (K n Y) (K n R) (K n Z)))
    (hgen : EdgeGen (univ.image x) (x C' - x P) (x P) (x C') (ST.image x) (SQ.image x) FT.N FQ.N)
    (c1 : det3 (x Y - x R) (x Z - x R) (x P - x R) ≠ 0)
    (c2 : det3 (x Y - x R) (x Z - x R) (x C' - x R) ≠ 0) : IsRupert (univ.image x) := by
  classical
  obtain ⟨tP, tC', tR, tY, tZ, tall⟩ := hT
  obtain ⟨qP, qC', qY, qR, qZ, qall⟩ := hQ
  have hgen' : EdgeGen (univ.image x) (x P - x C') (x C') (x P) (ST.image x) (SQ.image x)
      FT.N FQ.N := by
    have := hgen.rev; rwa [neg_sub] at this
  have fT := FT.hf (i₀ := P) tP
  have fQ := FQ.hf (i₀ := P) qP
  have fT' := FT.hf (i₀ := C') tC'
  have fQ' := FQ.hf (i₀ := C') qC'
  have sT : ∀ v w : Fin 7, ((v = P ∧ w = C') ∨ (v = C' ∧ w = P)) → ∀ i ∈ ST, ∀ j ∈ ST,
      i ≠ v → i ≠ w → i ≠ R → j ≠ v → j ≠ w → j ≠ R → i = j := by
    rintro v w hvw i hi j - h1 h2 h3 - - -
    rcases tall i hi with rfl | rfl | rfl
    · rcases hvw with ⟨rfl, -⟩ | ⟨-, rfl⟩ <;> contradiction
    · rcases hvw with ⟨-, rfl⟩ | ⟨rfl, -⟩ <;> contradiction
    · contradiction
  have sQ : ∀ v w : Fin 7, ((v = P ∧ w = C') ∨ (v = C' ∧ w = P)) → ∀ i ∈ SQ, ∀ j ∈ SQ,
      i ≠ v → i ≠ w → i ≠ Y → j ≠ v → j ≠ w → j ≠ Y → i = j := by
    rintro v w (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) i hi j hj h1 h2 h3 h4 h5 h6
    · exact qall i hi j hj h1 h2 h3 h4 h5 h6
    · exact qall i hi j hj h2 h1 h3 h5 h4 h6
  have e1 : ∀ X, det3 (x R - x Y) (x Z - x Y) (X - x Y) =
      -det3 (x Y - x R) (x Z - x R) (X - x R) := fun X => det3_lemmaE_swapAB _ _ _ _
  rcases frequently_or_distrib.mp hfreq with h | h
  · rcases frequently_or_distrib.mp h with h | h
    · exact isRupert_ePair_limit_facts x T.inj T.noSeg (v := P) (w := C') (a := R) (b := Y)
        (c := Z) hPC' fT fQ ⟨tP, tC', tR, tY, tZ, sT P C' (Or.inl ⟨rfl, rfl⟩)⟩
        ⟨qP, qC', qY, qR, qZ, sQ P C' (Or.inl ⟨rfl, rfl⟩)⟩ K hK (h.mono fun n hn => hn.facts)
        hgen ⟨c1, c2⟩
    · exact isRupert_ePair_limit_facts x T.inj T.noSeg (v := P) (w := C') (a := Y) (b := R)
        (c := Z) hPC' fQ fT ⟨qP, qC', qY, qR, qZ, sQ P C' (Or.inl ⟨rfl, rfl⟩)⟩
        ⟨tP, tC', tR, tY, tZ, sT P C' (Or.inl ⟨rfl, rfl⟩)⟩ K hK (h.mono fun n hn => hn.facts)
        hgen.swapF ⟨by rw [e1]; exact neg_ne_zero.mpr c1, by rw [e1]; exact neg_ne_zero.mpr c2⟩
  · rcases frequently_or_distrib.mp h with h | h
    · exact isRupert_ePair_limit_facts x T.inj T.noSeg (v := C') (w := P) (a := R) (b := Y)
        (c := Z) (Ne.symm hPC') fT' fQ' ⟨tC', tP, tR, tY, tZ, sT C' P (Or.inr ⟨rfl, rfl⟩)⟩
        ⟨qC', qP, qY, qR, qZ, sQ C' P (Or.inr ⟨rfl, rfl⟩)⟩ K hK (h.mono fun n hn => hn.facts)
        hgen' ⟨c2, c1⟩
    · exact isRupert_ePair_limit_facts x T.inj T.noSeg (v := C') (w := P) (a := Y) (b := R)
        (c := Z) (Ne.symm hPC') fQ' fT' ⟨qC', qP, qY, qR, qZ, sQ C' P (Or.inr ⟨rfl, rfl⟩)⟩
        ⟨tC', tP, tR, tY, tZ, sT C' P (Or.inr ⟨rfl, rfl⟩)⟩ K hK (h.mono fun n hn => hn.facts)
        hgen'.swapF ⟨by rw [e1]; exact neg_ne_zero.mpr c2, by rw [e1]; exact neg_ne_zero.mpr c1⟩

/-! ### The edges `05` and `34` -/

/-- **The codimension-2 conditions at `05`** (labels `P, P', R, R', D, C' = 0, 3, 1, 6, 2, 5`
with `4` the antipode of `5`; at `34` their image under `σ1`): `EdgeGen` at the view `C' − P`
(§22.4) between the triangle `S_T = P C' R` and the quadrilateral `S_Q = P C' D R'`, and `P`,
`C'` off the planes `R R' Q'` and `R D P'` of Lemma E (`Q'` the antipode of `C'`). -/
def Q5Gen21 (x : Fin 7 → ℝ³) (NT NQ : ℝ³) (P P' R R' D C' Q' : Fin 7) (ST SQ : Finset (Fin 7)) :
    Prop :=
  EdgeGen (univ.image x) (x C' - x P) (x P) (x C') (ST.image x) (SQ.image x) NT NQ ∧
  det3 (x R' - x R) (x Q' - x R) (x P - x R) ≠ 0 ∧ det3 (x R' - x R) (x Q' - x R) (x C' - x R) ≠ 0 ∧
  det3 (x D - x R) (x P' - x R) (x P - x R) ≠ 0 ∧ det3 (x D - x R) (x P' - x R) (x C' - x R) ≠ 0

/-- `Q5Gen21` for every normal of the two facets. -/
def Q5GenAff21 (x : Fin 7 → ℝ³) (fT fQ : ℝ³ →ᵃ[ℝ] ℝ) (P P' R R' D C' Q' : Fin 7)
    (ST SQ : Finset (Fin 7)) : Prop :=
  ∀ NT NQ : ℝ³, (∀ y, fT.linear y = ⟪NT, y⟫) → (∀ y, fQ.linear y = ⟪NQ, y⟫) →
    Q5Gen21 x NT NQ P P' R R' D C' Q' ST SQ

/-- **The edge `05` (or `34`) at the limit.**  If shapes `K_n → x` frequently carry the edge
pairs of `05` with their data (`Q5E21`), then under `Q5Gen21` the limit is Rupert. -/
theorem isRupert_q5Edge21 {x : Fin 7 → ℝ³} (T : Facets21 x) {P P' R R' D C' Q' : Fin 7}
    {ST SQ : Finset (Fin 7)} (FT : Face16 x ST) (FQ : Face16 x SQ) (hPC' : P ≠ C')
    (hT : P ∈ ST ∧ C' ∈ ST ∧ R ∈ ST ∧ R' ∉ ST ∧ D ∉ ST ∧ Q' ∉ ST ∧ P' ∉ ST ∧
      ∀ i ∈ ST, i = P ∨ i = C' ∨ i = R)
    (hQ : P ∈ SQ ∧ C' ∈ SQ ∧ R' ∈ SQ ∧ D ∈ SQ ∧ R ∉ SQ ∧ Q' ∉ SQ ∧ P' ∉ SQ ∧
      ∀ i ∈ SQ, i = P ∨ i = C' ∨ i = R' ∨ i = D)
    (K : ℕ → Fin 7 → ℝ³) (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)))
    (hfreq : ∃ᶠ n in atTop,
      QEdge5 (univ.image (K n)) (K n P) (K n P') (K n Q') (K n C') (K n R) (K n R') (K n D)
        (K n P) (K n C') ∨
      QEdge5 (univ.image (K n)) (K n P) (K n P') (K n Q') (K n C') (K n R) (K n R') (K n D)
        (K n C') (K n P))
    (hg : Q5Gen21 x FT.N FQ.N P P' R R' D C' Q' ST SQ) : IsRupert (univ.image x) := by
  obtain ⟨tP, tC', tR, tR', tD, tQ', tP', tall⟩ := hT
  obtain ⟨qP, qC', qR', qD, qR, qQ', qP', qall⟩ := hQ
  obtain ⟨hgen, c1, c2, c3, c4⟩ := hg
  have sQ : ∀ Y Y' : Fin 7, ((Y = R' ∧ Y' = D) ∨ (Y = D ∧ Y' = R')) → ∀ i ∈ SQ, ∀ j ∈ SQ,
      i ≠ P → i ≠ C' → i ≠ Y → j ≠ P → j ≠ C' → j ≠ Y → i = j := by
    rintro Y Y' hY i hi j hj h1 h2 h3 h4 h5 h6
    have k : ∀ l ∈ SQ, l ≠ P → l ≠ C' → l ≠ Y → l = Y' := by
      intro l hl k1 k2 k3
      rcases qall l hl with rfl | rfl | rfl | rfl
      · exact absurd rfl k1
      · exact absurd rfl k2
      · rcases hY with ⟨rfl, -⟩ | ⟨-, rfl⟩
        · exact absurd rfl k3
        · rfl
      · rcases hY with ⟨-, rfl⟩ | ⟨rfl, -⟩
        · rfl
        · exact absurd rfl k3
    rw [k i hi h1 h2 h3, k j hj h4 h5 h6]
  have hsplit : ∃ᶠ n in atTop,
      ((QAData (univ.image (K n)) (K n P) (K n C') (K n R) (K n R') (K n Q') ∨
        QAData (univ.image (K n)) (K n P) (K n C') (K n R') (K n R) (K n Q')) ∨
      (QAData (univ.image (K n)) (K n C') (K n P) (K n R) (K n R') (K n Q') ∨
        QAData (univ.image (K n)) (K n C') (K n P) (K n R') (K n R) (K n Q'))) ∨
      ((QAData (univ.image (K n)) (K n P) (K n C') (K n R) (K n D) (K n P') ∨
        QAData (univ.image (K n)) (K n P) (K n C') (K n D) (K n R) (K n P')) ∨
      (QAData (univ.image (K n)) (K n C') (K n P) (K n R) (K n D) (K n P') ∨
        QAData (univ.image (K n)) (K n C') (K n P) (K n D) (K n R) (K n P'))) :=
    hfreq.mono fun n hn => by
      rcases hn with (h | h | h | h) | (h | h | h | h)
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inr (Or.inl (Or.inl h))
      · exact Or.inr (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr (Or.inl h))
      · exact Or.inl (Or.inr (Or.inr h))
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  rcases frequently_or_distrib.mp hsplit with h | h
  · exact isRupert_qPair21 T FT FQ hPC' ⟨tP, tC', tR, tR', tQ', tall⟩
      ⟨qP, qC', qR', qR, qQ', sQ R' D (Or.inl ⟨rfl, rfl⟩)⟩ K hK h hgen c1 c2
  · exact isRupert_qPair21 T FT FQ hPC' ⟨tP, tC', tR, tD, tP', tall⟩
      ⟨qP, qC', qD, qR, qP', sQ D R' (Or.inr ⟨rfl, rfl⟩)⟩ K hK h hgen c3 c4

/-- One edge `05` or `34` at the limit: no horizontal double normal there (Theorem 18.1 at the
limit), or the codimension-2 conditions (`isRupert_q5Edge21`). -/
theorem isRupert_q5Edge21_or {x : Fin 7 → ℝ³} (T : Facets21 x) {P P' R R' D C' Q' : Fin 7}
    {ST SQ : Finset (Fin 7)} (FT : Face16 x ST) (FQ : Face16 x SQ) (hPC' : P ≠ C')
    (hT : P ∈ ST ∧ C' ∈ ST ∧ R ∈ ST ∧ R' ∉ ST ∧ D ∉ ST ∧ Q' ∉ ST ∧ P' ∉ ST ∧
      ∀ i ∈ ST, i = P ∨ i = C' ∨ i = R)
    (hQ : P ∈ SQ ∧ C' ∈ SQ ∧ R' ∈ SQ ∧ D ∈ SQ ∧ R ∉ SQ ∧ Q' ∉ SQ ∧ P' ∉ SQ ∧
      ∀ i ∈ SQ, i = P ∨ i = C' ∨ i = R' ∨ i = D)
    (K : ℕ → Fin 7 → ℝ³) (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)))
    (hfreq : ∃ᶠ n in atTop, (QEdge5 (univ.image (K n)) (K n P) (K n P') (K n Q') (K n C') (K n R)
        (K n R') (K n D) (K n P) (K n C') ∨
      QEdge5 (univ.image (K n)) (K n P) (K n P') (K n Q') (K n C') (K n R) (K n R') (K n D)
        (K n C') (K n P)) ∧
      ∀ w a b, TieInst21 x w a b → ⟪K n a - K n b, view21 (K n) w⟫ = 0)
    (hg : NoHDNAt (univ.image x) (x C' - x P) ∨ Q5Gen21 x FT.N FQ.N P P' R R' D C' Q' ST SQ) :
    IsRupert (univ.image x) := by
  rcases hg with hn | hg
  · refine isRupert_of_cert_seq21 T (P := fun v => v = .inl (P, C') ∨ v = .inl (C', P)) ?_ K hK
      (hfreq.mono fun n hn => ⟨?_, hn.2⟩)
    · rintro v (rfl | rfl) -
      · exact hn
      · show NoHDNAt _ (x P - x C')
        rw [← neg_sub]; exact hn.neg
    · rcases hn.1 with h | h
      · exact ⟨_, ⟨.inl (P, C'), Or.inl rfl, 1, one_ne_zero, (one_smul _ _).symm⟩, h.rimCert⟩
      · exact ⟨_, ⟨.inl (C', P), Or.inr rfl, 1, one_ne_zero, (one_smul _ _).symm⟩, h.rimCert⟩
  · exact isRupert_q5Edge21 T FT FQ hPC' hT hQ K hK (hfreq.mono fun n hn => hn.1) hg

/-! ### A triangle closing on one realizing circle (Lemma 22.3 for three corners) -/

/-- Two vectors perpendicular to the same two independent vectors are parallel. -/
theorem cross_eq_zero_of_perp2 {ℓ N A U : ℝ³} (hℓA : ⟪ℓ, A⟫ = 0) (hℓU : ⟪ℓ, U⟫ = 0)
    (hNA : ⟪N, A⟫ = 0) (hNU : ⟪N, U⟫ = 0) (hAU : cross A U ≠ 0) : cross ℓ N = 0 := by
  have h1 : cross (cross A U) ℓ = 0 := by
    rw [cross_cross_eq, real_inner_comm ℓ A, real_inner_comm ℓ U, hℓA, hℓU, zero_smul, zero_smul,
      sub_zero]
  have h2 : cross (cross A U) N = 0 := by
    rw [cross_cross_eq, real_inner_comm N A, real_inner_comm N U, hNA, hNU, zero_smul, zero_smul,
      sub_zero]
  rw [eq_smul_of_cross_eq_zero hAU h1, eq_smul_of_cross_eq_zero hAU h2]
  ext j; fin_cases j <;> simp [cross] <;> ring

set_option maxHeartbeats 4000000 in
/-- **Lemma 22.3 for a triangle closing** (the slide on `F_a`'s circle).  At the view `u` along the
axle `v w` (`w = v + h u`), the closing `(v, a, b)` (counterclockwise, every point weakly left of
its sides), with `a` on the face `S_a ∋ v, w` and `b` on the face `S_b ∋ v, w`, is realized on
`S_a`'s circle when the side `v b` is an edge of `S_b` (`hAdjB`).  With only the axle seen
end-on, (G1) and distinct depths, `V` is Rupert, or the closing has a double normal in space
perpendicular to `S_a`: a horizontal double normal of `V` at `u` parallel to `N_a`. -/
theorem triSlide_or {n : ℕ} (x : Fin n → ℝ³) (hx : Function.Injective x)
    (hseg : ∀ i j m : Fin n, x m ≠ x i → x m ≠ x j → ∀ s : ℝ, 0 < s → s < 1 →
      x m ≠ x i + s • (x j - x i))
    {v w a b : Fin n} (hvw : v ≠ w) {Sa Sb : Finset (Fin n)} {Na Nb : ℝ³} {κa κb : ℝ}
    (hfa : ∀ i, (i ∈ Sa → ⟪Na, x i⟫ = κa) ∧ (i ∉ Sa → ⟪Na, x i⟫ < κa))
    (hfb : ∀ i, (i ∈ Sb → ⟪Nb, x i⟫ = κb) ∧ (i ∉ Sb → ⟪Nb, x i⟫ < κb))
    (hSa : v ∈ Sa ∧ w ∈ Sa ∧ a ∈ Sa ∧ b ∉ Sa) (hSb : v ∈ Sb ∧ w ∈ Sb ∧ b ∈ Sb ∧ a ∉ Sb)
    (hSab : ∀ i ∈ Sa, i ∈ Sb → i = v ∨ i = w)
    (hAdjB : ∀ i ∈ Sb, i ≠ v → i ≠ w → i ≠ b → ∃ NG : ℝ³, ⟪NG, x v - x b⟫ = 0 ∧
      ⟪NG, x w - x b⟫ < 0 ∧ ⟪NG, x i - x b⟫ < 0)
    {u : ℝ³} {h : ℝ} (hh : h ≠ 0) (hw : x w = x v + h • u)
    (hleft : ∀ z ∈ univ.image x, 0 ≤ det3 (x a - x v) (z - x v) u ∧
      0 ≤ det3 (x b - x a) (z - x a) u ∧ 0 ≤ det3 (x v - x b) (z - x b) u)
    (hpar : ParOnly (univ.image x) u (x v) (x w))
    (hg1 : G1At (univ.image x) u (Sa.image x) (Sb.image x))
    (hdist : ∀ y ∈ univ.image x, ∀ y' ∈ univ.image x, y ≠ y' → ⟪y, u⟫ ≠ ⟪y', u⟫) :
    IsRupert (univ.image x) ∨ ∃ ℓ, HDNDir (univ.image x) u ℓ ∧ cross ℓ Na = 0 := by
  classical
  obtain ⟨hvA, hwA, haA, hbA⟩ := hSa
  obtain ⟨hvB, hwB, hbB, haB⟩ := hSb
  set V := univ.image x with hVdef
  have mem : ∀ i, x i ∈ V := fun i => mem_image_of_mem x (mem_univ i)
  have hu : u ≠ 0 := by
    intro h0; rw [h0, smul_zero, add_zero] at hw; exact hvw (hx hw.symm)
  have hav : a ≠ v := fun h => haB (h ▸ hvB)
  have haw : a ≠ w := fun h => haB (h ▸ hwB)
  have hbv : b ≠ v := fun h => hbA (h ▸ hvA)
  have hbw : b ≠ w := fun h => hbA (h ▸ hwA)
  have hab : a ≠ b := fun h => haB (h ▸ hbB)
  have cne : ∀ {i j : Fin n}, i ≠ j → ¬ (i = v ∧ j = w) → ¬ (i = w ∧ j = v) →
      cross (x j - x i) u ≠ 0 := by
    intro i j hij h1 h2 h0
    rcases hpar _ (mem i) _ (mem j) (hx.ne hij) h0 with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact h1 ⟨hx e1, hx e2⟩
    · exact h2 ⟨hx e1, hx e2⟩
  have hcrossA := cne hav.symm (fun h => haw h.2) (fun h => hav h.2)
  have hcrossB := cne hbv (fun h => hbv h.1) (fun h => hbw h.1)
  have hcrossAB := cne hab (fun h => hav h.1) (fun h => haw h.1)
  have imgA : ∀ i, x i ∈ Sa.image x ↔ i ∈ Sa := fun i => by
    constructor
    · intro h; obtain ⟨j, hj, he⟩ := mem_image.mp h; exact hx he ▸ hj
    · intro h; exact mem_image_of_mem x h
  have imgB : ∀ i, x i ∈ Sb.image x ↔ i ∈ Sb := fun i => by
    constructor
    · intro h; obtain ⟨j, hj, he⟩ := mem_image.mp h; exact hx he ▸ hj
    · intro h; exact mem_image_of_mem x h
  -- the points over a side are on the face of the side
  have side : ∀ {p q : Fin n} {z : ℝ³}, z ∈ V → cross (x q - x p) u ≠ 0 →
      (∀ y ∈ V, 0 ≤ det3 (x q - x p) (y - x p) u) → det3 (x q - x p) (z - x p) u = 0 →
      z ≠ x p → z ≠ x q →
      (p ∈ Sa ∧ q ∈ Sa ∧ ∃ i ∈ Sa, x i = z) ∨ (p ∈ Sb ∧ q ∈ Sb ∧ ∃ i ∈ Sb, x i = z) := by
    intro p q z hz hc hl h0 h1 h2
    obtain ⟨m, -, rfl⟩ := mem_image.mp hz
    rcases hg1 _ (mem p) _ (mem q) _ hz hc hl h0 h1 h2 with ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩
    · exact Or.inl ⟨(imgA p).mp k1, (imgA q).mp k2, m, (imgA m).mp k3, rfl⟩
    · exact Or.inr ⟨(imgB p).mp k1, (imgB q).mp k2, m, (imgB m).mp k3, rfl⟩
  have hdab : 0 < det3 (x a - x v) (x b - x v) u := by
    refine lt_of_le_of_ne (hleft _ (mem b)).1 fun h0 => ?_
    rcases side (mem b) hcrossA (fun y hy => (hleft y hy).1) h0.symm (hx.ne hbv)
        (hx.ne hab.symm) with ⟨-, -, i, hi, he⟩ | ⟨-, hq, -⟩
    · exact hbA (hx he ▸ hi)
    · exact haB hq
  -- rotations of the orientation
  have r1 : det3 (x b - x a) (x v - x a) u = det3 (x a - x v) (x b - x v) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have r2 : det3 (x v - x b) (x a - x b) u = det3 (x a - x v) (x b - x v) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  -- the face normals
  have NaU : ⟪Na, u⟫ = 0 := by
    have e : ⟪Na, x w⟫ = ⟪Na, x v⟫ := by rw [(hfa w).1 hwA, (hfa v).1 hvA]
    rw [hw, inner_add_right, real_inner_smul_right] at e
    exact (mul_eq_zero.mp (by linarith : h * ⟪Na, u⟫ = 0)).resolve_left hh
  have Na0 : Na ≠ 0 := by
    intro h0; have := (hfa b).2 hbA; rw [(hfa v).1 hvA |>.symm] at this
    rw [h0, inner_zero_left, inner_zero_left] at this; exact lt_irrefl _ this
  have onA : ∀ i ∈ Sa, ⟪Na, x i - x v⟫ = 0 := fun i hi => by
    rw [inner_sub_right, (hfa i).1 hi, (hfa v).1 hvA, sub_self]
  have onB : ∀ i ∈ Sb, ⟪Nb, x i - x b⟫ = 0 := fun i hi => by
    rw [inner_sub_right, (hfb i).1 hi, (hfb b).1 hbB, sub_self]
  have Nb0 : Nb ≠ 0 := by
    intro h0; have := (hfb a).2 haB; rw [(hfb v).1 hvB |>.symm] at this
    rw [h0, inner_zero_left, inner_zero_left] at this; exact lt_irrefl _ this
  obtain ⟨b0, b1, b2⟩ := zmod3_add_one
  set X := tri (x v) (x a) (x b) with hX
  set e : ℝ³ := h • (x v - x a) with he
  -- the middles of `S_a` and `w`
  set M : Finset ℝ³ := insert (x w) ((Sa \ {v, w, a}).image x) with hM
  have midA : ∀ i ∈ Sa, i ≠ v → i ≠ w → i ≠ a → ∃ s₀ δ₀ : ℝ, 0 < s₀ ∧ s₀ < 1 ∧ δ₀ ≠ 0 ∧
      x i = x v + s₀ • (x a - x v) + δ₀ • u := by
    intro i hi hiv hiw hia
    obtain ⟨s₀, δ₀, hco⟩ := EdgeConf.exists_coords_of_perp (onA a haA) NaU (onA i hi)
      hcrossA Na0
    refine ⟨s₀, δ₀, ?_⟩
    have hxi : x i = x v + s₀ • (x a - x v) + δ₀ • u := by rw [add_assoc, ← hco]; abel
    have l2 := (hleft _ (mem i)).2.1
    have l3 := (hleft _ (mem i)).2.2
    have e2 : det3 (x b - x a) (x i - x a) u = (1 - s₀) * det3 (x a - x v) (x b - x v) u := by
      rw [hxi, ← r1]; simp only [det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
        smul_eq_mul]; ring
    have e3 : det3 (x v - x b) (x i - x b) u = s₀ * det3 (x a - x v) (x b - x v) u := by
      rw [hxi, ← r2]; simp only [det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
        smul_eq_mul]; ring
    rw [e2] at l2
    rw [e3] at l3
    have hs0 : 0 ≤ s₀ := nonneg_of_mul_nonneg_left l3 hdab
    have hs1 : s₀ ≤ 1 := by have := nonneg_of_mul_nonneg_left l2 hdab; linarith
    refine ⟨lt_of_le_of_ne hs0 fun h0 => ?_, lt_of_le_of_ne hs1 fun h1 => ?_, fun hδ => ?_, hxi⟩
    · rw [← h0, zero_smul, add_zero] at hxi
      refine cne (i := v) (j := i) (Ne.symm hiv) (fun h => hiw h.2) (fun h => hvw h.1) ?_
      rw [hxi, add_sub_cancel_left]; ext j; fin_cases j <;> simp [cross] <;> ring
    · rw [h1, one_smul] at hxi
      refine cne (i := a) (j := i) (Ne.symm hia) (fun h => hav h.1) (fun h => haw h.1) ?_
      rw [hxi, show x v + (x a - x v) + δ₀ • u - x a = δ₀ • u by abel]
      ext j; fin_cases j <;> simp [cross] <;> ring
    · rw [hδ, zero_smul, add_zero] at hxi
      exact hseg v a i (fun h => hiv (hx h)) (fun h => hia (hx h)) s₀
        (lt_of_le_of_ne hs0 fun h0 => by
          rw [← h0, zero_smul, add_zero] at hxi; exact hiv (hx hxi))
        (lt_of_le_of_ne hs1 fun h1 => by
          rw [h1, one_smul, add_sub_cancel] at hxi; exact hia (hx hxi)) hxi
  -- the slide
  have notM : ∀ i, (i = v ∨ i = a ∨ i = b) → x i ∉ M := by
    intro i hi hm
    rcases mem_insert.mp hm with h | h
    · have := hx h; subst this
      rcases hi with h | h | h
      · exact hvw h.symm
      · exact haw h.symm
      · exact hbw h.symm
    · obtain ⟨j, hj, hji⟩ := mem_image.mp h
      have := hx hji; subst this
      rw [Finset.mem_sdiff] at hj
      rcases hi with rfl | rfl | rfl
      · exact hj.2 (by simp)
      · exact hj.2 (by simp)
      · exact hbA hj.1
  have memX : ∀ i, X i ∈ V := fun i => by
    rcases zmod3_cases i with rfl | rfl | rfl
    exacts [mem v, mem a, mem b]
  have Xinj : Function.Injective X := by
    have n1 : x v ≠ x a := hx.ne hav.symm
    have n2 : x v ≠ x b := hx.ne hbv.symm
    have n3 : x a ≠ x b := hx.ne hab
    intro i j hij
    rcases zmod3_cases i with rfl | rfl | rfl <;> rcases zmod3_cases j with rfl | rfl | rfl <;>
      simp only [hX, tri_0, tri_1, tri_2] at hij <;>
      first | rfl | exact absurd hij n1 | exact absurd hij n2 | exact absurd hij n3 |
        exact absurd hij.symm n1 | exact absurd hij.symm n2 | exact absurd hij.symm n3
  have hinj0 : Function.Injective (fun i => ⟪X i, u⟫) := by
    intro i j hij
    by_contra hne
    exact hdist _ (memX i) _ (memX j) (Xinj.ne hne) hij
  have hcyc : ∀ i j : ZMod 3, j ≠ i → j ≠ i + 1 → 0 < det3 (X (i + 1) - X i) (X j - X i) u := by
    intro i j hi hj
    rcases zmod3_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [hX, b0, b1, b2, tri_0, tri_1, tri_2]
    · exact hdab
    · rw [r1]; exact hdab
    · rw [r2]; exact hdab
  have hR : RimCertPts V u X := by
    refine ⟨le_rfl, memX, hcyc, fun z hz i => ?_, ?_⟩
    · rcases zmod3_cases i with rfl | rfl | rfl <;> simp only [hX, b0, b1, b2, tri_0, tri_1, tri_2]
      exacts [(hleft z hz).1, (hleft z hz).2.1, (hleft z hz).2.2]
    · exact isRobustUnimodal_three fun h => hinj0.ne (by decide : (0 : ZMod 3) ≠ 1) h.1
  have hcrB : cross (x v - x b) (x w - x b) ≠ 0 := by
    have e : cross (x v - x b) (x w - x b) = h • cross (x v - x b) u := by
      rw [hw]; ext j; fin_cases j <;> simp [cross] <;> ring
    rw [e]; exact smul_ne_zero hh hcrossB
  have key := isRupert_of_slideP V M u e hu X memX (fun i => by
      rcases zmod3_cases i with rfl | rfl | rfl
      · exact notM v (Or.inl rfl)
      · exact notM a (Or.inr (Or.inl rfl))
      · exact notM b (Or.inr (Or.inr rfl)))
    (by norm_num) 1 one_ne_zero (fun i j hi hj => Or.inl (by rw [one_mul]; exact hcyc i j hi hj))
    ?_ ?_ hinj0 ?_
  · by_cases hbad : NoPersistHDN X u e
    · exact Or.inl (key hbad)
    · right
      unfold NoPersistHDN at hbad
      push Not at hbad
      obtain ⟨i, j, Y, hY, Y', hY', hne, hu1, he1, hext⟩ := hbad
      refine ⟨Y' - Y, hdnDir_of_rim X memX (fun z hz => rimCertPts_suppIn hR hu z hz) hY hY' hne
        hu1 hext, cross_eq_zero_of_perp2 (A := x a - x v) (U := u) ?_ hu1 (onA a haA) NaU hcrossA⟩
      rw [he, real_inner_smul_right] at he1
      have : ⟪Y' - Y, x v - x a⟫ = 0 := (mul_eq_zero.mp he1).resolve_left hh
      rw [show x a - x v = -(x v - x a) by abel, inner_neg_right, this, neg_zero]
  · -- the other points
    intro y hy hyM hyX i
    obtain ⟨m, -, rfl⟩ := mem_image.mp hy
    have hmv : m ≠ v := fun h => hyX 0 (by rw [h]; rfl)
    have hma : m ≠ a := fun h => hyX 1 (by rw [h]; rfl)
    have hmb : m ≠ b := fun h => hyX 2 (by rw [h]; rfl)
    have hmw : m ≠ w := fun h => hyM (by rw [h]; exact mem_insert_self _ _)
    have hmA : m ∉ Sa := fun h => hyM (mem_insert_of_mem (mem_image_of_mem x
      (Finset.mem_sdiff.mpr ⟨h, by simp [hmv, hmw, hma]⟩)))
    have s0 : 0 < det3 (x a - x v) (x m - x v) u := by
      refine lt_of_le_of_ne (hleft _ (mem m)).1 fun h0 => ?_
      rcases side (mem m) hcrossA (fun y hy => (hleft y hy).1) h0.symm (hx.ne hmv)
          (hx.ne hma) with ⟨-, -, i, hi, he⟩ | ⟨-, hq, -⟩
      · exact hmA (hx he ▸ hi)
      · exact haB hq
    have s1 : 0 < det3 (x b - x a) (x m - x a) u := by
      refine lt_of_le_of_ne (hleft _ (mem m)).2.1 fun h0 => ?_
      rcases side (mem m) hcrossAB (fun y hy => (hleft y hy).2.1) h0.symm (hx.ne hma)
          (hx.ne hmb) with ⟨-, hq, -⟩ | ⟨hp, -, -⟩
      · exact hbA hq
      · exact haB hp
    rcases zmod3_cases i with rfl | rfl | rfl <;> simp only [hX, b0, b1, b2, tri_0, tri_1, tri_2]
    · exact Or.inl (by rw [one_mul]; exact s0)
    · exact Or.inl (by rw [one_mul]; exact s1)
    · by_cases hmB : m ∈ Sb
      · obtain ⟨NG, hG1, hG2, hG3⟩ := hAdjB m hmB hmv hmw hmb
        obtain ⟨k, hk, hk'⟩ := real_of_adj (onB v hvB) (onB w hwB) (onB m hmB) hcrB Nb0 hG1 hG2
          hG3
        have hd : ∀ Z, det3 (x v - x b) (x m - x b) Z = k * det3 (x v - x b) (x w - x b) Z := by
          intro Z; rw [det3, hk', real_inner_smul_left]; rfl
        right
        refine ⟨?_, ?_⟩
        · rw [hd, hw]
          have : det3 (x v - x b) (x v + h • u - x b) u = 0 := by
            simp only [det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
              smul_eq_mul]; ring
          rw [this, mul_zero]
        · rw [one_mul, hd, hw, he]
          have e' : det3 (x v - x b) (x v + h • u - x b) (h • (x v - x a)) =
              (h * h) * det3 (x a - x v) (x b - x v) u := by
            simp only [det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
              smul_eq_mul]; ring
          rw [e']
          exact mul_pos hk (mul_pos (mul_self_pos.mpr hh) hdab)
      · left
        rw [one_mul]
        refine lt_of_le_of_ne (hleft _ (mem m)).2.2 fun h0 => ?_
        rcases side (mem m) hcrossB (fun y hy => (hleft y hy).2.2) h0.symm (hx.ne hmb)
            (hx.ne hmv) with ⟨hp, -, -⟩ | ⟨-, -, i, hi, he⟩
        · exact hbA hp
        · exact hmB (hx he ▸ hi)
  · -- the middles of `S_a` and `w` over the open side `(v, a)`
    intro y hy
    rcases mem_insert.mp hy with rfl | hy
    · have hh2 : 0 < h * h := mul_self_pos.mpr hh
      filter_upwards [eventually_pos_affine (A := 0) (B := h * h) (Or.inr ⟨rfl, hh2⟩),
        eventually_pos_affine (A := 1) (B := -(h * h)) (Or.inl one_pos)] with t ht1 ht2
      refine ⟨0, t * (h * h), h, by linarith, by linarith, hh, ?_⟩
      simp only [hX, b0, tri_0, tri_1]
      rw [hw, he]; module
    · obtain ⟨i, hi, rfl⟩ := mem_image.mp hy
      rw [Finset.mem_sdiff] at hi
      have hi' : i ≠ v ∧ i ≠ w ∧ i ≠ a := by simpa using hi.2
      obtain ⟨s₀, δ₀, hs0, hs1, hδ, hxi⟩ := midA i hi.1 hi'.1 hi'.2.1 hi'.2.2
      filter_upwards [eventually_mem_Ioo_affine (B := δ₀ * h) hs0 hs1] with t ht
      refine ⟨0, s₀ + t * (δ₀ * h), δ₀, ht.1, ht.2, hδ, ?_⟩
      simp only [hX, b0, tri_0, tri_1]
      rw [hxi, he]; module
  · left
    exact strictUnimodal_of_cyclic (by norm_num)
      (hR.robust.isCyclicUnimodal_of_order (by norm_num) (fun i j h => h) hinj0)

/-- The left facts of a triangle rim, moved along the view to the other axle end. -/
theorem triLeft_shift {V : Finset ℝ³} {v w a b u : ℝ³} {h : ℝ} (hw : w = v + h • u)
    (H : ∀ z ∈ V, 0 ≤ det3 (a - v) (z - v) u ∧ 0 ≤ det3 (b - a) (z - a) u ∧
      0 ≤ det3 (v - b) (z - b) u) :
    ∀ z ∈ V, 0 ≤ det3 (a - w) (z - w) u ∧ 0 ≤ det3 (b - a) (z - a) u ∧
      0 ≤ det3 (w - b) (z - b) u := by
  intro z hz
  obtain ⟨h1, h2, h3⟩ := H z hz
  subst hw
  refine ⟨?_, h2, ?_⟩
  · have e : det3 (a - (v + h • u)) (z - (v + h • u)) u = det3 (a - v) (z - v) u := by
      simp only [det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e]; exact h1
  · have e : det3 (v + h • u - b) (z - b) u = det3 (v - b) (z - b) u := by
      simp only [det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e]; exact h3

/-- The left facts of a triangle rim, in the reversed orientation at the opposite view. -/
theorem triLeft_flip {V : Finset ℝ³} {v a b u : ℝ³}
    (H : ∀ z ∈ V, 0 ≤ det3 (a - v) (z - v) u ∧ 0 ≤ det3 (b - a) (z - a) u ∧
      0 ≤ det3 (v - b) (z - b) u) :
    ∀ z ∈ V, 0 ≤ det3 (b - v) (z - v) (-u) ∧ 0 ≤ det3 (a - b) (z - b) (-u) ∧
      0 ≤ det3 (v - a) (z - a) (-u) := by
  intro z hz
  obtain ⟨h1, h2, h3⟩ := H z hz
  have e1 : det3 (b - v) (z - v) (-u) = det3 (v - b) (z - b) u := by
    simp only [det3_expand, PiLp.sub_apply, PiLp.neg_apply]; ring
  have e2 : det3 (a - b) (z - b) (-u) = det3 (b - a) (z - a) u := by
    simp only [det3_expand, PiLp.sub_apply, PiLp.neg_apply]; ring
  have e3 : det3 (v - a) (z - a) (-u) = det3 (a - v) (z - v) u := by
    simp only [det3_expand, PiLp.sub_apply, PiLp.neg_apply]; ring
  rw [e1, e2, e3]
  exact ⟨h3, h2, h1⟩

theorem HDNDir.neg_view {V : Finset ℝ³} {u ℓ : ℝ³} (h : HDNDir V (-u) ℓ) : HDNDir V u ℓ := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, h3⟩
  rw [inner_neg_right, neg_eq_zero] at h2; exact h2

set_option maxHeartbeats 1000000 in
/-- **Triangle closings at a ridge view, at the limit** (§22.3 with the partner closing).  At the
view `u` along the common edge `v w` of two faces `S_A ∋ A` and `S_B ∋ B`, the triangle rim
`(v, A, B)` (every point weakly left of its sides) is the rim of the closings `K_v` and `K_w`.
If one of them (apex `p₁`) is realized on `S_A`'s circle and one (apex `p₂`) on `S_B`'s circle
(`hAdj₁`, `hAdj₂`: the sides `p₁ B`, `p₂ A` are edges of their faces), then with only the axle
seen end-on, (G1), distinct depths and at most one direction of horizontal double normals,
`V` is Rupert: a closing fails on its circle only with a double normal perpendicular to the
circle's face (Lemma 22.3, `triSlide_or`), and the two directions differ. -/
theorem isRupert_ridgeTri {n : ℕ} (x : Fin n → ℝ³) (hx : Function.Injective x)
    (hseg : ∀ i j m : Fin n, x m ≠ x i → x m ≠ x j → ∀ s : ℝ, 0 < s → s < 1 →
      x m ≠ x i + s • (x j - x i))
    {v w A B : Fin n} (hvw : v ≠ w) {SA SB : Finset (Fin n)} {NA NB : ℝ³} {κA κB : ℝ}
    (hfA : ∀ i, (i ∈ SA → ⟪NA, x i⟫ = κA) ∧ (i ∉ SA → ⟪NA, x i⟫ < κA))
    (hfB : ∀ i, (i ∈ SB → ⟪NB, x i⟫ = κB) ∧ (i ∉ SB → ⟪NB, x i⟫ < κB))
    (hSA : v ∈ SA ∧ w ∈ SA ∧ A ∈ SA ∧ B ∉ SA) (hSB : v ∈ SB ∧ w ∈ SB ∧ B ∈ SB ∧ A ∉ SB)
    (hSAB : ∀ i ∈ SA, i ∈ SB → i = v ∨ i = w)
    {p₁ q₁ p₂ q₂ : Fin n} (h₁ : (p₁ = v ∧ q₁ = w) ∨ (p₁ = w ∧ q₁ = v))
    (h₂ : (p₂ = v ∧ q₂ = w) ∨ (p₂ = w ∧ q₂ = v))
    (hAdj₁ : ∀ i ∈ SB, i ≠ v → i ≠ w → i ≠ B → ∃ NG : ℝ³, ⟪NG, x p₁ - x B⟫ = 0 ∧
      ⟪NG, x q₁ - x B⟫ < 0 ∧ ⟪NG, x i - x B⟫ < 0)
    (hAdj₂ : ∀ i ∈ SA, i ≠ v → i ≠ w → i ≠ A → ∃ NG : ℝ³, ⟪NG, x p₂ - x A⟫ = 0 ∧
      ⟪NG, x q₂ - x A⟫ < 0 ∧ ⟪NG, x i - x A⟫ < 0)
    {u : ℝ³} {h : ℝ} (hh : h ≠ 0) (hw : x w = x v + h • u)
    (hleft : ∀ z ∈ univ.image x, 0 ≤ det3 (x A - x v) (z - x v) u ∧
      0 ≤ det3 (x B - x A) (z - x A) u ∧ 0 ≤ det3 (x v - x B) (z - x B) u)
    (hpar : ParOnly (univ.image x) u (x v) (x w))
    (hg1 : G1At (univ.image x) u (SA.image x) (SB.image x))
    (hdist : ∀ y ∈ univ.image x, ∀ y' ∈ univ.image x, y ≠ y' → ⟪y, u⟫ ≠ ⟪y', u⟫)
    (hone : OneHDNDir (univ.image x) u) : IsRupert (univ.image x) := by
  obtain ⟨hvA, hwA, hAA, hBA⟩ := hSA
  obtain ⟨hvB, hwB, hBB, hAB⟩ := hSB
  -- the axle from `p` to `q`, both orders
  have axle : ∀ {p q : Fin n}, ((p = v ∧ q = w) ∨ (p = w ∧ q = v)) →
      p ≠ q ∧ p ∈ SA ∧ q ∈ SA ∧ p ∈ SB ∧ q ∈ SB ∧ (∀ i ∈ SA, i ∈ SB → i = p ∨ i = q) ∧
      (∃ h' : ℝ, h' ≠ 0 ∧ x q = x p + h' • u) ∧ ParOnly (univ.image x) u (x p) (x q) ∧
      (∀ z ∈ univ.image x, 0 ≤ det3 (x A - x p) (z - x p) u ∧
        0 ≤ det3 (x B - x A) (z - x A) u ∧ 0 ≤ det3 (x p - x B) (z - x B) u) := by
    rintro p q (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨hvw, hvA, hwA, hvB, hwB, hSAB, ⟨h, hh, hw⟩, hpar, hleft⟩
    · refine ⟨hvw.symm, hwA, hvA, hwB, hvB, fun i hi hi' => (hSAB i hi hi').symm, ⟨-h,
        neg_ne_zero.mpr hh, by rw [hw]; module⟩, EdgeConf.ParOnly.symm hpar,
        triLeft_shift hw hleft⟩
  obtain ⟨n₁, a₁, b₁, c₁, d₁, s₁, ⟨k₁, hk₁, e₁⟩, par₁, left₁⟩ := axle h₁
  obtain ⟨n₂, a₂, b₂, c₂, d₂, s₂, ⟨k₂, hk₂, e₂⟩, par₂, left₂⟩ := axle h₂
  have adj₁ : ∀ i ∈ SB, i ≠ p₁ → i ≠ q₁ → i ≠ B → ∃ NG : ℝ³, ⟪NG, x p₁ - x B⟫ = 0 ∧
      ⟪NG, x q₁ - x B⟫ < 0 ∧ ⟪NG, x i - x B⟫ < 0 := by
    intro i hi k1 k2 k3
    rcases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hAdj₁ i hi k1 k2 k3
    · exact hAdj₁ i hi k2 k1 k3
  have adj₂ : ∀ i ∈ SA, i ≠ p₂ → i ≠ q₂ → i ≠ A → ∃ NG : ℝ³, ⟪NG, x p₂ - x A⟫ = 0 ∧
      ⟪NG, x q₂ - x A⟫ < 0 ∧ ⟪NG, x i - x A⟫ < 0 := by
    intro i hi k1 k2 k3
    rcases h₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hAdj₂ i hi k1 k2 k3
    · exact hAdj₂ i hi k2 k1 k3
  have hdist' : ∀ y ∈ univ.image x, ∀ y' ∈ univ.image x, y ≠ y' → ⟪y, -u⟫ ≠ ⟪y', -u⟫ := by
    intro y hy y' hy' hne e
    rw [inner_neg_right, inner_neg_right, neg_inj] at e
    exact hdist y hy y' hy' hne e
  rcases triSlide_or x hx hseg n₁ hfA hfB ⟨a₁, b₁, hAA, hBA⟩ ⟨c₁, d₁, hBB, hAB⟩ s₁ adj₁ hk₁ e₁
      left₁ par₁ hg1 hdist with h1 | ⟨ℓ₁, hℓ₁, hc₁⟩
  · exact h1
  rcases triSlide_or x hx hseg n₂ (u := -u) (h := -k₂) hfB hfA ⟨c₂, d₂, hBB, hAB⟩
      ⟨a₂, b₂, hAA, hBA⟩ (fun i hi hi' => s₂ i hi' hi) adj₂ (neg_ne_zero.mpr hk₂)
      (by rw [e₂]; module) (triLeft_flip left₂) (EdgeConf.ParOnly.neg' par₂)
      (EdgeConf.G1At.neg hg1) hdist' with h2 | ⟨ℓ₂, hℓ₂, hc₂⟩
  · exact h2
  exfalso
  have hℓ₂' := hℓ₂.neg_view
  have h12 := hone ℓ₁ ℓ₂ hℓ₁ hℓ₂'
  have hNA : NA ≠ 0 := by
    intro h0; have := (hfA B).2 hBA; rw [(hfA v).1 hvA |>.symm, h0, inner_zero_left,
      inner_zero_left] at this; exact lt_irrefl _ this
  have hN : cross NA NB ≠ 0 := cross_normals_ne hNA (p := x v) (q := x A)
    (by rw [inner_sub_right, (hfA A).1 hAA, (hfA v).1 hvA, sub_self])
    (by rw [inner_sub_right]; linarith [(hfB A).2 hAB, (hfB v).1 hvB])
  apply hN
  have e1 := eq_smul_of_cross_eq_zero hℓ₁.1 hc₁
  have e2 := eq_smul_of_cross_eq_zero hℓ₂'.1 hc₂
  have e3 := eq_smul_of_cross_eq_zero hℓ₁.1 h12
  rw [e1, e2, e3]
  ext j; fin_cases j <;> simp [cross] <;> ring

/-- The left facts of a triangle rim certificate pass to the limit. -/
theorem triLeft_limit {n : ℕ} {x : Fin n → ℝ³} {K : ℕ → Fin n → ℝ³}
    (hK : ∀ m, Tendsto (fun k => K k m) atTop (𝓝 (x m))) {v w a b : Fin n}
    (hfreq : ∃ᶠ k in atTop,
      RimCertPts (univ.image (K k)) (K k w - K k v) (tri (K k v) (K k a) (K k b))) :
    ∀ z ∈ univ.image x, 0 ≤ det3 (x a - x v) (z - x v) (x w - x v) ∧
      0 ≤ det3 (x b - x a) (z - x a) (x w - x v) ∧ 0 ≤ det3 (x v - x b) (z - x b) (x w - x v) := by
  have memK : ∀ k i, K k i ∈ univ.image (K k) := fun k i => mem_image_of_mem _ (mem_univ i)
  have hus : Tendsto (fun k => K k w - K k v) atTop (𝓝 (x w - x v)) := (hK w).sub (hK v)
  have lim0 : ∀ {f : ℕ → ℝ} {L : ℝ}, Tendsto f atTop (𝓝 L) → (∃ᶠ k in atTop, 0 ≤ f k) →
      0 ≤ L := fun hf hfr => le_of_tendsto_frequently tendsto_const_nhds hf hfr
  obtain ⟨b0, b1, b2⟩ := zmod3_add_one
  intro z hz
  obtain ⟨m, -, rfl⟩ := mem_image.mp hz
  refine ⟨lim0 (Tendsto.det3' ((hK a).sub (hK v)) ((hK m).sub (hK v)) hus)
    (hfreq.mono fun k hk => ?_), lim0 (Tendsto.det3' ((hK b).sub (hK a)) ((hK m).sub (hK a)) hus)
    (hfreq.mono fun k hk => ?_), lim0 (Tendsto.det3' ((hK v).sub (hK b)) ((hK m).sub (hK b)) hus)
    (hfreq.mono fun k hk => ?_)⟩
  · simpa [b0, tri_0, tri_1] using hk.left _ (memK k m) 0
  · simpa [b1, tri_1, tri_2] using hk.left _ (memK k m) 1
  · simpa [b2, tri_2, tri_0] using hk.left _ (memK k m) 2

/-- A side of a quadrilateral of type 21 at the ridge `26` that is an edge of the
quadrilateral (`46` and `06` on `046`, `23` and `25` on `235`): the adjacent facet has the other
axle end and the middle strictly beneath it. -/
theorem ridge_adj21 {x : Fin 7 → ℝ³} (T : Facets21 x) {B p q m : Fin 7}
    (h : (B = 4 ∧ p = 6 ∧ q = 2 ∧ m = 3) ∨ (B = 3 ∧ p = 2 ∧ q = 6 ∧ m = 4) ∨
      (B = 0 ∧ p = 6 ∧ q = 2 ∧ m = 5) ∨ (B = 5 ∧ p = 2 ∧ q = 6 ∧ m = 0)) :
    ∃ NG : ℝ³, ⟪NG, x p - x B⟫ = 0 ∧ ⟪NG, x q - x B⟫ < 0 ∧ ⟪NG, x m - x B⟫ < 0 := by
  rcases h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨_, T.f046.adj (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨_, T.f235.adj (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨_, T.f046.adj (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨_, T.f235.adj (by decide) (by decide) (by decide) (by decide)⟩

/-- **The codimension-2 conditions at the ridge `26`**: `EdgeGen` at the view `2 − 6` for the faces
`0256`, `2346` (§22.4), and `2`, `6` off the planes `013` and `514` of Lemma E (Lemma 16.5). -/
def R26Gen21 (x : Fin 7 → ℝ³) (NA NB : ℝ³) : Prop :=
  EdgeGen (univ.image x) (x 2 - x 6) (x 6) (x 2) (({0, 2, 5, 6} : Finset (Fin 7)).image x)
    (({2, 3, 4, 6} : Finset (Fin 7)).image x) NA NB ∧
  det3 (x 3 - x 0) (x 1 - x 0) (x 6 - x 0) ≠ 0 ∧ det3 (x 3 - x 0) (x 1 - x 0) (x 2 - x 0) ≠ 0 ∧
  det3 (x 4 - x 5) (x 1 - x 5) (x 6 - x 5) ≠ 0 ∧ det3 (x 4 - x 5) (x 1 - x 5) (x 2 - x 5) ≠ 0

/-- The labels of tier R at the ridge `26`. -/
theorem ridge21_labels {v w A B mA mB : Fin 7}
    (hvw : (v = 6 ∧ w = 2) ∨ (v = 2 ∧ w = 6)) (hA : (A = 0 ∧ mA = 5) ∨ (A = 5 ∧ mA = 0))
    (hB : (B = 3 ∧ mB = 4) ∨ (B = 4 ∧ mB = 3)) :
    v ≠ w ∧ v ∈ ({0, 2, 5, 6} : Finset (Fin 7)) ∧ w ∈ ({0, 2, 5, 6} : Finset (Fin 7)) ∧
      A ∈ ({0, 2, 5, 6} : Finset (Fin 7)) ∧ B ∉ ({0, 2, 5, 6} : Finset (Fin 7)) ∧
      (1 : Fin 7) ∉ ({0, 2, 5, 6} : Finset (Fin 7)) ∧
      v ∈ ({2, 3, 4, 6} : Finset (Fin 7)) ∧ w ∈ ({2, 3, 4, 6} : Finset (Fin 7)) ∧
      B ∈ ({2, 3, 4, 6} : Finset (Fin 7)) ∧ A ∉ ({2, 3, 4, 6} : Finset (Fin 7)) ∧
      (1 : Fin 7) ∉ ({2, 3, 4, 6} : Finset (Fin 7)) ∧
      (∀ i ∈ ({0, 2, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 2, 5, 6} : Finset (Fin 7)),
        i ≠ v → i ≠ w → i ≠ A → j ≠ v → j ≠ w → j ≠ A → i = j) ∧
      (∀ i ∈ ({2, 3, 4, 6} : Finset (Fin 7)), ∀ j ∈ ({2, 3, 4, 6} : Finset (Fin 7)),
        i ≠ v → i ≠ w → i ≠ B → j ≠ v → j ≠ w → j ≠ B → i = j) ∧
      (∀ i ∈ ({0, 2, 5, 6} : Finset (Fin 7)), i ∈ ({2, 3, 4, 6} : Finset (Fin 7)) →
        i = v ∨ i = w) ∧
      (((if B = 4 then 6 else 2 : Fin 7) = v ∧ (if B = 4 then 2 else 6 : Fin 7) = w) ∨
        ((if B = 4 then 6 else 2 : Fin 7) = w ∧ (if B = 4 then 2 else 6 : Fin 7) = v)) ∧
      (((if A = 0 then 6 else 2 : Fin 7) = v ∧ (if A = 0 then 2 else 6 : Fin 7) = w) ∨
        ((if A = 0 then 6 else 2 : Fin 7) = w ∧ (if A = 0 then 2 else 6 : Fin 7) = v)) ∧
      ((B = 4 ∧ (if B = 4 then 6 else 2 : Fin 7) = 6 ∧ (if B = 4 then 2 else 6 : Fin 7) = 2 ∧
          mB = 3) ∨
        (B = 3 ∧ (if B = 4 then 6 else 2 : Fin 7) = 2 ∧ (if B = 4 then 2 else 6 : Fin 7) = 6 ∧
          mB = 4)) ∧
      ((A = 0 ∧ (if A = 0 then 6 else 2 : Fin 7) = 6 ∧ (if A = 0 then 2 else 6 : Fin 7) = 2 ∧
          mA = 5) ∨
        (A = 5 ∧ (if A = 0 then 6 else 2 : Fin 7) = 2 ∧ (if A = 0 then 2 else 6 : Fin 7) = 6 ∧
          mA = 0)) ∧
      mA ∈ ({0, 2, 5, 6} : Finset (Fin 7)) ∧ mB ∈ ({2, 3, 4, 6} : Finset (Fin 7)) ∧ mA ≠ v ∧
      mA ≠ w ∧ mA ≠ A ∧ mB ≠ v ∧ mB ≠ w ∧ mB ≠ B := by
  rcases hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases hB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
/-- **One labelled certificate of tier R at the limit** (§22 at the ridge `26`): far ends
`A ∈ {0, 5}` of `0256` and `B ∈ {3, 4}` of `2346`, the closings along `v → w` (`{v, w} = {6, 2}`).
An edge pair with Lemma E by §22.3–22.8 (`isRupert_ePair_limit_facts`); the triangle closings by
Lemma 22.3 on the two face circles with the two directions of double normals
(`isRupert_ridgeTri`). -/
theorem isRupert_ridge21_lab {x : Fin 7 → ℝ³} (T : Facets21 x) {v w A B mA mB : Fin 7}
    (hvw : (v = 6 ∧ w = 2) ∨ (v = 2 ∧ w = 6)) (hA : (A = 0 ∧ mA = 5) ∨ (A = 5 ∧ mA = 0))
    (hB : (B = 3 ∧ mB = 4) ∨ (B = 4 ∧ mB = 3))
    (K : ℕ → Fin 7 → ℝ³) (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)))
    (hfreq : ∃ᶠ n in atTop,
      RidgeData (univ.image (K n)) (K n v) (K n w) (K n A) (K n B) (K n 1))
    (hgen : EdgeGen (univ.image x) (x 2 - x 6) (x 6) (x 2)
      (({0, 2, 5, 6} : Finset (Fin 7)).image x) (({2, 3, 4, 6} : Finset (Fin 7)).image x)
      T.f0256.N T.f2346.N)
    (hcop : det3 (x B - x A) (x 1 - x A) (x 6 - x A) ≠ 0 ∧
      det3 (x B - x A) (x 1 - x A) (x 2 - x A) ≠ 0) : IsRupert (univ.image x) := by
  obtain ⟨hvw', vA, wA, AA, BA, cA, vB, wB, BB, AB, cB, oA, oB, sAB, h₁, h₂, j₁, j₂,
      mAA, mBB, mAv, mAw, mAA', mBv, mBw, mBB'⟩ := ridge21_labels hvw hA hB
  set SA : Finset (Fin 7) := {0, 2, 5, 6} with hSAdef
  set SB : Finset (Fin 7) := {2, 3, 4, 6} with hSBdef
  set p₁ : Fin 7 := if B = 4 then 6 else 2 with hp₁
  set q₁ : Fin 7 := if B = 4 then 2 else 6 with hq₁
  set p₂ : Fin 7 := if A = 0 then 6 else 2 with hp₂
  set q₂ : Fin 7 := if A = 0 then 2 else 6 with hq₂
  have onlyA : ∀ i ∈ SA, i ≠ v → i ≠ w → i ≠ A → i = mA := fun i hi k1 k2 k3 =>
    oA i hi mA mAA k1 k2 k3 mAv mAw mAA'
  have onlyB : ∀ i ∈ SB, i ≠ v → i ≠ w → i ≠ B → i = mB := fun i hi k1 k2 k3 =>
    oB i hi mB mBB k1 k2 k3 mBv mBw mBB'
  -- the view along `v → w`
  have G : EdgeGen (univ.image x) (x w - x v) (x v) (x w) (SA.image x) (SB.image x)
      T.f0256.N T.f2346.N := by
    rcases hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hgen
    · have := hgen.rev; rwa [neg_sub] at this
  have hc : det3 (x B - x A) (x 1 - x A) (x v - x A) ≠ 0 ∧
      det3 (x B - x A) (x 1 - x A) (x w - x A) ≠ 0 := by
    rcases hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hcop
    · exact ⟨hcop.2, hcop.1⟩
  have fA := T.f0256.hf (i₀ := v) vA
  have fB := T.f2346.hf (i₀ := v) vB
  have e1 : ∀ X, det3 (x A - x B) (x 1 - x B) (X - x B) =
      -det3 (x B - x A) (x 1 - x A) (X - x A) := fun X => det3_lemmaE_swapAB _ _ _ _
  have adj₁ : ∀ i ∈ SB, i ≠ v → i ≠ w → i ≠ B → ∃ NG : ℝ³, ⟪NG, x p₁ - x B⟫ = 0 ∧
      ⟪NG, x q₁ - x B⟫ < 0 ∧ ⟪NG, x i - x B⟫ < 0 := by
    intro i hi k1 k2 k3
    rw [onlyB i hi k1 k2 k3]
    exact ridge_adj21 T (by rcases j₁ with h | h; exacts [Or.inl h, Or.inr (Or.inl h)])
  have adj₂ : ∀ i ∈ SA, i ≠ v → i ≠ w → i ≠ A → ∃ NG : ℝ³, ⟪NG, x p₂ - x A⟫ = 0 ∧
      ⟪NG, x q₂ - x A⟫ < 0 ∧ ⟪NG, x i - x A⟫ < 0 := by
    intro i hi k1 k2 k3
    rw [onlyA i hi k1 k2 k3]
    exact ridge_adj21 T (by
      rcases j₂ with h | h; exacts [Or.inr (Or.inr (Or.inl h)), Or.inr (Or.inr (Or.inr h))])
  have hw1 : x w = x v + (1 : ℝ) • (x w - x v) := by rw [one_smul]; abel
  rcases frequently_or_distrib.mp hfreq with h | h
  · exact isRupert_ePair_limit_facts x T.inj T.noSeg (v := v) (w := w) (a := A) (b := B)
      (c := 1) hvw' fA fB ⟨vA, wA, AA, BA, cA, oA⟩ ⟨vB, wB, BB, AB, cB, oB⟩ K hK
      (h.mono fun n hn => hn.facts) G hc
  rcases frequently_or_distrib.mp h with h | h
  · exact isRupert_ePair_limit_facts x T.inj T.noSeg (v := v) (w := w) (a := B) (b := A)
      (c := 1) hvw' fB fA ⟨vB, wB, BB, AB, cB, oB⟩ ⟨vA, wA, AA, BA, cA, oA⟩ K hK
      (h.mono fun n hn => hn.facts) G.swapF
      ⟨by rw [e1]; exact neg_ne_zero.mpr hc.1, by rw [e1]; exact neg_ne_zero.mpr hc.2⟩
  rcases frequently_or_distrib.mp h with h | h
  · exact isRupert_ridgeTri x T.inj T.noSeg hvw' fA fB ⟨vA, wA, AA, BA⟩ ⟨vB, wB, BB, AB⟩ sAB
      h₁ h₂ adj₁ adj₂ one_ne_zero hw1 (triLeft_limit hK h) G.par G.g1 G.dist G.one
  · exact isRupert_ridgeTri x T.inj T.noSeg hvw' fB fA ⟨vB, wB, BB, AB⟩ ⟨vA, wA, AA, BA⟩
      (fun i hi hi' => sAB i hi' hi) h₂ h₁ adj₂ adj₁ one_ne_zero hw1 (triLeft_limit hK h) G.par
      G.g1.swapF G.dist G.one

/-- **The ridge `26` at the limit**: if shapes `K_n → x` frequently carry the certificates of
tier R with their data (`R26E21`), then under `R26Gen21` the limit is Rupert. -/
theorem isRupert_ridge21 {x : Fin 7 → ℝ³} (T : Facets21 x)
    (K : ℕ → Fin 7 → ℝ³) (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)))
    (hfreq : ∃ᶠ n in atTop, R26E21 (K n)) (hg : R26Gen21 x T.f0256.N T.f2346.N) :
    IsRupert (univ.image x) := by
  obtain ⟨hgen, c1, c2, c3, c4⟩ := hg
  have h8 : ∃ᶠ n in atTop,
      ((RidgeData (univ.image (K n)) (K n 6) (K n 2) (K n 0) (K n 3) (K n 1) ∨
        RidgeData (univ.image (K n)) (K n 6) (K n 2) (K n 0) (K n 4) (K n 1)) ∨
      (RidgeData (univ.image (K n)) (K n 6) (K n 2) (K n 5) (K n 3) (K n 1) ∨
        RidgeData (univ.image (K n)) (K n 6) (K n 2) (K n 5) (K n 4) (K n 1))) ∨
      ((RidgeData (univ.image (K n)) (K n 2) (K n 6) (K n 0) (K n 3) (K n 1) ∨
        RidgeData (univ.image (K n)) (K n 2) (K n 6) (K n 0) (K n 4) (K n 1)) ∨
      (RidgeData (univ.image (K n)) (K n 2) (K n 6) (K n 5) (K n 3) (K n 1) ∨
        RidgeData (univ.image (K n)) (K n 2) (K n 6) (K n 5) (K n 4) (K n 1))) := by
    refine hfreq.mono fun n hn => ?_
    rcases hn with ⟨A, B, hA, hB, hd⟩ | ⟨A, B, hA, hB, hd⟩ <;>
      rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · exact Or.inl (Or.inl (Or.inl hd))
    · exact Or.inl (Or.inl (Or.inr hd))
    · exact Or.inl (Or.inr (Or.inl hd))
    · exact Or.inl (Or.inr (Or.inr hd))
    · exact Or.inr (Or.inl (Or.inl hd))
    · exact Or.inr (Or.inl (Or.inr hd))
    · exact Or.inr (Or.inr (Or.inl hd))
    · exact Or.inr (Or.inr (Or.inr hd))
  have k04 : det3 (x 4 - x 0) (x 1 - x 0) (x 6 - x 0) ≠ 0 ∧
      det3 (x 4 - x 0) (x 1 - x 0) (x 2 - x 0) ≠ 0 :=
    ⟨T.f014.det3_ne (by decide) (by decide) (by decide) (by decide)
      (cross_ne_zero_of_noSeg T.inj T.noSeg (by decide) (by decide) (by decide)),
     T.f014.det3_ne (by decide) (by decide) (by decide) (by decide)
      (cross_ne_zero_of_noSeg T.inj T.noSeg (by decide) (by decide) (by decide))⟩
  have k53 : det3 (x 3 - x 5) (x 1 - x 5) (x 6 - x 5) ≠ 0 ∧
      det3 (x 3 - x 5) (x 1 - x 5) (x 2 - x 5) ≠ 0 :=
    ⟨T.f135.det3_ne (by decide) (by decide) (by decide) (by decide)
      (cross_ne_zero_of_noSeg T.inj T.noSeg (by decide) (by decide) (by decide)),
     T.f135.det3_ne (by decide) (by decide) (by decide) (by decide)
      (cross_ne_zero_of_noSeg T.inj T.noSeg (by decide) (by decide) (by decide))⟩
  rcases frequently_or_distrib.mp h8 with h | h
  · rcases frequently_or_distrib.mp h with h | h <;> rcases frequently_or_distrib.mp h with h | h
    · exact isRupert_ridge21_lab T (Or.inl ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩)
        K hK h hgen ⟨c1, c2⟩
    · exact isRupert_ridge21_lab T (Or.inl ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩)
        K hK h hgen k04
    · exact isRupert_ridge21_lab T (Or.inl ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩)
        K hK h hgen k53
    · exact isRupert_ridge21_lab T (Or.inl ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩)
        K hK h hgen ⟨c3, c4⟩
  · rcases frequently_or_distrib.mp h with h | h <;> rcases frequently_or_distrib.mp h with h | h
    · exact isRupert_ridge21_lab T (Or.inr ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩)
        K hK h hgen ⟨c1, c2⟩
    · exact isRupert_ridge21_lab T (Or.inr ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩)
        K hK h hgen k04
    · exact isRupert_ridge21_lab T (Or.inr ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩)
        K hK h hgen k53
    · exact isRupert_ridge21_lab T (Or.inr ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩)
        K hK h hgen ⟨c3, c4⟩

/-- `R26Gen21` for every normal of the two quadrilaterals. -/
def R26GenAff21 (x : Fin 7 → ℝ³) (fA fB : ℝ³ →ᵃ[ℝ] ℝ) : Prop :=
  ∀ NA NB : ℝ³, (∀ y, fA.linear y = ⟪NA, y⟫) → (∀ y, fB.linear y = ⟪NB, y⟫) → R26Gen21 x NA NB

theorem edgeX21_tri (s : Finset (Fin 7)) (h1 : s ∈ edgeSet21) (h2 : s ∉ qEdgeSet21)
    (h3 : s ∉ wEdgeSet21) : s ∈ triEdgeSet21 := by
  simp only [edgeSet21, Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | decide | exact absurd (by decide) h2 | exact absurd (by decide) h3

/-! ### Type 21 with the edges of tiers Q and R closed -/

/-- **Type 21 with §22 at the edges `06`, `46`, `25`, `23`, `05`, `34`, from the facets**: seven
points labelled so that `014`, `015`, `0256`, `046`, `134`, `135`, `2346`, `235` are facets
(functionals negative off them) are Rupert if, at the named views: along `06`, `46`, `25`, `23`
no horizontal double normal or the codimension-2 conditions of §22.4 (`hQ`, `QGenAff21`); along
`05`, `34` the same (`h5`, `Q5GenAff21`); along `26` no horizontal double normal or the
codimension-2 conditions there (`h26`, `R26GenAff21`); along
the six two-triangle edges no horizontal double normal or (G1) (`hEd`); along the lines of
`046/134`, `046/015`, `235/134`, `235/015` no horizontal double normal or (G1) (`hV`); and at most
one tie at these views (`OneTie21`).  Nothing is asked at the non-edge segments.  The
certificates at the four vertex lines with a quadrilateral (`CertD21`) are left to `hVq`
(closed in `Type21Vtx.lean`, `isRupert_type21_limit_facets_codim2`). -/
theorem isRupert_type21_limit_facets_codim2_of (x : Fin 7 → ℝ³) (hx : Function.Injective x)
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
      (i ∉ ({2, 3, 5} : Finset (Fin 7)) → fH (x i) < 0))
    (hQ : (NoHDNAt (univ.image x) (x 6 - x 0) ∨
        QGenAff21 x fD fC 0 3 4 5 6 {0, 4, 6} {0, 2, 5, 6}) ∧
      (NoHDNAt (univ.image x) (x 6 - x 4) ∨ QGenAff21 x fD fG 4 5 0 3 6 {0, 4, 6} {2, 3, 4, 6}) ∧
      (NoHDNAt (univ.image x) (x 2 - x 5) ∨ QGenAff21 x fH fC 5 4 3 0 2 {2, 3, 5} {0, 2, 5, 6}) ∧
      (NoHDNAt (univ.image x) (x 2 - x 3) ∨ QGenAff21 x fH fG 3 0 5 4 2 {2, 3, 5} {2, 3, 4, 6}))
    (h5 : (NoHDNAt (univ.image x) (x 5 - x 0) ∨
        Q5GenAff21 x fB fC 0 3 1 6 2 5 4 {0, 1, 5} {0, 2, 5, 6}) ∧
      (NoHDNAt (univ.image x) (x 3 - x 4) ∨
        Q5GenAff21 x fE fG 4 5 1 6 2 3 0 {1, 3, 4} {2, 3, 4, 6}))
    (h26 : NoHDNAt (univ.image x) (x 2 - x 6) ∨ R26GenAff21 x fC fG)
    (hEd : HDNOrG1Edge (univ.image x) (x 0) (x 1) (x 4) (x 5) ∧
      HDNOrG1Edge (univ.image x) (x 0) (x 4) (x 1) (x 6) ∧
      HDNOrG1Edge (univ.image x) (x 1) (x 4) (x 0) (x 3) ∧
      HDNOrG1Edge (univ.image x) (x 1) (x 5) (x 0) (x 3) ∧
      HDNOrG1Edge (univ.image x) (x 1) (x 3) (x 4) (x 5) ∧
      HDNOrG1Edge (univ.image x) (x 3) (x 5) (x 1) (x 2))
    (hVq : ∀ K : ℕ → Fin 7 → ℝ³, (∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) →
      (∃ᶠ n in atTop, CertD21 (K n) ∧
        ∀ w a b, TieInst21 x w a b → ⟪K n a - K n b, view21 (K n) w⟫ = 0) →
      IsRupert (univ.image x))
    (hV : HDNOrG1Aff (univ.image x) fD fE (x 4) (x 0) (x 6) (x 4) (x 3) (x 1) ∧
      HDNOrG1Aff (univ.image x) fD fB (x 0) (x 4) (x 6) (x 0) (x 5) (x 1) ∧
      HDNOrG1Aff (univ.image x) fH fE (x 3) (x 5) (x 2) (x 3) (x 4) (x 1) ∧
      HDNOrG1Aff (univ.image x) fH fB (x 5) (x 3) (x 2) (x 5) (x 0) (x 1))
    (htie : OneTie21 x) : IsRupert (univ.image x) := by
  let T := Facets21.ofAffine x hx fA fB fC fD fE fF fG fH hA hB hC hD hE hF hG hH
  obtain ⟨K, hK, hc⟩ := exists_certSeq21 T htie
  have hsplit : (∃ᶠ n in atTop, CertP21 UsedX21 (K n) ∧
      ∀ w a b, TieInst21 x w a b → ⟪K n a - K n b, view21 (K n) w⟫ = 0) ∨
      (∃ᶠ n in atTop, CertQ21 (K n) ∧
        ∀ w a b, TieInst21 x w a b → ⟪K n a - K n b, view21 (K n) w⟫ = 0) ∨
      (∃ᶠ n in atTop, CertW21 (K n) ∧
        ∀ w a b, TieInst21 x w a b → ⟪K n a - K n b, view21 (K n) w⟫ = 0) ∨
      ∃ᶠ n in atTop, CertD21 (K n) ∧
        ∀ w a b, TieInst21 x w a b → ⟪K n a - K n b, view21 (K n) w⟫ = 0 := by
    have : ∃ᶠ n in atTop, (CertP21 UsedX21 (K n) ∧
        ∀ w a b, TieInst21 x w a b → ⟪K n a - K n b, view21 (K n) w⟫ = 0) ∨
        ((CertQ21 (K n) ∧ ∀ w a b, TieInst21 x w a b → ⟪K n a - K n b, view21 (K n) w⟫ = 0) ∨
        ((CertW21 (K n) ∧ ∀ w a b, TieInst21 x w a b → ⟪K n a - K n b, view21 (K n) w⟫ = 0) ∨
        (CertD21 (K n) ∧ ∀ w a b, TieInst21 x w a b → ⟪K n a - K n b, view21 (K n) w⟫ = 0))) :=
      hc.mono fun n ⟨h, ht⟩ =>
        h.elim (fun h => Or.inl ⟨h, ht⟩) (fun h => Or.inr (h.elim (fun h => Or.inl ⟨h, ht⟩)
          (fun h => Or.inr (h.elim (fun h => Or.inl ⟨h, ht⟩) (fun h => Or.inr ⟨h, ht⟩)))))
    rcases frequently_or_distrib.mp this with h | h
    · exact Or.inl h
    rcases frequently_or_distrib.mp h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (frequently_or_distrib.mp h))
  rcases hsplit with h | h | h | h
  · -- the certificates without data
    have hE' : ∀ e : Fin 6, HDNOrG1Edge (univ.image x) (x (triEdge21 e).1)
        (x (triEdge21 e).2.1) (x (triEdge21 e).2.2.1) (x (triEdge21 e).2.2.2) := by
      obtain ⟨e0, e1, e2, e3, e4, e5⟩ := hEd
      intro e; fin_cases e
      exacts [e0, e1, e2, e3, e4, e5]
    refine isRupert_of_cert_seq21_sec T (P := UsedX21) (fun v hu hv => ?_) K hK h
    rcases v with ⟨i, j⟩ | t
    · have hmem := edgeX21_tri _ hu.1 hu.2.1 hu.2.2
      obtain ⟨e, he⟩ := triEdgeSet21_mem i j hmem
      rcases hE' e with h | h
      · left
        rcases he with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · show NoHDNAt _ (x j - x i)
          rw [← e1, ← e2]; exact h
        · show NoHDNAt _ (x j - x i)
          rw [← e1, ← e2, ← neg_sub]; exact h.neg
      · exact Or.inr ⟨e, he, h⟩
    · obtain ⟨V5, V6, V7, V8⟩ := hV
      have hu' : 4 ≤ t.val := hu
      fin_cases t
      · exact absurd hu' (by decide)
      · exact absurd hu' (by decide)
      · exact absurd hu' (by decide)
      · exact absurd hu' (by decide)
      · rcases V5 _ hv (affine_planeLine_perp fD hD (by decide) (by decide) (by decide))
          (affine_planeLine_perp' fE hE (by decide) (by decide) (by decide)) with h | h
        · exact Or.inl h
        · exact Or.inr ⟨Or.inl rfl, h⟩
      · rcases V6 _ hv (affine_planeLine_perp fD hD (by decide) (by decide) (by decide))
          (affine_planeLine_perp' fB hB (by decide) (by decide) (by decide)) with h | h
        · exact Or.inl h
        · exact Or.inr ⟨Or.inr (Or.inl rfl), h⟩
      · rcases V7 _ hv (affine_planeLine_perp fH hH (by decide) (by decide) (by decide))
          (affine_planeLine_perp' fE hE (by decide) (by decide) (by decide)) with h | h
        · exact Or.inl h
        · exact Or.inr ⟨Or.inr (Or.inr (Or.inl rfl)), h⟩
      · rcases V8 _ hv (affine_planeLine_perp fH hH (by decide) (by decide) (by decide))
          (affine_planeLine_perp' fB hB (by decide) (by decide) (by decide)) with h | h
        · exact Or.inl h
        · exact Or.inr ⟨Or.inr (Or.inr (Or.inr rfl)), h⟩
  · -- the certificates of tier Q at `06`, `46`, `25`, `23`
    obtain ⟨Q1, Q2, Q3, Q4⟩ := hQ
    have gen : ∀ {fT fQ : ℝ³ →ᵃ[ℝ] ℝ} {ST SQ : Finset (Fin 7)}
        (hT : ∀ i, (i ∈ ST → fT (x i) = 0) ∧ (i ∉ ST → fT (x i) < 0))
        (hQ : ∀ i, (i ∈ SQ → fQ (x i) = 0) ∧ (i ∉ SQ → fQ (x i) < 0)) {P P' R R' C' : Fin 7},
        NoHDNAt (univ.image x) (x C' - x P) ∨ QGenAff21 x fT fQ P P' R R' C' ST SQ →
        NoHDNAt (univ.image x) (x C' - x P) ∨
          QGen21 x (Face16.ofAffine fT hT).N (Face16.ofAffine fQ hQ).N P P' R R' C' ST SQ :=
      fun hT hQ _ _ _ _ _ h => h.imp_right fun h' =>
        h' _ _ (fun y => (Face16.ofAffine_inner _ hT y).symm)
          (fun y => (Face16.ofAffine_inner _ hQ y).symm)
    simp only [CertQ21, or_and_right] at h
    rcases frequently_or_distrib.mp h with h | h
    · exact isRupert_qEdge21_or T T.f046 T.f0256 T.f2346 (by decide) (by decide) (by decide)
        (by decide) K hK h (gen hD hC Q1)
    rcases frequently_or_distrib.mp h with h | h
    · exact isRupert_qEdge21_or T T.f046 T.f2346 T.f0256 (by decide) (by decide) (by decide)
        (by decide) K hK h (gen hD hG Q2)
    rcases frequently_or_distrib.mp h with h | h
    · exact isRupert_qEdge21_or T T.f235 T.f0256 T.f2346 (by decide) (by decide) (by decide)
        (by decide) K hK h (gen hH hC Q3)
    · exact isRupert_qEdge21_or T T.f235 T.f2346 T.f0256 (by decide) (by decide) (by decide)
        (by decide) K hK h (gen hH hG Q4)
  · -- the certificates at `05`, `34`, `26`
    obtain ⟨Q5, Q6⟩ := h5
    have gen : ∀ {fT fQ : ℝ³ →ᵃ[ℝ] ℝ} {ST SQ : Finset (Fin 7)}
        (hT : ∀ i, (i ∈ ST → fT (x i) = 0) ∧ (i ∉ ST → fT (x i) < 0))
        (hQ : ∀ i, (i ∈ SQ → fQ (x i) = 0) ∧ (i ∉ SQ → fQ (x i) < 0))
        {P P' R R' D C' Q' : Fin 7},
        NoHDNAt (univ.image x) (x C' - x P) ∨ Q5GenAff21 x fT fQ P P' R R' D C' Q' ST SQ →
        NoHDNAt (univ.image x) (x C' - x P) ∨
          Q5Gen21 x (Face16.ofAffine fT hT).N (Face16.ofAffine fQ hQ).N P P' R R' D C' Q' ST SQ :=
      fun hT hQ _ _ _ _ _ _ _ h => h.imp_right fun h' =>
        h' _ _ (fun y => (Face16.ofAffine_inner _ hT y).symm)
          (fun y => (Face16.ofAffine_inner _ hQ y).symm)
    simp only [CertW21, or_and_right] at h
    rcases frequently_or_distrib.mp h with h | h
    · exact isRupert_q5Edge21_or T T.f015 T.f0256 (P := 0) (C' := 5) (by decide) (by decide)
        (by decide) K hK h (gen hB hC Q5)
    rcases frequently_or_distrib.mp h with h | h
    · exact isRupert_q5Edge21_or T T.f134 T.f2346 (P := 4) (C' := 3) (by decide) (by decide)
        (by decide) K hK h (gen hE hG Q6)
    · rcases h26 with h26 | h26
      swap
      · exact isRupert_ridge21 T K hK (h.mono fun n hn => hn.1)
          (h26 _ _ (fun y => (Face16.ofAffine_inner _ hC y).symm)
            (fun y => (Face16.ofAffine_inner _ hG y).symm))
      refine isRupert_of_cert_seq21 T (P := fun v => v = .inl (6, 2) ∨ v = .inl (2, 6)) ?_ K hK
        (h.mono fun n hn => ⟨?_, hn.2⟩)
      · rintro v (rfl | rfl) -
        · exact h26
        · show NoHDNAt _ (x 6 - x 2)
          rw [← neg_sub]; exact h26.neg
      · rcases hn.1 with h | h
        · exact ⟨_, ⟨.inl (6, 2), Or.inl rfl, 1, one_ne_zero, (one_smul _ _).symm⟩, h.rimCert⟩
        · exact ⟨_, ⟨.inl (2, 6), Or.inr rfl, 1, one_ne_zero, (one_smul _ _).symm⟩, h.rimCert⟩
  · -- the four vertex lines with a quadrilateral
    exact hVq K hK h

end Minimality

end
