module

public import Minimality.Type21Sector
public import Minimality.Type16Edge2

@[expose] public section

/-!
# Type 21: no horizontal-double-normal exception at `06`, `46`, `25`, `23` (§22)

The certificates of the tier cover at the views along `06` and its images `46`, `25`, `23`
(under `σ1`, `σ2`, `σ2σ1`) are those of tier Q (Lemma 3 of §9 at `0 → 6` and `6 → 0`, in `K − 2`
and, by `σ2`, in `K − 6`) and the planar closing of Lemma 3 (c).  The cover records them with
their data (`QEdge21`, `CertQ21`): an edge pair with Lemma E (`QAData`: Lemma E from the
dependency `[x' ·]` of the E-good edge, `lemmaE_of_dep`), or the planar closing `K_6` with the
rim `4, 6, 2, 3`, realized on both face circles.  At the limit the edge pairs are closed by §22
(`isRupert_ePair_limit_facts`) and the planar closing by Proposition 22.2
(`isRupert_twoFace_limit`), under the codimension-2 conditions `QGen21`.  (The switch surface of
Theorem 16.30, whose certificate is at `25`, is a `NoPlaneParallel` position:
`IsCap21.not_switch`.)

* `QAData.facts`: the approximants' facts of an edge pair of tier Q.
* `QGen21`, `isRupert_qEdge21`: one edge, generic in the labels.
* The type-21 statement with these edges closed is in `Type21Ridge.lean`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### The approximants' facts -/

/-- **An edge pair of tier Q gives the facts of the limit lemma** (as `ePair_facts`). -/
theorem QAData.facts {V : Finset ℝ³} {v w a b c : ℝ³} (h : QAData V v w a b c) :
    EPairFacts V v w a b c := by
  obtain ⟨hr, hE⟩ := h
  refine ⟨?_, hE⟩
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  have tr : ∀ X : ℝ³, ⟪X, w - v⟫ = 0 → ⟪X, w⟫ = ⟪X, v⟫ := by
    intro X hX; rw [inner_sub_right] at hX; linarith
  rcases hr with ⟨hN, hR⟩ | ⟨hN, hR⟩
  · have hu : w - v ≠ 0 := by
      intro h0
      have := hR.cyc 0 2 (by decide) (by decide)
      rw [h0] at this; simp [det3] at this
    refine ⟨fun z hz => ?_, fun z hz => rimCertPts_suppIn hR hu z hz, Or.inl hN⟩
    have hl := hR.left z hz
    exact ⟨by simpa [a0, quad_0, quad_1] using hl 0, by simpa [a1, quad_1, quad_2] using hl 1,
      by simpa [a2, quad_2, quad_3] using hl 2, by simpa [a3, quad_3, quad_0] using hl 3⟩
  · have hu : w - v ≠ 0 := by
      intro h0
      have := hR.cyc 0 2 (by decide) (by decide)
      rw [h0] at this; simp [det3] at this
    refine ⟨fun z hz => ?_, fun z hz => ?_, Or.inr hN⟩
    · have hl := hR.left z hz
      have l0 := hl 0
      have l3 := hl 3
      simp only [a0, a3, quad_0, quad_1, quad_3] at l0 l3
      refine ⟨by rw [← det3_vw_both]; simpa only [sub_sub_sub_cancel_right] using l0,
        by simpa [a1, quad_1, quad_2] using hl 1, by simpa [a2, quad_2, quad_3] using hl 2, ?_⟩
      have e : det3 (v - b) (z - b) (w - v) = det3 (w - b) (z - b) (w - v) := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      rw [e]; exact l3
    · intro ℓ hℓ
      obtain ⟨i, hi⟩ := rimCertPts_suppIn hR hu z hz ℓ hℓ
      refine ⟨i, ?_⟩
      rcases zmod4_cases i with rfl | rfl | rfl | rfl
      · simp only [quad_0] at hi ⊢; rw [← tr ℓ hℓ]; exact hi
      · exact hi
      · exact hi
      · exact hi

/-! ### One edge of tier Q at the limit -/

/-- **The codimension-2 conditions at the edge `P C'`** (between the triangle `S_T ∋ P, C', R`
and the quadrilateral `S_Q ∋ P, C', D, R'`, with normals `N_T`, `N_Q`): `EdgeGen` at the view
`C' − P` (§22.4), and `P`, `C'` off the planes `R R' 1` and `R R' P'` of Lemma E. -/
def QGen21 (x : Fin 7 → ℝ³) (NT NQ : ℝ³) (P P' R R' C' : Fin 7) (ST SQ : Finset (Fin 7)) :
    Prop :=
  EdgeGen (univ.image x) (x C' - x P) (x P) (x C') (ST.image x) (SQ.image x) NT NQ ∧
  det3 (x R' - x R) (x 1 - x R) (x P - x R) ≠ 0 ∧ det3 (x R' - x R) (x 1 - x R) (x C' - x R) ≠ 0 ∧
  det3 (x R' - x R) (x P' - x R) (x P - x R) ≠ 0 ∧ det3 (x R' - x R) (x P' - x R) (x C' - x R) ≠ 0

theorem det3_lemmaE_swapAB (a b c X : ℝ³) :
    det3 (a - b) (c - b) (X - b) = -det3 (b - a) (c - a) (X - a) := by
  simp only [det3_expand, PiLp.sub_apply]; ring

/-- **A side sign of a face from an adjacent facet**: the vertices `m₀`, `m` of the face `S` lie on
one side of its edge `p q` when another facet through `p q` has both strictly beneath it. -/
theorem side_pos21 {x : Fin 7 → ℝ³} (T : Facets21 x) {S SO : Finset (Fin 7)} (F : Face16 x S)
    (FO : Face16 x SO) {p q m₀ m : Fin 7} (hp : p ∈ S) (hq : q ∈ S) (hm₀ : m₀ ∈ S) (hm : m ∈ S)
    (hpO : p ∈ SO) (hqO : q ∈ SO) (hm₀O : m₀ ∉ SO) (hmO : m ∉ SO) (hpq : p ≠ q) (hpm₀ : p ≠ m₀)
    (hqm₀ : q ≠ m₀) {j₀ : Fin 7} (hj₀ : j₀ ∉ S) :
    0 < det3 (x q - x p) (x m₀ - x p) F.N * det3 (x q - x p) (x m - x p) F.N := by
  have adj := FO.adj (p := p) (q := q) (r := m₀) (s := m) hpO hqO hm₀O hmO
  have := side_sign_of_adj (N := F.N) (NG := FO.N) (p := x p) (q := x q) (m₀ := x m₀) (m := x m)
    (F.inner_sub hq hp) (F.inner_sub hm₀ hp) (F.inner_sub hm hp)
    (cross_ne_zero_of_noSeg T.inj T.noSeg hpq hpm₀ hqm₀) (F.N_ne hp hj₀) adj.1 adj.2.1 adj.2.2
  linarith [mul_comm (det3 (x q - x p) (x m - x p) F.N) (det3 (x q - x p) (x m₀ - x p) F.N)]

set_option maxHeartbeats 1000000 in
/-- **One edge of tier Q at the limit** (§22, generic in the labels).  The edge `P C'` of type 21
lies on the triangle `S_T = {P, C', R}` and the quadrilateral `S_Q = {P, C', D, R'}` (cyclic
`P, C', D, R'`); `S_O` is the other facet through `C' D`.  If shapes `K_n → x` frequently carry
the certificates of tier Q at this edge with their data (`QE21`), then under the
codimension-2 conditions `QGen21` the limit `x` is Rupert: the edge pairs by §22
(`isRupert_ePair_limit_facts`, Lemma E from the approximants), the planar closing `K_{C'}` by
Proposition 22.2 (`isRupert_twoFace_limit`: it is realized on both face circles). -/
theorem isRupert_qEdge21 {x : Fin 7 → ℝ³} (T : Facets21 x) {P P' R R' D C' : Fin 7}
    {ST SQ SO : Finset (Fin 7)} (FT : Face16 x ST) (FQ : Face16 x SQ) (FO : Face16 x SO)
    (hlab : [P, P', R, R', D, C', 1].Nodup)
    (hT : P ∈ ST ∧ C' ∈ ST ∧ R ∈ ST ∧ R' ∉ ST ∧ D ∉ ST ∧ P' ∉ ST ∧ (1 : Fin 7) ∉ ST ∧
      ∀ i ∈ ST, i = P ∨ i = C' ∨ i = R)
    (hQ : P ∈ SQ ∧ C' ∈ SQ ∧ R' ∈ SQ ∧ D ∈ SQ ∧ R ∉ SQ ∧ P' ∉ SQ ∧ (1 : Fin 7) ∉ SQ ∧
      ∀ i ∈ SQ, i = P ∨ i = C' ∨ i = R' ∨ i = D)
    (hO : D ∈ SO ∧ C' ∈ SO ∧ P ∉ SO ∧ R' ∉ SO)
    (K : ℕ → Fin 7 → ℝ³) (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)))
    (hfreq : ∃ᶠ n in atTop, QE21 (K n) P P' R R' D C')
    (hg : QGen21 x FT.N FQ.N P P' R R' C' ST SQ) : IsRupert (univ.image x) := by
  classical
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hlab
  obtain ⟨⟨hPP', hPR, hPR', hPD, hPC', hP1⟩, ⟨hP'R, hP'R', hP'D, hP'C', hP'1⟩,
    ⟨hRR', hRD, hRC', hR1⟩, ⟨hR'D, hR'C', hR'1⟩, ⟨hDC', hD1⟩, hC'1, -⟩ := hlab
  obtain ⟨tP, tC', tR, tR', tD, tP', t1, tall⟩ := hT
  obtain ⟨qP, qC', qR', qD, qR, qP', q1, qall⟩ := hQ
  obtain ⟨oD, oC', oP, oR'⟩ := hO
  obtain ⟨hgen, c1, c2, c3, c4⟩ := hg
  have hgen' : EdgeGen (univ.image x) (x P - x C') (x C') (x P) (ST.image x) (SQ.image x)
      FT.N FQ.N := by
    have := hgen.rev; rwa [neg_sub] at this
  -- the approximants' alternatives
  have hne : ∀ᶠ n in atTop, K n P ≠ K n C' :=
    (((hK P).sub (hK C')).eventually_ne (sub_ne_zero.mpr (T.inj.ne hPC'))).mono
      fun n hn h => hn (by rw [h, sub_self])
  have hfreq' : ∃ᶠ n in atTop,
      (QAData (univ.image (K n)) (K n P) (K n C') (K n R) (K n R') (K n 1) ∨
        QAData (univ.image (K n)) (K n P) (K n C') (K n R') (K n R) (K n 1)) ∨
      (QAData (univ.image (K n)) (K n C') (K n P) (K n R) (K n R') (K n P') ∨
        QAData (univ.image (K n)) (K n C') (K n P) (K n R') (K n R) (K n P')) ∨
      (RimCertPts (univ.image (K n)) (K n P - K n C')
          (quad (K n R) (K n C') (K n D) (K n P')) ∨
        RimCertPts (univ.image (K n)) (K n P - K n C')
          (quad (K n R) (K n P') (K n D) (K n C'))) := by
    refine (hfreq.and_eventually hne).mono fun n ⟨h, hn⟩ => ?_
    rcases h with (⟨-, -, h⟩ | ⟨e, -, -⟩) | (⟨e, -, -⟩ | ⟨-, -, h | h | h | h⟩)
    · exact Or.inl h
    · exact absurd e hn
    · exact absurd e.symm hn
    · exact Or.inr (Or.inl (Or.inl h))
    · exact Or.inr (Or.inl (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  -- the face data
  have fT := FT.hf (i₀ := P) tP
  have fQ := FQ.hf (i₀ := P) qP
  have fT' := FT.hf (i₀ := C') tC'
  have fQ' := FQ.hf (i₀ := C') qC'
  have sT : ∀ i ∈ ST, ∀ j ∈ ST, ∀ v w a : Fin 7, ((v = P ∧ w = C') ∨ (v = C' ∧ w = P)) →
      a = R → i ≠ v → i ≠ w → i ≠ a → j ≠ v → j ≠ w → j ≠ a → i = j := by
    rintro i hi j - v w a hvw rfl h1 h2 h3 - - -
    rcases tall i hi with rfl | rfl | rfl
    · rcases hvw with ⟨rfl, -⟩ | ⟨-, rfl⟩ <;> contradiction
    · rcases hvw with ⟨-, rfl⟩ | ⟨rfl, -⟩ <;> contradiction
    · contradiction
  have sQ : ∀ i ∈ SQ, ∀ j ∈ SQ, ∀ v w a : Fin 7, ((v = P ∧ w = C') ∨ (v = C' ∧ w = P)) →
      a = R' → i ≠ v → i ≠ w → i ≠ a → j ≠ v → j ≠ w → j ≠ a → i = j := by
    rintro i hi j hj v w a hvw rfl h1 h2 h3 h4 h5 h6
    have hi' : i = D := by
      rcases qall i hi with rfl | rfl | rfl | rfl
      · rcases hvw with ⟨rfl, -⟩ | ⟨-, rfl⟩ <;> contradiction
      · rcases hvw with ⟨-, rfl⟩ | ⟨rfl, -⟩ <;> contradiction
      · contradiction
      · rfl
    have hj' : j = D := by
      rcases qall j hj with rfl | rfl | rfl | rfl
      · rcases hvw with ⟨rfl, -⟩ | ⟨-, rfl⟩ <;> contradiction
      · rcases hvw with ⟨-, rfl⟩ | ⟨rfl, -⟩ <;> contradiction
      · contradiction
      · rfl
    rw [hi', hj']
  have e1 : ∀ X, det3 (x R - x R') (x 1 - x R') (X - x R') =
      -det3 (x R' - x R) (x 1 - x R) (X - x R) := fun X => det3_lemmaE_swapAB _ _ _ _
  have e2 : ∀ X, det3 (x R - x R') (x P' - x R') (X - x R') =
      -det3 (x R' - x R) (x P' - x R) (X - x R) := fun X => det3_lemmaE_swapAB _ _ _ _
  rcases frequently_or_distrib.mp hfreq' with h | h
  · rcases frequently_or_distrib.mp h with h | h
    · -- `P → C'`, `a = R` on the triangle
      exact isRupert_ePair_limit_facts x T.inj T.noSeg (v := P) (w := C') (a := R) (b := R')
        (c := 1) hPC' fT fQ ⟨tP, tC', tR, tR', t1, fun i hi j hj => sT i hi j hj P C' R
          (Or.inl ⟨rfl, rfl⟩) rfl⟩
        ⟨qP, qC', qR', qR, q1, fun i hi j hj => sQ i hi j hj P C' R' (Or.inl ⟨rfl, rfl⟩) rfl⟩
        K hK (h.mono fun n hn => hn.facts) hgen ⟨c1, c2⟩
    · -- `P → C'`, `a = R'` on the quadrilateral
      exact isRupert_ePair_limit_facts x T.inj T.noSeg (v := P) (w := C') (a := R') (b := R)
        (c := 1) hPC' fQ fT
        ⟨qP, qC', qR', qR, q1, fun i hi j hj => sQ i hi j hj P C' R' (Or.inl ⟨rfl, rfl⟩) rfl⟩
        ⟨tP, tC', tR, tR', t1, fun i hi j hj => sT i hi j hj P C' R (Or.inl ⟨rfl, rfl⟩) rfl⟩
        K hK (h.mono fun n hn => hn.facts) hgen.swapF
        ⟨by rw [e1]; exact neg_ne_zero.mpr c1, by rw [e1]; exact neg_ne_zero.mpr c2⟩
  rcases frequently_or_distrib.mp h with h | h
  · rcases frequently_or_distrib.mp h with h | h
    · -- `C' → P`, `a = R`
      exact isRupert_ePair_limit_facts x T.inj T.noSeg (v := C') (w := P) (a := R) (b := R')
        (c := P') (Ne.symm hPC') fT' fQ'
        ⟨tC', tP, tR, tR', tP', fun i hi j hj => sT i hi j hj C' P R (Or.inr ⟨rfl, rfl⟩) rfl⟩
        ⟨qC', qP, qR', qR, qP', fun i hi j hj => sQ i hi j hj C' P R' (Or.inr ⟨rfl, rfl⟩) rfl⟩
        K hK (h.mono fun n hn => hn.facts) hgen' ⟨c4, c3⟩
    · -- `C' → P`, `a = R'`
      exact isRupert_ePair_limit_facts x T.inj T.noSeg (v := C') (w := P) (a := R') (b := R)
        (c := P') (Ne.symm hPC') fQ' fT'
        ⟨qC', qP, qR', qR, qP', fun i hi j hj => sQ i hi j hj C' P R' (Or.inr ⟨rfl, rfl⟩) rfl⟩
        ⟨tC', tP, tR, tR', tP', fun i hi j hj => sT i hi j hj C' P R (Or.inr ⟨rfl, rfl⟩) rfl⟩
        K hK (h.mono fun n hn => hn.facts) hgen'.swapF
        ⟨by rw [e2]; exact neg_ne_zero.mpr c4, by rw [e2]; exact neg_ne_zero.mpr c3⟩
  -- the planar closing `K_{C'}`: Proposition 22.2
  have hN := FT.N_ne tP tR'
  have hab : cross FT.N FQ.N ≠ 0 :=
    cross_normals_ne hN (FT.inner_sub tR tP) (by
      have := (fQ R).2 qR; rw [inner_sub_right]; linarith)
  have hfa : ∀ i, i ∈ ST → ⟪FT.N, x i⟫ = ⟪FT.N, x P⟫ := fun i hi => (fT i).1 hi
  have hfb : ∀ i, i ∈ SQ → ⟪FQ.N, x i⟫ = ⟪FQ.N, x P⟫ := fun i hi => (fQ i).1 hi
  have hσT : det3 (x C' - x R) (x P - x R) FT.N ≠ 0 :=
    det3_face_ne (FT.inner_sub tC' tR) (FT.inner_sub tP tR)
      (cross_ne_zero_of_noSeg T.inj T.noSeg hRC' (Ne.symm hPR) (Ne.symm hPC')) hN
  have hσT' : det3 (x R - x C') (x P - x C') FT.N ≠ 0 :=
    det3_face_ne (FT.inner_sub tR tC') (FT.inner_sub tP tC')
      (cross_ne_zero_of_noSeg T.inj T.noSeg (Ne.symm hRC') (Ne.symm hPC') (Ne.symm hPR)) hN
  have hNQ := FQ.N_ne qP qR
  have hσQ : det3 (x D - x C') (x P - x C') FQ.N ≠ 0 :=
    det3_face_ne (FQ.inner_sub qD qC') (FQ.inner_sub qP qC')
      (cross_ne_zero_of_noSeg T.inj T.noSeg (Ne.symm hDC') (Ne.symm hPC') (Ne.symm hPD)) hNQ
  have hσQ' : det3 (x C' - x D) (x P - x D) FQ.N ≠ 0 :=
    det3_face_ne (FQ.inner_sub qC' qD) (FQ.inner_sub qP qD)
      (cross_ne_zero_of_noSeg T.inj T.noSeg hDC' (Ne.symm hPD) (Ne.symm hPC')) hNQ
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  rcases frequently_or_distrib.mp h with h | h
  · have hf : ∃ᶠ n in atTop, RimCertAt (K n) ((1 : ℝ) • (K n P - K n C')) (quad R C' D P') :=
      h.mono fun n hn => by rw [one_smul]; exact rimCertAt_quad hn
    refine isRupert_twoFace_limit x T.inj (quad R C' D P') (v := C') (w := P) (Ne.symm hPC') 1
      (Or.inl rfl) K hK hf hfa hfb hab hgen'.par hgen'.g1 hgen'.dist hσT hσQ ?_ ?_
    · intro i m hi hi1 hm h1 h2
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3] at hi hi1 h1 h2 ⊢
      · rcases tall m hm with rfl | rfl | rfl
        · exact mul_self_pos.mpr hσT
        · exact absurd rfl h2
        · exact absurd rfl h1
      · exact absurd hi1 tD
      · exact absurd hi tD
      · exact absurd hi tP'
    · intro i m hi hi1 hm h1 h2
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3] at hi hi1 h1 h2 ⊢
      · exact absurd hi qR
      · rcases qall m hm with rfl | rfl | rfl | rfl
        · exact mul_self_pos.mpr hσQ
        · exact absurd rfl h1
        · exact side_pos21 T FQ FO qC' qD qP qR' oC' oD oP oR' (Ne.symm hDC') (Ne.symm hPC')
            (Ne.symm hPD) qR
        · exact absurd rfl h2
      · exact absurd hi1 qP'
      · exact absurd hi qP'
  · have hf : ∃ᶠ n in atTop, RimCertAt (K n) ((1 : ℝ) • (K n P - K n C')) (quad R P' D C') :=
      h.mono fun n hn => by rw [one_smul]; exact rimCertAt_quad hn
    refine isRupert_twoFace_limit x T.inj (quad R P' D C') (v := C') (w := P) (Ne.symm hPC') 1
      (Or.inl rfl) K hK hf hfa hfb hab hgen'.par hgen'.g1 hgen'.dist hσT' hσQ' ?_ ?_
    · intro i m hi hi1 hm h1 h2
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3] at hi hi1 h1 h2 ⊢
      · exact absurd hi1 tP'
      · exact absurd hi tP'
      · exact absurd hi tD
      · rcases tall m hm with rfl | rfl | rfl
        · exact mul_self_pos.mpr hσT'
        · exact absurd rfl h1
        · exact absurd rfl h2
    · intro i m hi hi1 hm h1 h2
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3] at hi hi1 h1 h2 ⊢
      · exact absurd hi qR
      · exact absurd hi qP'
      · rcases qall m hm with rfl | rfl | rfl | rfl
        · exact mul_self_pos.mpr hσQ'
        · exact absurd rfl h2
        · exact side_pos21 T FQ FO qD qC' qP qR' oD oC' oP oR' hDC' (Ne.symm hPD) (Ne.symm hPC')
            qR
        · exact absurd rfl h1
      · exact absurd hi1 qR

/-! ### Type 21 with the edges of tier Q closed -/

/-- The certificates of tier Q at one edge, as certificates at the view along it. -/
theorem QE21.certP {y : Fin 7 → ℝ³} {P P' R R' D C' : Fin 7} (h : QE21 y P P' R R' D C') :
    CertP21 (fun v => v = .inl (P, C') ∨ v = .inl (C', P)) y := by
  rcases h with h | h
  · exact ⟨_, ⟨.inl (P, C'), Or.inl rfl, 1, one_ne_zero, (one_smul _ _).symm⟩, h.rimCert⟩
  · exact ⟨_, ⟨.inl (C', P), Or.inr rfl, 1, one_ne_zero, (one_smul _ _).symm⟩, h.rimCert⟩

/-- **The codimension-2 conditions at an edge of tier Q, from the facet functions** (`QGen21` for
every normal of the two facets). -/
def QGenAff21 (x : Fin 7 → ℝ³) (fT fQ : ℝ³ →ᵃ[ℝ] ℝ) (P P' R R' C' : Fin 7)
    (ST SQ : Finset (Fin 7)) : Prop :=
  ∀ NT NQ : ℝ³, (∀ y, fT.linear y = ⟪NT, y⟫) → (∀ y, fQ.linear y = ⟪NQ, y⟫) →
    QGen21 x NT NQ P P' R R' C' ST SQ

/-- One edge of tier Q at the limit: no horizontal double normal there (Theorem 18.1 at the
limit), or the codimension-2 conditions (`isRupert_qEdge21`). -/
theorem isRupert_qEdge21_or {x : Fin 7 → ℝ³} (T : Facets21 x) {P P' R R' D C' : Fin 7}
    {ST SQ SO : Finset (Fin 7)} (FT : Face16 x ST) (FQ : Face16 x SQ) (FO : Face16 x SO)
    (hlab : [P, P', R, R', D, C', 1].Nodup)
    (hT : P ∈ ST ∧ C' ∈ ST ∧ R ∈ ST ∧ R' ∉ ST ∧ D ∉ ST ∧ P' ∉ ST ∧ (1 : Fin 7) ∉ ST ∧
      ∀ i ∈ ST, i = P ∨ i = C' ∨ i = R)
    (hQ : P ∈ SQ ∧ C' ∈ SQ ∧ R' ∈ SQ ∧ D ∈ SQ ∧ R ∉ SQ ∧ P' ∉ SQ ∧ (1 : Fin 7) ∉ SQ ∧
      ∀ i ∈ SQ, i = P ∨ i = C' ∨ i = R' ∨ i = D)
    (hO : D ∈ SO ∧ C' ∈ SO ∧ P ∉ SO ∧ R' ∉ SO)
    (K : ℕ → Fin 7 → ℝ³) (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)))
    (hfreq : ∃ᶠ n in atTop, QE21 (K n) P P' R R' D C' ∧
      ∀ w a b, TieInst21 x w a b → ⟪K n a - K n b, view21 (K n) w⟫ = 0)
    (hg : NoHDNAt (univ.image x) (x C' - x P) ∨ QGen21 x FT.N FQ.N P P' R R' C' ST SQ) :
    IsRupert (univ.image x) := by
  rcases hg with hn | hg
  · refine isRupert_of_cert_seq21 T (P := fun v => v = .inl (P, C') ∨ v = .inl (C', P)) ?_ K hK
      (hfreq.mono fun n hn => ⟨hn.1.certP, hn.2⟩)
    rintro v (rfl | rfl) -
    · exact hn
    · show NoHDNAt _ (x P - x C')
      rw [← neg_sub]; exact hn.neg
  · exact isRupert_qEdge21 T FT FQ FO hlab hT hQ hO K hK (hfreq.mono fun n hn => hn.1) hg

end Minimality

end
