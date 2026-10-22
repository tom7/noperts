module

public import Minimality.Type16Limit
public import Minimality.Sector

@[expose] public section

/-!
# Type 16: no horizontal-double-normal exception at the two-triangle views (§22.2)

Proposition 22.2 (`isRupert_of_tiltHides`) at the named views of type 16 where both faces seen
edge-on are triangles: the edges `04`, `06`, `14`, `24`, `45`, `46` and the vertex crossings
`046/145`, `036/146`, `046/245`, `036/024`.  There every closing is realized on both face
circles (a triangle has no middle on the far side of its chord), so the limit rim of any
certificate at that view has a hiding tilt as soon as (G1) holds there (`G1Edge`, `G1Vtx`:
the axle is the only pair of points over one point, every other point over a support line lies
on one of the two triangles with the line's ends).  With a horizontal double normal at the view,
(G1) fails only in codimension 2 (§22.4).

* `triEdge16`, `G1Edge`, `G1Vtx`, `Sec16`: the tilt alternative at the named views.
* `Sec16.tiltHides`: the limit rim of a certificate at a view with `Sec16` has a hiding tilt.
* `isRupert_of_certL_seq_sec`, `isRupert_of_cert_seq_sec`: Lemma 18.2 with
  "no horizontal double normal, or `Sec16`" at the limit view.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### The two-triangle views of type 16 -/

/-- The six edges of type 16 between two triangles, `(v, w, a, b)` for the edge `vw` between the
triangles `vwa` and `vwb`: `04` (`024`, `046`), `06` (`036`, `046`), `14` (`145`, `146`), `24`
(`024`, `245`), `45` (`145`, `245`), `46` (`046`, `146`). -/
def triEdge16 : Fin 6 → Fin 7 × Fin 7 × Fin 7 × Fin 7 :=
  ![(0, 4, 2, 6), (0, 6, 3, 4), (1, 4, 5, 6), (2, 4, 0, 5), (4, 5, 1, 2), (4, 6, 0, 1)]

/-- The vertex crossings of type 16 between two triangles: `046/145`, `036/146`, `046/245`,
`036/024` (`vtx16` 0, 1, 3, 4). -/
def TriVtx16 (t : Fin 6) : Prop := t = 0 ∨ t = 1 ∨ t = 3 ∨ t = 4

/-- **The tilt alternative at a named view of type 16**: a two-triangle edge or vertex crossing
with (G1). -/
def Sec16 (x : Fin 7 → ℝ³) : (Fin 7 × Fin 7) ⊕ Fin 6 → Prop
  | .inl (i, j) => ∃ e : Fin 6,
      (((triEdge16 e).1 = i ∧ (triEdge16 e).2.1 = j) ∨
        ((triEdge16 e).1 = j ∧ (triEdge16 e).2.1 = i)) ∧
      G1Edge (univ.image x) (x (triEdge16 e).1) (x (triEdge16 e).2.1) (x (triEdge16 e).2.2.1)
        (x (triEdge16 e).2.2.2)
  | .inr t => TriVtx16 t ∧
      G1Vtx (univ.image x) (vtxView16 x t) (x (vtx16 t).1.1) (x (vtx16 t).1.2.1)
        (x (vtx16 t).1.2.2) (x (vtx16 t).2.1) (x (vtx16 t).2.2.1) (x (vtx16 t).2.2.2)

theorem planeLine_eq_cross16 (p₀ p₁ p₂ q₀ q₁ q₂ : ℝ³) :
    planeLine p₀ p₁ p₂ q₀ q₁ q₂ =
      cross (cross (p₁ - p₀) (p₂ - p₀)) (cross (q₁ - q₀) (q₂ - q₀)) := by
  ext i; fin_cases i <;>
    simp only [planeLine, det3_expand, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul] <;> ring

/-- A point off a facet is off the plane of three non-collinear points of the facet. -/
theorem Face16.det3_ne {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (F : Face16 x S) {i j a b : Fin 7}
    (hi : i ∈ S) (hj : j ∈ S) (ha : a ∈ S) (hb : b ∉ S)
    (hc : cross (x j - x i) (x a - x i) ≠ 0) :
    det3 (x j - x i) (x a - x i) (x b - x i) ≠ 0 := by
  set e := cross (x j - x i) (x a - x i) with he
  have hN : F.N = (⟪F.N, e⟫ / ⟪e, e⟫) • e := eq_smul_of_cross_eq_zero hc (by
    rw [he, cross_cross_eq, real_inner_comm, F.inner_sub hj hi, real_inner_comm,
      F.inner_sub ha hi, zero_smul, zero_smul, sub_zero])
  intro h0
  have k := F.hN (x b) (x i)
  rw [F.zero i hi, sub_zero, hN, real_inner_smul_left] at k
  have : ⟪e, x b - x i⟫ = 0 := h0
  rw [this, mul_zero] at k
  linarith [F.neg b hb]

theorem triEdge16_det {x : Fin 7 → ℝ³} (T : Type16 x) (e : Fin 6) :
    det3 (x (triEdge16 e).2.1 - x (triEdge16 e).1) (x (triEdge16 e).2.2.1 - x (triEdge16 e).1)
      (x (triEdge16 e).2.2.2 - x (triEdge16 e).1) ≠ 0 := by
  have nc : ∀ {i j a : Fin 7}, i ≠ j → i ≠ a → j ≠ a → cross (x j - x i) (x a - x i) ≠ 0 :=
    fun h1 h2 h3 => cross_ne_zero_of_noSeg T.inj T.noSeg h1 h2 h3
  fin_cases e <;> simp only [triEdge16, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  · exact T.t024.det3_ne (by decide) (by decide) (by decide) (by decide) (nc (by decide)
      (by decide) (by decide))
  · exact T.t036.det3_ne (by decide) (by decide) (by decide) (by decide) (nc (by decide)
      (by decide) (by decide))
  · exact T.t145.det3_ne (by decide) (by decide) (by decide) (by decide) (nc (by decide)
      (by decide) (by decide))
  · exact T.t024.det3_ne (by decide) (by decide) (by decide) (by decide) (nc (by decide)
      (by decide) (by decide))
  · exact T.t145.det3_ne (by decide) (by decide) (by decide) (by decide) (nc (by decide)
      (by decide) (by decide))
  · exact T.t046.det3_ne (by decide) (by decide) (by decide) (by decide) (nc (by decide)
      (by decide) (by decide))

theorem triEdge16_ne (e : Fin 6) :
    (triEdge16 e).1 ≠ (triEdge16 e).2.1 ∧ (triEdge16 e).2.1 ≠ (triEdge16 e).2.2.1 ∧
      (triEdge16 e).1 ≠ (triEdge16 e).2.2.1 ∧ (triEdge16 e).2.1 ≠ (triEdge16 e).2.2.2 ∧
      (triEdge16 e).1 ≠ (triEdge16 e).2.2.2 := by
  fin_cases e <;> decide

theorem triVtx16_ne {t : Fin 6} (ht : TriVtx16 t) :
    (vtx16 t).1.1 ≠ (vtx16 t).1.2.1 ∧ (vtx16 t).1.2.1 ≠ (vtx16 t).1.2.2 ∧
      (vtx16 t).1.1 ≠ (vtx16 t).1.2.2 ∧ (vtx16 t).2.1 ≠ (vtx16 t).2.2.1 ∧
      (vtx16 t).2.2.1 ≠ (vtx16 t).2.2.2 ∧ (vtx16 t).2.1 ≠ (vtx16 t).2.2.2 := by
  rcases ht with rfl | rfl | rfl | rfl <;> decide

theorem sgnB_cases (ε : Bool) : sgnB ε = 1 ∨ sgnB ε = -1 := by
  cases ε <;> simp [sgnB]

/-- **The tilt alternative gives a hiding tilt for the limit rim** of a certificate at a view
with `Sec16`. -/
theorem Sec16.tiltHides {x : Fin 7 → ℝ³} (T : Type16 x) {v : (Fin 7 × Fin 7) ⊕ Fin 6}
    (hv0 : view16 x v ≠ 0) (hsec : Sec16 x v) (ε : Bool) {k : ℕ} [NeZero k]
    {lab : ZMod k → Fin 7} {y : Fin 7 → ℝ³} (hy : RimCertAt y (sgnB ε • view16 y v) lab)
    (hleft : ∀ m i, 0 ≤ det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i))
      (sgnB ε • view16 x v)) :
    ∃ d, TiltHides (univ.image x) (sgnB ε • view16 x v) d (fun i => x (lab i)) := by
  have hk := hy.three
  have hlab := hy.lab_injective
  have hσ := sgnB_cases ε
  have hs := sgnB_ne_zero ε
  rcases v with ⟨i, j⟩ | t
  · obtain ⟨e, he, hpar, hG⟩ := hsec
    obtain ⟨n1, n2, n3, n4, n5⟩ := triEdge16_ne e
    set v₀ := (triEdge16 e).1
    set w₀ := (triEdge16 e).2.1
    set a₀ := (triEdge16 e).2.2.1
    set b₀ := (triEdge16 e).2.2.2
    -- the view is `± (w₀ − v₀)`
    obtain ⟨c, hc, hview, hnot⟩ : ∃ c : ℝ, (c = 1 ∨ c = -1) ∧
        sgnB ε • view16 x (.inl (i, j)) = c • (x w₀ - x v₀) ∧
        ∀ m : ZMod k, ¬ ((lab m = v₀ ∧ lab (m + 1) = w₀) ∨ (lab m = w₀ ∧ lab (m + 1) = v₀)) := by
      have hna := hy.not_axle (i₀ := i) (j₀ := j)
      rcases he with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · refine ⟨sgnB ε, hσ, by rw [← e1, ← e2]; rfl, fun m => ?_⟩
        rw [e1, e2]; exact hna m
      · refine ⟨-sgnB ε, by rcases hσ with h | h <;> rw [h] <;> norm_num, ?_, fun m => ?_⟩
        · show sgnB ε • (x j - x i) = _
          rw [← e1, ← e2, neg_smul, ← smul_neg, neg_sub]
        · rw [e1, e2]; exact fun h => hna m (Or.comm.mp h)
    rw [hview] at hleft ⊢
    refine exists_tiltHides_limit T.inj hk hlab (hpar.smul (by rcases hc with h | h <;> rw [h] <;>
      norm_num)) hnot (p₁ := x v₀) (q₁ := x w₀) (r₁ := x a₀) (p₂ := x v₀) (q₂ := x w₀)
      (r₂ := x b₀) ⟨T.inj.ne n1, T.inj.ne n2, T.inj.ne n3⟩ ⟨T.inj.ne n1, T.inj.ne n4, T.inj.ne n5⟩
      ?_ (hG.sigma hc) hleft
    rw [cross_cross_common]
    exact smul_ne_zero (triEdge16_det T e) (sub_ne_zero.mpr (T.inj.ne n1).symm)
  · obtain ⟨ht, hpar, hG⟩ := hsec
    obtain ⟨n1, n2, n3, n4, n5, n6⟩ := triVtx16_ne ht
    have hnot : ∀ m : ZMod k, ¬ ((lab m = (vtx16 t).1.1 ∧ lab (m + 1) = (vtx16 t).1.1) ∨
        (lab m = (vtx16 t).1.1 ∧ lab (m + 1) = (vtx16 t).1.1)) := by
      intro m h
      have e : lab m = lab (m + 1) := by rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
      exact zmod_ne_add_one (by omega) m (hlab e)
    refine exists_tiltHides_limit T.inj hk hlab ((hpar.parOnly _).smul hs) hnot
      ⟨T.inj.ne n1, T.inj.ne n2, T.inj.ne n3⟩ ⟨T.inj.ne n4, T.inj.ne n5, T.inj.ne n6⟩ ?_
      (hG.sigma hσ) hleft
    rw [← planeLine_eq_cross16]
    exact hv0

/-! ### The limit lemma with the tilt alternative -/

/-- **Lemma 18.2 for one labelled certificate, with Proposition 22.2**: as
`isRupert_of_certL_seq`, with "no horizontal double normal at the named view, or `Sec16`". -/
theorem isRupert_of_certL_seq_sec {x : Fin 7 → ℝ³} (T : Type16 x)
    (hnd : ∀ v, view16 x v ≠ 0 → NoHDNAt (univ.image x) (view16 x v) ∨ Sec16 x v)
    (K : ℕ → Fin 7 → ℝ³) (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)))
    {k : ℕ} [NeZero k] (v : (Fin 7 × Fin 7) ⊕ Fin 6) (ε : Bool) (lab : ZMod k → Fin 7)
    (hc : ∃ᶠ n in atTop, RimCertAt (K n) (sgnB ε • view16 (K n) v) lab ∧
      ∀ w a b, TieInst16 x w a b → ⟪K n a - K n b, view16 (K n) w⟫ = 0) :
    IsRupert (univ.image x) := by
  obtain ⟨n₀, hn₀, -⟩ := hc.exists
  have hv : ∀ i, v ≠ .inl (i, i) := by
    rintro i rfl
    apply hn₀.ne_zero
    simp [view16]
  have hv0 := T.view16_ne_zero v hv
  have hs := sgnB_ne_zero ε
  refine isRupert_of_tendsto_rimCert_or x T.inj T.noSeg ⟨3, 0, 5, 6, T.det_ne⟩ lab
    (smul_ne_zero hs hv0) ?_ K (fun n => sgnB ε • view16 (K n) v) hK
    ((tendsto_view16 hK v).const_smul _) (hc.mono fun n hn => ⟨hn.1, fun i j e => ?_⟩)
  · rcases hnd v hv0 with h | h
    · exact Or.inl (h.smul_view hs)
    · exact Or.inr fun hleft => h.tiltHides T hv0 ε hn₀ hleft
  · by_cases hij : lab i = lab j
    · rw [hij]
    · rw [real_inner_smul_right, real_inner_smul_right] at e
      have e' := mul_left_cancel₀ hs e
      have h := hn.2 v (lab i) (lab j) ⟨hij, hv0, by rw [inner_sub_left, e', sub_self]⟩
      rw [inner_sub_left, sub_eq_zero] at h
      simp only [real_inner_smul_right, h]

/-- **A frequent certificate along a sequence of type-16 shapes, with Proposition 22.2.** -/
theorem isRupert_of_cert_seq_sec {x : Fin 7 → ℝ³} (T : Type16 x)
    (hnd : ∀ v, view16 x v ≠ 0 → NoHDNAt (univ.image x) (view16 x v) ∨ Sec16 x v)
    (K : ℕ → Fin 7 → ℝ³) (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)))
    (hc : ∃ᶠ n in atTop, Cert16 (K n) ∧
      ∀ w a b, TieInst16 x w a b → ⟪K n a - K n b, view16 (K n) w⟫ = 0) :
    IsRupert (univ.image x) := by
  have h : ∃ᶠ n in atTop, ∃ q : ((Fin 7 × Fin 7) ⊕ Fin 6) × Bool ×
      ((ZMod 3 → Fin 7) ⊕ (ZMod 4 → Fin 7) ⊕ (ZMod 5 → Fin 7)),
      CertL16 (K n) q.1 q.2.1 q.2.2 ∧
        ∀ w a b, TieInst16 x w a b → ⟪K n a - K n b, view16 (K n) w⟫ = 0 :=
    hc.mono fun n hn => by
      obtain ⟨v, ε, L, hL⟩ := hn.1.exists_certL
      exact ⟨(v, ε, L), hL, hn.2⟩
  obtain ⟨⟨v, ε, L⟩, hq⟩ := frequently_exists_of_finite h
  rcases L with lab | lab | lab
  · exact isRupert_of_certL_seq_sec T hnd K hK v ε lab hq
  · exact isRupert_of_certL_seq_sec T hnd K hK v ε lab hq
  · exact isRupert_of_certL_seq_sec T hnd K hK v ε lab hq


/-! ### Type 16 outside the HDN set at its one-circle views and codimension 2 -/

/-- **Theorem 19.8 with Proposition 22.2**: a type-16 shape with at most one tie at its named
views is Rupert if at each named view there is no horizontal double normal or `Sec16` holds
(a two-triangle view with (G1)). -/
theorem isRupert_type16_limit_sec {x : Fin 7 → ℝ³} (T : Type16 x)
    (hnd : ∀ v, view16 x v ≠ 0 → NoHDNAt (univ.image x) (view16 x v) ∨ Sec16 x v)
    (htie : OneTie16 x) : IsRupert (univ.image x) := by
  obtain ⟨K, hK, hc⟩ := exists_certSeq16 T htie
  exact isRupert_of_cert_seq_sec T hnd K hK hc

/-- No horizontal double normal at the view `w − v`, or (G1) there for the two triangles
`vwa`, `vwb`. -/
def HDNOrG1Edge (V : Finset ℝ³) (v w a b : ℝ³) : Prop :=
  NoHDNAt V (w - v) ∨ G1Edge V v w a b

/-- At every view along the line of two planes given by affine face functions: no horizontal
double normal, or (G1) for the triangles `p₀ p₁ p₂`, `q₀ q₁ q₂` on them. -/
def HDNOrG1Aff (V : Finset ℝ³) (fP fQ : ℝ³ →ᵃ[ℝ] ℝ) (p₀ p₁ p₂ q₀ q₁ q₂ : ℝ³) : Prop :=
  ∀ u : ℝ³, u ≠ 0 → fP.linear u = 0 → fQ.linear u = 0 → NoHDNAt V u ∨ G1Vtx V u p₀ p₁ p₂ q₀ q₁ q₂

/-- The two-triangle edges of type 16 as pairs. -/
def triEdgeSet16 : Finset (Finset (Fin 7)) := {{0, 4}, {0, 6}, {1, 4}, {2, 4}, {4, 5}, {4, 6}}

theorem triEdgeSet16_mem : ∀ i j : Fin 7, ({i, j} : Finset (Fin 7)) ∈ triEdgeSet16 →
    ∃ e : Fin 6, ((triEdge16 e).1 = i ∧ (triEdge16 e).2.1 = j) ∨
      ((triEdge16 e).1 = j ∧ (triEdge16 e).2.1 = i) := by
  decide

theorem affine_planeLine_perp {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (f : ℝ³ →ᵃ[ℝ] ℝ)
    (h : ∀ i, (i ∈ S → f (x i) = 0) ∧ (i ∉ S → f (x i) < 0)) {p₀ p₁ p₂ q₀ q₁ q₂ : Fin 7}
    (h₀ : p₀ ∈ S) (h₁ : p₁ ∈ S) (h₂ : p₂ ∈ S) :
    f.linear (planeLine (x p₀) (x p₁) (x p₂) (x q₀) (x q₁) (x q₂)) = 0 := by
  set F := Face16.ofAffine f h
  rw [← Face16.ofAffine_inner f h]
  have := inner_planeLine_left (q₀ := x q₀) (q₁ := x q₁) (q₂ := x q₂)
    (F.inner_sub h₁ h₀) (F.inner_sub h₂ h₀)
  exact this

theorem affine_planeLine_perp' {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (f : ℝ³ →ᵃ[ℝ] ℝ)
    (h : ∀ i, (i ∈ S → f (x i) = 0) ∧ (i ∉ S → f (x i) < 0)) {p₀ p₁ p₂ q₀ q₁ q₂ : Fin 7}
    (k₀ : q₀ ∈ S) (k₁ : q₁ ∈ S) (k₂ : q₂ ∈ S) :
    f.linear (planeLine (x p₀) (x p₁) (x p₂) (x q₀) (x q₁) (x q₂)) = 0 := by
  set F := Face16.ofAffine f h
  rw [← Face16.ofAffine_inner f h]
  exact inner_planeLine_right (F.inner_sub k₁ k₀) (F.inner_sub k₂ k₀)

/-- **Theorem 19.8 with Proposition 22.2, from the facets**: seven points labelled so that
`0235`, `1356` (quadrilaterals), `024`, `036`, `046`, `145`, `146`, `245` are facets
(functionals negative off them) are Rupert if, at the named views, there is no horizontal double
normal or (G1) holds at a view between two triangles: along each segment other than the six
two-triangle edges no horizontal double normal of the closing (`hnd`); along the edges `04`,
`06`, `14`, `24`, `45`, `46` no horizontal double normal or (G1) (`hE`); along the lines of
`046/145`, `036/146`, `046/245`, `036/024` no horizontal double normal or (G1), along those of
`0235/046`, `1356/046` no horizontal double normal (`hV`); and at most one tie at these views
(`OneTie16`). -/
theorem isRupert_type16_limit_facets_sec (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (fA fB fC fD fE fF fG fH : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 2, 3, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 2, 3, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({1, 3, 5, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({1, 3, 5, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({0, 2, 4} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({0, 2, 4} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 3, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 3, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) < 0))
    (hF : ∀ i, (i ∈ ({1, 4, 5} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({1, 4, 5} : Finset (Fin 7)) → fF (x i) < 0))
    (hG : ∀ i, (i ∈ ({1, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({1, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hH : ∀ i, (i ∈ ({2, 4, 5} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({2, 4, 5} : Finset (Fin 7)) → fH (x i) < 0))
    (hnd : ∀ i j : Fin 7, i ≠ j → ({i, j} : Finset (Fin 7)) ∉ triEdgeSet16 →
      NoHDNAt ((univ.image x).erase (x j)) (x j - x i))
    (hEd : HDNOrG1Edge (univ.image x) (x 0) (x 4) (x 2) (x 6) ∧
      HDNOrG1Edge (univ.image x) (x 0) (x 6) (x 3) (x 4) ∧
      HDNOrG1Edge (univ.image x) (x 1) (x 4) (x 5) (x 6) ∧
      HDNOrG1Edge (univ.image x) (x 2) (x 4) (x 0) (x 5) ∧
      HDNOrG1Edge (univ.image x) (x 4) (x 5) (x 1) (x 2) ∧
      HDNOrG1Edge (univ.image x) (x 4) (x 6) (x 0) (x 1))
    (hV : HDNOrG1Aff (univ.image x) fE fF (x 0) (x 4) (x 6) (x 1) (x 4) (x 5) ∧
      HDNOrG1Aff (univ.image x) fD fG (x 0) (x 3) (x 6) (x 1) (x 4) (x 6) ∧
      NoHDNAff (univ.image x) fA fE ∧
      HDNOrG1Aff (univ.image x) fE fH (x 6) (x 4) (x 0) (x 2) (x 4) (x 5) ∧
      HDNOrG1Aff (univ.image x) fD fC (x 6) (x 3) (x 0) (x 2) (x 4) (x 0) ∧
      NoHDNAff (univ.image x) fB fE)
    (htie : OneTie16 x) : IsRupert (univ.image x) := by
  let T : Type16 x := ⟨hx, Face16.ofAffine fA hA, Face16.ofAffine fB hB, Face16.ofAffine fC hC,
    Face16.ofAffine fD hD, Face16.ofAffine fE hE, Face16.ofAffine fF hF, Face16.ofAffine fG hG,
    Face16.ofAffine fH hH⟩
  have hE' : ∀ e : Fin 6, HDNOrG1Edge (univ.image x) (x (triEdge16 e).1) (x (triEdge16 e).2.1)
      (x (triEdge16 e).2.2.1) (x (triEdge16 e).2.2.2) := by
    obtain ⟨e0, e1, e2, e3, e4, e5⟩ := hEd
    intro e; fin_cases e
    exacts [e0, e1, e2, e3, e4, e5]
  refine isRupert_type16_limit_sec T (fun v hv => ?_) htie
  rcases v with ⟨i, j⟩ | t
  · have hij : i ≠ j := fun h => hv (by simp [view16, h])
    by_cases hmem : ({i, j} : Finset (Fin 7)) ∈ triEdgeSet16
    · obtain ⟨e, he⟩ := triEdgeSet16_mem i j hmem
      rcases hE' e with h | h
      · left
        rcases he with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · show NoHDNAt _ (x j - x i)
          rw [← e1, ← e2]; exact h
        · show NoHDNAt _ (x j - x i)
          rw [← e1, ← e2, ← neg_sub]; exact h.neg
      · exact Or.inr ⟨e, he, h⟩
    · left
      have hji : ({j, i} : Finset (Fin 7)) ∉ triEdgeSet16 := by rwa [Finset.pair_comm]
      exact noHDNAt_of_erase (hx.ne hij) (hnd i j hij hmem)
        (by simpa only [neg_sub] using (hnd j i (Ne.symm hij) hji).neg)
  · obtain ⟨V1, V2, V3, V4, V5, V6⟩ := hV
    fin_cases t
    · rcases V1 _ hv (affine_planeLine_perp fE hE (by decide) (by decide) (by decide))
        (affine_planeLine_perp' fF hF (by decide)
        (by decide) (by decide)) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨Or.inl rfl, h⟩
    · rcases V2 _ hv (affine_planeLine_perp fD hD (by decide) (by decide) (by decide))
        (affine_planeLine_perp' fG hG (by decide)
        (by decide) (by decide)) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨Or.inr (Or.inl rfl), h⟩
    · exact Or.inl (V3 _ hv (affine_planeLine_perp fA hA (by decide) (by decide) (by decide))
        (affine_planeLine_perp' fE hE (by decide)
        (by decide) (by decide)))
    · rcases V4 _ hv (affine_planeLine_perp fE hE (by decide) (by decide) (by decide))
        (affine_planeLine_perp' fH hH (by decide)
        (by decide) (by decide)) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨Or.inr (Or.inr (Or.inl rfl)), h⟩
    · rcases V5 _ hv (affine_planeLine_perp fD hD (by decide) (by decide) (by decide))
        (affine_planeLine_perp' fC hC (by decide)
        (by decide) (by decide)) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨Or.inr (Or.inr (Or.inr rfl)), h⟩
    · exact Or.inl (V6 _ hv (affine_planeLine_perp fB hB (by decide) (by decide) (by decide))
        (affine_planeLine_perp' fE hE (by decide)
        (by decide) (by decide)))


end Minimality

end
