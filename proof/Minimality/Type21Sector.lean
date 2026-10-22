module

public import Minimality.Type21Limit
public import Minimality.Type16Sector

@[expose] public section

/-!
# Type 21: no horizontal-double-normal exception at the two-triangle views (§22.2)

Proposition 22.2 (`isRupert_of_tiltHides`) at the named views of type 21 where both faces seen
edge-on are triangles: the edges `01`, `04`, `14`, `15`, `13`, `35` (tier H's `13, 15` of `O` and
`14, 10` of `O2`, and `Y`'s `04`) and the vertex crossings `046/134`, `046/015`, `235/134`,
`235/015` (F2's `V′` and its images).  As for type 16 (`Type16Sector.lean`), every closing there
is realized on both face circles, and the limit rim of any certificate at that view has a hiding
tilt under (G1).

* `triEdge21`, `TriVtx21`, `Sec21`, `Sec21.tiltHides`.
* `isRupert_of_certL_seq21_sec`, `isRupert_of_cert_seq21_sec`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- The six edges of type 21 between two triangles, `(v, w, a, b)` for the edge `vw` between
the triangles `vwa` and `vwb`: `01` (`014`, `015`), `04` (`014`, `046`), `14` (`014`, `134`),
`15` (`015`, `135`), `13` (`134`, `135`), `35` (`135`, `235`). -/
def triEdge21 : Fin 6 → Fin 7 × Fin 7 × Fin 7 × Fin 7 :=
  ![(0, 1, 4, 5), (0, 4, 1, 6), (1, 4, 0, 3), (1, 5, 0, 3), (1, 3, 4, 5), (3, 5, 1, 2)]

/-- The vertex crossings of type 21 between two triangles: `046/134`, `046/015`, `235/134`,
`235/015` (`vtx21` 4–7). -/
def TriVtx21 (t : Fin 8) : Prop := t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7

/-- **The tilt alternative at a named view of type 21**: a two-triangle edge or vertex crossing
with (G1). -/
def Sec21 (x : Fin 7 → ℝ³) : (Fin 7 × Fin 7) ⊕ Fin 8 → Prop
  | .inl (i, j) => ∃ e : Fin 6,
      (((triEdge21 e).1 = i ∧ (triEdge21 e).2.1 = j) ∨
        ((triEdge21 e).1 = j ∧ (triEdge21 e).2.1 = i)) ∧
      G1Edge (univ.image x) (x (triEdge21 e).1) (x (triEdge21 e).2.1) (x (triEdge21 e).2.2.1)
        (x (triEdge21 e).2.2.2)
  | .inr t => TriVtx21 t ∧
      G1Vtx (univ.image x) (vtxView21 x t) (x (vtx21 t).1.1) (x (vtx21 t).1.2.1)
        (x (vtx21 t).1.2.2) (x (vtx21 t).2.1) (x (vtx21 t).2.2.1) (x (vtx21 t).2.2.2)

theorem triEdge21_det {x : Fin 7 → ℝ³} (T : Facets21 x) (e : Fin 6) :
    det3 (x (triEdge21 e).2.1 - x (triEdge21 e).1) (x (triEdge21 e).2.2.1 - x (triEdge21 e).1)
      (x (triEdge21 e).2.2.2 - x (triEdge21 e).1) ≠ 0 := by
  have nc : ∀ {i j a : Fin 7}, i ≠ j → i ≠ a → j ≠ a → cross (x j - x i) (x a - x i) ≠ 0 :=
    fun h1 h2 h3 => cross_ne_zero_of_noSeg T.inj T.noSeg h1 h2 h3
  fin_cases e <;> simp only [triEdge21, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  · exact T.f014.det3_ne (by decide) (by decide) (by decide) (by decide) (nc (by decide)
      (by decide) (by decide))
  · exact T.f014.det3_ne (by decide) (by decide) (by decide) (by decide) (nc (by decide)
      (by decide) (by decide))
  · exact T.f014.det3_ne (by decide) (by decide) (by decide) (by decide) (nc (by decide)
      (by decide) (by decide))
  · exact T.f015.det3_ne (by decide) (by decide) (by decide) (by decide) (nc (by decide)
      (by decide) (by decide))
  · exact T.f134.det3_ne (by decide) (by decide) (by decide) (by decide) (nc (by decide)
      (by decide) (by decide))
  · exact T.f135.det3_ne (by decide) (by decide) (by decide) (by decide) (nc (by decide)
      (by decide) (by decide))

theorem triEdge21_ne (e : Fin 6) :
    (triEdge21 e).1 ≠ (triEdge21 e).2.1 ∧ (triEdge21 e).2.1 ≠ (triEdge21 e).2.2.1 ∧
      (triEdge21 e).1 ≠ (triEdge21 e).2.2.1 ∧ (triEdge21 e).2.1 ≠ (triEdge21 e).2.2.2 ∧
      (triEdge21 e).1 ≠ (triEdge21 e).2.2.2 := by
  fin_cases e <;> decide

theorem triVtx21_ne {t : Fin 8} (ht : TriVtx21 t) :
    (vtx21 t).1.1 ≠ (vtx21 t).1.2.1 ∧ (vtx21 t).1.2.1 ≠ (vtx21 t).1.2.2 ∧
      (vtx21 t).1.1 ≠ (vtx21 t).1.2.2 ∧ (vtx21 t).2.1 ≠ (vtx21 t).2.2.1 ∧
      (vtx21 t).2.2.1 ≠ (vtx21 t).2.2.2 ∧ (vtx21 t).2.1 ≠ (vtx21 t).2.2.2 := by
  rcases ht with rfl | rfl | rfl | rfl <;> decide

/-- **The tilt alternative gives a hiding tilt for the limit rim** of a certificate at a view
with `Sec21`. -/
theorem Sec21.tiltHides {x : Fin 7 → ℝ³} (T : Facets21 x) {v : (Fin 7 × Fin 7) ⊕ Fin 8}
    (hv0 : view21 x v ≠ 0) (hsec : Sec21 x v) (ε : Bool) {k : ℕ} [NeZero k]
    {lab : ZMod k → Fin 7} {y : Fin 7 → ℝ³} (hy : RimCertAt y (sgnB ε • view21 y v) lab)
    (hleft : ∀ m i, 0 ≤ det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i))
      (sgnB ε • view21 x v)) :
    ∃ d, TiltHides (univ.image x) (sgnB ε • view21 x v) d (fun i => x (lab i)) := by
  have hk := hy.three
  have hlab := hy.lab_injective
  have hσ := sgnB_cases ε
  have hs := sgnB_ne_zero ε
  rcases v with ⟨i, j⟩ | t
  · obtain ⟨e, he, hpar, hG⟩ := hsec
    obtain ⟨n1, n2, n3, n4, n5⟩ := triEdge21_ne e
    set v₀ := (triEdge21 e).1
    set w₀ := (triEdge21 e).2.1
    set a₀ := (triEdge21 e).2.2.1
    set b₀ := (triEdge21 e).2.2.2
    obtain ⟨c, hc, hview, hnot⟩ : ∃ c : ℝ, (c = 1 ∨ c = -1) ∧
        sgnB ε • view21 x (.inl (i, j)) = c • (x w₀ - x v₀) ∧
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
    exact smul_ne_zero (triEdge21_det T e) (sub_ne_zero.mpr (T.inj.ne n1).symm)
  · obtain ⟨ht, hpar, hG⟩ := hsec
    obtain ⟨n1, n2, n3, n4, n5, n6⟩ := triVtx21_ne ht
    have hnot : ∀ m : ZMod k, ¬ ((lab m = (vtx21 t).1.1 ∧ lab (m + 1) = (vtx21 t).1.1) ∨
        (lab m = (vtx21 t).1.1 ∧ lab (m + 1) = (vtx21 t).1.1)) := by
      intro m h
      have e : lab m = lab (m + 1) := by rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
      exact zmod_ne_add_one (by omega) m (hlab e)
    refine exists_tiltHides_limit T.inj hk hlab (hpar.parOnly _ |>.smul hs) hnot
      ⟨T.inj.ne n1, T.inj.ne n2, T.inj.ne n3⟩ ⟨T.inj.ne n4, T.inj.ne n5, T.inj.ne n6⟩ ?_
      (hG.sigma hσ) hleft
    rw [← planeLine_eq_cross16]
    exact hv0

/-- **Lemma 18.2 for one labelled certificate, with Proposition 22.2**: as
`isRupert_of_certL_seq21`, with "no horizontal double normal at the named view, or `Sec21`". -/
theorem isRupert_of_certL_seq21_sec {x : Fin 7 → ℝ³} (T : Facets21 x)
    (hnd : ∀ v, view21 x v ≠ 0 → NoHDNAt (univ.image x) (view21 x v) ∨ Sec21 x v)
    (K : ℕ → Fin 7 → ℝ³) (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)))
    {k : ℕ} [NeZero k] (v : (Fin 7 × Fin 7) ⊕ Fin 8) (ε : Bool) (lab : ZMod k → Fin 7)
    (hc : ∃ᶠ n in atTop, RimCertAt (K n) (sgnB ε • view21 (K n) v) lab ∧
      ∀ w a b, TieInst21 x w a b → ⟪K n a - K n b, view21 (K n) w⟫ = 0) :
    IsRupert (univ.image x) := by
  obtain ⟨n₀, hn₀, -⟩ := hc.exists
  have hv : ∀ i, v ≠ .inl (i, i) := by
    rintro i rfl
    apply hn₀.ne_zero
    simp [view21]
  have hv0 := T.view21_ne_zero v hv
  have hs := sgnB_ne_zero ε
  refine isRupert_of_tendsto_rimCert_or x T.inj T.noSeg ⟨2, 0, 3, 6, T.det_ne⟩ lab
    (smul_ne_zero hs hv0) ?_ K (fun n => sgnB ε • view21 (K n) v) hK
    ((tendsto_view21 hK v).const_smul _) (hc.mono fun n hn => ⟨hn.1, fun i j e => ?_⟩)
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

/-- **A frequent certificate along a sequence of type-21 shapes, with Proposition 22.2.** -/
theorem isRupert_of_cert_seq21_sec {x : Fin 7 → ℝ³} (T : Facets21 x)
    (hnd : ∀ v, view21 x v ≠ 0 → NoHDNAt (univ.image x) (view21 x v) ∨ Sec21 x v)
    (K : ℕ → Fin 7 → ℝ³) (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)))
    (hc : ∃ᶠ n in atTop, Cert21 (K n) ∧
      ∀ w a b, TieInst21 x w a b → ⟪K n a - K n b, view21 (K n) w⟫ = 0) :
    IsRupert (univ.image x) := by
  have h : ∃ᶠ n in atTop, ∃ q : ((Fin 7 × Fin 7) ⊕ Fin 8) × Bool ×
      ((ZMod 3 → Fin 7) ⊕ (ZMod 4 → Fin 7) ⊕ (ZMod 5 → Fin 7)),
      CertL21 (K n) q.1 q.2.1 q.2.2 ∧
        ∀ w a b, TieInst21 x w a b → ⟪K n a - K n b, view21 (K n) w⟫ = 0 :=
    hc.mono fun n hn => by
      obtain ⟨v, ε, L, hL⟩ := hn.1.exists_certL
      exact ⟨(v, ε, L), hL, hn.2⟩
  obtain ⟨⟨v, ε, L⟩, hq⟩ := frequently_exists_of_finite h
  rcases L with lab | lab | lab
  · exact isRupert_of_certL_seq21_sec T hnd K hK v ε lab hq
  · exact isRupert_of_certL_seq21_sec T hnd K hK v ε lab hq
  · exact isRupert_of_certL_seq21_sec T hnd K hK v ε lab hq


/-! ### Type 21 outside the HDN set at its one-circle views and codimension 2 -/

/-- **§18.6 step 2 for type 21 with Proposition 22.2**: a type-21 shape with at most one tie at
its named views is Rupert if at each named view there is no horizontal double normal or `Sec21`
holds (a two-triangle view with (G1)). -/
theorem isRupert_type21_limit_sec {x : Fin 7 → ℝ³} (T : Facets21 x)
    (hnd : ∀ v, view21 x v ≠ 0 → NoHDNAt (univ.image x) (view21 x v) ∨ Sec21 x v)
    (htie : OneTie21 x) : IsRupert (univ.image x) := by
  obtain ⟨K, hK, hc⟩ := exists_certSeq21 T htie
  exact isRupert_of_cert_seq21_sec T hnd K hK hc

/-- The two-triangle edges of type 21 as pairs. -/
def triEdgeSet21 : Finset (Finset (Fin 7)) := {{0, 1}, {0, 4}, {1, 4}, {1, 5}, {1, 3}, {3, 5}}

theorem triEdgeSet21_mem : ∀ i j : Fin 7, ({i, j} : Finset (Fin 7)) ∈ triEdgeSet21 →
    ∃ e : Fin 6, ((triEdge21 e).1 = i ∧ (triEdge21 e).2.1 = j) ∨
      ((triEdge21 e).1 = j ∧ (triEdge21 e).2.1 = i) := by
  decide

/-- **Type 21 with Proposition 22.2, from the facets**: seven points labelled so that `014`,
`015`, `0256`, `046`, `134`, `135`, `2346`, `235` are facets (functionals negative off them) are
Rupert if, at the named views, there is no horizontal double normal or (G1) holds at a view
between two triangles: along each segment other than the six two-triangle edges no horizontal
double normal of the closing (`hnd`); along the edges `01`, `04`, `14`, `15`, `13`, `35` no
horizontal double normal or (G1) (`hEd`); along the lines of `014/0256`, `014/2346`, `135/0256`,
`135/2346` no horizontal double normal, along those of `046/134`, `046/015`, `235/134`,
`235/015` no horizontal double normal or (G1) (`hV`); and at most one tie at these views
(`OneTie21`). -/
theorem isRupert_type21_limit_facets_sec (x : Fin 7 → ℝ³) (hx : Function.Injective x)
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
    (hnd : ∀ i j : Fin 7, i ≠ j → ({i, j} : Finset (Fin 7)) ∉ triEdgeSet21 →
      NoHDNAt ((univ.image x).erase (x j)) (x j - x i))
    (hEd : HDNOrG1Edge (univ.image x) (x 0) (x 1) (x 4) (x 5) ∧
      HDNOrG1Edge (univ.image x) (x 0) (x 4) (x 1) (x 6) ∧
      HDNOrG1Edge (univ.image x) (x 1) (x 4) (x 0) (x 3) ∧
      HDNOrG1Edge (univ.image x) (x 1) (x 5) (x 0) (x 3) ∧
      HDNOrG1Edge (univ.image x) (x 1) (x 3) (x 4) (x 5) ∧
      HDNOrG1Edge (univ.image x) (x 3) (x 5) (x 1) (x 2))
    (hV : NoHDNAff (univ.image x) fA fC ∧ NoHDNAff (univ.image x) fA fG ∧
      NoHDNAff (univ.image x) fF fC ∧ NoHDNAff (univ.image x) fF fG ∧
      HDNOrG1Aff (univ.image x) fD fE (x 4) (x 0) (x 6) (x 4) (x 3) (x 1) ∧
      HDNOrG1Aff (univ.image x) fD fB (x 0) (x 4) (x 6) (x 0) (x 5) (x 1) ∧
      HDNOrG1Aff (univ.image x) fH fE (x 3) (x 5) (x 2) (x 3) (x 4) (x 1) ∧
      HDNOrG1Aff (univ.image x) fH fB (x 5) (x 3) (x 2) (x 5) (x 0) (x 1))
    (htie : OneTie21 x) : IsRupert (univ.image x) := by
  let T := Facets21.ofAffine x hx fA fB fC fD fE fF fG fH hA hB hC hD hE hF hG hH
  have hE' : ∀ e : Fin 6, HDNOrG1Edge (univ.image x) (x (triEdge21 e).1) (x (triEdge21 e).2.1)
      (x (triEdge21 e).2.2.1) (x (triEdge21 e).2.2.2) := by
    obtain ⟨e0, e1, e2, e3, e4, e5⟩ := hEd
    intro e; fin_cases e
    exacts [e0, e1, e2, e3, e4, e5]
  refine isRupert_type21_limit_sec T (fun v hv => ?_) htie
  rcases v with ⟨i, j⟩ | t
  · have hij : i ≠ j := fun h => hv (by simp [view21, h])
    by_cases hmem : ({i, j} : Finset (Fin 7)) ∈ triEdgeSet21
    · obtain ⟨e, he⟩ := triEdgeSet21_mem i j hmem
      rcases hE' e with h | h
      · left
        rcases he with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · show NoHDNAt _ (x j - x i)
          rw [← e1, ← e2]; exact h
        · show NoHDNAt _ (x j - x i)
          rw [← e1, ← e2, ← neg_sub]; exact h.neg
      · exact Or.inr ⟨e, he, h⟩
    · left
      have hji : ({j, i} : Finset (Fin 7)) ∉ triEdgeSet21 := by rwa [Finset.pair_comm]
      exact noHDNAt_of_erase (hx.ne hij) (hnd i j hij hmem)
        (by simpa only [neg_sub] using (hnd j i (Ne.symm hij) hji).neg)
  · obtain ⟨V1, V2, V3, V4, V5, V6, V7, V8⟩ := hV
    fin_cases t
    · exact Or.inl (V1 _ hv (affine_planeLine_perp fA hA (by decide) (by decide) (by decide))
        (affine_planeLine_perp' fC hC (by decide) (by decide) (by decide)))
    · exact Or.inl (V2 _ hv (affine_planeLine_perp fA hA (by decide) (by decide) (by decide))
        (affine_planeLine_perp' fG hG (by decide) (by decide) (by decide)))
    · exact Or.inl (V3 _ hv (affine_planeLine_perp fF hF (by decide) (by decide) (by decide))
        (affine_planeLine_perp' fC hC (by decide) (by decide) (by decide)))
    · exact Or.inl (V4 _ hv (affine_planeLine_perp fF hF (by decide) (by decide) (by decide))
        (affine_planeLine_perp' fG hG (by decide) (by decide) (by decide)))
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


end Minimality

end
