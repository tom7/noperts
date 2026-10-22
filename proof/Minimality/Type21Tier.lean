module

public import Minimality.Type21LiftCert
public import Minimality.EdgePair

@[expose] public section

/-!
# Type 21: the tiers Q and H of §16 (`FEWER-FACES-PROOFS.md` §16.1–16.2)

Labels as in `Type21Lemmas.lean`: `a, a', b, b', c, c', d = 0, 3, 4, 5, 1, 6, 2`,
`O = K − 2` (`F`, the cap `d`, `IsCap21`), `O2 = K − 6` (`IsCap21.O2`, labelled
`b', b, a', a, c, d = 5, 4, 3, 0, 1, 2`, the cap `c' = 6`).  `[s t] = galeD l m s t` for
Gale data `(l, m)` of the octahedron.

* **Lemma 16.1 (E-good quad edges)** — `EGoodQuad l m x x' y p p'`: `x → y` is a quad edge
  in Gale form (`|[p y]| > |[p x]|` and `|[p' y]| > |[p' x]|`, written
  `[p x] ([p x] + [p y]) < 0`, part (i)) and *E-good* (`[x' x] [x' y] > 0`, part (ii)).
  `EGoodQuad.tests`: the two facet inequalities (Lemma 9.6, `facet_lt_of_dep`) and "not bad":
  the dependency `[x' ·]` has one sign on `x, y, y'` and the other on `p, p'` (`pole_signs'`),
  which is `not_bad_of_dep` (E-good implies not bad, the remark after 16.1).
* **Tier Q** — `Type21Q`: one of the eight directed K-quad edges `0→5, 5→0, 0→6, 6→0, 4→3,
  3→4, 4→6, 6→4` of an octahedron labelled like `O` is E-good; `cert_type21_Q` (for `O`,
  through Lemma 3 of §9 in `Type21Lift.lean`) and `cert_type21_Q2` (the same for `O2`,
  i.e. the K-quad edges `05, 34, 25, 23` of `K − 6`, through `σ2`).
* **Tier H** — `Type21H`: `1 → 3` or `1 → 5` is an E-good quad edge.  The cap is then hidden
  along that edge: it is beneath the two vertical faces `134`, `135` (resp. `015`, `135`) and
  beneath or on the two faces of each far edge (`quadHidden_of_beneath`), so Lemma 16.4's
  silhouette argument is replaced by facet inequalities, and Lemma 2 (b) of §12
  (`isRupert_quad_edge_lift`) gives a passage (`cert_type21_H`; for `O2` at `1 → 4`,
  `1 → 0`: `cert_type21_H2`).

Special positions: those of the lifts (`GenPosTie`, `NoHDNEdges`), as in §9.

**Certificate form** (§18.2, §18.6 step 2): every theorem of the tier cover concludes a rim
certificate at a named view (`CertV`: a segment view or a view satisfying `L`, the named vertex
crossings) instead of Rupertness; no horizontal double normal is assumed.  The old statement
`isRupert_type21_facets` and the limit theorem are in `Type21Limit.lean`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

variable {L : ℝ³ → Prop}

/-! ### Lemma 16.1 -/

/-- **An E-good quad edge `x → y` in Gale form** (Lemma 16.1): `x'` is hidden along `x y`
(`|[p y]| > |[p x]|` and `|[p' y]| > |[p' x]|`, part (i); `[p x]` and `[p y]` have opposite
signs, so this is `[p x] ([p x] + [p y]) < 0`), and the pair of closings satisfies Lemma E
(`[x' x] [x' y] > 0`, part (ii)). -/
def EGoodQuad (l m : ℝ³ → ℝ) (x x' y p p' : ℝ³) : Prop :=
  galeD l m p x * (galeD l m p x + galeD l m p y) < 0 ∧
  galeD l m p' x * (galeD l m p' x + galeD l m p' y) < 0 ∧
  0 < galeD l m x' x * galeD l m x' y

/-- **E-good implies not bad** (the remark after Lemma 16.1): if `[x' x] [x' y] > 0`, the
dependency `[x' ·]` (normalized to be negative at `x`) is negative at `y`, `y'` and positive
at `p`, `p'` (Lemma 13.4), so `x → y` is not bad (`not_bad_of_dep`). -/
theorem not_bad_of_egood {x x' y y' p p' : ℝ³} (F : OctFacets x x' y y' p p')
    (G : GaleData x x' y y' p p') (h : 0 < galeD G.l G.m x' x * galeD G.l G.m x' y) :
    ¬ max ⟪y, y - x⟫ ⟪y', y - x⟫ ≤ min ⟪p, y - x⟫ ⟪p', y - x⟫ := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  have hxy : x ≠ y := hnd.1.2.1
  have hy : galeD G.l G.m x' y ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h; exact lt_irrefl _ h
  obtain ⟨s1, s2, s3⟩ := pole_signs' F.swap₁ (G.hl.galeD G.hm x').swap₁ (galeD_self _ _ _) hy
  rcases lt_or_gt_of_ne (show galeD G.l G.m x' x ≠ 0 by
      intro h0; rw [h0, zero_mul] at h; exact lt_irrefl _ h) with hx | hx
  · have hy' : galeD G.l G.m x' y < 0 := by nlinarith
    exact not_bad_of_dep (G.hl.galeD G.hm x') hxy (galeD_self _ _ _) hx (by linarith)
      (by nlinarith) (by nlinarith) (by nlinarith)
  · have hy' : 0 < galeD G.l G.m x' y := by nlinarith
    have anti := galeD_anti G.l G.m
    have e : ∀ t, galeD G.l G.m t x' = -galeD G.l G.m x' t := fun t => anti x' t
    exact not_bad_of_dep (G.hl.galeD' G.hm x') hxy (galeD_self _ _ _)
      (by show galeD G.l G.m x x' < 0; rw [e]; linarith)
      (by show galeD G.l G.m x x' + galeD G.l G.m y x' ≤ 0; rw [e, e]; linarith)
      (by show galeD G.l G.m y' x' ≤ 0; rw [e]; nlinarith)
      (by show 0 ≤ galeD G.l G.m p x'; rw [e]; nlinarith)
      (by show 0 ≤ galeD G.l G.m p' x'; rw [e]; nlinarith)

/-- **Lemma 16.1 as the hypotheses of Lemma 9.3**: an E-good quad edge `x → y` in Gale form
has the two facet inequalities at the faces `x' y' p`, `x' y' p'` (`x'` hidden) and is not
bad. -/
theorem EGoodQuad.tests {x x' y y' p p' : ℝ³} (F : OctFacets x x' y y' p p')
    (G : GaleData x x' y y' p p') (h : EGoodQuad G.l G.m x x' y p p') :
    F.a'b'c.f x < F.a'b'c.f y ∧ F.a'b'c'.f x < F.a'b'c'.f y ∧
      ¬ max ⟪y, y - x⟫ ⟪y', y - x⟫ ≤ min ⟪p, y - x⟫ ⟪p', y - x⟫ := by
  obtain ⟨hp, hp', he⟩ := h
  refine ⟨facet_lt_of_dep (G.hl.galeD G.hm p') F.a'b'c (by simp) (by simp) F.nodup
      (galeD_self _ _ _) hp', ?_, not_bad_of_egood F G he⟩
  exact facet_lt_of_dep (G.hl.galeD G.hm p).swap₃ F.swap₃.a'b'c (by simp) (by simp)
    F.swap₃.nodup (galeD_self _ _ _) hp

/-! ### Tier Q -/

/-- **Lemma E at `05` in case (b) of Lemma 3** (Proposition 14.2, by a direct dependency
argument): if the dependency `[4 ·]` of `O` has `[4 5] [4 0] > 0` (the edge `5 → 0` is E-good
in `O`), then `5` and `0` lie weakly on opposite sides of the plane `1 3 2` (the far corners of
the closings at `05` when the cap `2` is the far end of `0256`).  The dependency of `O2` at `4`
is `[4 ·]` with `6` replaced by `2`; its values at `0` and `5` keep their sign because `2` is
beneath `135`. -/
theorem lemmaE_far21 {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c') (hd : IsCap21 F d)
    {L : ℝ³ → ℝ} (hL : IsDep a a' b b' c c' L) (h0 : L b = 0) (hE : 0 < L b' * L a) :
    det3 (d - c) (a' - c) (b' - c) * det3 (d - c) (a' - c) (a - c) ≤ 0 := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have hLa : L a ≠ 0 := fun h => by rw [h, mul_zero] at hE; exact lt_irrefl _ hE
  obtain ⟨-, s2, s3⟩ := pole_signs' F.perm₁₂ hL.perm₁₂ h0 hLa
  obtain ⟨α, β, hα, hβ, -, hco⟩ := hd.coords'
  -- the plane `c a' d`
  set f : ℝ³ → ℝ := fun t => det3 (d - c) (a' - c) (t - c) with hfdef
  have hf : ∀ s t, f s - f t = ⟪cross (d - c) (a' - c), s - t⟫ := by
    intro s t; simp only [hfdef, det3, ← inner_sub_right]; congr 1; abel
  have fc : f c = 0 := by simp [hfdef, det3_expand]
  have fa' : f a' = 0 := by simp only [hfdef, det3_expand, PiLp.sub_apply]; ring
  have fd : f d = 0 := by simp only [hfdef, det3_expand, PiLp.sub_apply]; ring
  have r1 := hL.apply hf
  rw [fc, fa', h0] at r1
  have r2 := affine_frame hf a b' c' α β
  rw [← hco, fd] at r2
  -- the face `a' b' c` (`135`), beneath which `a`, `c'`, `d` lie
  have m1 := hL.apply F.a'b'c.hN
  rw [F.a'b'c.hP, F.a'b'c.hQ, F.a'b'c.hR, h0] at m1
  have ma := F.a'b'c.neg a (by simp) haa' hab' hac
  have mc' := F.a'b'c.neg c' (by simp) (Ne.symm ha'c') (Ne.symm hb'c') (Ne.symm hcc')
  have md := hd.a'b'c
  have m2 := affine_frame F.a'b'c.hN a b' c' α β
  rw [← hco, F.a'b'c.hQ] at m2
  -- `f a · A = −f b' · B` with `A B > 0`
  set A := (1 - α - β) * L c' - β * L a with hA
  set B := α * L c' - β * L b' with hB
  have key : f a * A + f b' * B = 0 := by
    simp only [hA, hB]; linear_combination (-β) * r1 - L c' * r2
  have hAm : A * F.a'b'c.f c' = -(L a * F.a'b'c.f d) := by
    simp only [hA]; rw [m2]; linear_combination (1 - α - β) * m1
  have hAB : 0 < A * B := by
    have hmd : F.a'b'c.f d < 0 := md
    rcases lt_or_gt_of_ne hLa with h | h
    · have hc : 0 < L c := pos_of_mul_neg_right s3 h.le
      have hc' : 0 < L c' := (pos_iff_pos_of_mul_pos s2).mp hc
      have hb' : L b' < 0 := neg_of_mul_pos_left hE h.le
      have hBp : 0 < B := by
        simp only [hB]; linarith [mul_pos hα hc', mul_pos hβ (neg_pos.mpr hb')]
      have h1 : A * F.a'b'c.f c' < 0 := by rw [hAm]; linarith [mul_pos_of_neg_of_neg h hmd]
      exact mul_pos (pos_of_mul_neg_left h1 mc'.le) hBp
    · have hc : L c < 0 := neg_of_mul_neg_right s3 h.le
      have hc' : L c' < 0 := (neg_iff_neg_of_mul_pos s2).mp hc
      have hb' : 0 < L b' := pos_of_mul_pos_left hE h.le
      have hBn : B < 0 := by
        simp only [hB]; linarith [mul_pos hα (neg_pos.mpr hc'), mul_pos hβ hb']
      have h1 : 0 < A * F.a'b'c.f c' := by rw [hAm]; linarith [mul_neg_of_pos_of_neg h hmd]
      exact mul_pos_of_neg_of_neg (neg_of_mul_pos_left h1 mc'.le) hBn
  have e : f a * A = -(f b' * B) := by linarith
  have h2 : f b' * f a * (A * B) ≤ 0 := by
    have : f b' * f a * (A * B) = -(f b' * B) ^ 2 := by
      calc f b' * f a * (A * B) = f b' * B * (f a * A) := by ring
        _ = _ := by rw [e]; ring
    rw [this]; exact neg_nonpos.mpr (sq_nonneg _)
  change f b' * f a ≤ 0
  by_contra hc
  push Not at hc
  linarith [mul_pos hc hAB]


/-- **Tier Q of §16** for an octahedron labelled like `O = K − 2` (pairs `(a, a') = (0, 3)`,
`(b, b') = (4, 5)`, `(c, c') = (1, 6)`): one of the eight directed K-quad edges
`0→5, 5→0, 0→6, 6→0, 4→3, 3→4, 4→6, 6→4` is an E-good quad edge (`EGoodQuad`). -/
def Type21Q (l m : ℝ³ → ℝ) (a a' b b' c c' : ℝ³) : Prop :=
  EGoodQuad l m a a' b' c c' ∨ EGoodQuad l m b' b a c c' ∨
  EGoodQuad l m a a' c' b b' ∨ EGoodQuad l m c' c a b b' ∨
  EGoodQuad l m b b' a' c c' ∨ EGoodQuad l m a' a b c c' ∨
  EGoodQuad l m b b' c' a a' ∨ EGoodQuad l m c' c b a a'

/-- **Tier Q for `O = K − 2`.**  If one of the K-quad edges of `O` is an E-good quad edge,
then it is a quad edge that is not bad (Lemma 16.1), Lemma 3 of §9 lifts Lemma 9.3 to `K`,
and `K` has a rim certificate (off `GenPosTie`). -/
theorem cert_type21_Q {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap21 F d) (G : GaleData a a' b b' c c')
    (hgen : GenPosTie (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hQ : Type21Q G.l G.m a a' b b' c c') :
    CertV (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L
      (SegOK21 (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) a a' b b' c c' d) := by
  rcases hQ with h | h | h | h | h | h | h | h
  · obtain ⟨h1, h2, h3⟩ := h.tests F.swap₂ G.swap₂
    exact cert_type21_05 F hd h1 h2 h3
      (lemmaE_of_dep (G.hl.galeD G.hm a').swap₂ (galeD_self _ _ _) h.2.2) hgen
  · obtain ⟨h1, h2, h3⟩ := h.tests F.perm₁₂.swap₁ G.perm₁₂.swap₁
    exact cert_type21_50 F hd h1 h2 h3
      (lemmaE_far21 F hd (G.hl.galeD G.hm b) (galeD_self _ _ _) h.2.2) hgen
  · obtain ⟨h1, h2, h3⟩ := h.tests F.perm₂₃.swap₂ G.perm₂₃.swap₂
    exact cert_type21_06 F hd h1 h2 h3
      (lemmaE_of_dep (G.hl.galeD G.hm a').perm₂₃.swap₂ (galeD_self _ _ _) h.2.2) hgen
  · obtain ⟨h1, h2, h3⟩ := h.tests F.perm₂₃.swap₂.perm₁₂ G.perm₂₃.swap₂.perm₁₂
    exact cert_type21_60 F hd h1 h2 h3
      (lemmaE_of_dep (G.hl.galeD G.hm c).perm₂₃.perm₁₂.swap₁ (galeD_self _ _ _) h.2.2) hgen
  · obtain ⟨h1, h2, h3⟩ := h.tests F.perm₁₂.swap₂ G.perm₁₂.swap₂
    exact cert_type21_43 F hd h1 h2 h3
      (lemmaE_of_dep (G.hl.galeD G.hm b').perm₁₂.swap₂ (galeD_self _ _ _) h.2.2) hgen
  · obtain ⟨h1, h2, h3⟩ := h.tests F.swap₁ G.swap₁
    exact cert_type21_34 F hd h1 h2 h3
      (lemmaE_far21 F.perm₁₂ hd.sigma1 (G.hl.galeD G.hm a).perm₁₂ (galeD_self _ _ _) h.2.2) hgen
  · obtain ⟨h1, h2, h3⟩ := h.tests F.perm₁₂.perm₂₃.swap₂ G.perm₁₂.perm₂₃.swap₂
    exact cert_type21_46 F hd h1 h2 h3
      (lemmaE_of_dep (G.hl.galeD G.hm b').perm₁₂.perm₂₃.swap₂ (galeD_self _ _ _) h.2.2) hgen
  · obtain ⟨h1, h2, h3⟩ := h.tests F.perm₁₂.perm₂₃.swap₂.perm₁₂ G.perm₁₂.perm₂₃.swap₂.perm₁₂
    exact cert_type21_64 F hd h1 h2 h3
      (lemmaE_of_dep (G.hl.galeD G.hm c).perm₁₂.perm₂₃.perm₁₂.swap₁ (galeD_self _ _ _) h.2.2)
      hgen

/-- **Tier Q for `O2 = K − 6`** (labelled `5, 4, 3, 0, 1, 2` by `σ2`; its K-quad edges are
`50, 43, 52, 32`): Gale data `G2` of `O2` with an E-good K-quad edge give a passage of `K`. -/
theorem cert_type21_Q2 {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap21 F d) (G2 : GaleData b' b a' a c d)
    (hgen : GenPosTie (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hQ : Type21Q G2.l G2.m b' b a' a c d) :
    CertV (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L
      (SegOK21 (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) a a' b b' c c' d) := by
  rw [← type21_set_O2] at hgen ⊢
  exact (cert_type21_Q hd.O2 hd.sigma2 G2 hgen hQ).monoE fun _ _ h => h.sigma2

/-! ### Tier H -/

/-- **Tier H of §16**: `1 → 3` or `1 → 5` (`c → a'` or `c → b'`) is an E-good quad edge. -/
def Type21H (l m : ℝ³ → ℝ) (a a' b b' c c' : ℝ³) : Prop :=
  EGoodQuad l m c c' a' b b' ∨ EGoodQuad l m c c' b' a a'

/-- **Tier H for `O = K − 2`** (Lemma 16.4 and Lemma 2 (a) of §9).  If `1 → 3` (or `1 → 5`)
is an E-good quad edge of `O`, the cap `2` is hidden at the view along it: it is strictly
beneath the vertical faces `134`, `135` (resp. `015`, `135`) and beneath or on both faces of
each far edge (`014`, `046` and `015`, `056`; resp. `014`, `046` and `134`, `346`), so its
image is strictly inside the shadow (`quadHidden_of_beneath`).  Then `K`'s test at that edge
is the octahedron's, which is not bad (Lemma 16.1), and `K` has a rim certificate (`CertV`). -/
theorem cert_type21_H {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap21 F d) (G : GaleData a a' b b' c c')
    (hgen : GenPosTie (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hH : Type21H G.l G.m a a' b b' c c') :
    CertV (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L
      (SegOK21 (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) a a' b b' c c' d) := by
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd'
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := hd.ne
  rcases hH with h | h
  · -- `1 → 3`: the octahedron `(c, c', a', a, b, b')`
    set F' := F.perm₂₃.perm₁₂.swap₂
    obtain ⟨h1, h2, h3⟩ := h.tests F' G.perm₂₃.perm₁₂.swap₂
    have hhid := quadHidden_of_beneath F' h1 h2 hd.a'bc hd.a'b'c
      ⟨hd.abc.le, hd.abc'.le, Or.inl hd.abc⟩ ⟨hd.ab'c.le, hd.ab'c'.le, Or.inl hd.ab'c⟩
    have e : insert d ({c, c', a', a, b, b'} : Finset ℝ³) = insert d {a, a', b, b', c, c'} := by
      ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [← e] at hgen ⊢
    exact CertV.seg (by simp) (by simp) (Ne.symm ha'c)
      (SegOK21.of_edge (by simp [Edge21, SPair]) (by spair_ne) (by spair_ne) (by spair_ne)
        (by spair_ne) (by spair_ne) (by spair_ne) (by spair_ne))
      (rimCert_quad_edge_lift_tie F' h1 h2 h3 (Or.inr hhid)
      ⟨hdc, hdc', hda', hda, hdb, hdb'⟩
      (hgen.touch_oct F'))
  · -- `1 → 5`: the octahedron `(c, c', b', b, a, a')`
    set F' := F.perm₁₂.perm₂₃.perm₁₂.swap₂
    obtain ⟨h1, h2, h3⟩ := h.tests F' G.perm₁₂.perm₂₃.perm₁₂.swap₂
    have hhid := quadHidden_of_beneath F' h1 h2 hd.ab'c hd.a'b'c
      ⟨hd.abc.le, hd.abc'.le, Or.inl hd.abc⟩ ⟨hd.a'bc.le, hd.a'bc'.le, Or.inl hd.a'bc⟩
    have e : insert d ({c, c', b', b, a, a'} : Finset ℝ³) = insert d {a, a', b, b', c, c'} := by
      ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [← e] at hgen ⊢
    exact CertV.seg (by simp) (by simp) (Ne.symm hb'c)
      (SegOK21.of_edge (by simp [Edge21, SPair]) (by spair_ne) (by spair_ne) (by spair_ne)
        (by spair_ne) (by spair_ne) (by spair_ne) (by spair_ne))
      (rimCert_quad_edge_lift_tie F' h1 h2 h3 (Or.inr hhid)
      ⟨hdc, hdc', hdb', hdb, hda, hda'⟩
      (hgen.touch_oct F'))

/-- **Tier H for `O2 = K − 6`** (`1 → 4` or `1 → 0`, the images of `1 → 3`, `1 → 5` under
`σ2`): the cap `6` is hidden, and `K` has a rim certificate (`CertV`). -/
theorem cert_type21_H2 {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap21 F d) (G2 : GaleData b' b a' a c d)
    (hgen : GenPosTie (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hH : Type21H G2.l G2.m b' b a' a c d) :
    CertV (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L
      (SegOK21 (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) a a' b b' c c' d) := by
  rw [← type21_set_O2] at hgen ⊢
  exact (cert_type21_H hd.O2 hd.sigma2 G2 hgen hH).monoE fun _ _ h => h.sigma2

end Minimality

end
