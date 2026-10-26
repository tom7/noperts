module

public import Minimality.ClassifyCert
public import Minimality.TriBridge
public import Minimality.Octahedron
public import Minimality.BadViews

@[expose] public section

/-!
# Classification of the non-simplicial 7-vertex types

`exists_sevenType`: seven points in convex position with a facet of exactly 4 of them can be
labelled `x 0, …, x 6` so that they realize the faces of one of the 29 types of
`Minimality/SevenTypes.lean`.

The proof goes through the 35 orientation signs `sig y i = ν · sign det4 (quad i)` of a
labelling `y` (`ν` normalizes the sign at `(0,1,2,4)` to `+`):
* the labelling puts the facet at `{0,1,2,3}` (`exists_labelling`);
* `Geo y` collects the geometry used: injective, the facet `{0,1,2,3}` with the other points
  strictly on one side, no three points collinear, no point in the hull of others;
* the signs of such a labelling satisfy `Classify.Hyps` except the minimality condition:
  the 3-term Grassmann–Plücker relations (`gp_of_geo`, from the polynomial identity
  `det4_gp`), convex position by signs (`tet_of_geo`, Cramer's rule `det4_sum`,
  `det4_cramer`), and the facet signs (`q1_of_geo`, `facet_det4`, from Lagrange's identity);
* `exists_canonical`: relabelling by a permutation fixing `{0,1,2,3}` acts on the signs by
  `Classify.act` (`sig_comp`), so some relabelling has lexicographically least signs;
* the finite part `Classify.allGood` (the certificate checked in the kernel) gives a type
  and a relabelling whose faces are all one-sided triples, hence facets (`realizes_of_good`).
-/

namespace Minimality.Classify

open scoped RealInnerProductSpace

/-! ### Orientation determinants of labelled points -/

/-- `det4` in coordinates. -/
theorem det4_eq (a b c d : ℝ³) : det4 a b c d =
    (b 0 - a 0) * ((c 1 - a 1) * (d 2 - a 2) - (c 2 - a 2) * (d 1 - a 1)) -
      (b 1 - a 1) * ((c 0 - a 0) * (d 2 - a 2) - (c 2 - a 2) * (d 0 - a 0)) +
      (b 2 - a 2) * ((c 0 - a 0) * (d 1 - a 1) - (c 1 - a 1) * (d 0 - a 0)) := by
  simp [det4, cross, PiLp.inner_apply, Fin.sum_univ_three]
  ring

/-- The orientation determinant of the labelled points `a b c d`. -/
noncomputable def D (y : Fin 7 → ℝ³) (a b c d : Fin 7) : ℝ := det4 (y a) (y b) (y c) (y d)

/-- `D` is alternating: permuting the arguments multiplies it by the sign. -/
theorem D_perm (y : Fin 7 → ℝ³) (p : (Fin 4 × Fin 4 × Fin 4 × Fin 4) × SignType)
    (hp : p ∈ permTable) (t : Fin 7 × Fin 7 × Fin 7 × Fin 7) :
    D y (tget t p.1.1) (tget t p.1.2.1) (tget t p.1.2.2.1) (tget t p.1.2.2.2) =
      (p.2 : ℝ) * D y t.1 t.2.1 t.2.2.1 t.2.2.2 := by
  simp only [permTable, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  first | (simp [tget, D, det4_eq]; done) | (simp [tget, D, det4_eq]; ring)

/-- The determinant of a tuple is `±` that of its sorted 4-set, `0` at a repeated point. -/
theorem D_lookup (y : Fin 7 → ℝ³) (a b c d : Fin 7) :
    D y a b c d = ((lookup a b c d).2 : ℝ) *
      D y (quad (lookup a b c d).1).1 (quad (lookup a b c d).1).2.1
        (quad (lookup a b c d).1).2.2.1 (quad (lookup a b c d).1).2.2.2 := by
  have h := lookupOK_all a b c d
  simp only [lookupOK, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at h
  generalize lookup a b c d = r at h ⊢
  rcases h with ⟨h0, hrep⟩ | ⟨p, hp, ⟨⟨⟨⟨he, ha⟩, hb⟩, hc⟩, hd⟩⟩
  · rw [h0]
    simp only [SignType.zero_eq_zero, SignType.coe_zero, zero_mul]
    rcases hrep with (((((h | h) | h) | h) | h) | h) <;> subst h <;>
      first | (simp [D, det4_eq]; done) | (simp [D, det4_eq]; ring)
  · subst ha hb hc hd
    rw [D_perm y p hp, he]

/-- The normalizing sign: that of `det4` at `(0,1,2,4)`. -/
noncomputable def nu (y : Fin 7 → ℝ³) : SignType := SignType.sign (D y 0 1 2 4)

/-- The sign vector of the labelling `y`, normalized to `+` at `(0,1,2,4)`. -/
noncomputable def sig (y : Fin 7 → ℝ³) (i : Fin 35) : SignType :=
  nu y * SignType.sign (D y (quad i).1 (quad i).2.1 (quad i).2.2.1 (quad i).2.2.2)

theorem sign_coe_signType (e : SignType) : SignType.sign (e : ℝ) = e := by
  cases e <;> simp

/-- The sign of any 4-tuple under `sig y` is `ν` times the sign of its determinant. -/
theorem fsg_sig (y : Fin 7 → ℝ³) (a b c d : Fin 7) :
    fsg (sig y) a b c d = nu y * SignType.sign (D y a b c d) := by
  rw [fsg, sig, D_lookup y a b c d, sign_mul, sign_coe_signType, mul_left_comm]

theorem mul_self_of_ne_zero {n : SignType} (hn : n ≠ 0) : n * n = 1 := by
  cases n <;> first | decide | exact (hn rfl).elim

theorem mul_mul_cancel {n : SignType} (hn : n ≠ 0) (a b : SignType) : n * a * (n * b) = a * b := by
  cases n <;> cases a <;> cases b <;> first | decide | exact (hn rfl).elim

theorem mul_cancel_left' {n : SignType} (hn : n ≠ 0) {a b : SignType} (h : n * a = n * b) :
    a = b := by
  have := congrArg (n * ·) h
  simp only [← mul_assoc, mul_self_of_ne_zero hn, one_mul] at this
  exact this

/-! ### Polynomial identities -/

/-- The 3-term Grassmann–Plücker relation. -/
theorem det4_gp (y : Fin 7 → ℝ³) (x z a b c d : Fin 7) :
    D y x z a b * D y x z c d + -(D y x z a c * D y x z b d) + D y x z a d * D y x z b c = 0 := by
  simp only [D, det4_eq]
  ring

/-- The barycentric weights `[vbcd], [avcd], [abvd], [abcv]` sum to `[abcd]`. -/
theorem det4_sum (y : Fin 7 → ℝ³) (v a b c d : Fin 7) :
    D y v b c d + D y a v c d + D y a b v d + D y a b c v = D y a b c d := by
  simp only [D, det4_eq]
  ring

/-- Cramer's rule. -/
theorem det4_cramer (y : Fin 7 → ℝ³) (v a b c d : Fin 7) (k : Fin 3) :
    D y v b c d * y a k + D y a v c d * y b k + D y a b v d * y c k + D y a b c v * y d k =
      D y a b c d * y v k := by
  fin_cases k <;>
  · simp [D, det4_eq]
    ring

/-- The inner product in coordinates. -/
theorem inner_eq3 (a b : ℝ³) : ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
  ring

theorem cross_apply (a b : ℝ³) : cross a b 0 = a 1 * b 2 - a 2 * b 1 ∧
    cross a b 1 = a 2 * b 0 - a 0 * b 2 ∧ cross a b 2 = a 0 * b 1 - a 1 * b 0 := by
  simp [cross]

/-- Lagrange's identity, in the form used for facets. -/
theorem lagrange (l u v w : ℝ³) :
    ⟪l, w⟫ * ⟪cross u v, cross u v⟫ - ⟪l, cross u v⟫ * ⟪cross u v, w⟫ =
      ⟪l, v⟫ * ⟪u, cross w (cross u v)⟫ - ⟪l, u⟫ * ⟪v, cross w (cross u v)⟫ := by
  simp only [inner_eq3, (cross_apply _ _).1, (cross_apply _ _).2.1, (cross_apply _ _).2.2]
  ring

/-! ### Sign lemmas -/

theorem sign_trich (u : ℝ) : (u < 0 ∧ SignType.sign u = -1) ∨ (u = 0 ∧ SignType.sign u = 0) ∨
    (0 < u ∧ SignType.sign u = 1) := by
  rcases lt_trichotomy u 0 with h | h | h
  · exact Or.inl ⟨h, sign_neg h⟩
  · exact Or.inr (Or.inl ⟨h, by rw [h, sign_zero]⟩)
  · exact Or.inr (Or.inr ⟨h, sign_pos h⟩)

/-- The signs of three reals with sum `0`. -/
theorem viol3_sum {u v w : ℝ} (h : u + v + w = 0) :
    viol3 (SignType.sign u) (SignType.sign v) (SignType.sign w) = false := by
  rcases sign_trich u with ⟨hu, su⟩ | ⟨hu, su⟩ | ⟨hu, su⟩ <;>
  rcases sign_trich v with ⟨hv, sv⟩ | ⟨hv, sv⟩ | ⟨hv, sv⟩ <;>
  rcases sign_trich w with ⟨hw, sw⟩ | ⟨hw, sw⟩ | ⟨hw, sw⟩ <;>
  rw [su, sv, sw] <;> first | decide | (exfalso; linarith)

theorem div_nonneg_of_sign {u w : ℝ} (hw : w ≠ 0)
    (h : SignType.sign u = 0 ∨ SignType.sign u = SignType.sign w) : 0 ≤ u / w := by
  rcases sign_trich w with ⟨hw', sw⟩ | ⟨hw', sw⟩ | ⟨hw', sw⟩
  · rcases sign_trich u with ⟨hu, su⟩ | ⟨hu, su⟩ | ⟨hu, su⟩
    · exact div_nonneg_of_nonpos hu.le hw'.le
    · rw [hu, zero_div]
    · rw [su, sw] at h; exact absurd h (by decide)
  · exact absurd hw' hw
  · rcases sign_trich u with ⟨hu, su⟩ | ⟨hu, su⟩ | ⟨hu, su⟩
    · rw [su, sw] at h; exact absurd h (by decide)
    · rw [hu, zero_div]
    · exact (div_pos hu hw').le

/-! ### The geometric hypotheses -/

/-- The geometry of a labelling used by the classification. -/
structure Geo (y : Fin 7 → ℝ³) : Prop where
  inj : Function.Injective y
  facet : ∃ φ : ℝ³ →ᵃ[ℝ] ℝ, ∀ i : Fin 7, (i.val < 4 → φ (y i) = 0) ∧ (4 ≤ i.val → φ (y i) < 0)
  ncol : ∀ a b c : Fin 7, a ≠ b → a ≠ c → b ≠ c → cross (y b - y a) (y c - y a) ≠ 0
  hull : ∀ (v : Fin 7) (S : Finset (Fin 7)), v ∉ S →
    y v ∉ convexHull ℝ ((S.image y : Finset ℝ³) : Set ℝ³)

/-- Relabelling by a permutation fixing `{0,1,2,3}` keeps the hypotheses. -/
theorem Geo.comp {y : Fin 7 → ℝ³} (hG : Geo y) {h : Fin 7 → Fin 7} (hh : Function.Injective h)
    (hq : ∀ i, (h i).val < 4 ↔ i.val < 4) : Geo (y ∘ h) where
  inj := hG.inj.comp hh
  facet := by
    obtain ⟨φ, hφ⟩ := hG.facet
    exact ⟨φ, fun i => ⟨fun hi => (hφ (h i)).1 ((hq i).2 hi),
      fun hi => (hφ (h i)).2 (by have := (hq i).1; omega)⟩⟩
  ncol a b c hab hac hbc := hG.ncol (h a) (h b) (h c) (hh.ne hab) (hh.ne hac) (hh.ne hbc)
  hull v S hv := by
    rw [← Finset.image_image]
    exact hG.hull (h v) (S.image h) (fun hm => hv (hh.mem_finset_image.mp hm))

/-- The facet `{0,1,2,3}` in signs: for a triple `abc` of it, `det4 (a,b,c,·)` vanishes on the
facet and has one nonzero sign at the other points. -/
theorem facet_det4 {y : Fin 7 → ℝ³} (hG : Geo y) {a b c : Fin 7} (ha : a.val < 4)
    (hb : b.val < 4) (hc : c.val < 4) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ s : SignType, s ≠ 0 ∧ (∀ l : Fin 7, 4 ≤ l.val → SignType.sign (D y a b c l) = s) ∧
      ∀ d : Fin 7, d.val < 4 → D y a b c d = 0 := by
  obtain ⟨φ, hφ⟩ := hG.facet
  obtain ⟨L, hL⟩ := exists_normal_of_affine φ
  set n := cross (y b - y a) (y c - y a) with hn
  have hn0 : n ≠ 0 := hG.ncol a b c hab hac hbc
  have hnn : 0 < ⟪n, n⟫ := real_inner_self_pos.mpr hn0
  have hu : ⟪L, y b - y a⟫ = 0 := by rw [← hL, (hφ b).1 hb, (hφ a).1 ha, sub_zero]
  have hv : ⟪L, y c - y a⟫ = 0 := by rw [← hL, (hφ c).1 hc, (hφ a).1 ha, sub_zero]
  -- `φ · |n|² = ⟪L, n⟫ · det4 (a, b, c, ·)`
  have key : ∀ z : Fin 7, φ (y z) * ⟪n, n⟫ = ⟪L, n⟫ * D y a b c z := by
    intro z
    have hz : φ (y z) = ⟪L, y z - y a⟫ := by rw [← hL, (hφ a).1 ha, sub_zero]
    have := lagrange L (y b - y a) (y c - y a) (y z - y a)
    rw [hu, hv, zero_mul, zero_mul, sub_zero] at this
    rw [hz, D, det4, ← hn]
    linarith
  have h4 : (4 : Fin 7).val = 4 := rfl
  have hLn : ⟪L, n⟫ ≠ 0 := by
    intro h0
    have := key 4
    rw [h0, zero_mul] at this
    have h1 := (hφ 4).2 (by rw [h4])
    nlinarith
  refine ⟨-SignType.sign ⟪L, n⟫, ?_, fun l hl => ?_, fun d hd => ?_⟩
  · simpa using hLn
  · have hk := key l
    have hlt : ⟪L, n⟫ * D y a b c l < 0 := by
      rw [← hk]; exact mul_neg_of_neg_of_pos ((hφ l).2 hl) hnn
    rcases sign_trich ⟪L, n⟫ with ⟨h1, s1⟩ | ⟨h1, s1⟩ | ⟨h1, s1⟩
    · rw [s1, sign_pos (pos_of_mul_neg_right hlt h1.le)]; decide
    · exact absurd h1 hLn
    · rw [s1, sign_neg (neg_of_mul_neg_right hlt h1.le)]
  · have hk := key d
    rw [(hφ d).1 hd, zero_mul] at hk
    exact (mul_eq_zero.mp hk.symm).resolve_left hLn

theorem nu_ne_zero {y : Fin 7 → ℝ³} (hG : Geo y) : nu y ≠ 0 := by
  obtain ⟨s, hs, hl, -⟩ := facet_det4 hG (a := 0) (b := 1) (c := 2) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  rw [nu, hl 4 (by decide)]
  exact hs

/-! ### The sign conditions of a labelling -/

/-- The Grassmann–Plücker relations in sign form. -/
theorem gp_of_geo (y : Fin 7 → ℝ³) (hn : nu y ≠ 0) (x z a b c d : Fin 7) :
    gpV (sig y) x z a b c d = false := by
  simp only [gpV, fsg_sig, mul_mul_cancel hn, ← sign_mul, ← Left.sign_neg]
  exact viol3_sum (det4_gp y x z a b c d)

/-- Convex position in sign form: no point in a tetrahedron of four others (Cramer). -/
theorem tet_of_geo {y : Fin 7 → ℝ³} (hG : Geo y) (v a b c d : Fin 7) (hva : v ≠ a) (hvb : v ≠ b)
    (hvc : v ≠ c) (hvd : v ≠ d) :
    tetV (fsg (sig y) a b c d) (fsg (sig y) v b c d) (fsg (sig y) a v c d) (fsg (sig y) a b v d)
      (fsg (sig y) a b c v) = false := by
  have hn := nu_ne_zero hG
  by_contra hne
  rw [Bool.not_eq_false] at hne
  simp only [tetV, fsg_sig, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, beq_iff_eq] at hne
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := hne
  -- the weights are nonnegative
  set D0 := D y a b c d
  have hD0 : D0 ≠ 0 := by
    intro h; apply h0; rw [h, sign_zero, mul_zero]; rfl
  have hw : ∀ u : ℝ, (nu y * SignType.sign u = 0 ∨
      nu y * SignType.sign u = nu y * SignType.sign D0) → 0 ≤ u / D0 := by
    intro u hu
    refine div_nonneg_of_sign hD0 ?_
    rcases hu with hu | hu
    · left
      rcases mul_eq_zero.mp hu with h | h
      · exact absurd h hn
      · exact h
    · exact Or.inr (mul_cancel_left' hn hu)
  -- `y v` is in the hull of `y a, y b, y c, y d`
  apply hG.hull v {a, b, c, d} (by simp [hva, hvb, hvc, hvd])
  have hsum := det4_sum y v a b c d
  have hpt : y v = ∑ i : Fin 4, (![D y v b c d / D0, D y a v c d / D0, D y a b v d / D0,
      D y a b c v / D0] i) • (![y a, y b, y c, y d] i) := by
    ext k
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp
    linarith [det4_cramer y v a b c d k]
  rw [hpt]
  refine (convex_convexHull ℝ _).sum_mem (fun i _ => ?_) ?_ (fun i _ => ?_)
  · fin_cases i
    · exact hw _ h1
    · exact hw _ h2
    · exact hw _ h3
    · exact hw _ h4
  · simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    field_simp
    linarith
  · apply subset_convexHull
    fin_cases i <;> simp

/-- The facet `{0,1,2,3}` in sign form. -/
theorem q1_of_geo {y : Fin 7 → ℝ³} (hG : Geo y) (a b c l m : Fin 7) (ha : a.val < 4)
    (hb : b.val < 4) (hc : c.val < 4) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hl : 4 ≤ l.val)
    (hm : 4 ≤ m.val) :
    fsg (sig y) a b c l ≠ .zero ∧ fsg (sig y) a b c l = fsg (sig y) a b c m := by
  obtain ⟨s, hs, hsl, -⟩ := facet_det4 hG ha hb hc hab hac hbc
  rw [fsg_sig, fsg_sig, hsl l hl, hsl m hm]
  refine ⟨fun h => ?_, rfl⟩
  rcases mul_eq_zero.mp h with h | h
  · exact nu_ne_zero hG h
  · exact hs h

/-! ### Relabelling -/

/-- The sign vector of a relabelling `y ∘ h` is `act (sig y) h`. -/
theorem sig_comp {y : Fin 7 → ℝ³} (hn : nu y ≠ 0) (h : Fin 7 → Fin 7) :
    sig (y ∘ h) = act (sig y) h := by
  funext i
  rw [act, fsg_sig, fsg_sig, mul_mul_cancel hn]
  rfl

/-- The relabellings fixing `{0,1,2,3}`. -/
def fixQ : Finset (Equiv.Perm (Fin 7)) :=
  Finset.univ.filter fun h => ∀ i, (h i).val < 4 ↔ i.val < 4

/-- Some relabelling fixing `{0,1,2,3}` has lexicographically least signs: its sign vector
satisfies all of `Hyps`. -/
theorem exists_canonical {x : Fin 7 → ℝ³} (hG : Geo x) :
    ∃ g ∈ fixQ, Geo (x ∘ g) ∧ Hyps (sig (x ∘ g)) := by
  obtain ⟨g, hg, hmin⟩ := fixQ.exists_min_image (fun g => lexOrd.map (sig (x ∘ g)))
    ⟨1, by simp [fixQ]⟩
  have hgq : ∀ i, (g i).val < 4 ↔ i.val < 4 := (Finset.mem_filter.mp hg).2
  have hGy : Geo (x ∘ g) := hG.comp g.injective hgq
  refine ⟨g, hg, hGy, ?_⟩
  have hn := nu_ne_zero hGy
  obtain ⟨s012, -, h012, h012d⟩ := facet_det4 hGy (a := 0) (b := 1) (c := 2) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨gp_of_geo _ hn, tet_of_geo hGy, ?_, ?_, q1_of_geo hGy, ?_⟩
  · rw [fsg_sig, h012d 3 (by decide), sign_zero, mul_zero]; rfl
  · rw [fsg_sig, ← nu, mul_self_of_ne_zero hn]; rfl
  · intro h hh hq hlt
    have hbij := (Finite.injective_iff_bijective).mp hh
    set e := Equiv.ofBijective h hbij
    have hge : g * e ∈ fixQ := by
      simp only [fixQ, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.Perm.coe_mul,
        Function.comp_apply]
      intro i
      rw [hgq, Equiv.ofBijective_apply, hq]
    have hle := hmin (g * e) hge
    have hcomp : x ∘ ⇑(g * e) = (x ∘ g) ∘ h := by
      funext i; simp [e]
    rw [hcomp, sig_comp hn h] at hle
    exact absurd hlt (not_lt.mpr hle)

/-! ### From one-sided triples to facets -/

/-- The affine functional `c · ⟪N, z - p⟫`. -/
noncomputable def affOf (c : ℝ) (N p : ℝ³) : ℝ³ →ᵃ[ℝ] ℝ where
  toFun z := c * ⟪N, z - p⟫
  linear := c • innerₛₗ ℝ N
  map_vadd' q v := by
    simp only [vadd_eq_add, LinearMap.smul_apply, innerₛₗ_apply_apply, smul_eq_mul]
    rw [add_sub_assoc, inner_add_right]
    ring

theorem affOf_apply (c : ℝ) (N p z : ℝ³) : affOf c N p z = c * ⟪N, z - p⟫ := rfl

/-- A face of the sign vector is a facet of the relabelled points. -/
theorem realizes_of_good {y : Fin 7 → ℝ³} (hn : nu y ≠ 0) {k : Fin 29} {π : Fin 7 → Fin 7}
    (hπ : Function.Injective π) (hf : ∀ l ∈ typeL k, FaceF (sig y) (l.map π)) :
    RealizesFaces (y ∘ π) (sevenTypeFaces k) := by
  intro f hfk
  rw [sevenTypeFaces_eq, List.mem_map] at hfk
  obtain ⟨l, hl, rfl⟩ := hfk
  obtain ⟨t0, t1, t2, -, -, -, s, hs, hj⟩ := hf l hl
  refine ⟨affOf (-((nu y * s : SignType) : ℝ)) (cross (y t1 - y t0) (y t2 - y t0)) (y t0),
    fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
  · have hm : π i ∈ l.map π := List.mem_map_of_mem (List.mem_toFinset.mp hi)
    have h0 := (hj (π i)).1 hm
    rw [fsg_sig] at h0
    have hD : D y t0 t1 t2 (π i) = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h hn
      · exact sign_eq_zero_iff.mp h
    rw [Function.comp_apply, affOf_apply]
    simp only [D, det4] at hD
    rw [hD, mul_zero]
  · have hm : π i ∉ l.map π := by
      intro hm
      obtain ⟨j, hj', hji⟩ := List.mem_map.mp hm
      exact hi (List.mem_toFinset.mpr (hπ hji ▸ hj'))
    have h1 := (hj (π i)).2 hm
    rw [fsg_sig] at h1
    have hsD : SignType.sign (D y t0 t1 t2 (π i)) = nu y * s := by
      rw [← h1, ← mul_assoc, mul_self_of_ne_zero hn, one_mul]
    rw [Function.comp_apply, affOf_apply]
    have hpos : 0 < ((nu y * s : SignType) : ℝ) * D y t0 t1 t2 (π i) := by
      rw [← hsD]
      rcases sign_trich (D y t0 t1 t2 (π i)) with ⟨h, sh⟩ | ⟨h, sh⟩ | ⟨h, sh⟩
      · rw [sh]; simp only [SignType.coe_neg_one]; linarith
      · exfalso
        rw [sh] at hsD
        rcases mul_eq_zero.mp hsD.symm with h' | h'
        · exact hn h'
        · exact hs h'
      · rw [sh]; simp only [SignType.coe_one]; linarith
    simp only [D, det4] at hpos
    linarith

/-! ### The finite part and the labelling -/

/-- **The finite part** (kernel-checked certificate): every sign vector satisfying `Hyps` has
the faces of a relabelled type. -/
theorem allGood (σ : Fin 35 → SignType) (h : Hyps σ) : Good σ :=
  check_sound cert _ cert_ok σ (fun _ _ h => by simp at h) h

/-- Label the points so that the facet `F` gets the labels `0, 1, 2, 3`. -/
theorem exists_labelling (V F : Finset ℝ³) (hV : V.card = 7) (hFV : F ⊆ V) (hF : F.card = 4) :
    ∃ x : Fin 7 → ℝ³, Function.Injective x ∧ Finset.univ.image x = V ∧
      ∀ i, (x i ∈ F ↔ i.val < 4) := by
  classical
  set L := F.toList ++ (V \ F).toList with hLdef
  have hlen : L.length = 7 := by
    rw [hLdef, List.length_append, Finset.length_toList, Finset.length_toList,
      Finset.card_sdiff_of_subset hFV, hV, hF]
  have hnd : L.Nodup := by
    rw [hLdef, List.nodup_append]
    refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, fun a ha b hb hab => ?_⟩
    rw [Finset.mem_toList] at ha hb
    exact (Finset.mem_sdiff.mp hb).2 (hab ▸ ha)
  have hF4 : F.toList.length = 4 := by rw [Finset.length_toList, hF]
  refine ⟨fun i => L[i.val]'(by omega), fun i j hij => Fin.ext ((hnd.getElem_inj_iff).mp hij),
    ?_, fun i => ?_⟩
  · refine Finset.eq_of_subset_of_card_le (fun p hp => ?_) ?_
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
      have hm : L[i.val]'(by omega) ∈ F.toList ++ (V \ F).toList := by
        rw [← hLdef]; exact List.getElem_mem _
      rw [List.mem_append, Finset.mem_toList, Finset.mem_toList] at hm
      rcases hm with hm | hm
      · exact hFV hm
      · exact (Finset.mem_sdiff.mp hm).1
    · rw [hV, Finset.card_image_of_injective _
        (fun i j hij => Fin.ext ((hnd.getElem_inj_iff).mp hij)), Finset.card_univ, Fintype.card_fin]
  · by_cases hi : i.val < 4
    · simp only [hi, iff_true]
      have := List.getElem_append_left (as := F.toList) (bs := (V \ F).toList)
        (h := by omega) (i := i.val) (h' := by rw [← hLdef]; omega)
      simp only [← hLdef] at this
      have hm := List.getElem_mem (l := F.toList) (n := i.val) (by omega)
      rw [Finset.mem_toList] at hm
      rw [this]
      exact hm
    · simp only [hi, iff_false]
      have := List.getElem_append_right (as := F.toList) (bs := (V \ F).toList)
        (h₁ := by omega) (i := i.val) (h₂ := by rw [← hLdef]; omega)
      simp only [← hLdef] at this
      rw [this]
      have hm := List.getElem_mem (l := (V \ F).toList) (n := i.val - F.toList.length)
        (by simp only [Finset.length_toList, Finset.card_sdiff_of_subset hFV, hV, hF]; omega)
      rw [Finset.mem_toList] at hm
      exact (Finset.mem_sdiff.mp hm).2

end Minimality.Classify

namespace Minimality

open Classify

/-- **Classification of the types with a quadrilateral facet**: seven points in convex
position (none in the hull of the others) with a facet containing exactly 4 of them can be
labelled `x 0, …, x 6` so that they realize the faces of one of the 29 types. (The types with
a face of 5 or 6 vertices occur too: the hypotheses do not exclude them.) -/
theorem exists_sevenType (V : Finset ℝ³) (hV : V.card = 7)
    (hvert : ∀ v ∈ V, v ∉ convexHull ℝ ((V.erase v : Finset ℝ³) : Set ℝ³))
    (F : Finset ℝ³) (hFV : F ⊆ V) (hF : F.card = 4) (hfacet : IsFacet V F) :
    ∃ k : Fin 29, ∃ x : Fin 7 → ℝ³, Function.Injective x ∧ Finset.univ.image x = V ∧
      RealizesFaces x (sevenTypeFaces k) := by
  classical
  obtain ⟨x, hx, hxV, hxF⟩ := exists_labelling V F hV hFV hF
  have hmem : ∀ i, x i ∈ V := fun i => hxV ▸ Finset.mem_image_of_mem x (Finset.mem_univ i)
  have hG : Geo x := by
    refine ⟨hx, ?_, ?_, ?_⟩
    · obtain ⟨φ, hφF, hφV⟩ := hfacet
      exact ⟨φ, fun i => ⟨fun hi => hφF _ ((hxF i).2 hi),
        fun hi => hφV _ (hmem i) (fun h => by have := (hxF i).1 h; omega)⟩⟩
    · intro a b c hab hac hbc h0
      have hba : x b - x a ≠ 0 := sub_ne_zero.mpr (hx.ne hab.symm)
      obtain ⟨p, hp, hph⟩ := exists_mem_convexHull_erase_of_collinear (hmem a) (hmem b) (hmem c)
        (hx.ne hab) (hx.ne hac) (hx.ne hbc) (eq_smul_of_cross_eq_zero hba h0)
      exact hvert p hp hph
    · intro v S hv hin
      refine hvert (x v) (hmem v) (convexHull_mono (fun p hp => ?_) hin)
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hp)
      exact Finset.mem_coe.mpr (Finset.mem_erase.mpr
        ⟨hx.ne (fun h => hv (h ▸ hs)), hmem s⟩)
  obtain ⟨g, -, hGy, hH⟩ := exists_canonical hG
  obtain ⟨k, π, hπ, hf⟩ := allGood _ hH
  refine ⟨k, (x ∘ g) ∘ π, hGy.inj.comp hπ, ?_, realizes_of_good (nu_ne_zero hGy) hπ hf⟩
  rw [← hxV, ← Finset.image_image, ← Finset.image_image,
    Finset.image_univ_of_surjective ((Finite.injective_iff_surjective).mp hπ),
    Finset.image_univ_of_surjective g.surjective]

end Minimality

end
