module

public import Minimality.LimitCert
public import Mathlib.Analysis.Convex.KreinMilman

@[expose] public section

/-!
# The limit lemma with lost corners (`FEWER-FACES-PROOFS.md` §18.2 (a), (c))

`LimitCert.lean` passes a labelled rim to the limit when the corner rim of the limit shape is
given.  Here the corner rim is constructed: the shapes `K_t → K` (points `xs t : Fin n → ℝ³`)
carry one labelled rim certificate (`RimCertAt`: the labels `lab : ZMod k → Fin n` form a
strictly convex counterclockwise polygon at the view `us t`, every point lies weakly inside, the
depths are robustly unimodal), with views `us t → u`.  At `K` the labelled rim is only weakly
convex: corners may be lost (two labels over one corner, a label over an open side).

* `RimCertAt`, `RimCertAt.smul`: the frame-free certificate; positive scaling of the view.
* `SuppIn`: `y` lies in the cylinder over the hull of a polygon, in support-function form (closed
  under limits, `suppIn_of_tendsto`); `RimCertAt.suppIn`.
* `exists_cornerRim` (the rim only loses corners): a weakly convex cyclic polygon in the plane,
  not on one line, has a cyclic subsequence that lists the extreme points of its hull
  counterclockwise (the least label over each corner; Krein–Milman for the hull).
* `IsCcwPolygon.mem_side_of_mem_convexHull`: a hull point is interior or on a closed side.
* `isRobustUnimodal_of_tendsto_ties`: robust unimodality passes to a limit whose ties are ties
  along the sequence (in particular, with distinct depths).
* **`isRupert_of_tendsto_rimCert`** (Lemma 18.2 with Theorems 18.1 and 18.3): if `K` has no point
  inside a segment of two others and does not lie in a plane, the ties of the labelled depths of
  `K` are ties along the sequence, and there is no horizontal double normal at `u`, then `K` is
  Rupert.  No (G1), no corner structure and none of the tier's hypotheses at `K`.
* `frequently_exists_of_finite`: a finite pigeonhole for `∃ᶠ`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### The frame-free certificate -/

/-- **A labelled rim certificate at the view `u`** (frame-free): the labels `lab` form a strictly
convex counterclockwise polygon (determinant tests at `u`), every point lies weakly left of every
side, and the depths along `u` are robustly unimodal.  This is what the crossing tests of the
tiers prove at a shape, before the horizontal double normal is excluded. -/
structure RimCertAt {n k : ℕ} (x : Fin n → ℝ³) (u : ℝ³) (lab : ZMod k → Fin n) : Prop where
  three : 3 ≤ k
  cyc : ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 →
    0 < det3 (x (lab (i + 1)) - x (lab i)) (x (lab j) - x (lab i)) u
  left : ∀ (m : Fin n) (i : ZMod k), 0 ≤ det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) u
  robust : IsRobustUnimodal (fun i => ⟪x (lab i), u⟫)

theorem RimCertAt.smul {n k : ℕ} {x : Fin n → ℝ³} {u : ℝ³} {lab : ZMod k → Fin n}
    (h : RimCertAt x u lab) {c : ℝ} (hc : 0 < c) : RimCertAt x (c • u) lab where
  three := h.three
  cyc i j hi hj := by rw [det3_smul_right]; exact mul_pos hc (h.cyc i j hi hj)
  left m i := by rw [det3_smul_right]; exact mul_nonneg hc.le (h.left m i)
  robust := by
    simp only [real_inner_smul_right]
    exact h.robust.smul hc

theorem RimCertAt.ne_zero {n k : ℕ} {x : Fin n → ℝ³} {u : ℝ³} {lab : ZMod k → Fin n}
    (h : RimCertAt x u lab) : u ≠ 0 := by
  rintro rfl
  have := h.cyc 0 (0 - 1) (zmod_sub_one_ne h.three 0) (zmod_sub_one_ne_add_one h.three 0)
  simp [det3] at this

/-! ### Pigeonhole and limits of inequalities -/

theorem frequently_exists_of_finite {ι α : Type*} [Finite α] {l : Filter ι} {P : α → ι → Prop}
    (h : ∃ᶠ t in l, ∃ a, P a t) : ∃ a, ∃ᶠ t in l, P a t := by
  by_contra hc
  have hc' : ∀ a, ∀ᶠ t in l, ¬ P a t := fun a => not_frequently.mp fun h' => hc ⟨a, h'⟩
  exact h ((eventually_all.mpr hc').mono fun t ht ⟨a, ha⟩ => ht a ha)

theorem le_of_tendsto_frequently {ι : Type*} {l : Filter ι} {f g : ι → ℝ} {a b : ℝ}
    (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) (h : ∃ᶠ t in l, f t ≤ g t) : a ≤ b := by
  by_contra hc
  push Not at hc
  exact h ((hg.eventually_lt hf hc).mono fun t ht ht' => absurd ht' (not_le.mpr ht))

theorem eq_of_tendsto_frequently {ι : Type*} {l : Filter ι} {f g : ι → ℝ} {a b : ℝ}
    (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) (h : ∃ᶠ t in l, f t = g t) : a = b :=
  le_antisymm (le_of_tendsto_frequently hf hg (h.mono fun _ e => e.le))
    (le_of_tendsto_frequently hg hf (h.mono fun _ e => e.ge))

theorem Tendsto.det3' {ι : Type*} {l : Filter ι} {a b c : ι → ℝ³} {a₀ b₀ c₀ : ℝ³}
    (ha : Tendsto a l (𝓝 a₀)) (hb : Tendsto b l (𝓝 b₀)) (hc : Tendsto c l (𝓝 c₀)) :
    Tendsto (fun t => det3 (a t) (b t) (c t)) l (𝓝 (det3 a₀ b₀ c₀)) := by
  have co : ∀ {v : ι → ℝ³} {v₀ : ℝ³} (i : Fin 3), Tendsto v l (𝓝 v₀) →
      Tendsto (fun t => v t i) l (𝓝 (v₀ i)) := fun i h =>
    ((PiLp.continuous_apply 2 _ i).tendsto _).comp h
  simp only [det3_expand]
  exact ((((co 1 ha).mul (co 2 hb)).sub ((co 2 ha).mul (co 1 hb))).mul (co 0 hc)).add
    ((((co 2 ha).mul (co 0 hb)).sub ((co 0 ha).mul (co 2 hb))).mul (co 1 hc)) |>.add
    ((((co 0 ha).mul (co 1 hb)).sub ((co 1 ha).mul (co 0 hb))).mul (co 2 hc))

theorem Tendsto.inner' {ι : Type*} {l : Filter ι} {a b : ι → ℝ³} {a₀ b₀ : ℝ³}
    (ha : Tendsto a l (𝓝 a₀)) (hb : Tendsto b l (𝓝 b₀)) :
    Tendsto (fun t => ⟪a t, b t⟫) l (𝓝 ⟪a₀, b₀⟫) :=
  ha.inner hb

/-- **Robust unimodality in the limit, with ties**: the ties of the limit are ties along the
sequence (for instance, the limit has distinct entries, or the sequence keeps its ties). -/
theorem isRobustUnimodal_of_tendsto_ties {k : ℕ} {ι : Type*} {l : Filter ι}
    {zs : ι → ZMod k → ℝ} {z : ZMod k → ℝ}
    (hlim : ∀ i, Tendsto (fun n => zs n i) l (𝓝 (z i)))
    (hrob : ∃ᶠ n in l, IsRobustUnimodal (zs n) ∧ ∀ i j, z i = z j → zs n i = zs n j) :
    IsRobustUnimodal z where
  noPeaks B a b c d hab hbc hcd hdk h := by
    obtain ⟨h1, h2, h3, h4⟩ := h
    have ev : ∀ x y : ZMod k, z x < z y → ∀ᶠ n in l, zs n x < zs n y := fun x y hxy =>
      (hlim x).eventually_lt (hlim y) hxy
    obtain ⟨n, ⟨hn, -⟩, e1, e2, e3, e4⟩ := (hrob.and_eventually ((ev _ _ h1).and
      ((ev _ _ h2).and ((ev _ _ h3).and (ev _ _ h4))))).exists
    exact hn.noPeaks B a b c d hab hbc hcd hdk ⟨e1, e2, e3, e4⟩
  noTriple i j m hij hjm him e1 e2 := by
    obtain ⟨n, hn, ht⟩ := hrob.exists
    exact hn.noTriple i j m hij hjm him (ht i j e1) (ht j m e2)
  noLevelRun B a b c d hab hbc hcd hdk e := by
    have ev : ∀ x y : ZMod k, z x < z y → ∀ᶠ n in l, zs n x < zs n y := fun x y hxy =>
      (hlim x).eventually_lt (hlim y) hxy
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨n, ⟨hn, ht⟩, e1, e2⟩ := (hrob.and_eventually ((ev _ _ h1).and
        (ev _ _ h2))).exists
      exact (hn.noLevelRun B a b c d hab hbc hcd hdk (ht _ _ e)).1 ⟨e1, e2⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨n, ⟨hn, ht⟩, e1, e2⟩ := (hrob.and_eventually ((ev _ _ h1).and
        (ev _ _ h2))).exists
      exact (hn.noLevelRun B a b c d hab hbc hcd hdk (ht _ _ e)).2 ⟨e1, e2⟩

/-! ### Hulls in support-function form -/

/-- `y` lies in the closed cylinder along `u` over the hull of `X`, in support-function form:
every functional vanishing on `u` is at most its maximum over `X` at `y`. -/
def SuppIn {k : ℕ} (u : ℝ³) (X : ZMod k → ℝ³) (y : ℝ³) : Prop :=
  ∀ w : ℝ³, ⟪w, u⟫ = 0 → ∃ i, ⟪w, y⟫ ≤ ⟪w, X i⟫

/-- At a rotation taking `u` to `r e_z`, a vector orthogonal to `u` is a screen functional. -/
theorem inner_eq_proj_of_perp {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO3) {u : ℝ³} {r : ℝ}
    (hr : r ≠ 0) (hRu : R.toEuclideanLin u = r • ez) {w : ℝ³} (hw : ⟪w, u⟫ = 0) (y : ℝ³) :
    ⟪w, y⟫ = ⟪proj_xy (R.toEuclideanLin w), proj_xy (R.toEuclideanLin y)⟫ := by
  have h2 : (R.toEuclideanLin w) 2 = 0 := by
    have := inner_toEuclideanLin_SO3 hR w u
    rw [hRu, hw, real_inner_smul_right, inner_ez] at this
    exact (mul_eq_zero.mp this).resolve_left hr
  rw [inner_proj_xy_of_horizontal h2, inner_toEuclideanLin_SO3 hR]

theorem RimCertAt.isCcwPolygon {n k : ℕ} {x : Fin n → ℝ³} {u : ℝ³} {lab : ZMod k → Fin n}
    (h : RimCertAt x u lab) {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO3) {r : ℝ} (hr : 0 < r)
    (hRu : R.toEuclideanLin u = r • ez) :
    IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x (lab i)))) :=
  ⟨h.three, fun i j hi hj => by
    simp only [proj_rot_sub]; exact cross2_proj_rot_pos hR hr hRu (h.cyc i j hi hj)⟩

/-- **The certified rim sees every point inside** (support-function form). -/
theorem RimCertAt.suppIn {n k : ℕ} [NeZero k] {x : Fin n → ℝ³} {u : ℝ³} {lab : ZMod k → Fin n}
    (h : RimCertAt x u lab) (m : Fin n) : SuppIn u (fun i => x (lab i)) (x m) := by
  obtain ⟨R, hR, r, hr, hRu⟩ := exists_rotation_to_ez_pos u h.ne_zero
  have hp := h.isCcwPolygon hR hr hRu
  have hq : proj_xy (R.toEuclideanLin (x m)) ∈
      convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x (lab i)))) := by
    refine hp.mem_convexHull_of_left fun i => ?_
    have := h.left m i
    rw [← cross2_proj_rot hR hRu] at this
    simp only [proj_rot_sub]
    exact nonneg_of_mul_nonneg_right (by linarith) hr
  intro w hw
  obtain ⟨y', ⟨i, rfl⟩, hle⟩ := ((innerₛₗ ℝ (proj_xy (R.toEuclideanLin w))).convexOn
    (convex_convexHull ℝ _)).exists_ge_of_mem_convexHull (subset_convexHull ℝ _) hq
  refine ⟨i, ?_⟩
  rw [inner_eq_proj_of_perp hR hr.ne' hRu hw, inner_eq_proj_of_perp hR hr.ne' hRu hw]
  simpa only [innerₛₗ_apply_apply] using hle

/-- **Strict convexity for every cyclic triple** (determinant form). -/
theorem RimCertAt.cyc_all {n k : ℕ} [NeZero k] {x : Fin n → ℝ³} {u : ℝ³}
    {lab : ZMod k → Fin n} (h : RimCertAt x u lab) {a b c : ZMod k} (hc : CycBetween a b c) :
    0 < det3 (x (lab b) - x (lab a)) (x (lab c) - x (lab a)) u := by
  obtain ⟨R, hR, r, hr, hRu⟩ := exists_rotation_to_ez_pos u h.ne_zero
  have := (h.isCcwPolygon hR hr hRu).cross2_pos_of_cycBetween hc
  rw [← cross2_proj_rot hR hRu, ← proj_rot_sub, ← proj_rot_sub]
  exact mul_pos hr this

theorem tendsto_perp {ι : Type*} {l : Filter ι} {us : ι → ℝ³} {u w : ℝ³} (hu : u ≠ 0)
    (hus : Tendsto us l (𝓝 u)) (hw : ⟪w, u⟫ = 0) :
    Tendsto (fun t => w - (⟪w, us t⟫ / ⟪us t, us t⟫) • us t) l (𝓝 w) := by
  have huu : ⟪u, u⟫ ≠ 0 := (real_inner_self_pos.mpr hu).ne'
  have h1 : Tendsto (fun t => ⟪w, us t⟫ / ⟪us t, us t⟫) l (𝓝 (⟪w, u⟫ / ⟪u, u⟫)) :=
    (tendsto_const_nhds.inner hus).div (hus.inner hus) huu
  have h2 := h1.smul hus
  rw [hw, zero_div, zero_smul] at h2
  simpa using tendsto_const_nhds.sub h2

/-- **Hulls pass to limits** (Lemma 18.2 (a): every vertex of `K` projects into the hull of the
labels). -/
theorem suppIn_of_tendsto {k : ℕ} [NeZero k] {ι : Type*} {l : Filter ι} {us : ι → ℝ³} {u : ℝ³}
    {Xs : ι → ZMod k → ℝ³} {X : ZMod k → ℝ³} {ys : ι → ℝ³} {y : ℝ³} (hu : u ≠ 0)
    (hus : Tendsto us l (𝓝 u)) (hX : ∀ i, Tendsto (fun t => Xs t i) l (𝓝 (X i)))
    (hy : Tendsto ys l (𝓝 y)) (h : ∃ᶠ t in l, SuppIn (us t) (Xs t) (ys t)) : SuppIn u X y := by
  intro w hw
  set ws := fun t => w - (⟪w, us t⟫ / ⟪us t, us t⟫) • us t
  have hws : Tendsto ws l (𝓝 w) := tendsto_perp hu hus hw
  have hperp : ∀ᶠ t in l, ⟪ws t, us t⟫ = 0 := by
    have huu : ⟪u, u⟫ ≠ 0 := (real_inner_self_pos.mpr hu).ne'
    filter_upwards [(hus.inner hus).eventually_ne huu] with t ht
    simp only [ws, inner_sub_left, real_inner_smul_left]
    field_simp; ring
  have hfreq : ∃ᶠ t in l, ∃ i, ⟪ws t, ys t⟫ ≤ ⟪ws t, Xs t i⟫ :=
    (h.and_eventually hperp).mono fun t ⟨ht, hp⟩ => ht _ hp
  obtain ⟨i, hi⟩ := frequently_exists_of_finite hfreq
  exact ⟨i, le_of_tendsto_frequently (hws.inner hy) (hws.inner (hX i)) hi⟩

/-- **Weak convexity in the limit**: the labelled rim of `K` is weakly counterclockwise. -/
theorem cyc_nonneg_of_tendsto {n k : ℕ} [NeZero k] {ι : Type*} {l : Filter ι}
    {xs : ι → Fin n → ℝ³} {x : Fin n → ℝ³} {us : ι → ℝ³} {u : ℝ³} {lab : ZMod k → Fin n}
    (hxs : ∀ m, Tendsto (fun t => xs t m) l (𝓝 (x m))) (hus : Tendsto us l (𝓝 u))
    (h : ∃ᶠ t in l, RimCertAt (xs t) (us t) lab) {a b c : ZMod k} (hc : CycBetween a b c) :
    0 ≤ det3 (x (lab b) - x (lab a)) (x (lab c) - x (lab a)) u :=
  le_of_tendsto_frequently tendsto_const_nhds
    (Tendsto.det3' ((hxs _).sub (hxs _)) ((hxs _).sub (hxs _)) hus)
    (h.mono fun _ ht => (ht.cyc_all hc).le)


/-! ### Cyclic order by values, and enumerations -/

theorem zmod_val_sub_cases {k : ℕ} [NeZero k] (i j : ZMod k) :
    (j - i).val = if i.val ≤ j.val then j.val - i.val else j.val + k - i.val := by
  split_ifs with h
  · exact ZMod.val_sub h
  · have hi := ZMod.val_lt i
    have e : j - i = ((j.val + k - i.val : ℕ) : ZMod k) := by
      rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self, ZMod.natCast_zmod_val,
        ZMod.natCast_zmod_val]
      ring
    rw [e, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]

/-- **Cyclic order by values**: `j` lies between `i` and `l` iff the values are in one of the
three rotations of increasing order. -/
theorem cycBetween_iff_val {k : ℕ} [NeZero k] {i j l : ZMod k} :
    CycBetween i j l ↔ (i.val < j.val ∧ j.val < l.val) ∨ (j.val < l.val ∧ l.val < i.val) ∨
      (l.val < i.val ∧ i.val < j.val) := by
  have hi := ZMod.val_lt i; have hj := ZMod.val_lt j; have hl := ZMod.val_lt l
  unfold CycBetween
  rw [zmod_val_sub_cases i j, zmod_val_sub_cases i l]
  split_ifs <;> omega

theorem cycBetween_of_val_mono {k k' : ℕ} [NeZero k] [NeZero k'] {σ : ZMod k' → ZMod k}
    (hσ : ∀ j j' : ZMod k', j.val < j'.val → (σ j).val < (σ j').val) {i j l : ZMod k'}
    (h : CycBetween i j l) : CycBetween (σ i) (σ j) (σ l) := by
  rw [cycBetween_iff_val] at h ⊢
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨hσ _ _ h1, hσ _ _ h2⟩
  · exact Or.inr (Or.inl ⟨hσ _ _ h1, hσ _ _ h2⟩)
  · exact Or.inr (Or.inr ⟨hσ _ _ h1, hσ _ _ h2⟩)

/-- A side and any third corner are in cyclic order. -/
theorem cycBetween_add_one {k : ℕ} [NeZero k] (hk : 3 ≤ k) {a b : ZMod k} (h1 : b ≠ a)
    (h2 : b ≠ a + 1) : CycBetween a (a + 1) b := by
  have e1 : (a + 1 - a : ZMod k) = ((1 : ℕ) : ZMod k) := by push_cast; ring
  have v1 : (a + 1 - a : ZMod k).val = 1 := by
    rw [e1, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have v0 : (b - a).val ≠ 0 := fun h => h1 (sub_eq_zero.mp ((ZMod.val_eq_zero _).mp h))
  have v2 : (b - a).val ≠ 1 := by
    intro h
    apply h2
    have : b - a = ((1 : ℕ) : ZMod k) := by
      rw [← ZMod.natCast_zmod_val (b - a), h]
    rw [← sub_eq_iff_eq_add', this, Nat.cast_one]
  unfold CycBetween
  rw [v1]
  omega

/-- **The increasing enumeration** of a nonempty set of positions. -/
theorem exists_enum {k : ℕ} [NeZero k] (S : Finset (ZMod k)) [NeZero S.card] :
    ∃ σ : ZMod S.card → ZMod k, (∀ j, σ j ∈ S) ∧ (∀ i ∈ S, ∃ j, σ j = i) ∧
      ∀ j j' : ZMod S.card, j.val < j'.val → (σ j).val < (σ j').val := by
  classical
  set T := S.image ZMod.val
  have hT : T.card = S.card := card_image_of_injective _ (ZMod.val_injective k)
  set e := T.orderEmbOfFin hT
  have he : ∀ f, ∃ i ∈ S, i.val = e f := fun f => by
    obtain ⟨i, hi, h⟩ := mem_image.mp (T.orderEmbOfFin_mem hT f)
    exact ⟨i, hi, h⟩
  have hval : ∀ f, ((e f : ℕ) : ZMod k).val = e f := fun f => by
    obtain ⟨i, -, h⟩ := he f
    rw [← h, ZMod.natCast_zmod_val]
  refine ⟨fun j => ((e ⟨j.val, ZMod.val_lt j⟩ : ℕ) : ZMod k), fun j => ?_, fun i hi => ?_,
    fun j j' h => ?_⟩
  · obtain ⟨i, hi, h⟩ := he ⟨j.val, ZMod.val_lt j⟩
    show ((e ⟨j.val, ZMod.val_lt j⟩ : ℕ) : ZMod k) ∈ S
    rw [← h, ZMod.natCast_zmod_val]; exact hi
  · have : i.val ∈ Set.range e := by
      rw [T.range_orderEmbOfFin hT]; exact mem_image_of_mem _ hi
    obtain ⟨f, hf⟩ := this
    refine ⟨(f.val : ZMod S.card), ?_⟩
    have hv : ((f.val : ℕ) : ZMod S.card).val = f.val := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt f.isLt]
    simp only [hv, Fin.eta, hf, ZMod.natCast_zmod_val]
  · simp only [hval]
    exact e.strictMono (Fin.mk_lt_mk.mpr h)

/-! ### Extreme points in the plane -/

theorem eq_smul_of_cross2_eq_zero {d v : ℝ²} (hd : d ≠ 0) (h : cross2 d v = 0) :
    v = (⟪v, d⟫ / ⟪d, d⟫) • d := by
  have hdd : ⟪d, d⟫ ≠ 0 := (real_inner_self_pos.mpr hd).ne'
  have hA : ⟪v, d⟫ = v 0 * d 0 + v 1 * d 1 := by
    simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]; ring
  have hB : ⟪d, d⟫ = d 0 * d 0 + d 1 * d 1 := by
    simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]
  rw [hB] at hdd
  simp only [cross2] at h
  ext i; fin_cases i
  · show v 0 = (⟪v, d⟫ / ⟪d, d⟫) * d 0
    rw [hA, hB, div_mul_eq_mul_div, eq_div_iff hdd]; linear_combination (-(d 1)) * h
  · show v 1 = (⟪v, d⟫ / ⟪d, d⟫) * d 1
    rw [hA, hB, div_mul_eq_mul_div, eq_div_iff hdd]; linear_combination (d 0) * h

/-- **Three distinct extreme points are not collinear.** -/
theorem cross2_ne_zero_of_extremePoints {A : Set ℝ²} {a b c : ℝ²}
    (ha : a ∈ A.extremePoints ℝ) (hb : b ∈ A.extremePoints ℝ) (hc : c ∈ A.extremePoints ℝ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : cross2 (b - a) (c - a) ≠ 0 := by
  intro h
  have hd : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  set t := ⟪c - a, b - a⟫ / ⟪b - a, b - a⟫
  have hct : c = a + t • (b - a) := by
    have := eq_smul_of_cross2_eq_zero hd h
    rw [← this]; abel
  have hA : ∀ {x : ℝ²}, x ∈ A.extremePoints ℝ → x ∈ A := fun h => extremePoints_subset h
  rcases lt_trichotomy t 0 with ht | ht | ht
  · -- `a` between `b` and `c`
    have h1 : 0 < 1 - t := by linarith
    have := (mem_extremePoints.mp ha).2 b (hA hb) c (hA hc)
      ⟨-t / (1 - t), 1 / (1 - t), div_pos (by linarith) h1, div_pos one_pos h1, by
        field_simp; ring, by
        rw [hct]; ext i
        simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
        field_simp; ring⟩
    exact hab this.1.symm
  · rw [ht, zero_smul, add_zero] at hct; exact hac hct.symm
  rcases lt_trichotomy t 1 with ht1 | ht1 | ht1
  · -- `c` between `a` and `b`
    have := (mem_extremePoints.mp hc).2 a (hA ha) b (hA hb)
      ⟨1 - t, t, by linarith, ht, by ring, by
        rw [hct]; ext i
        simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
        ring⟩
    exact hac this.1
  · rw [ht1, one_smul, add_sub_cancel] at hct; exact hbc hct.symm
  · -- `b` between `a` and `c`
    have := (mem_extremePoints.mp hb).2 a (hA ha) c (hA hc)
      ⟨1 - 1 / t, 1 / t, by rw [sub_pos, div_lt_one (by linarith)]; exact ht1,
        div_pos one_pos (by linarith), by ring, by
        rw [hct]; ext i
        simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
        field_simp; ring⟩
    exact hab this.1

theorem cross2_eq_zero_of_mem_segment {e₁ e₂ z₁ z₂ z₃ : ℝ²} (h₁ : z₁ ∈ segment ℝ e₁ e₂)
    (h₂ : z₂ ∈ segment ℝ e₁ e₂) (h₃ : z₃ ∈ segment ℝ e₁ e₂) : cross2 (z₂ - z₁) (z₃ - z₁) = 0 := by
  rw [segment_eq_image'] at h₁ h₂ h₃
  obtain ⟨t₁, -, rfl⟩ := h₁
  obtain ⟨t₂, -, rfl⟩ := h₂
  obtain ⟨t₃, -, rfl⟩ := h₃
  simp only [cross2, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem exists_pair_of_card_le_two {α : Type*} [DecidableEq α] [Inhabited α] (S : Finset α)
    (h : S.card ≤ 2) : ∃ a b, ∀ x ∈ S, x = a ∨ x = b := by
  interval_cases hS : S.card
  · exact ⟨default, default, fun x hx => absurd hx (by rw [card_eq_zero.mp hS]; simp)⟩
  · obtain ⟨a, rfl⟩ := card_eq_one.mp hS
    exact ⟨a, a, fun x hx => Or.inl (mem_singleton.mp hx)⟩
  · obtain ⟨a, b, -, rfl⟩ := card_eq_two.mp hS
    exact ⟨a, b, fun x hx => by simpa using hx⟩

/-- **The rim only loses corners** (Lemma 18.2 (a), in the plane): a weakly counterclockwise
cyclic polygon, not on one line, has a cyclic subsequence (the least label over each extreme
point of its hull) that is a strictly convex counterclockwise polygon with the same hull. -/
theorem exists_cornerRim {k : ℕ} [NeZero k] (p : ZMod k → ℝ²)
    (hW : ∀ a b c : ZMod k, CycBetween a b c → 0 ≤ cross2 (p b - p a) (p c - p a))
    (hNC : ∃ a b c : ZMod k, cross2 (p b - p a) (p c - p a) ≠ 0) :
    ∃ (k' : ℕ) (_ : NeZero k') (σ : ZMod k' → ZMod k),
      (∀ i j l, CycBetween i j l → CycBetween (σ i) (σ j) (σ l)) ∧ IsCcwPolygon (p ∘ σ) ∧
      ∀ i, p i ∈ convexHull ℝ (Set.range (p ∘ σ)) := by
  classical
  set C := convexHull ℝ (Set.range p)
  have hCc : IsCompact C := (Set.finite_range p).isCompact_convexHull (𝕜 := ℝ)
  set E := C.extremePoints ℝ
  have hEr : E ⊆ Set.range p := extremePoints_convexHull_subset
  have hEf : E.Finite := (Set.finite_range p).subset hEr
  have hKM : convexHull ℝ E = C := by
    have h1 := closure_convexHull_extremePoints hCc (convex_convexHull ℝ _)
    rwa [(hEf.isCompact_convexHull (𝕜 := ℝ)).isClosed.closure_eq] at h1
  set S : Finset (ZMod k) := univ.filter (fun i => p i ∈ E ∧ ∀ j, p j = p i → i.val ≤ j.val)
  have hSE : ∀ i ∈ S, p i ∈ E := fun i hi => (mem_filter.mp hi).2.1
  have hSinj : ∀ i ∈ S, ∀ j ∈ S, p i = p j → i = j := by
    intro i hi j hj e
    have h1 := (mem_filter.mp hi).2.2 j e.symm
    have h2 := (mem_filter.mp hj).2.2 i e
    exact ZMod.val_injective k (le_antisymm h1 h2)
  have hES : ∀ e ∈ E, ∃ i ∈ S, p i = e := by
    intro e he
    obtain ⟨i₀, hi₀⟩ := hEr he
    obtain ⟨i, hi, hmin⟩ := (univ.filter fun j => p j = e).exists_min_image ZMod.val
      ⟨i₀, mem_filter.mpr ⟨mem_univ _, hi₀⟩⟩
    have hpi : p i = e := (mem_filter.mp hi).2
    refine ⟨i, mem_filter.mpr ⟨mem_univ _, hpi ▸ he, fun j hj => ?_⟩, hpi⟩
    exact hmin j (mem_filter.mpr ⟨mem_univ _, hj.trans hpi⟩)
  have hk3 : 3 ≤ S.card := by
    by_contra hlt
    obtain ⟨i₁, i₂, h12⟩ := exists_pair_of_card_le_two S (by omega)
    have hsub : Set.range p ⊆ segment ℝ (p i₁) (p i₂) := by
      intro z hz
      have hzC : z ∈ C := subset_convexHull ℝ _ hz
      rw [← hKM] at hzC
      rw [← convexHull_pair]
      refine convexHull_mono ?_ hzC
      intro e he
      obtain ⟨i, hi, rfl⟩ := hES e he
      rcases h12 i hi with rfl | rfl <;> simp
    obtain ⟨a, b, c, hne⟩ := hNC
    exact hne (cross2_eq_zero_of_mem_segment (hsub ⟨a, rfl⟩) (hsub ⟨b, rfl⟩) (hsub ⟨c, rfl⟩))
  have : NeZero S.card := ⟨by omega⟩
  obtain ⟨σ, hσS, hσsurj, hσmono⟩ := exists_enum S
  have hσcyc : ∀ i j l, CycBetween i j l → CycBetween (σ i) (σ j) (σ l) :=
    fun i j l h => cycBetween_of_val_mono hσmono h
  have hrange : Set.range (p ∘ σ) = E := by
    ext e; constructor
    · rintro ⟨j, rfl⟩; exact hSE _ (hσS j)
    · intro he
      obtain ⟨i, hi, rfl⟩ := hES e he
      obtain ⟨j, rfl⟩ := hσsurj i hi
      exact ⟨j, rfl⟩
  refine ⟨S.card, inferInstance, σ, hσcyc, ⟨hk3, fun a b h1 h2 => ?_⟩, fun i => ?_⟩
  · have hc := hσcyc _ _ _ (cycBetween_add_one hk3 h1 h2)
    obtain ⟨n1, n2, n3⟩ := hc.ne
    have pn : ∀ {i j : ZMod S.card}, σ i ≠ σ j → p (σ i) ≠ p (σ j) := fun hij e =>
      hij (hSinj _ (hσS _) _ (hσS _) e)
    exact lt_of_le_of_ne (hW _ _ _ hc) (Ne.symm (cross2_ne_zero_of_extremePoints
      (hSE _ (hσS a)) (hSE _ (hσS (a + 1))) (hSE _ (hσS b)) (pn n1) (pn n3) (pn n2)))
  · rw [hrange, hKM]; exact subset_convexHull ℝ _ ⟨i, rfl⟩

/-- **A hull point of a strictly convex polygon is interior or on a closed side.** -/
theorem IsCcwPolygon.mem_side_of_mem_convexHull {k : ℕ} [NeZero k] {q : ZMod k → ℝ²}
    (hq : IsCcwPolygon q) {z : ℝ²} (hz : z ∈ convexHull ℝ (Set.range q)) :
    z ∈ interior (convexHull ℝ (Set.range q)) ∨
      ∃ a : ZMod k, ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ z = q a + s • (q (a + 1) - q a) := by
  by_cases hall : ∀ a, 0 < cross2 (q (a + 1) - q a) (z - q a)
  · exact Or.inl (hq.mem_interior_of_left hall)
  right
  push Not at hall
  obtain ⟨a, ha⟩ := hall
  have h0 : cross2 (q (a + 1) - q a) (z - q a) = 0 :=
    le_antisymm ha (hq.left_of_mem_convexHull a hz)
  have hd := hq.edge_ne_zero a
  set d := q (a + 1) - q a
  set s := ⟪z - q a, d⟫ / ⟪d, d⟫
  have hzs : z - q a = s • d := eq_smul_of_cross2_eq_zero hd h0
  refine ⟨a, s, ?_, ?_, by rw [← hzs]; abel⟩
  · have h1 := hq.left_of_mem_convexHull (a - 1) hz
    rw [sub_add_cancel] at h1
    have e : z - q (a - 1) = (q a - q (a - 1)) + s • d := by rw [← hzs]; abel
    rw [e, cross2_add_right, cross2_self, zero_add, cross2_smul_right] at h1
    have hpos := hq.cross2_edge_pos a
    by_contra hs
    push Not at hs
    nlinarith
  · have h2 := hq.left_of_mem_convexHull (a + 1) hz
    have e : z - q (a + 1) = (s - 1) • d := by
      rw [sub_smul, one_smul, ← hzs]; simp only [d]; abel
    rw [e, cross2_smul_right] at h2
    have hpos := hq.cross2_edge_pos (a + 1)
    rw [add_sub_cancel_right, cross2_comm] at hpos
    by_contra hs
    push Not at hs
    nlinarith

/-- A vector with zero screen projection is a multiple of the view. -/
theorem eq_smul_of_proj_rot_eq_zero {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO3) {u : ℝ³}
    {r : ℝ} (hr : r ≠ 0) (hRu : R.toEuclideanLin u = r • ez) {v : ℝ³}
    (hv : proj_xy (R.toEuclideanLin v) = 0) : v = ((R.toEuclideanLin v) 2 / r) • u := by
  apply (so3Isometry hR).injective
  simp only [so3Isometry_apply, map_smul, hRu, smul_smul]
  rw [div_mul_cancel₀ _ hr]
  have h0 := congrFun (congrArg (fun z : ℝ² => (z : Fin 2 → ℝ)) hv) 0
  have h1 := congrFun (congrArg (fun z : ℝ² => (z : Fin 2 → ℝ)) hv) 1
  simp only [proj_xy] at h0 h1
  ext i; fin_cases i <;> simp_all [ez]


theorem inner_rot_eq_cross2 (d e : ℝ²) : ⟪!₂[-(d 1), d 0], e⟫ = cross2 d e := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, cross2]; ring

/-- **A screen functional lifts** to a functional orthogonal to the view. -/
theorem exists_lift_screen {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO3) {u : ℝ³} {r : ℝ}
    (hRu : R.toEuclideanLin u = r • ez) (ν : ℝ²) :
    ∃ w : ℝ³, (∀ v, ⟪w, v⟫ = ⟪ν, proj_xy (R.toEuclideanLin v)⟫) ∧ ⟪w, u⟫ = 0 ∧
      (ν ≠ 0 → w ≠ 0) := by
  obtain ⟨w, hw⟩ := (so3Isometry hR).surjective !₂[ν 0, ν 1, 0]
  simp only [so3Isometry_apply] at hw
  have key : ∀ v, ⟪w, v⟫ = ⟪ν, proj_xy (R.toEuclideanLin v)⟫ := by
    intro v
    rw [← inner_toEuclideanLin_SO3 hR w v, hw]
    simp [proj_xy, PiLp.inner_apply, Fin.sum_univ_three, Fin.sum_univ_two]
  refine ⟨w, key, ?_, fun hν hw0 => hν ?_⟩
  · rw [key, hRu, proj_xy_smul']
    have : proj_xy ez = 0 := by ext j; fin_cases j <;> simp [proj_xy, ez]
    rw [this, smul_zero, inner_zero_right]
  · rw [hw0, map_zero] at hw
    have h0 := congrArg (fun z : ℝ³ => z 0) hw
    have h1 := congrArg (fun z : ℝ³ => z 1) hw
    simp at h0 h1
    ext j; fin_cases j <;> simp [← h0, ← h1]

/-- **The limit lemma, with the corner rim constructed** (Lemma 18.2 (a)–(c) with Theorems 18.1
and 18.3).  Shapes `xs t → x` carry one labelled rim certificate (`RimCertAt`, views
`us t → u ≠ 0`), and the ties of the labelled depths of `x` are ties along the sequence (for
instance, the labelled depths of `x` are distinct).  If no point of `x` lies inside a segment of
two others, `x` does not lie in a plane, and there is no horizontal double normal at `u`, then
`x` is Rupert: the least label over each corner of the shadow gives a strictly convex rim
(`exists_cornerRim`) whose depths are robustly unimodal, and every other point is interior, a
chord middle (`δ ≠ 0` since no point is inside a segment) or a double. -/
theorem isRupert_of_tendsto_rimCert {n : ℕ} (x : Fin n → ℝ³)
    (hseg : ∀ i j m : Fin n, x m ≠ x i → x m ≠ x j → ∀ s : ℝ, 0 < s → s < 1 →
      x m ≠ x i + s • (x j - x i))
    (hsp : ∃ i j l m : Fin n, det3 (x j - x i) (x l - x i) (x m - x i) ≠ 0)
    {k : ℕ} [NeZero k] (lab : ZMod k → Fin n) {u : ℝ³} (hu : u ≠ 0)
    (hnd : NoHDNAt (univ.image x) u)
    {ι : Type*} {l : Filter ι} (xs : ι → Fin n → ℝ³) (us : ι → ℝ³)
    (hxs : ∀ m, Tendsto (fun t => xs t m) l (𝓝 (x m))) (hus : Tendsto us l (𝓝 u))
    (hcert : ∃ᶠ t in l, RimCertAt (xs t) (us t) lab ∧
      ∀ i j, ⟪x (lab i), u⟫ = ⟪x (lab j), u⟫ → ⟪xs t (lab i), us t⟫ = ⟪xs t (lab j), us t⟫) :
    IsRupert (univ.image x) := by
  classical
  set X : ZMod k → ℝ³ := fun i => x (lab i) with hXdef
  have hc := hcert.mono fun _ h => h.1
  -- Lemma 18.2 at `K`
  have hW : ∀ a b c, CycBetween a b c → 0 ≤ det3 (X b - X a) (X c - X a) u :=
    fun a b c h => cyc_nonneg_of_tendsto hxs hus hc h
  have hS : ∀ m, SuppIn u X (x m) := fun m =>
    suppIn_of_tendsto hu hus (fun i => hxs (lab i)) (hxs m) (hc.mono fun t ht => ht.suppIn m)
  have hZ : IsRobustUnimodal (fun i => ⟪X i, u⟫) :=
    isRobustUnimodal_of_tendsto_ties (fun i => (hxs (lab i)).inner hus)
      (hcert.mono fun t ht => ⟨ht.1.robust, ht.2⟩)
  -- the frame at `K`
  obtain ⟨R, hR, r, hr, hRu⟩ := exists_rotation_to_ez_pos u hu
  set P : ℝ³ → ℝ² := fun v => proj_xy (R.toEuclideanLin v) with hPdef
  have hPsub : ∀ a b, P a - P b = P (a - b) := fun a b => proj_rot_sub R a b
  have hPadd : ∀ a b, P (a + b) = P a + P b := fun a b => by
    simp only [hPdef, map_add, proj_xy_add']
  have hPsmul : ∀ (c : ℝ) a, P (c • a) = c • P a := fun c a => by
    simp only [hPdef, map_smul, proj_xy_smul']
  have hPu : P u = 0 := by
    simp only [hPdef, hRu, proj_xy_smul']
    have : proj_xy ez = 0 := by ext j; fin_cases j <;> simp [proj_xy, ez]
    rw [this, smul_zero]
  set p : ZMod k → ℝ² := fun i => P (X i) with hpdef
  have hW2 : ∀ a b c, CycBetween a b c → 0 ≤ cross2 (p b - p a) (p c - p a) := by
    intro a b c h
    have := hW a b c h
    rw [← cross2_proj_rot hR hRu, ← proj_rot_sub, ← proj_rot_sub] at this
    exact nonneg_of_mul_nonneg_right (by linarith) hr
  -- every point projects into the hull of the labels
  have hhull : ∀ m, P (x m) ∈ convexHull ℝ (Set.range p) := by
    intro m
    by_contra hnot
    obtain ⟨f, c, hfz, hfC⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ _)
      ((Set.finite_range p).isCompact_convexHull (𝕜 := ℝ)).isClosed hnot
    have hf : ∀ z : ℝ², f z = ⟪!₂[f (EuclideanSpace.single 0 1), f (EuclideanSpace.single 1 1)],
        z⟫ := by
      intro z
      have hz : z = z 0 • EuclideanSpace.single 0 1 + z 1 • EuclideanSpace.single 1 1 := by
        ext j; fin_cases j <;> simp
      conv_lhs => rw [hz]
      rw [map_add, map_smul, map_smul]
      simp [PiLp.inner_apply, Fin.sum_univ_two, smul_eq_mul]
    obtain ⟨w, hwv, hwu, -⟩ := exists_lift_screen hR hRu
      (-!₂[f (EuclideanSpace.single 0 1), f (EuclideanSpace.single 1 1)])
    obtain ⟨i, hi⟩ := hS m w hwu
    rw [hwv, hwv, inner_neg_left, inner_neg_left, ← hf, ← hf] at hi
    have := hfC (p i) (subset_convexHull ℝ _ ⟨i, rfl⟩)
    simp only [hpdef, hXdef] at this hi
    linarith
  -- the labels are not on one line
  have hNC : ∃ a b c, cross2 (p b - p a) (p c - p a) ≠ 0 := by
    by_contra hcol
    push Not at hcol
    obtain ⟨i, j, l', m, hdet⟩ := hsp
    apply hdet
    -- a nonzero screen functional constant on the labels
    obtain ⟨ν, hν0, hν⟩ : ∃ ν : ℝ², ν ≠ 0 ∧ ∀ a, ⟪ν, p a - p 0⟫ = 0 := by
      by_cases hall : ∀ a, p a = p 0
      · refine ⟨EuclideanSpace.single 0 1, ?_, fun a => by rw [hall a, sub_self, inner_zero_right]⟩
        intro h0
        have := congrArg (fun z : ℝ² => z 0) h0
        simp at this
      push Not at hall
      obtain ⟨b, hb⟩ := hall
      refine ⟨!₂[-(p b - p 0) 1, (p b - p 0) 0], ?_, fun a => ?_⟩
      · intro h0
        apply hb
        have h0' := congrArg (fun z : ℝ² => z 0) h0
        have h1' := congrArg (fun z : ℝ² => z 1) h0
        simp at h0' h1'
        rw [← sub_eq_zero]
        ext j; fin_cases j <;> simp <;> linarith
      · rw [inner_rot_eq_cross2]; exact hcol 0 b a
    have hplane : ∀ z ∈ convexHull ℝ (Set.range p), ⟪ν, z - p 0⟫ = 0 := by
      intro z hz
      have hconv : Convex ℝ {z : ℝ² | ⟪ν, z - p 0⟫ = 0} := by
        have : {z : ℝ² | ⟪ν, z - p 0⟫ = 0} = {z : ℝ² | ⟪ν, z⟫ = ⟪ν, p 0⟫} := by
          ext z; simp only [Set.mem_setOf_eq, inner_sub_right, sub_eq_zero]
        rw [this]
        exact convex_hyperplane (innerₛₗ ℝ ν).isLinear _
      refine convexHull_min ?_ hconv hz
      rintro _ ⟨a, rfl⟩
      exact hν a
    obtain ⟨w, hwv, -, hw0⟩ := exists_lift_screen hR hRu ν
    have hperp : ∀ a b : Fin n, ⟪w, x b - x a⟫ = 0 := by
      intro a b
      have ha := hplane _ (hhull a)
      have hb := hplane _ (hhull b)
      have e : proj_xy (R.toEuclideanLin (x b - x a)) = (P (x b) - p 0) - (P (x a) - p 0) := by
        rw [← proj_rot_sub]; abel
      rw [hwv, e, inner_sub_right, ha, hb, sub_zero]
    exact det3_eq_zero_of_perp (hw0 hν0) (by rw [real_inner_comm]; exact hperp _ _)
      (by rw [real_inner_comm]; exact hperp _ _) (by rw [real_inner_comm]; exact hperp _ _)
  -- the corner rim
  obtain ⟨k', hk', σ, hσcyc, hq, hpin⟩ := exists_cornerRim p hW2 hNC
  set xc : ZMod k' → ℝ³ := fun i => X (σ i) with hxcdef
  set q : ZMod k' → ℝ² := fun i => P (xc i) with hqdef
  have hq' : IsCcwPolygon q := hq
  have hhull' : ∀ m, P (x m) ∈ convexHull ℝ (Set.range q) := fun m =>
    convexHull_min (by rintro _ ⟨i, rfl⟩; exact hpin i) (convex_convexHull ℝ _) (hhull m)
  set V := univ.image x with hVdef
  have hmem : ∀ m, x m ∈ V := fun m => mem_image_of_mem x (mem_univ m)
  set M := V.filter (fun y => ∃ a : ZMod k', ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
    y = xc a + s • (xc (a + 1) - xc a) + δ • u) with hMdef
  set D := V.filter (fun y => (∀ i, y ≠ xc i) ∧ ∃ i : ZMod k', ∃ h : ℝ, h ≠ 0 ∧
    y = xc i - h • u) with hDdef
  -- lifting from the screen
  have hlift : ∀ (y : ℝ³) (a : ZMod k') (s : ℝ), P y = q a + s • (q (a + 1) - q a) →
      ∃ δ : ℝ, y = xc a + s • (xc (a + 1) - xc a) + δ • u := by
    intro y a s h
    have h0 : P (y - xc a - s • (xc (a + 1) - xc a)) = 0 := by
      rw [← hPsub, ← hPsub, hPsmul, ← hPsub, h]; simp only [hqdef]; abel
    exact ⟨_, by rw [← eq_smul_of_proj_rot_eq_zero hR hr.ne' hRu h0]; abel⟩
  have hproj : ∀ (a : ZMod k') (s δ : ℝ),
      P (xc a + s • (xc (a + 1) - xc a) + δ • u) = q a + s • (q (a + 1) - q a) := by
    intro a s δ
    rw [hPadd, hPadd, hPsmul, hPsmul, hPu, smul_zero, add_zero, ← hPsub]
  have hxM : ∀ i, xc i ∉ M := by
    intro i hi
    obtain ⟨-, a, s, δ, hs0, hs1, -, he⟩ := mem_filter.mp hi
    have hP := congrArg P he
    rw [hproj] at hP
    have hd := hq'.edge_ne_zero a
    by_cases h1 : i = a
    · subst h1
      apply hd
      have : s • (q (i + 1) - q i) = 0 := by
        have := hP; simp only [hqdef] at this ⊢; rw [eq_comm, add_eq_left] at this; exact this
      exact (smul_eq_zero.mp this).resolve_left hs0.ne'
    by_cases h2 : i = a + 1
    · subst h2
      apply hd
      have : (1 - s) • (q (a + 1) - q a) = 0 := by
        rw [sub_smul, one_smul]
        have := hP; simp only [hqdef] at this ⊢
        rw [← sub_eq_zero] at this
        rw [← this]; abel
      exact (smul_eq_zero.mp this).resolve_left (by linarith)
    · have := hq'.2 a i h1 h2
      have e : q i - q a = s • (q (a + 1) - q a) := by
        simp only [hqdef] at hP ⊢; rw [hP]; abel
      rw [e, cross2_smul_right, cross2_self, mul_zero] at this
      exact lt_irrefl _ this
  have hin : ∀ v ∈ V, v ∉ M → v ∉ D → (∀ i, v ≠ xc i) →
      P v ∈ interior (convexHull ℝ (Set.range q)) := by
    intro v hv hvM hvD hvx
    obtain ⟨m, -, rfl⟩ := mem_image.mp hv
    rcases hq'.mem_side_of_mem_convexHull (hhull' m) with h | ⟨a, s, hs0, hs1, hside⟩
    · exact h
    exfalso
    obtain ⟨δ, hδ⟩ := hlift _ a s hside
    rcases hs0.lt_or_eq with hs0 | rfl
    · rcases hs1.lt_or_eq with hs1 | rfl
      · by_cases hδ0 : δ = 0
        · rw [hδ0, zero_smul, add_zero] at hδ
          exact hseg (lab (σ a)) (lab (σ (a + 1))) m (hvx a) (hvx (a + 1)) s hs0 hs1 hδ
        · exact hvM (mem_filter.mpr ⟨hv, a, s, δ, hs0, hs1, hδ0, hδ⟩)
      · refine hvD (mem_filter.mpr ⟨hv, hvx, a + 1, -δ, ?_, ?_⟩)
        · intro h0; apply hvx (a + 1); rw [hδ, neg_eq_zero.mp h0]; simp
        · rw [hδ]; simp only [one_smul, neg_smul, sub_neg_eq_add]; abel
    · refine hvD (mem_filter.mpr ⟨hv, hvx, a, -δ, ?_, ?_⟩)
      · intro h0; apply hvx a; rw [hδ, neg_eq_zero.mp h0]; simp
      · rw [hδ]; simp only [zero_smul, add_zero, neg_smul, sub_neg_eq_add]
  have hz : IsRobustUnimodal (fun i => (R.toEuclideanLin (xc i)) 2) := by
    have hdepth : ∀ y, (R.toEuclideanLin y) 2 = r⁻¹ * ⟪y, u⟫ := by
      intro y
      have : r * (R.toEuclideanLin y) 2 = ⟪y, u⟫ := by
        rw [← inner_ez, ← real_inner_smul_right, ← hRu, inner_toEuclideanLin_SO3 hR]
      rw [← this]; field_simp
    simp only [hdepth]
    exact (hZ.comp σ hσcyc).smul (inv_pos.mpr hr)
  exact isRupert_of_uniform_doubles_robustUnimodal V M D R hR hr hRu xc (fun i => hmem _) hxM hq'
    hin hz (hnd R hR r hr.ne' hRu k' xc (fun i => hmem _) hq')
    (fun m hm => (mem_filter.mp hm).2) (fun y hy => (mem_filter.mp hy).2.2)


end Minimality

end
