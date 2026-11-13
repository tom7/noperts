module

public import Minimality.EdgeMain
public import Minimality.Type16NF

@[expose] public section

/-!
# Edge pairs at the limit (`FEWER-FACES-PROOFS.md` §18.2 with §22)

A limit shape `x` of shapes `K_k` that carry one labelled edge pair of Lemma E (`EPairData`):
the closing `K_v` or `K_w` passes to the limit (Lemma 18.2: weakly convex rim, every point in
the cylinder over it, robust unimodality, Lemma E weakly), and at the limit view §22's
codimension-2 conditions (`EdgeGen`) make `x` Rupert (`EdgeConf.isRupert_edgeClosing`).

* `NormalFootGen`, `EdgeGen`: the conditions at the view (each fails in codimension 1; with a
  horizontal double normal at the view, in codimension 2).
* `rimCertPts_suppIn`, `EPairData.flip`, `ePair_facts`: the approximants.
* `isRupert_ePair_limit`: the limit theorem.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- **No double normal perpendicular to the face `⟪N, ·⟫ = max` from a vertex of the face**: for
every vertex `p` of the face `S` and every point `F` of a segment `[y, y']` of points off the
face with `y`, `y'` at one level of `⟪N, ·⟫` (`y = y'` allowed), `F − p` is not a nonzero
multiple of `N`.  Each instance is two conditions on the shape. -/
def NormalFootGen (V : Finset ℝ³) (N : ℝ³) (S : Finset ℝ³) : Prop :=
  ∀ p ∈ S, ∀ y ∈ V, ∀ y' ∈ V, y ∉ S → y' ∉ S → ⟪N, y⟫ = ⟪N, y'⟫ →
    ∀ F ∈ segment ℝ y y', ∀ r : ℝ, r ≠ 0 → F - p ≠ r • N

/-- **The conditions of §22.4 at an edge view `u`** (axle `v w`, faces `SA`, `SB` with normals
`NA`, `NB`): only the axle seen end-on, (G1), distinct depths, at most one direction of
horizontal double normals, and no double normal perpendicular to a face from a face vertex. -/
structure EdgeGen (V : Finset ℝ³) (u v w : ℝ³) (SA SB : Finset ℝ³) (NA NB : ℝ³) : Prop where
  par : ParOnly V u v w
  g1 : G1At V u SA SB
  dist : ∀ y ∈ V, ∀ y' ∈ V, y ≠ y' → ⟪y, u⟫ ≠ ⟪y', u⟫
  one : OneHDNDir V u
  footA : NormalFootGen V NA SA
  footB : NormalFootGen V NB SB

/-- The cylinder over a certified rim contains every point (support-function form). -/
theorem rimCertPts_suppIn {k : ℕ} [NeZero k] {V : Finset ℝ³} {u : ℝ³} {y : ZMod k → ℝ³}
    (h : RimCertPts V u y) (hu : u ≠ 0) : ∀ z ∈ V, SuppIn u y z := by
  obtain ⟨R, hR, r, hr, hRu⟩ := exists_rotation_to_ez_pos u hu
  have hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (y i))) :=
    ⟨h.three, fun i j hi hj => by
      simp only [proj_rot_sub]; exact cross2_proj_rot_pos hR hr hRu (h.cyc i j hi hj)⟩
  intro z hz
  have hq : proj_xy (R.toEuclideanLin z) ∈
      convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (y i))) := by
    refine hp.mem_convexHull_of_left fun i => ?_
    have := h.left z hz i
    rw [← cross2_proj_rot hR hRu] at this
    simp only [proj_rot_sub]
    exact nonneg_of_mul_nonneg_right (by linarith) hr
  intro w hw
  obtain ⟨y', ⟨i, rfl⟩, hle⟩ := ((innerₛₗ ℝ (proj_xy (R.toEuclideanLin w))).convexOn
    (convex_convexHull ℝ _)).exists_ge_of_mem_convexHull (subset_convexHull ℝ _) hq
  refine ⟨i, ?_⟩
  rw [inner_eq_proj_of_perp hR hr.ne' hRu hw, inner_eq_proj_of_perp hR hr.ne' hRu hw]
  simpa only [innerₛₗ_apply_apply] using hle

/-- An edge pair in the clockwise orientation is the edge pair with `a`, `b` exchanged. -/
theorem EPairData.flip {V : Finset ℝ³} {v w a b c : ℝ³} (h : EPairData V (-1) v w a b c) :
    EPairData V 1 v w b a c := by
  obtain ⟨-, q₁, q₂, q₃, q₄, hE, h3, hV⟩ := h
  have e1 : det3 (b - v) (c - v) (w - v) = -det3 (b - c) (v - c) (w - v) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have e2 : det3 (c - b) (a - b) (w - v) = -det3 (c - a) (b - a) (w - v) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have e3 : det3 (a - c) (v - c) (w - v) = -det3 (a - v) (c - v) (w - v) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have e4 : det3 (v - a) (b - a) (w - v) = -det3 (v - b) (a - b) (w - v) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have eE : ∀ y, det3 (a - b) (c - b) (y - b) = -det3 (b - a) (c - a) (y - a) := by
    intro y; simp only [det3_expand, PiLp.sub_apply]; ring
  refine ⟨Or.inl rfl, by rw [one_mul, e1]; linarith, by rw [one_mul, e2]; linarith,
    by rw [one_mul, e3]; linarith, by rw [one_mul, e4]; linarith, by rw [eE, eE]; linarith,
    fun h => h3 ⟨h.2.symm, h.1.symm⟩, fun z hz => ?_⟩
  rcases hV z hz with h | h | h | h | h | h | ⟨h1, h2, h3, h4⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h.swap)))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩)))))
    · rw [one_mul, det3_rev]; linarith
    · rw [one_mul, det3_rev]; linarith
    · rw [one_mul, det3_rev]; linarith
    · rw [one_mul, det3_rev]; linarith

/-- No weak saddle passes to a limit with distinct entries. -/
theorem nws4_of_tendsto {ι : Type*} {l : Filter ι} {zs : ι → ZMod 4 → ℝ} {z : ZMod 4 → ℝ}
    (hlim : ∀ i, Tendsto (fun t => zs t i) l (𝓝 (z i))) (hinj : Function.Injective z)
    (h : ∃ᶠ t in l, NWS4 (zs t)) : NWS4 z := by
  by_contra hc
  have ev : ∀ i j : ZMod 4, z i < z j → ∀ᶠ t in l, zs t i < zs t j := fun i j hij =>
    (hlim i).eventually_lt (hlim j) hij
  have st : ∀ i j : ZMod 4, i ≠ j → z i ≤ z j → z i < z j := fun i j hij hle =>
    lt_of_le_of_ne hle fun e => hij (hinj e)
  unfold NWS4 at hc
  rcases not_and_or.mp hc with hA | hB
  · push Not at hA
    obtain ⟨e1, e2, e3, e4⟩ := hA
    have := ((ev _ _ (st 1 0 (by decide) e1)).and ((ev _ _ (st 3 0 (by decide) e2)).and
      ((ev _ _ (st 1 2 (by decide) e3)).and (ev _ _ (st 3 2 (by decide) e4)))))
    exact h (this.mono fun t ⟨f1, f2, f3, f4⟩ hN => by
      rcases hN.1 with g | g | g | g <;> linarith)
  · push Not at hB
    obtain ⟨e1, e2, e3, e4⟩ := hB
    have := ((ev _ _ (st 0 1 (by decide) e1)).and ((ev _ _ (st 0 3 (by decide) e2)).and
      ((ev _ _ (st 2 1 (by decide) e3)).and (ev _ _ (st 2 3 (by decide) e4)))))
    exact h (this.mono fun t ⟨f1, f2, f3, f4⟩ hN => by
      rcases hN.2 with g | g | g | g <;> linarith)

/-- A point of a segment at the minimum of a functional over its ends, with distinct values,
is the lower end. -/
theorem seg_min_eq {p q F N : ℝ³} (hF : F ∈ segment ℝ p q) (hmin : ⟪N, F⟫ = min ⟪N, p⟫ ⟪N, q⟫)
    (hpq : ⟪N, p⟫ < ⟪N, q⟫) : F = p := by
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hF
  rw [min_eq_left hpq.le] at hmin
  simp only [inner_add_right, real_inner_smul_right] at hmin
  have hβ0 : β = 0 := by
    rw [show α = 1 - β by linarith] at hmin
    by_contra hβ0
    have : β * (⟪N, q⟫ - ⟪N, p⟫) = 0 := by linarith
    exact hβ0 ((mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hpq.ne'))
  rw [hβ0, show α = 1 by linarith]; simp

/-- `NormalFootGen` gives `FootA` for a side `[p, a]` of the face and far corners `c`, `b`. -/
theorem footA_of_gen {V S : Finset ℝ³} {N p a c b : ℝ³} (hg : NormalFootGen V N S)
    (hp : p ∈ S) (ha : a ∈ S) (hc : c ∈ V) (hb : b ∈ V) (hcS : c ∉ S) (hbS : b ∉ S) :
    FootA p a c b N := by
  intro F hF hFmin r hr
  have key : ∀ q ∈ S, F - q ≠ r • N := by
    intro q hq
    rcases lt_trichotomy ⟪N, c⟫ ⟪N, b⟫ with h | h | h
    · have := seg_min_eq hF hFmin h
      subst this
      exact hg q hq F hc F hc hcS hcS rfl F (left_mem_segment ℝ F F) r hr
    · exact hg q hq c hc b hb hcS hbS h F hF r hr
    · rw [segment_symm] at hF
      have := seg_min_eq hF (by rw [min_comm]; exact hFmin) h
      subst this
      exact hg q hq F hb F hb hbS hbS rfl F (left_mem_segment ℝ F F) r hr
  exact ⟨key p hp, key a ha⟩

theorem det3_lemmaE_mirror (a b c X : ℝ³) :
    det3 (c - b) (a - b) (X - b) = det3 (b - a) (c - a) (X - a) := by
  simp only [det3_expand, PiLp.sub_apply]; ring

theorem det3_lemmaE_swap (a b c X : ℝ³) :
    det3 (c - a) (b - a) (X - a) = -det3 (b - a) (c - a) (X - a) := by
  simp only [det3_expand, PiLp.sub_apply]; ring

/-- **The approximants' facts of an edge pair** (`ePair_facts` with Lemma E): every point weakly
left of the four sides of `v a c b` at `w − v`, in the cylinder over it, one of `K_v`, `K_w`
without a weak saddle, and Lemma E (weakly). -/
abbrev EPairFacts (V : Finset ℝ³) (v w a b c : ℝ³) : Prop :=
  ((∀ z ∈ V, 0 ≤ det3 (a - v) (z - v) (w - v) ∧ 0 ≤ det3 (c - a) (z - a) (w - v) ∧
      0 ≤ det3 (b - c) (z - c) (w - v) ∧ 0 ≤ det3 (v - b) (z - b) (w - v)) ∧
    (∀ z ∈ V, SuppIn (w - v) (quad v a c b) z) ∧
    (NWS4 (quad ⟪v, w - v⟫ ⟪a, w - v⟫ ⟪c, w - v⟫ ⟪b, w - v⟫) ∨
      NWS4 (quad ⟪w, w - v⟫ ⟪a, w - v⟫ ⟪c, w - v⟫ ⟪b, w - v⟫))) ∧
  det3 (b - a) (c - a) (v - a) * det3 (b - a) (c - a) (w - a) ≤ 0

set_option maxHeartbeats 1000000 in
/-- **An edge pair at the limit, from the approximants' facts** (`isRupert_ePair_limit` with
`EPairFacts` in place of `EPairData`). -/
theorem isRupert_ePair_limit_facts {n : ℕ} (x : Fin n → ℝ³) (hx : Function.Injective x)
    (hseg : ∀ i j m : Fin n, x m ≠ x i → x m ≠ x j → ∀ s : ℝ, 0 < s → s < 1 →
      x m ≠ x i + s • (x j - x i))
    {v w a b c : Fin n} (hvw : v ≠ w) {Sa Sb : Finset (Fin n)} {Na Nb : ℝ³} {κa κb : ℝ}
    (hfa : ∀ i, (i ∈ Sa → ⟪Na, x i⟫ = κa) ∧ (i ∉ Sa → ⟪Na, x i⟫ < κa))
    (hfb : ∀ i, (i ∈ Sb → ⟪Nb, x i⟫ = κb) ∧ (i ∉ Sb → ⟪Nb, x i⟫ < κb))
    (hSa : v ∈ Sa ∧ w ∈ Sa ∧ a ∈ Sa ∧ b ∉ Sa ∧ c ∉ Sa ∧ ∀ i ∈ Sa, ∀ j ∈ Sa,
      i ≠ v → i ≠ w → i ≠ a → j ≠ v → j ≠ w → j ≠ a → i = j)
    (hSb : v ∈ Sb ∧ w ∈ Sb ∧ b ∈ Sb ∧ a ∉ Sb ∧ c ∉ Sb ∧ ∀ i ∈ Sb, ∀ j ∈ Sb,
      i ≠ v → i ≠ w → i ≠ b → j ≠ v → j ≠ w → j ≠ b → i = j)
    (K : ℕ → Fin n → ℝ³) (hK : ∀ m, Tendsto (fun k => K k m) atTop (𝓝 (x m)))
    (hfacts : ∃ᶠ k in atTop,
      EPairFacts (univ.image (K k)) (K k v) (K k w) (K k a) (K k b) (K k c))
    (hgen : EdgeGen (univ.image x) (x w - x v) (x v) (x w) (Sa.image x) (Sb.image x) Na Nb)
    (hcop : det3 (x b - x a) (x c - x a) (x v - x a) ≠ 0 ∧
      det3 (x b - x a) (x c - x a) (x w - x a) ≠ 0) :
    IsRupert (univ.image x) := by
  classical
  obtain ⟨hvA, hwA, haA, hbA, hcA, hA1⟩ := hSa
  obtain ⟨hvB, hwB, hbB, haB, hcB, hB1⟩ := hSb
  set V := univ.image x with hVdef
  have mem : ∀ i, x i ∈ V := fun i => mem_image_of_mem x (mem_univ i)
  have memK : ∀ k i, K k i ∈ univ.image (K k) := fun k i => mem_image_of_mem _ (mem_univ i)
  set u := x w - x v with hudef
  have hu : u ≠ 0 := sub_ne_zero.mpr (hx.ne hvw.symm)
  -- the approximants' facts and their limits
  have hus : Tendsto (fun k => K k w - K k v) atTop (𝓝 u) := (hK w).sub (hK v)
  have lim0 : ∀ {f : ℕ → ℝ} {L : ℝ}, Tendsto f atTop (𝓝 L) → (∃ᶠ k in atTop, 0 ≤ f k) →
      0 ≤ L := fun hf hfr => le_of_tendsto_frequently tendsto_const_nhds hf hfr
  have hleft : ∀ z ∈ V, 0 ≤ det3 (x a - x v) (z - x v) u ∧ 0 ≤ det3 (x c - x a) (z - x a) u ∧
      0 ≤ det3 (x b - x c) (z - x c) u ∧ 0 ≤ det3 (x v - x b) (z - x b) u := by
    intro z hz
    obtain ⟨m, -, rfl⟩ := mem_image.mp hz
    refine ⟨lim0 (Tendsto.det3' ((hK a).sub (hK v)) ((hK m).sub (hK v)) hus)
      (hfacts.mono fun k hk => (hk.1.1 _ (memK k m)).1),
      lim0 (Tendsto.det3' ((hK c).sub (hK a)) ((hK m).sub (hK a)) hus)
      (hfacts.mono fun k hk => (hk.1.1 _ (memK k m)).2.1),
      lim0 (Tendsto.det3' ((hK b).sub (hK c)) ((hK m).sub (hK c)) hus)
      (hfacts.mono fun k hk => (hk.1.1 _ (memK k m)).2.2.1),
      lim0 (Tendsto.det3' ((hK v).sub (hK b)) ((hK m).sub (hK b)) hus)
      (hfacts.mono fun k hk => (hk.1.1 _ (memK k m)).2.2.2)⟩
  have hXq : ∀ i, Tendsto (fun k => quad (K k v) (K k a) (K k c) (K k b) i) atTop
      (𝓝 (quad (x v) (x a) (x c) (x b) i)) := by
    intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
    exacts [hK v, hK a, hK c, hK b]
  have hsupp : ∀ z ∈ V, SuppIn u (quad (x v) (x a) (x c) (x b)) z := by
    intro z hz
    obtain ⟨m, -, rfl⟩ := mem_image.mp hz
    exact suppIn_of_tendsto hu hus hXq (hK m) (hfacts.mono fun k hk => hk.1.2.1 _ (memK k m))
  have hEweak : det3 (x b - x a) (x c - x a) (x v - x a) *
      det3 (x b - x a) (x c - x a) (x w - x a) ≤ 0 := by
    refine le_of_tendsto_frequently
      ((Tendsto.det3' ((hK b).sub (hK a)) ((hK c).sub (hK a)) ((hK v).sub (hK a))).mul
        (Tendsto.det3' ((hK b).sub (hK a)) ((hK c).sub (hK a)) ((hK w).sub (hK a))))
      tendsto_const_nhds (hfacts.mono fun k hk => hk.2)
  have hEstrict : det3 (x b - x a) (x c - x a) (x v - x a) *
      det3 (x b - x a) (x c - x a) (x w - x a) < 0 :=
    lt_of_le_of_ne hEweak (mul_ne_zero hcop.1 hcop.2)
  -- the configuration at the limit
  set Ma := (Sa \ {v, w, a}).image x with hMadef
  set Mb := (Sb \ {v, w, b}).image x with hMbdef
  have memMa : ∀ z, z ∈ Ma ↔ ∃ i ∈ Sa, i ≠ v ∧ i ≠ w ∧ i ≠ a ∧ x i = z := by
    intro z
    simp only [hMadef, mem_image, Finset.mem_sdiff, mem_insert, mem_singleton, not_or]
    constructor
    · rintro ⟨i, ⟨hi, h1, h2, h3⟩, rfl⟩; exact ⟨i, hi, h1, h2, h3, rfl⟩
    · rintro ⟨i, hi, h1, h2, h3, rfl⟩; exact ⟨i, ⟨hi, h1, h2, h3⟩, rfl⟩
  have memMb : ∀ z, z ∈ Mb ↔ ∃ i ∈ Sb, i ≠ v ∧ i ≠ w ∧ i ≠ b ∧ x i = z := by
    intro z
    simp only [hMbdef, mem_image, Finset.mem_sdiff, mem_insert, mem_singleton, not_or]
    constructor
    · rintro ⟨i, ⟨hi, h1, h2, h3⟩, rfl⟩; exact ⟨i, hi, h1, h2, h3, rfl⟩
    · rintro ⟨i, hi, h1, h2, h3, rfl⟩; exact ⟨i, ⟨hi, h1, h2, h3⟩, rfl⟩
  have hSAeq : Sa.image x = insert (x v) (insert (x w) (insert (x a) Ma)) := by
    ext z
    simp only [mem_image, mem_insert, memMa]
    constructor
    · rintro ⟨i, hi, rfl⟩
      by_cases h1 : i = v; · left; rw [h1]
      by_cases h2 : i = w; · right; left; rw [h2]
      by_cases h3 : i = a; · right; right; left; rw [h3]
      exact Or.inr (Or.inr (Or.inr ⟨i, hi, h1, h2, h3, rfl⟩))
    · rintro (rfl | rfl | rfl | ⟨i, hi, -, -, -, rfl⟩)
      exacts [⟨v, hvA, rfl⟩, ⟨w, hwA, rfl⟩, ⟨a, haA, rfl⟩, ⟨i, hi, rfl⟩]
  have hSBeq : Sb.image x = insert (x v) (insert (x w) (insert (x b) Mb)) := by
    ext z
    simp only [mem_image, mem_insert, memMb]
    constructor
    · rintro ⟨i, hi, rfl⟩
      by_cases h1 : i = v; · left; rw [h1]
      by_cases h2 : i = w; · right; left; rw [h2]
      by_cases h3 : i = b; · right; right; left; rw [h3]
      exact Or.inr (Or.inr (Or.inr ⟨i, hi, h1, h2, h3, rfl⟩))
    · rintro (rfl | rfl | rfl | ⟨i, hi, -, -, -, rfl⟩)
      exacts [⟨v, hvB, rfl⟩, ⟨w, hwB, rfl⟩, ⟨b, hbB, rfl⟩, ⟨i, hi, rfl⟩]
  have notMa : ∀ j, j ∉ Sa → x j ∉ Ma := by
    intro j hj hm
    obtain ⟨i, hi, -, -, -, he⟩ := (memMa _).mp hm
    exact hj (hx he ▸ hi)
  have notMb : ∀ j, j ∉ Sb → x j ∉ Mb := by
    intro j hj hm
    obtain ⟨i, hi, -, -, -, he⟩ := (memMb _).mp hm
    exact hj (hx he ▸ hi)
  have ne : ∀ {i j : Fin n}, (i ∈ Sa ∧ j ∉ Sa) ∨ (i ∈ Sb ∧ j ∉ Sb) → x j ≠ x i := by
    rintro i j (⟨hi, hj⟩ | ⟨hi, hj⟩) e <;> exact hj (hx e ▸ hi)
  have E : EdgeConf V u (x v) (x w) (x a) (x b) (x c) 1 Na Nb κa κb Ma Mb := {
    hu := hu
    hh := one_ne_zero
    hw := by rw [one_smul, hudef]; abel
    hv := mem v
    hwV := mem w
    ha := mem a
    hb := mem b
    hc := mem c
    hMa := fun z hz => by obtain ⟨i, -, -, -, -, rfl⟩ := (memMa z).mp hz; exact mem i
    hMb := fun z hz => by obtain ⟨i, -, -, -, -, rfl⟩ := (memMb z).mp hz; exact mem i
    faceA := by
      intro z hz
      obtain ⟨i, -, rfl⟩ := mem_image.mp hz
      constructor
      · rintro (e | e | e | e)
        · rw [hx e]; exact (hfa v).1 hvA
        · rw [hx e]; exact (hfa w).1 hwA
        · rw [hx e]; exact (hfa a).1 haA
        · obtain ⟨j, hj, -, -, -, he⟩ := (memMa _).mp e
          rw [← he]; exact (hfa j).1 hj
      · intro he
        have hi : i ∈ Sa := by
          by_contra hi; exact absurd he ((hfa i).2 hi).ne
        by_cases h1 : i = v; · left; rw [h1]
        by_cases h2 : i = w; · right; left; rw [h2]
        by_cases h3 : i = a; · right; right; left; rw [h3]
        exact Or.inr (Or.inr (Or.inr ((memMa _).mpr ⟨i, hi, h1, h2, h3, rfl⟩)))
    faceA_le := by
      intro z hz
      obtain ⟨i, -, rfl⟩ := mem_image.mp hz
      by_cases hi : i ∈ Sa
      · exact ((hfa i).1 hi).le
      · exact ((hfa i).2 hi).le
    faceB := by
      intro z hz
      obtain ⟨i, -, rfl⟩ := mem_image.mp hz
      constructor
      · rintro (e | e | e | e)
        · rw [hx e]; exact (hfb v).1 hvB
        · rw [hx e]; exact (hfb w).1 hwB
        · rw [hx e]; exact (hfb b).1 hbB
        · obtain ⟨j, hj, -, -, -, he⟩ := (memMb _).mp e
          rw [← he]; exact (hfb j).1 hj
      · intro he
        have hi : i ∈ Sb := by
          by_contra hi; exact absurd he ((hfb i).2 hi).ne
        by_cases h1 : i = v; · left; rw [h1]
        by_cases h2 : i = w; · right; left; rw [h2]
        by_cases h3 : i = b; · right; right; left; rw [h3]
        exact Or.inr (Or.inr (Or.inr ((memMb _).mpr ⟨i, hi, h1, h2, h3, rfl⟩)))
    faceB_le := by
      intro z hz
      obtain ⟨i, -, rfl⟩ := mem_image.mp hz
      by_cases hi : i ∈ Sb
      · exact ((hfb i).1 hi).le
      · exact ((hfb i).2 hi).le
    hbA := ⟨ne (Or.inl ⟨hvA, hbA⟩), ne (Or.inl ⟨hwA, hbA⟩), ne (Or.inl ⟨haA, hbA⟩),
      notMa b hbA⟩
    hcA := ⟨ne (Or.inl ⟨hvA, hcA⟩), ne (Or.inl ⟨hwA, hcA⟩), ne (Or.inl ⟨haA, hcA⟩),
      notMa c hcA⟩
    haB := ⟨ne (Or.inr ⟨hvB, haB⟩), ne (Or.inr ⟨hwB, haB⟩), notMb a haB⟩
    hcB := ⟨ne (Or.inr ⟨hbB, hcB⟩), notMb c hcB⟩
    hMa' := by
      intro z hz
      obtain ⟨i, -, h1, h2, h3, rfl⟩ := (memMa z).mp hz
      exact ⟨hx.ne h1, hx.ne h2, hx.ne h3⟩
    hMb' := by
      intro z hz
      obtain ⟨i, -, h1, h2, h3, rfl⟩ := (memMb z).mp hz
      exact ⟨hx.ne h1, hx.ne h2, hx.ne h3⟩
    left := hleft
    par := hgen.par
    g1 := by rw [← hSAeq, ← hSBeq]; exact hgen.g1
    noSeg := by
      intro p hp q hq y hy hyp hyq s hs0 hs1
      obtain ⟨i, -, rfl⟩ := mem_image.mp hp
      obtain ⟨j, -, rfl⟩ := mem_image.mp hq
      obtain ⟨m, -, rfl⟩ := mem_image.mp hy
      exact hseg i j m hyp hyq s hs0 hs1
    supp := hsupp }
  have hMa1 : ∀ m ∈ Ma, ∀ m' ∈ Ma, m = m' := by
    intro z hz z' hz'
    obtain ⟨i, hi, h1, h2, h3, rfl⟩ := (memMa z).mp hz
    obtain ⟨j, hj, k1, k2, k3, rfl⟩ := (memMa z').mp hz'
    rw [hA1 i hi j hj h1 h2 h3 k1 k2 k3]
  have hMb1 : ∀ m ∈ Mb, ∀ m' ∈ Mb, m = m' := by
    intro z hz z' hz'
    obtain ⟨i, hi, h1, h2, h3, rfl⟩ := (memMb z).mp hz
    obtain ⟨j, hj, k1, k2, k3, rfl⟩ := (memMb z').mp hz'
    rw [hB1 i hi j hj h1 h2 h3 k1 k2 k3]
  have imgA : ∀ i ∈ Sa, x i ∈ Sa.image x := fun i hi => mem_image_of_mem x hi
  have imgB : ∀ i ∈ Sb, x i ∈ Sb.image x := fun i hi => mem_image_of_mem x hi
  have nimA : ∀ i ∉ Sa, x i ∉ Sa.image x := fun i hi h => by
    obtain ⟨j, hj, he⟩ := mem_image.mp h; exact hi (hx he ▸ hj)
  have nimB : ∀ i ∉ Sb, x i ∉ Sb.image x := fun i hi h => by
    obtain ⟨j, hj, he⟩ := mem_image.mp h; exact hi (hx he ▸ hj)
  have fA := fun p (hp : p ∈ Sa) => footA_of_gen hgen.footA (imgA p hp) (imgA a haA) (mem c)
    (mem b) (nimA c hcA) (nimA b hbA)
  have fB := fun p (hp : p ∈ Sb) => footA_of_gen hgen.footB (imgB p hp) (imgB b hbB) (mem c)
    (mem a) (nimB c hcB) (nimB a haB)
  have hEa : ⟪Na, x c⟫ = ⟪Na, x b⟫ → det3 (x c - x a) (x b - x a) (x v - x a) *
      det3 (x c - x a) (x b - x a) (x w - x a) < 0 := fun _ => by
    rw [det3_lemmaE_swap (x a) (x b) (x c) (x v), det3_lemmaE_swap (x a) (x b) (x c) (x w),
      neg_mul_neg]; exact hEstrict
  have hEb : ⟪Nb, x c⟫ = ⟪Nb, x a⟫ → det3 (x c - x b) (x a - x b) (x v - x b) *
      det3 (x c - x b) (x a - x b) (x w - x b) < 0 := fun _ => by
    rw [det3_lemmaE_mirror (x a) (x b) (x c) (x v), det3_lemmaE_mirror (x a) (x b) (x c) (x w)]
    exact hEstrict
  -- the frequent closing
  have hdq : ∀ p : ℝ³, ∀ i : ZMod 4, p = x v ∨ p = x w → Function.Injective
      (fun i => ⟪quad p (x a) (x c) (x b) i, u⟫) := by
    intro p i hp j k hjk
    have hpV : p ∈ V := by rcases hp with rfl | rfl; exacts [mem v, mem w]
    have hpq : ∀ i, quad p (x a) (x c) (x b) i ∈ V := by
      intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
      exacts [hpV, mem a, mem c, mem b]
    have hinjq : Function.Injective (quad p (x a) (x c) (x b)) := by
      rcases hp with rfl | rfl
      · exact E.quad_injective
      · exact E.swap.quad_injective
    by_contra hne
    exact hgen.dist _ (hpq j) _ (hpq k) (hinjq.ne hne) hjk
  have hNfreq := hfacts.mono fun k hk => hk.1.2.2
  rcases frequently_or_distrib.mp hNfreq with hNv | hNw
  · have hz : NWS4 (quad ⟪x v, u⟫ ⟪x a, u⟫ ⟪x c, u⟫ ⟪x b, u⟫) := by
      have hinj := hdq (x v) 0 (Or.inl rfl)
      rw [quad_inner'] at hinj
      refine nws4_of_tendsto (fun i => ?_) hinj hNv
      rcases zmod4_cases i with rfl | rfl | rfl | rfl
      exacts [(hK v).inner hus, (hK a).inner hus, (hK c).inner hus, (hK b).inner hus]
    refine E.isRupert_edgeClosing hMa1 hMb1 ?_ hgen.dist hgen.one (fA v hvA) (fB v hvB)
      (fun h _ => hEa h) (fun h _ => hEb h)
    rw [quad_inner']
    exact hz.isRobustUnimodal
  · have hz : NWS4 (quad ⟪x w, u⟫ ⟪x a, u⟫ ⟪x c, u⟫ ⟪x b, u⟫) := by
      have hinj := hdq (x w) 0 (Or.inr rfl)
      rw [quad_inner'] at hinj
      refine nws4_of_tendsto (fun i => ?_) hinj hNw
      rcases zmod4_cases i with rfl | rfl | rfl | rfl
      exacts [(hK w).inner hus, (hK a).inner hus, (hK c).inner hus, (hK b).inner hus]
    refine E.swap.isRupert_edgeClosing hMa1 hMb1 ?_ hgen.dist hgen.one (fA w hwA) (fB w hwB)
      (fun h _ => by rw [mul_comm]; exact hEa h) (fun h _ => by rw [mul_comm]; exact hEb h)
    rw [quad_inner']
    exact hz.isRobustUnimodal

/-! ### Triangle closings (two realizing circles) -/
/-- A triangle closing in the clockwise orientation is the closing with `a`, `b` exchanged. -/
theorem ETriData.flip {V : Finset ℝ³} {v w a b : ℝ³} (h : ETriData V (-1) v w a b) :
    ETriData V 1 v w b a := by
  obtain ⟨-, hT, hz, hV⟩ := h
  have e : det3 (b - v) (a - v) (w - v) = -det3 (a - v) (b - v) (w - v) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  refine ⟨Or.inl rfl, by rw [one_mul, e]; linarith, fun h => hz ⟨h.1.trans h.2, h.2.symm⟩,
    fun z hz' => ?_⟩
  rcases hV z hz' with h | h | h | h | h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h.swap))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))))
    · rw [one_mul, det3_rev]; linarith
    · rw [one_mul, det3_rev]; linarith
    · rw [one_mul, det3_rev]; linarith

/-- **A face realizes the closing** when the side `p q` of the rim on it is an edge of the face
(an adjacent facet through `p`, `q`, below at the other vertices): every other vertex `z` of the
face lies on `w`'s side of the chord. -/
theorem real_of_adj {N NG p q w z : ℝ³} (hq : ⟪N, q - p⟫ = 0) (hw : ⟪N, w - p⟫ = 0)
    (hz : ⟪N, z - p⟫ = 0) (hqw : cross (q - p) (w - p) ≠ 0) (hN : N ≠ 0)
    (hGq : ⟪NG, q - p⟫ = 0) (hGw : ⟪NG, w - p⟫ < 0) (hGz : ⟪NG, z - p⟫ < 0) :
    ∃ k : ℝ, 0 < k ∧ cross (q - p) (z - p) = k • cross (q - p) (w - p) := by
  obtain ⟨α, β, hzab⟩ := EdgeConf.exists_coords_of_perp hq hw hz hqw hN
  have hβ : ⟪NG, z - p⟫ = β * ⟪NG, w - p⟫ := by
    rw [hzab, inner_add_right, real_inner_smul_right, real_inner_smul_right, hGq]; ring
  refine ⟨β, ?_, ?_⟩
  · rw [hβ] at hGz; exact pos_of_mul_neg_left hGz hGw.le |> fun h => by nlinarith
  · rw [hzab]; ext j; fin_cases j <;> simp [cross] <;> ring

end Minimality

end
