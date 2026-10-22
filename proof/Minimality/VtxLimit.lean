module

public import Minimality.VtxMain

@[expose] public section

/-!
# Vertex closings at the limit (`FEWER-FACES-PROOFS.md` §18.2 with §22.9, §22.10)

A limit shape `x` of shapes `K_k` that carry one labelled four-corner rim certificate at a
vertex view `u_k → u`, where the two faces of the crossing are a quadrilateral `S_a` with its
apex `v` and far end `a` opposite (middles `p` above, `q` below the chord along `u`) and a
triangle `S_b` (middle `m`): the rim passes to the limit (Lemma 18.2: weakly convex, every point
in the cylinder over it, robust unimodality with distinct depths), and §22's conditions at `u`
(`VtxGen`) with (H4) or Lemma 22.10's coplanarity make `x` Rupert
(`VtxConf.isRupert_vtxClosing`).

* `VtxGen`: the conditions at the view (each fails in codimension 1; with a horizontal double
  normal at the view, in codimension 2).
* `isRupert_vtx_limit`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- **The conditions of §22.4 at a vertex view `u`** (faces `SA` (the quadrilateral, normal
`NA`), `SB`): no two points over one point, (G1), distinct depths, at most one direction of
horizontal double normals, and no double normal perpendicular to `SA` from a vertex of `SA`. -/
structure VtxGen (V : Finset ℝ³) (u : ℝ³) (SA SB : Finset ℝ³) (NA : ℝ³) : Prop where
  par : NoParAt V u
  g1 : G1At V u SA SB
  dist : ∀ y ∈ V, ∀ y' ∈ V, y ≠ y' → ⟪y, u⟫ ≠ ⟪y', u⟫
  one : OneHDNDir V u
  footA : NormalFootGen V NA SA

theorem VtxGen.smul {V : Finset ℝ³} {u : ℝ³} {SA SB : Finset ℝ³} {NA : ℝ³}
    (h : VtxGen V u SA SB NA) {r : ℝ} (hr : 0 < r) : VtxGen V (r • u) SA SB NA where
  par := fun y hy y' hy' hne => by
    rw [cross_smul_right']; exact smul_ne_zero hr.ne' (h.par y hy y' hy' hne)
  g1 := fun p hp q hq y hy hc hl h0 h1 h2 => by
    refine h.g1 p hp q hq y hy ?_ ?_ ?_ h1 h2
    · intro e; apply hc; rw [cross_smul_right', e, smul_zero]
    · intro z hz; have := hl z hz; rw [det3_smul_right] at this
      exact nonneg_of_mul_nonneg_right (by linarith) hr
    · rw [det3_smul_right] at h0; exact (mul_eq_zero.mp h0).resolve_left hr.ne'
  dist := fun y hy y' hy' hne e => by
    rw [real_inner_smul_right, real_inner_smul_right] at e
    exact h.dist y hy y' hy' hne (mul_left_cancel₀ hr.ne' e)
  one := fun ℓ ℓ' h1 h2 => h.one ℓ ℓ'
    ⟨h1.1, by have := h1.2.1; rw [real_inner_smul_right] at this
              exact (mul_eq_zero.mp this).resolve_left hr.ne', h1.2.2⟩
    ⟨h2.1, by have := h2.2.1; rw [real_inner_smul_right] at this
              exact (mul_eq_zero.mp this).resolve_left hr.ne', h2.2.2⟩
  footA := h.footA

theorem VtxGen.neg {V : Finset ℝ³} {u : ℝ³} {SA SB : Finset ℝ³} {NA : ℝ³}
    (h : VtxGen V u SA SB NA) : VtxGen V (-u) SA SB NA where
  par := fun y hy y' hy' hne => by
    rw [cross_neg_right']; exact neg_ne_zero.mpr (h.par y hy y' hy' hne)
  g1 := fun p hp q hq y hy hc hl h0 h1 h2 =>
    (EdgeConf.G1At.neg h.g1 p hp q hq y hy hc hl h0 h1 h2).symm
  dist := fun y hy y' hy' hne e => by
    simp only [inner_neg_right, neg_inj] at e; exact h.dist y hy y' hy' hne e
  one := h.one.neg_u
  footA := h.footA

/-- `VtxGen` at `u` gives it at `±u`. -/
theorem VtxGen.sign {V : Finset ℝ³} {u : ℝ³} {SA SB : Finset ℝ³} {NA : ℝ³}
    (h : VtxGen V u SA SB NA) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) : VtxGen V (ε • u) SA SB NA := by
  rcases hε with rfl | rfl
  · rwa [one_smul]
  · rw [neg_one_smul]; exact h.neg

set_option maxHeartbeats 1000000 in
/-- **A vertex closing at the limit** (Lemma 18.2 with §22.9, §22.10).  The shapes `K_k → x`
carry one labelled four-corner rim certificate `v a c b` at views `u_k → u`; at the limit `u`
lies in the planes of the facets `S_a = {v, a, p, q}` (a quadrilateral with `p` above and `q`
below the chord `v a` along `u`) and `S_b = {v, b, m}`; at `u` the conditions of §22.4 hold
(`VtxGen`), and where the far edge `[c, b]` is parallel to `S_a`, (H4) or Lemma 22.10's
coplanarity holds in both senses (`hD`, which may use the configuration at the limit, e.g.
`VtxConf.hD_of_copl`).  Then `x` is Rupert. -/
theorem isRupert_vtx_limit {n : ℕ} (x : Fin n → ℝ³) (hx : Function.Injective x)
    (hseg : ∀ i j m : Fin n, x m ≠ x i → x m ≠ x j → ∀ s : ℝ, 0 < s → s < 1 →
      x m ≠ x i + s • (x j - x i))
    {v a c b p q m : Fin n} (hlab : [v, a, c, b, p, q, m].Nodup)
    {Sa Sb : Finset (Fin n)} (hSa : Sa = {v, a, p, q}) (hSb : Sb = {v, b, m})
    {Na Nb : ℝ³} {κa κb : ℝ}
    (hfa : ∀ i, (i ∈ Sa → ⟪Na, x i⟫ = κa) ∧ (i ∉ Sa → ⟪Na, x i⟫ < κa))
    (hfb : ∀ i, (i ∈ Sb → ⟪Nb, x i⟫ = κb) ∧ (i ∉ Sb → ⟪Nb, x i⟫ < κb))
    {u : ℝ³} (hu : u ≠ 0) (hNa : ⟪Na, u⟫ = 0) (hNb : ⟪Nb, u⟫ = 0)
    (hpu : ∃ s δ : ℝ, 0 < δ ∧ x p = x v + s • (x a - x v) + δ • u)
    (hqu : ∃ s δ : ℝ, δ < 0 ∧ x q = x v + s • (x a - x v) + δ • u)
    (K : ℕ → Fin n → ℝ³) (hK : ∀ i, Tendsto (fun k => K k i) atTop (𝓝 (x i)))
    (us : ℕ → ℝ³) (hus : Tendsto us atTop (𝓝 u))
    (hfreq : ∃ᶠ k in atTop,
      RimCertPts (univ.image (K k)) (us k) (quad (K k v) (K k a) (K k c) (K k b)))
    (hgen : VtxGen (univ.image x) u (Sa.image x) (Sb.image x) Na)
    (hD : VtxConf (univ.image x) u (x v) (x a) (x c) (x b) (x p) (x q) (x m) Na Nb κa κb →
      ⟪Na, x c⟫ = ⟪Na, x b⟫ → VtxConf.H4orCopl u (x v) (x a) (x c) (x b) (x p) 1 ∧
      VtxConf.H4orCopl u (x v) (x a) (x c) (x b) (x q) (-1)) :
    IsRupert (univ.image x) := by
  classical
  set V := univ.image x with hVdef
  have mem : ∀ i, x i ∈ V := fun i => mem_image_of_mem x (mem_univ i)
  have memK : ∀ k i, K k i ∈ univ.image (K k) := fun k i => mem_image_of_mem _ (mem_univ i)
  have hl := hlab
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hl
  obtain ⟨⟨hva, hvc, hvb, hvp, hvq, hvm⟩, ⟨hac, hab, hap, haq, ham⟩, ⟨hcb, hcp, hcq, hcm⟩,
    ⟨hbp, hbq, hbm⟩, ⟨hpq, hpm⟩, hqm⟩ := hl
  -- the approximants' facts and their limits
  have hXq : ∀ i, Tendsto (fun k => quad (K k v) (K k a) (K k c) (K k b) i) atTop
      (𝓝 (quad (x v) (x a) (x c) (x b) i)) := by
    intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
    exacts [hK v, hK a, hK c, hK b]
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  have lim0 : ∀ {f : ℕ → ℝ} {L : ℝ}, Tendsto f atTop (𝓝 L) → (∃ᶠ k in atTop, 0 ≤ f k) →
      0 ≤ L := fun hf hfr => le_of_tendsto_frequently tendsto_const_nhds hf hfr
  have hleft : ∀ z ∈ V, 0 ≤ det3 (x a - x v) (z - x v) u ∧ 0 ≤ det3 (x c - x a) (z - x a) u ∧
      0 ≤ det3 (x b - x c) (z - x c) u ∧ 0 ≤ det3 (x v - x b) (z - x b) u := by
    intro z hz
    obtain ⟨i, -, rfl⟩ := mem_image.mp hz
    refine ⟨lim0 (Tendsto.det3' ((hK a).sub (hK v)) ((hK i).sub (hK v)) hus)
      (hfreq.mono fun k hk => by simpa [a0, quad_0, quad_1] using hk.left _ (memK k i) 0),
      lim0 (Tendsto.det3' ((hK c).sub (hK a)) ((hK i).sub (hK a)) hus)
      (hfreq.mono fun k hk => by simpa [a1, quad_1, quad_2] using hk.left _ (memK k i) 1),
      lim0 (Tendsto.det3' ((hK b).sub (hK c)) ((hK i).sub (hK c)) hus)
      (hfreq.mono fun k hk => by simpa [a2, quad_2, quad_3] using hk.left _ (memK k i) 2),
      lim0 (Tendsto.det3' ((hK v).sub (hK b)) ((hK i).sub (hK b)) hus)
      (hfreq.mono fun k hk => by simpa [a3, quad_3, quad_0] using hk.left _ (memK k i) 3)⟩
  have hsupp : ∀ z ∈ V, SuppIn u (quad (x v) (x a) (x c) (x b)) z := by
    intro z hz
    obtain ⟨i, -, rfl⟩ := mem_image.mp hz
    refine suppIn_of_tendsto hu hus hXq (hK i) (hfreq.mono fun k hk => ?_)
    have hne : us k ≠ 0 := by
      intro h0
      have := hk.cyc 0 2 (by decide) (by decide)
      rw [h0] at this; simp [det3_expand] at this
    exact rimCertPts_suppIn hk hne _ (memK k i)
  have hrob : IsRobustUnimodal (fun i => ⟪quad (x v) (x a) (x c) (x b) i, u⟫) := by
    refine isRobustUnimodal_of_tendsto_ties (fun i => (hXq i).inner hus)
      (hfreq.mono fun k hk => ⟨hk.robust, fun i i' e => ?_⟩)
    by_cases hii : i = i'
    · rw [hii]
    · exfalso
      have hq : Function.Injective (quad (x v) (x a) (x c) (x b)) := by
        intro i j hij
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
          rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
          simp only [quad_0, quad_1, quad_2, quad_3] at hij <;>
          first | rfl | (exfalso; exact (hx.ne (by assumption)) hij) |
            (exfalso; exact (hx.ne (Ne.symm (by assumption))) hij)
      have hm : ∀ i, quad (x v) (x a) (x c) (x b) i ∈ V := by
        intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
        exacts [mem v, mem a, mem c, mem b]
      exact hgen.dist _ (hm i) _ (hm i') (hq.ne hii) e
  -- the configuration at the limit
  have hSAeq : Sa.image x = {x v, x a, x p, x q} := by
    rw [hSa]; simp [Finset.image_insert, Finset.image_singleton]
  have hSBeq : Sb.image x = {x v, x b, x m} := by
    rw [hSb]; simp [Finset.image_insert, Finset.image_singleton]
  have E : VtxConf V u (x v) (x a) (x c) (x b) (x p) (x q) (x m) Na Nb κa κb := {
    hu := hu
    hv := mem v
    ha := mem a
    hb := mem b
    hc := mem c
    hp := mem p
    hq := mem q
    hn := mem m
    faceA := by
      intro z hz
      obtain ⟨i, -, rfl⟩ := mem_image.mp hz
      constructor
      · intro h
        have hi : i ∈ Sa := by
          rw [hSa]
          rcases h with e | e | e | e <;> rw [hx e] <;> simp
        exact (hfa i).1 hi
      · intro he
        have hi : i ∈ Sa := by
          by_contra hi; exact absurd he ((hfa i).2 hi).ne
        rw [hSa] at hi
        simp only [mem_insert, mem_singleton] at hi
        rcases hi with rfl | rfl | rfl | rfl
        exacts [Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inl rfl)),
          Or.inr (Or.inr (Or.inr rfl))]
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
      · intro h
        have hi : i ∈ Sb := by
          rw [hSb]
          rcases h with e | e | e <;> rw [hx e] <;> simp
        exact (hfb i).1 hi
      · intro he
        have hi : i ∈ Sb := by
          by_contra hi; exact absurd he ((hfb i).2 hi).ne
        rw [hSb] at hi
        simp only [mem_insert, mem_singleton] at hi
        rcases hi with rfl | rfl | rfl
        exacts [Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)]
    faceB_le := by
      intro z hz
      obtain ⟨i, -, rfl⟩ := mem_image.mp hz
      by_cases hi : i ∈ Sb
      · exact ((hfb i).1 hi).le
      · exact ((hfb i).2 hi).le
    Na_u := hNa
    Nb_u := hNb
    nodup := by
      have := hlab.map hx
      simpa using this
    left := hleft
    par := hgen.par
    g1 := by rw [← hSAeq, ← hSBeq]; exact hgen.g1
    noSeg := by
      intro p' hp' q' hq' y hy hyp hyq s hs0 hs1
      obtain ⟨i, -, rfl⟩ := mem_image.mp hp'
      obtain ⟨j, -, rfl⟩ := mem_image.mp hq'
      obtain ⟨k, -, rfl⟩ := mem_image.mp hy
      exact hseg i j k hyp hyq s hs0 hs1
    supp := hsupp
    hpu := hpu
    hqu := hqu }
  have hvS : x v ∈ Sa.image x := by rw [hSAeq]; simp
  have haS : x a ∈ Sa.image x := by rw [hSAeq]; simp
  have hcS : x c ∉ Sa.image x := by
    rw [hSAeq]; simp only [mem_insert, mem_singleton, not_or]
    exact ⟨hx.ne (Ne.symm hvc), hx.ne (Ne.symm hac), hx.ne hcp, hx.ne hcq⟩
  have hbS : x b ∉ Sa.image x := by
    rw [hSAeq]; simp only [mem_insert, mem_singleton, not_or]
    exact ⟨hx.ne (Ne.symm hvb), hx.ne (Ne.symm hab), hx.ne hbp, hx.ne hbq⟩
  exact E.isRupert_vtxClosing hrob hgen.dist hgen.one
    (footA_of_gen hgen.footA hvS haS (mem c) (mem b) hcS hbS) (hD E)

end Minimality

end
