module

public import Minimality.HullChain
public import Minimality.TriFaces
public import Minimality.TriBridge

@[expose] public section

/-!
# Lemma T for two facets sharing a vertex

Lemma T of `FEWER-FACES-PROOFS.md` §7 for any two facets `Q1`, `Q2` of `V`
meeting in one vertex `v`: view `V` along the line of the two planes; if every
point off both facets projects strictly inside the triangle of `v` and the far
points of the two facets, `V` is Rupert.  The faces may have any number of
vertices: their chains come from `exists_chainOK` (gift wrapping).

The interior condition is stated with the facet functionals: for the far
points (or any points) `xa ∈ Q1`, `xb ∈ Q2` other than `v`,
`f2 y / f2 xa + f1 y / f1 xb < 1`, the barycentric form of "inside the shadow
triangle `v, xa, xb`" (in the plane of `Q1`, `f2` measures the distance from the
view line, and vice versa).
-/

namespace Minimality

open Finset Filter Topology
open scoped RealInnerProductSpace

set_option maxHeartbeats 4000000 in
/-- **Lemma T over a vertex, in frame coordinates.**  The points of `V` are
`oblPt O r1 r2 (a p) (b p) (p 2)`; `Q1` lies on the ray `b = 0`, `Q2` on `a = 0`,
every other point at `a, b > 0`. -/
theorem isRupert_vertex_coords (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (V Q1 Q2 : Finset ℝ³)
    (v : ℝ³) (a b : ℝ³ → ℝ) (hy : ∀ p ∈ V, p = oblPt O r1 r2 (a p) (b p) (p 2))
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v})
    (hb1 : ∀ p ∈ Q1, b p = 0) (hb1' : ∀ p ∈ V, p ∉ Q1 → 0 < b p)
    (ha2 : ∀ p ∈ Q2, a p = 0) (ha2' : ∀ p ∈ V, p ∉ Q2 → 0 < a p)
    (hne1 : ∃ p ∈ Q1, p ≠ v) (hne2 : ∃ p ∈ Q2, p ≠ v)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hinj : Set.InjOn (fun p => (a p, b p)) (V : Set ℝ³))
    (hfarZ : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, a p' ≤ a p) → (∀ q' ∈ Q2, b q' ≤ b q) →
      p 2 ≠ q 2)
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ≠ v ∧ xb ≠ v ∧
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → a y / a xa + b y / b xb < 1) : IsRupert V := by
  classical
  have hv1 : v ∈ Q1 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).1
  have hv2 : v ∈ Q2 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).2
  have only : ∀ p ∈ Q1, p ∈ Q2 → p = v := by
    intro p h1 h2
    have : p ∈ Q1 ∩ Q2 := Finset.mem_inter.mpr ⟨h1, h2⟩
    rwa [hint, Finset.mem_singleton] at this
  have hav : a v = 0 := ha2 v hv2
  have hbv : b v = 0 := hb1 v hv1
  have apos : ∀ p ∈ Q1, p ≠ v → 0 < a p := fun p hp hpv =>
    ha2' p (h1V hp) (fun h => hpv (only p hp h))
  have bpos : ∀ p ∈ Q2, p ≠ v → 0 < b p := fun p hp hpv =>
    hb1' p (h2V hp) (fun h => hpv (only p h hp))
  -- the faces in their planes
  set S1 := Q1.image (fun p => (a p, p 2)) with hS1
  set S2 := Q2.image (fun p => (b p, p 2)) with hS2
  have ofS1 : ∀ x z, (x, z) ∈ S1 → ∃ p ∈ Q1, a p = x ∧ p 2 = z := by
    intro x z h; rw [hS1, Finset.mem_image] at h
    obtain ⟨p, hp, e⟩ := h; simp only [Prod.mk.injEq] at e; exact ⟨p, hp, e.1, e.2⟩
  have ofS2 : ∀ x z, (x, z) ∈ S2 → ∃ p ∈ Q2, b p = x ∧ p 2 = z := by
    intro x z h; rw [hS2, Finset.mem_image] at h
    obtain ⟨p, hp, e⟩ := h; simp only [Prod.mk.injEq] at e; exact ⟨p, hp, e.1, e.2⟩
  have pt1 : ∀ p ∈ Q1, p = oblPt O r1 r2 (a p) 0 (p 2) := fun p hp => by
    conv_lhs => rw [hy p (h1V hp), hb1 p hp]
  have pt2 : ∀ p ∈ Q2, p = oblPt O r1 r2 0 (b p) (p 2) := fun p hp => by
    conv_lhs => rw [hy p (h2V hp), ha2 p hp]
  -- chains
  have chains1 : ∀ s : ℝ, (s = 1 ∨ s = -1) → ∃ m ca cz, ChainOK (fun x z => (x, z) ∈ S1) (v 2) s m ca cz := by
    intro s hs
    apply exists_chainOK S1 (v 2) (by rw [hS1, Finset.mem_image]; exact ⟨v, hv1, by rw [hav]⟩)
    · intro q hq hne
      obtain ⟨p, hp, e1, e2⟩ := ofS1 q.1 q.2 hq
      rw [← e1]; refine apos p hp (fun h => hne ?_)
      exact Prod.ext (by show q.1 = 0; rw [← e1, h, hav]) (by show q.2 = v 2; rw [← e2, h])
    · obtain ⟨p, hp, hpv⟩ := hne1
      refine ⟨(a p, p 2), Finset.mem_image_of_mem _ hp, fun h => ?_⟩
      have := congrArg Prod.fst h; simp only at this; linarith [apos p hp hpv]
    · intro q hq q' hq' e
      obtain ⟨p, hp, e1, e2⟩ := ofS1 q.1 q.2 hq
      obtain ⟨p', hp', e1', e2'⟩ := ofS1 q'.1 q'.2 hq'
      have : p = p' := hinj (h1V hp) (h1V hp') (by simp only [Prod.mk.injEq]; rw [hb1 p hp, hb1 p' hp']; exact ⟨by rw [e1, e1']; exact e, rfl⟩)
      exact Prod.ext e (by rw [← e2, ← e2', this])
    · intro q hq q' hq' q'' hq'' n1 n2 n3
      obtain ⟨p, hp, e1, e2⟩ := ofS1 q.1 q.2 hq
      obtain ⟨p', hp', e1', e2'⟩ := ofS1 q'.1 q'.2 hq'
      obtain ⟨p'', hp'', e1'', e2''⟩ := ofS1 q''.1 q''.2 hq''
      have d : ∀ {r r' : ℝ × ℝ} {u u' : ℝ³}, r ≠ r' → a u = r.1 → u 2 = r.2 → a u' = r'.1 →
          u' 2 = r'.2 → u ≠ u' := by
        intro r r' u u' h h1 h2 h1' h2' hu; apply h
        exact Prod.ext (by rw [← h1, ← h1', hu]) (by rw [← h2, ← h2', hu])
      have hne : a p ≠ a p' := fun h => d n1 e1 e2 e1' e2'
        (hinj (h1V hp) (h1V hp') (by simp only [Prod.mk.injEq]; rw [hb1 p hp, hb1 p' hp']; exact ⟨h, rfl⟩))
      have := orient_ne_of_frame1 (O := O) (r1 := r1) (r2 := r2) (zi := p 2) (zj := p' 2) (zk := p'' 2)
        (ak := a p'') hne (by
          intro c; rw [← pt1 p hp, ← pt1 p' hp', ← pt1 p'' hp'']
          exact hcol p (h1V hp) p' (h1V hp') p'' (h1V hp'') (d n1 e1 e2 e1' e2')
            (d n2 e1 e2 e1'' e2'') (d n3 e1' e2' e1'' e2'') c)
      unfold orient2 at this; rwa [e1, e2, e1', e2', e1'', e2''] at this
    · exact hs
  have chains2 : ∀ s : ℝ, (s = 1 ∨ s = -1) → ∃ m ca cz, ChainOK (fun x z => (x, z) ∈ S2) (v 2) s m ca cz := by
    intro s hs
    apply exists_chainOK S2 (v 2) (by rw [hS2, Finset.mem_image]; exact ⟨v, hv2, by rw [hbv]⟩)
    · intro q hq hne
      obtain ⟨p, hp, e1, e2⟩ := ofS2 q.1 q.2 hq
      rw [← e1]; refine bpos p hp (fun h => hne ?_)
      exact Prod.ext (by show q.1 = 0; rw [← e1, h, hbv]) (by show q.2 = v 2; rw [← e2, h])
    · obtain ⟨p, hp, hpv⟩ := hne2
      refine ⟨(b p, p 2), Finset.mem_image_of_mem _ hp, fun h => ?_⟩
      have := congrArg Prod.fst h; simp only at this; linarith [bpos p hp hpv]
    · intro q hq q' hq' e
      obtain ⟨p, hp, e1, e2⟩ := ofS2 q.1 q.2 hq
      obtain ⟨p', hp', e1', e2'⟩ := ofS2 q'.1 q'.2 hq'
      have : p = p' := hinj (h2V hp) (h2V hp') (by simp only [Prod.mk.injEq]; rw [ha2 p hp, ha2 p' hp']; exact ⟨rfl, by rw [e1, e1']; exact e⟩)
      exact Prod.ext e (by rw [← e2, ← e2', this])
    · intro q hq q' hq' q'' hq'' n1 n2 n3
      obtain ⟨p, hp, e1, e2⟩ := ofS2 q.1 q.2 hq
      obtain ⟨p', hp', e1', e2'⟩ := ofS2 q'.1 q'.2 hq'
      obtain ⟨p'', hp'', e1'', e2''⟩ := ofS2 q''.1 q''.2 hq''
      have d : ∀ {r r' : ℝ × ℝ} {u u' : ℝ³}, r ≠ r' → b u = r.1 → u 2 = r.2 → b u' = r'.1 →
          u' 2 = r'.2 → u ≠ u' := by
        intro r r' u u' h h1 h2 h1' h2' hu; apply h
        exact Prod.ext (by rw [← h1, ← h1', hu]) (by rw [← h2, ← h2', hu])
      have hne : b p ≠ b p' := fun h => d n1 e1 e2 e1' e2'
        (hinj (h2V hp) (h2V hp') (by simp only [Prod.mk.injEq]; rw [ha2 p hp, ha2 p' hp']; exact ⟨rfl, h⟩))
      have := orient_ne_of_frame2 (O := O) (r1 := r1) (r2 := r2) (zi := p 2) (zj := p' 2) (zk := p'' 2)
        (bk := b p'') hne (by
          intro c; rw [← pt2 p hp, ← pt2 p' hp', ← pt2 p'' hp'']
          exact hcol p (h2V hp) p' (h2V hp') p'' (h2V hp'') (d n1 e1 e2 e1' e2')
            (d n2 e1 e2 e1'' e2'') (d n3 e1' e2' e1'' e2'') c)
      unfold orient2 at this; rwa [e1, e2, e1', e2', e1'', e2''] at this
    · exact hs
  obtain ⟨xa, hxa, xb, hxb, hxav, hxbv, hin'⟩ := hin
  refine isRupert_vertex_frame O r1 r2 hρ (fun x z => (x, z) ∈ S1) (fun x z => (x, z) ∈ S2)
    (z0 := v 2) (chains1 1 (Or.inl rfl)) (chains1 (-1) (Or.inr rfl)) (chains2 1 (Or.inl rfl))
    (chains2 (-1) (Or.inr rfl)) ?_ ?_ ?_ ?_ V ?_ ?_ ?_ ?_
  · intro z h
    obtain ⟨p, hp, e1, e2⟩ := ofS1 0 z h
    by_cases hpv : p = v
    · rw [← e2, hpv]
    · linarith [apos p hp hpv]
  · intro z h
    obtain ⟨p, hp, e1, e2⟩ := ofS2 0 z h
    by_cases hpv : p = v
    · rw [← e2, hpv]
    · linarith [bpos p hp hpv]
  · intro x z h
    obtain ⟨p, hp, e1, e2⟩ := ofS1 x z h
    by_cases hpv : p = v
    · rw [← e1, hpv, hav]
    · rw [← e1]; exact (apos p hp hpv).le
  · intro x z h
    obtain ⟨p, hp, e1, e2⟩ := ofS2 x z h
    by_cases hpv : p = v
    · rw [← e1, hpv, hbv]
    · rw [← e1]; exact (bpos p hp hpv).le
  · intro x z h
    obtain ⟨p, hp, e1, e2⟩ := ofS1 x z h
    rw [← e1, ← e2, ← pt1 p hp]; exact h1V hp
  · intro x z h
    obtain ⟨p, hp, e1, e2⟩ := ofS2 x z h
    rw [← e1, ← e2, ← pt2 p hp]; exact h2V hp
  · intro y hy'
    refine ⟨a y, b y, y 2, hy y hy', ?_⟩
    by_cases h1 : y ∈ Q1
    · exact Or.inl ⟨hb1 y h1, Finset.mem_image_of_mem _ h1⟩
    by_cases h2 : y ∈ Q2
    · exact Or.inr (Or.inl ⟨ha2 y h2, Finset.mem_image_of_mem (fun p => (b p, p 2)) h2⟩)
    refine Or.inr (Or.inr ⟨ha2' y hy' h2, hb1' y hy' h1, ?_⟩)
    intro m ca cz n cb dz C1 C2
    have hA := C1.far_pos
    have hB := C2.far_pos
    have hxa0 := apos xa hxa hxav
    have hxb0 := bpos xb hxb hxbv
    have le1 : a xa ≤ ca m := by
      by_cases e : a xa = ca m ∧ xa 2 = cz m
      · exact e.1.le
      · exact (C1.far _ _ (Finset.mem_image_of_mem _ hxa) e).le
    have le2 : b xb ≤ cb n := by
      by_cases e : b xb = cb n ∧ xb 2 = dz n
      · exact e.1.le
      · exact (C2.far _ _ (Finset.mem_image_of_mem (fun p => (b p, p 2)) hxb) e).le
    have k := hin' y hy' h1 h2
    have ha := ha2' y hy' h2
    have hb := hb1' y hy' h1
    have t1 : a y / ca m ≤ a y / a xa := div_le_div_of_nonneg_left ha.le hxa0 le1
    have t2 : b y / cb n ≤ b y / b xb := div_le_div_of_nonneg_left hb.le hxb0 le2
    have : a y / ca m + b y / cb n < 1 := by linarith
    rw [div_add_div _ _ hA.ne' hB.ne', div_lt_one (mul_pos hA hB)] at this
    linarith
  · intro m ca cz n cb dz C1 C2 h
    obtain ⟨p, hp, e1, e2⟩ := ofS1 _ _ (C1.mem m le_rfl)
    obtain ⟨q, hq, f1, f2⟩ := ofS2 _ _ (C2.mem n le_rfl)
    have hpq : p ≠ q := by
      intro e; subst e
      have := only p hp hq; subst this
      linarith [C1.far_pos]
    refine hfarZ p hp q hq hpq (fun p' hp' => ?_) (fun q' hq' => ?_) (by rw [e2, f2, h])
    · rw [e1]
      by_cases e : a p' = ca m ∧ p' 2 = cz m
      · exact e.1.le
      · exact (C1.far _ _ (Finset.mem_image_of_mem _ hp') e).le
    · rw [f1]
      by_cases e : b q' = cb n ∧ q' 2 = dz n
      · exact e.1.le
      · exact (C2.far _ _ (Finset.mem_image_of_mem (fun p => (b p, p 2)) hq') e).le

set_option maxHeartbeats 4000000 in
/-- **Lemma T over a vertex, the planes vertical.**  `Q1`, `Q2` are facets
(functionals `f1`, `f2`) meeting in `v`, both planes containing the vertical line
through `v`. -/
theorem isRupert_facets_vertex_vertical (V Q1 Q2 : Finset ℝ³) (v : ℝ³)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v}) (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ)
    (z1 : ∀ p ∈ Q1, f1 p = 0) (n1 : ∀ p ∈ V, p ∉ Q1 → f1 p < 0)
    (z2 : ∀ p ∈ Q2, f2 p = 0) (n2 : ∀ p ∈ V, p ∉ Q2 → f2 p < 0)
    (e1 : f1 (v + ez) = 0) (e2 : f2 (v + ez) = 0)
    (hne1 : ∃ p ∈ Q1, p ≠ v) (hne2 : ∃ p ∈ Q2, p ≠ v)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hpar : ∀ p ∈ V, ∀ q ∈ V, p ≠ q → p 0 ≠ q 0 ∨ p 1 ≠ q 1)
    (hfarZ : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
      p 2 ≠ q 2)
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ≠ v ∧ xb ≠ v ∧
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1) : IsRupert V := by
  classical
  have hv1 : v ∈ Q1 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).1
  have hv2 : v ∈ Q2 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).2
  have only : ∀ p ∈ Q1, p ∈ Q2 → p = v := by
    intro p h1 h2
    have : p ∈ Q1 ∩ Q2 := Finset.mem_inter.mpr ⟨h1, h2⟩
    rwa [hint, Finset.mem_singleton] at this
  obtain ⟨p1, hp1, hp1v⟩ := hne1
  obtain ⟨p2, hp2, hp2v⟩ := hne2
  have m21 : f2 p1 < 0 := n2 p1 (h1V hp1) (fun h => hp1v (only p1 hp1 h))
  have m12 : f1 p2 < 0 := n1 p2 (h2V hp2) (fun h => hp2v (only p2 h hp2))
  obtain ⟨K1, α1, β1, γ1, h1⟩ := affine_xyz f1
  obtain ⟨K2, α2, β2, γ2, h2⟩ := affine_xyz f2
  have v1 := z1 v hv1; have v2 := z2 v hv2
  have hγ1 : γ1 = 0 := by
    rw [h1] at e1 v1; simp [ez] at e1; linarith
  have hγ2 : γ2 = 0 := by
    rw [h2] at e2 v2; simp [ez] at e2; linarith
  have g1 : ∀ p, f1 p = α1 * (p 0 - v 0) + β1 * (p 1 - v 1) := by
    intro p; have := v1; rw [h1, hγ1] at this ⊢; linarith
  have g2 : ∀ p, f2 p = α2 * (p 0 - v 0) + β2 * (p 1 - v 1) := by
    intro p; have := v2; rw [h2, hγ2] at this ⊢; linarith
  -- the frame
  set O : ℝ² := !₂[v 0, v 1] with hO
  set r1 : ℝ² := !₂[p1 0 - v 0, p1 1 - v 1] with hr1
  set r2 : ℝ² := !₂[p2 0 - v 0, p2 1 - v 1] with hr2
  have q11 : α1 * (p1 0 - v 0) + β1 * (p1 1 - v 1) = 0 := by rw [← g1]; exact z1 p1 hp1
  have q22 : α2 * (p2 0 - v 0) + β2 * (p2 1 - v 1) = 0 := by rw [← g2]; exact z2 p2 hp2
  have hρ : cross2 r1 r2 ≠ 0 := by
    intro hρ0
    simp only [hr1, hr2, cross2] at hρ0
    simp at hρ0
    have k0 : f1 p2 * (p1 0 - v 0) = 0 := by
      rw [g1]; linear_combination (p2 0 - v 0) * q11 + β1 * hρ0
    have k1 : f1 p2 * (p1 1 - v 1) = 0 := by
      rw [g1]; linear_combination (p2 1 - v 1) * q11 - α1 * hρ0
    have r10 := (mul_eq_zero.mp k0).resolve_left m12.ne
    have r11 := (mul_eq_zero.mp k1).resolve_left m12.ne
    have := g2 p1; rw [r10, r11] at this; linarith
  set ρ := cross2 r1 r2 with hρdef
  set a : ℝ³ → ℝ := fun p => cross2 !₂[p 0 - v 0, p 1 - v 1] r2 / ρ with ha
  set b : ℝ³ → ℝ := fun p => cross2 r1 !₂[p 0 - v 0, p 1 - v 1] / ρ with hb
  have hxy : ∀ p : ℝ³, p 0 - v 0 = a p * r1 0 + b p * r2 0 ∧ p 1 - v 1 = a p * r1 1 + b p * r2 1 := by
    intro p
    obtain ⟨c0, c1⟩ := cramer2 !₂[p 0 - v 0, p 1 - v 1] r1 r2 hρ
    simp at c0 c1; exact ⟨c0, c1⟩
  have hy : ∀ p : ℝ³, p = oblPt O r1 r2 (a p) (b p) (p 2) := by
    intro p; obtain ⟨c0, c1⟩ := hxy p
    ext j; fin_cases j
    · simp only [oblPt, hO]; simp; linarith
    · simp only [oblPt, hO]; simp; linarith
    · simp [oblPt]
  have r10 : r1 0 = p1 0 - v 0 := by simp [hr1]
  have r11 : r1 1 = p1 1 - v 1 := by simp [hr1]
  have r20 : r2 0 = p2 0 - v 0 := by simp [hr2]
  have r21 : r2 1 = p2 1 - v 1 := by simp [hr2]
  have G1 : ∀ p, f1 p = b p * f1 p2 := by
    intro p; rw [g1 p, g1 p2, (hxy p).1, (hxy p).2, r10, r11, r20, r21]
    linear_combination a p * q11
  have G2 : ∀ p, f2 p = a p * f2 p1 := by
    intro p; rw [g2 p, g2 p1, (hxy p).1, (hxy p).2, r10, r11, r20, r21]
    linear_combination b p * q22
  have hb1 : ∀ p ∈ Q1, b p = 0 := fun p hp => by
    have := G1 p; rw [z1 p hp] at this
    exact (mul_eq_zero.mp this.symm).resolve_right m12.ne
  have ha2 : ∀ p ∈ Q2, a p = 0 := fun p hp => by
    have := G2 p; rw [z2 p hp] at this
    exact (mul_eq_zero.mp this.symm).resolve_right m21.ne
  have hb1' : ∀ p ∈ V, p ∉ Q1 → 0 < b p := fun p hp hq => by
    have := n1 p hp hq; rw [G1] at this; nlinarith
  have ha2' : ∀ p ∈ V, p ∉ Q2 → 0 < a p := fun p hp hq => by
    have := n2 p hp hq; rw [G2] at this; nlinarith
  have hinj : Set.InjOn (fun p => (a p, b p)) (V : Set ℝ³) := by
    intro p hp q hq e
    simp only [Prod.mk.injEq] at e
    by_contra hpq
    obtain ⟨c0, c1⟩ := hxy p; obtain ⟨d0, d1⟩ := hxy q
    rw [e.1, e.2] at c0 c1
    rcases hpar p hp q hq hpq with h | h <;> apply h <;> linarith
  have hfar' : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, a p' ≤ a p) → (∀ q' ∈ Q2, b q' ≤ b q) →
      p 2 ≠ q 2 := fun p hp q hq hpq h1 h2 =>
    hfarZ p hp q hq hpq (fun p' hp' => by
        rw [G2 p, G2 p']; exact mul_le_mul_of_nonpos_right (h1 p' hp') m21.le)
      (fun q' hq' => by rw [G1 q, G1 q']; exact mul_le_mul_of_nonpos_right (h2 q' hq') m12.le)
  have hin' : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ≠ v ∧ xb ≠ v ∧
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → a y / a xa + b y / b xb < 1 := by
    obtain ⟨xa, hxa, xb, hxb, hxav, hxbv, h⟩ := hin
    refine ⟨xa, hxa, xb, hxb, hxav, hxbv, fun y hy hy1 hy2 => ?_⟩
    have k := h y hy hy1 hy2
    rw [G1 y, G1 xb, G2 y, G2 xa, mul_div_mul_right _ _ m21.ne, mul_div_mul_right _ _ m12.ne] at k
    exact k
  rcases lt_or_gt_of_ne hρ with hneg | hpos
  · -- negative orientation: exchange the two faces
    have hpos' : 0 < cross2 r2 r1 := by
      have : cross2 r2 r1 = -cross2 r1 r2 := by unfold cross2; ring
      rw [this]; linarith
    have swap : ∀ p q z, oblPt O r2 r1 q p z = oblPt O r1 r2 p q z := by
      intro p q z; ext j; fin_cases j <;> simp [oblPt] <;> ring
    refine isRupert_vertex_coords O r2 r1 hpos' V Q2 Q1 v b a (fun p _ => by rw [swap]; exact hy p)
      h2V h1V (by rw [Finset.inter_comm]; exact hint) ha2 ha2' hb1 hb1' ⟨p2, hp2, hp2v⟩
      ⟨p1, hp1, hp1v⟩ hcol ?_
      (fun p hp q hq hpq h1 h2 => (hfar' q hq p hp (Ne.symm hpq) h2 h1).symm) ?_
    · intro p hp q hq e
      simp only [Prod.mk.injEq] at e
      exact hinj hp hq (by simp only [Prod.mk.injEq]; exact ⟨e.2, e.1⟩)
    · obtain ⟨xa, hxa, xb, hxb, hxav, hxbv, h⟩ := hin'
      exact ⟨xb, hxb, xa, hxa, hxbv, hxav, fun y hy hy2 hy1 => by
        rw [add_comm]; exact h y hy hy1 hy2⟩
  · exact isRupert_vertex_coords O r1 r2 hpos V Q1 Q2 v a b (fun p _ => hy p) h1V h2V hint
      hb1 hb1' ha2 ha2' ⟨p1, hp1, hp1v⟩ ⟨p2, hp2, hp2v⟩ hcol hinj hfar' hin'

set_option maxHeartbeats 4000000 in
/-- **Lemma T over a vertex** for two facets `Q1`, `Q2` (functionals `f1`,
`f2`) meeting in `v`, viewed along the line `v + ℝ e` of their planes: no three
points collinear, no segment parallel to `e`, distinct depths along `e` at the
far ends (the point of `Q1` where `f2` is least, that of `Q2` where `f1` is least),
and every point off both facets inside the shadow triangle of `v` and some
`xa ∈ Q1`, `xb ∈ Q2`. -/
theorem isRupert_facets_vertex (V Q1 Q2 : Finset ℝ³) (v : ℝ³)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v}) (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ)
    (z1 : ∀ p ∈ Q1, f1 p = 0) (n1 : ∀ p ∈ V, p ∉ Q1 → f1 p < 0)
    (z2 : ∀ p ∈ Q2, f2 p = 0) (n2 : ∀ p ∈ V, p ∉ Q2 → f2 p < 0)
    (e : ℝ³) (he : e ≠ 0) (e1 : f1 (v + e) = 0) (e2 : f2 (v + e) = 0)
    (hne1 : ∃ p ∈ Q1, p ≠ v) (hne2 : ∃ p ∈ Q2, p ≠ v)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hpar : ∀ p ∈ V, ∀ q ∈ V, p ≠ q → ∀ c : ℝ, q - p ≠ c • e)
    (hfarZ : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
      ⟪p, e⟫ ≠ ⟪q, e⟫)
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ≠ v ∧ xb ≠ v ∧
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1) : IsRupert V := by
  classical
  obtain ⟨R, hR, r, hr, hRe⟩ := exists_rotation_to_ez_pos e he
  apply isRupert_of_isRupert_image_rotation R hR
  set g := R.toEuclideanLin with hg
  set I := so3Isometry hR with hI
  have hgI : ∀ p, g p = I p := fun p => rfl
  have hginj : Function.Injective g := I.injective
  have hgz : ∀ p, g p 2 = ⟪p, e⟫ / r := fun p => by
    have := inner_toEuclideanLin_SO3 hR p e
    rw [hRe, real_inner_smul_right, inner_ez] at this
    field_simp; linarith
  have hIe : I.symm ez = r⁻¹ • e := by
    apply I.injective
    rw [LinearIsometryEquiv.apply_symm_apply, map_smul, ← hgI, hRe, smul_smul,
      inv_mul_cancel₀ hr.ne', one_smul]
  -- functionals transported by the inverse rotation
  set F1 := f1.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap with hF1
  set F2 := f2.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap with hF2
  have tF1 : ∀ p, F1 (g p) = f1 p := fun p => by simp [hF1, hgI]
  have tF2 : ∀ p, F2 (g p) = f2 p := fun p => by simp [hF2, hgI]
  have tz : ∀ f : ℝ³ →ᵃ[ℝ] ℝ, f v = 0 → f (v + e) = 0 →
      (f.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap) (g v + ez) = 0 := by
    intro f h0 h1
    have : (f.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap) (g v + ez) = f (v + r⁻¹ • e) := by
      simp [hgI, map_add, hIe]
    rw [this]; exact affine_zero_line f h0 h1 _
  have hv1 : v ∈ Q1 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).1
  have hv2 : v ∈ Q2 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).2
  have memg : ∀ (S : Finset ℝ³) p, g p ∈ S.image g ↔ p ∈ S := fun S p =>
    ⟨fun h => by obtain ⟨q, hq, e⟩ := Finset.mem_image.mp h; rwa [← hginj e], Finset.mem_image_of_mem g⟩
  have allg : ∀ (S : Finset ℝ³) (P : ℝ³ → Prop), (∀ p ∈ S, P (g p)) → ∀ q ∈ S.image g, P q := by
    intro S P h q hq; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq; exact h p hp
  refine isRupert_facets_vertex_vertical (V.image g) (Q1.image g) (Q2.image g) (g v)
    (Finset.image_subset_image h1V) (Finset.image_subset_image h2V)
    (by rw [← Finset.image_inter _ _ hginj, hint, Finset.image_singleton]) F1 F2
    (allg Q1 _ (fun p hp => by rw [tF1]; exact z1 p hp))
    (allg V _ (fun p hp hq => by rw [tF1]; exact n1 p hp (fun h => hq ((memg Q1 p).mpr h))))
    (allg Q2 _ (fun p hp => by rw [tF2]; exact z2 p hp))
    (allg V _ (fun p hp hq => by rw [tF2]; exact n2 p hp (fun h => hq ((memg Q2 p).mpr h))))
    (tz f1 (z1 v hv1) e1) (tz f2 (z2 v hv2) e2) ?_ ?_ ?_ ?_ ?_ ?_
  · obtain ⟨p, hp, hpv⟩ := hne1
    exact ⟨g p, Finset.mem_image_of_mem g hp, fun h => hpv (hginj h)⟩
  · obtain ⟨p, hp, hpv⟩ := hne2
    exact ⟨g p, Finset.mem_image_of_mem g hp, fun h => hpv (hginj h)⟩
  · refine allg V _ (fun p hp => allg V _ (fun q hq => allg V _ (fun w hw => ?_)))
    intro hpq hpw hqw c h
    apply hcol p hp q hq w hw (fun e => hpq (by rw [e])) (fun e => hpw (by rw [e]))
      (fun e => hqw (by rw [e])) c
    apply hginj
    simp only [map_sub, map_smul] at h ⊢; exact h
  · refine allg V _ (fun p hp => allg V _ (fun q hq => ?_))
    intro hpq
    by_contra h; push Not at h
    obtain ⟨h0, h1⟩ := h
    apply hpar p hp q hq (fun e => hpq (by rw [e])) ((g (q - p)) 2 / r)
    apply hginj
    rw [map_smul, hRe]
    ext k; fin_cases k
    · simp [ez, map_sub]; linarith
    · simp [ez, map_sub]; linarith
    · simp [ez]; field_simp
  · refine allg Q1 _ (fun p hp => allg Q2 _ (fun q hq => ?_))
    intro hpq h1 h2 h
    simp only [hgz] at h
    refine hfarZ p hp q hq (fun e => hpq (by rw [e])) (fun p' hp' => ?_) (fun q' hq' => ?_)
      (by simpa [hr.ne'] using h)
    · have := h1 (g p') (Finset.mem_image_of_mem g hp'); rwa [tF2, tF2] at this
    · have := h2 (g q') (Finset.mem_image_of_mem g hq'); rwa [tF1, tF1] at this
  · obtain ⟨xa, hxa, xb, hxb, hxav, hxbv, h⟩ := hin
    refine ⟨g xa, Finset.mem_image_of_mem g hxa, g xb, Finset.mem_image_of_mem g hxb,
      fun e => hxav (hginj e), fun e => hxbv (hginj e), allg V _ (fun y hy hy1 hy2 => ?_)⟩
    rw [tF1, tF1, tF2, tF2]
    exact h y hy (fun h => hy1 ((memg Q1 y).mpr h)) (fun h => hy2 ((memg Q2 y).mpr h))

/-- General position for Lemma T at the line of the planes of two facets `Q1`,
`Q2` (through `v`): no segment between points of `V` is parallel to the line,
and the far ends of the two faces in the shadow (the point of `Q1` where `f2`
is least, the point of `Q2` where `f1` is least) have distinct depths along it.
Weaker than `TriGen` (`TriGen.far`). -/
def TriGenFar (V Q1 Q2 : Finset ℝ³) (v : ℝ³) : Prop :=
  ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ, (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
    (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
    ∀ e : ℝ³, e ≠ 0 → f1 (v + e) = 0 → f2 (v + e) = 0 →
      (∀ p ∈ V, ∀ q ∈ V, p ≠ q → ∀ c : ℝ, q - p ≠ c • e) ∧
      ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
        ⟪p, e⟫ ≠ ⟪q, e⟫

theorem TriGen.far {V Q1 Q2 : Finset ℝ³} {v : ℝ³} (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V)
    (h : TriGen V Q1 Q2 v) : TriGenFar V Q1 Q2 v := by
  intro f1 f2 z1 n1 z2 n2 e he e1 e2
  obtain ⟨hpar, hZ⟩ := h f1 f2 z1 n1 z2 n2 e he e1 e2
  exact ⟨hpar, fun p hp q hq hpq _ _ hd => hpq (hZ (h1V hp) (h2V hq) hd)⟩

set_option maxHeartbeats 4000000 in
/-- **Lemma T over a vertex, facet form** (`FEWER-FACES-PROOFS.md` §7): two
facets `Q1`, `Q2` of `V` in general position meeting in the single vertex `v`,
with `TriGenFar` at the line of their planes, and every point off both facets
inside the shadow triangle of `v`, `xa ∈ Q1`, `xb ∈ Q2` (stated with any facet
functionals `f1`, `f2`): Rupert. -/
theorem isRupert_of_facets_vertex (V : Finset ℝ³) (hgen : GenPos V)
    (Q1 Q2 : Finset ℝ³) (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (h1f : IsFacet V Q1) (h2f : IsFacet V Q2)
    (v : ℝ³) (hint : Q1 ∩ Q2 = {v}) (hne1 : ∃ p ∈ Q1, p ≠ v) (hne2 : ∃ p ∈ Q2, p ≠ v)
    (hT : TriGenFar V Q1 Q2 v)
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ≠ v ∧ xb ≠ v ∧ ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ,
      (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
      (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1) : IsRupert V := by
  classical
  have hv1 : v ∈ Q1 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).1
  have hv2 : v ∈ Q2 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).2
  have only : ∀ p ∈ Q1, p ∈ Q2 → p = v := by
    intro p h1 h2
    have : p ∈ Q1 ∩ Q2 := Finset.mem_inter.mpr ⟨h1, h2⟩
    rwa [hint, Finset.mem_singleton] at this
  obtain ⟨p1, hp1, hp1v⟩ := hne1
  obtain ⟨p2, hp2, hp2v⟩ := hne2
  obtain ⟨f1, z1, n1⟩ := h1f
  obtain ⟨f2, z2, n2⟩ := h2f
  obtain ⟨K1, α1, β1, γ1, hf1⟩ := affine_xyz f1
  obtain ⟨K2, α2, β2, γ2, hf2⟩ := affine_xyz f2
  set e : ℝ³ := !₂[β1 * γ2 - γ1 * β2, γ1 * α2 - α1 * γ2, α1 * β2 - β1 * α2] with he
  have dif : ∀ (f : ℝ³ →ᵃ[ℝ] ℝ) (K α β γ : ℝ), (∀ p, f p = K + α * p 0 + β * p 1 + γ * p 2) →
      ∀ p q, f q - f p = α * (q 0 - p 0) + β * (q 1 - p 1) + γ * (q 2 - p 2) := by
    intro f K α β γ h p q; rw [h, h]; ring
  have e1 : f1 (v + e) = 0 := by
    have := dif f1 K1 α1 β1 γ1 hf1 v (v + e)
    rw [z1 v hv1] at this; rw [sub_zero] at this; rw [this]; simp [he]; ring
  have e2 : f2 (v + e) = 0 := by
    have := dif f2 K2 α2 β2 γ2 hf2 v (v + e)
    rw [z2 v hv2] at this; rw [sub_zero] at this; rw [this]; simp [he]; ring
  have hn1 : f1 p2 < 0 := n1 p2 (h2V hp2) (fun h => hp2v (only p2 h hp2))
  have hn2 : f2 p1 < 0 := n2 p1 (h1V hp1) (fun h => hp1v (only p1 hp1 h))
  have hne : e ≠ 0 := by
    intro h0
    have c0 := congrArg (fun p : ℝ³ => p 0) h0
    have c1 := congrArg (fun p : ℝ³ => p 1) h0
    have c2 := congrArg (fun p : ℝ³ => p 2) h0
    simp [he] at c0 c1 c2
    have d14 := dif f1 K1 α1 β1 γ1 hf1 v p2
    have d21 := dif f2 K2 α2 β2 γ2 hf2 v p1
    have d11 := dif f1 K1 α1 β1 γ1 hf1 v p1
    rw [z1 v hv1, sub_zero] at d14
    rw [z1 v hv1, z1 p1 hp1, sub_zero] at d11
    rw [z2 v hv2, sub_zero] at d21
    have key : (f1 p2) * (f2 p1) = 0 := by
      rw [d14, d21]
      have := d11
      linear_combination (α2 * (p2 0 - v 0) + β2 * (p2 1 - v 1) + γ2 * (p2 2 - v 2)) * this.symm +
        ((p1 1 - v 1) * (p2 0 - v 0) - (p1 0 - v 0) * (p2 1 - v 1)) * c2 +
        ((p1 2 - v 2) * (p2 1 - v 1) - (p1 1 - v 1) * (p2 2 - v 2)) * c0 +
        ((p1 0 - v 0) * (p2 2 - v 2) - (p1 2 - v 2) * (p2 0 - v 0)) * c1
    nlinarith
  obtain ⟨hpar, hfarZ⟩ := hT f1 f2 z1 n1 z2 n2 e hne e1 e2
  obtain ⟨xa, hxa, xb, hxb, hxav, hxbv, hin'⟩ := hin
  refine isRupert_facets_vertex V Q1 Q2 v h1V h2V hint f1 f2 z1 n1 z2 n2 e hne e1 e2
    ⟨p1, hp1, hp1v⟩ ⟨p2, hp2, hp2v⟩ ?_ hpar hfarZ
    ⟨xa, hxa, xb, hxb, hxav, hxbv, hin' f1 f2 z1 n1 z2 n2⟩
  intro p hp q hq r hr hpq hpr hqr c
  exact (hgen p hp r hr p hp q hq hpr hpq (by
    intro h
    have : r ∈ ({p, q} : Finset ℝ³) := h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h' | h'
    · exact hpr h'.symm
    · exact hqr h'.symm)).1 c

end Minimality

end
