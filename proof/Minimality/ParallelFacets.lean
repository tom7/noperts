module

public import Minimality.ParallelFar
public import Minimality.TriFacetsEdge

@[expose] public section

/-!
# The facet bridge for Lemma T with segments parallel to the view line

Step (ii) of removing the parallel-segment condition (FEWER-FACES.md §11):
the coordinates layer of `TriFacets.lean` with the chains of
`exists_chainOKc` and the frame `isRupert_vertex_frame_par`.
-/

namespace Minimality

open Finset
open scoped RealInnerProductSpace

set_option maxHeartbeats 4000000 in
/-- **Lemma T over a vertex in coordinates, segments parallel to the view
line allowed.** As `isRupert_vertex_coords` without the injectivity of
`(a, b)` (two vertices may lie on one line parallel to the view, anywhere on
a face), provided one of the two faces has a single vertex of largest `a`
(resp. `b`) (else Corollary T1's rectangle exception). -/
theorem isRupert_vertex_coords_par (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (V Q1 Q2 : Finset ℝ³)
    (v : ℝ³) (a b : ℝ³ → ℝ) (hy : ∀ p ∈ V, p = oblPt O r1 r2 (a p) (b p) (p 2))
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v})
    (hb1 : ∀ p ∈ Q1, b p = 0) (hb1' : ∀ p ∈ V, p ∉ Q1 → 0 < b p)
    (ha2 : ∀ p ∈ Q2, a p = 0) (ha2' : ∀ p ∈ V, p ∉ Q2 → 0 < a p)
    (hne1 : ∃ p ∈ Q1, p ≠ v) (hne2 : ∃ p ∈ Q2, p ≠ v)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hfarZ : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, a p' ≤ a p) → (∀ q' ∈ Q2, b q' ≤ b q) →
      p 2 ≠ q 2)
    (hone : (∀ p ∈ Q1, ∀ p' ∈ Q1, (∀ p'' ∈ Q1, a p'' ≤ a p) → a p' = a p → p' = p) ∨
      (∀ q ∈ Q2, ∀ q' ∈ Q2, (∀ q'' ∈ Q2, b q'' ≤ b q) → b q' = b q → q' = q))
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
  have chains1 : ∀ s : ℝ, (s = 1 ∨ s = -1) → ∃ m ca cz, ChainOKc (fun x z => (x, z) ∈ S1) (v 2) s m ca cz := by
    intro s hs
    apply exists_chainOKc S1 (v 2) (by rw [hS1, Finset.mem_image]; exact ⟨v, hv1, by rw [hav]⟩)
    · intro q hq hne
      obtain ⟨p, hp, e1, e2⟩ := ofS1 q.1 q.2 hq
      rw [← e1]; refine apos p hp (fun h => hne ?_)
      exact Prod.ext (by show q.1 = 0; rw [← e1, h, hav]) (by show q.2 = v 2; rw [← e2, h])
    · obtain ⟨p, hp, hpv⟩ := hne1
      refine ⟨(a p, p 2), Finset.mem_image_of_mem _ hp, fun h => ?_⟩
      have := congrArg Prod.fst h; simp only at this; linarith [apos p hp hpv]
    · intro q hq q' hq' q'' hq'' n1 n2 n3
      obtain ⟨p, hp, e1, e2⟩ := ofS1 q.1 q.2 hq
      obtain ⟨p', hp', e1', e2'⟩ := ofS1 q'.1 q'.2 hq'
      obtain ⟨p'', hp'', e1'', e2''⟩ := ofS1 q''.1 q''.2 hq''
      have d : ∀ {r r' : ℝ × ℝ} {u u' : ℝ³}, r ≠ r' → a u = r.1 → u 2 = r.2 → a u' = r'.1 →
          u' 2 = r'.2 → u ≠ u' := by
        intro r r' u u' h h1 h2 h1' h2' hu; apply h
        exact Prod.ext (by rw [← h1, ← h1', hu]) (by rw [← h2, ← h2', hu])
      have hne : (a p, p 2) ≠ (a p', p' 2) := by rw [e1, e2, e1', e2']; exact n1
      have := orient_ne_of_frame1' (O := O) (r1 := r1) (r2 := r2) (zi := p 2) (zj := p' 2) (zk := p'' 2)
        (ak := a p'') hne (by
          intro c; rw [← pt1 p hp, ← pt1 p' hp', ← pt1 p'' hp'']
          exact hcol p (h1V hp) p' (h1V hp') p'' (h1V hp'') (d n1 e1 e2 e1' e2')
            (d n2 e1 e2 e1'' e2'') (d n3 e1' e2' e1'' e2'') c)
      unfold orient2 at this; rwa [e1, e2, e1', e2', e1'', e2''] at this
    · exact hs
  have chains2 : ∀ s : ℝ, (s = 1 ∨ s = -1) → ∃ m ca cz, ChainOKc (fun x z => (x, z) ∈ S2) (v 2) s m ca cz := by
    intro s hs
    apply exists_chainOKc S2 (v 2) (by rw [hS2, Finset.mem_image]; exact ⟨v, hv2, by rw [hbv]⟩)
    · intro q hq hne
      obtain ⟨p, hp, e1, e2⟩ := ofS2 q.1 q.2 hq
      rw [← e1]; refine bpos p hp (fun h => hne ?_)
      exact Prod.ext (by show q.1 = 0; rw [← e1, h, hbv]) (by show q.2 = v 2; rw [← e2, h])
    · obtain ⟨p, hp, hpv⟩ := hne2
      refine ⟨(b p, p 2), Finset.mem_image_of_mem _ hp, fun h => ?_⟩
      have := congrArg Prod.fst h; simp only at this; linarith [bpos p hp hpv]
    · intro q hq q' hq' q'' hq'' n1 n2 n3
      obtain ⟨p, hp, e1, e2⟩ := ofS2 q.1 q.2 hq
      obtain ⟨p', hp', e1', e2'⟩ := ofS2 q'.1 q'.2 hq'
      obtain ⟨p'', hp'', e1'', e2''⟩ := ofS2 q''.1 q''.2 hq''
      have d : ∀ {r r' : ℝ × ℝ} {u u' : ℝ³}, r ≠ r' → b u = r.1 → u 2 = r.2 → b u' = r'.1 →
          u' 2 = r'.2 → u ≠ u' := by
        intro r r' u u' h h1 h2 h1' h2' hu; apply h
        exact Prod.ext (by rw [← h1, ← h1', hu]) (by rw [← h2, ← h2', hu])
      have hne : (b p, p 2) ≠ (b p', p' 2) := by rw [e1, e2, e1', e2']; exact n1
      have := orient_ne_of_frame2' (O := O) (r1 := r1) (r2 := r2) (zi := p 2) (zj := p' 2) (zk := p'' 2)
        (bk := b p'') hne (by
          intro c; rw [← pt2 p hp, ← pt2 p' hp', ← pt2 p'' hp'']
          exact hcol p (h2V hp) p' (h2V hp') p'' (h2V hp'') (d n1 e1 e2 e1' e2')
            (d n2 e1 e2 e1'' e2'') (d n3 e1' e2' e1'' e2'') c)
      unfold orient2 at this; rwa [e1, e2, e1', e2', e1'', e2''] at this
    · exact hs
  -- the far points of the chains
  have far1 : ∀ {s : ℝ} {m : ℕ} {ca cz : ℕ → ℝ}, ChainOKc (fun x z => (x, z) ∈ S1) (v 2) s m ca cz →
      ∃ p ∈ Q1, a p = ca m ∧ p 2 = cz m ∧ ∀ p'' ∈ Q1, a p'' ≤ a p := by
    intro s m ca cz C
    obtain ⟨p, hp, e1, e2⟩ := ofS1 _ _ (C.mem m le_rfl)
    refine ⟨p, hp, e1, e2, fun p'' hp'' => ?_⟩
    rw [e1]
    by_cases e : a p'' = ca m ∧ p'' 2 = cz m
    · exact e.1.le
    rcases C.far _ _ (Finset.mem_image_of_mem _ hp'') e with h | ⟨h, -⟩
    · exact h.le
    · exact h.le
  have far2 : ∀ {s : ℝ} {n : ℕ} {cb dz : ℕ → ℝ}, ChainOKc (fun x z => (x, z) ∈ S2) (v 2) s n cb dz →
      ∃ q ∈ Q2, b q = cb n ∧ q 2 = dz n ∧ ∀ q'' ∈ Q2, b q'' ≤ b q := by
    intro s n cb dz C
    obtain ⟨q, hq, e1, e2⟩ := ofS2 _ _ (C.mem n le_rfl)
    refine ⟨q, hq, e1, e2, fun q'' hq'' => ?_⟩
    rw [e1]
    by_cases e : b q'' = cb n ∧ q'' 2 = dz n
    · exact e.1.le
    rcases C.far _ _ (Finset.mem_image_of_mem (fun p => (b p, p 2)) hq'') e with h | ⟨h, -⟩
    · exact h.le
    · exact h.le
  -- an upper chain ends above a lower one
  have topbot : ∀ {Q : ℝ → ℝ → Prop} {z0 z0' : ℝ} {m m' : ℕ} {ca cz ca' cz' : ℕ → ℝ},
      ChainOKc Q z0 1 m ca cz → ChainOKc Q z0' (-1) m' ca' cz' → cz' m' ≤ cz m := by
    intro Q z0 z0' m m' ca cz ca' cz' U L
    have ea := U.far_a_eq L
    by_cases e : ca' m' = ca m ∧ cz' m' = cz m
    · exact e.2.le
    rcases U.far _ _ (L.mem m' le_rfl) e with h | ⟨-, h⟩
    · exact absurd ea (by linarith)
    · linarith
  have pq : ∀ p ∈ Q1, ∀ q ∈ Q2, (∀ p'' ∈ Q1, a p'' ≤ a p) → p ≠ q := by
    intro p hp q hq hmax e; subst e
    have := only p hp hq; subst this
    obtain ⟨p', hp', hp'v⟩ := hne1
    have := hmax p' hp'; linarith [apos p' hp' hp'v]
  obtain ⟨xa, hxa, xb, hxb, hxav, hxbv, hin'⟩ := hin
  refine isRupert_vertex_frame_par O r1 r2 hρ (fun x z => (x, z) ∈ S1) (fun x z => (x, z) ∈ S2)
    (z0 := v 2) (chains1 1 (Or.inl rfl)) (chains1 (-1) (Or.inr rfl)) (chains2 1 (Or.inl rfl))
    (chains2 (-1) (Or.inr rfl)) ?_ ?_ ?_ ?_ ?_ ?_ V ?_ ?_ ?_
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
  · -- one face has a single far vertex
    rcases hone with h1 | h2
    · left; intro m ca cz C z hz
      obtain ⟨p, hp, e1, e2, hmax⟩ := far1 C
      obtain ⟨p', hp', e1', e2'⟩ := ofS1 _ _ hz
      have := h1 p hp p' hp' hmax (by rw [e1, e1'])
      rw [← e2', this, e2]
    · right; intro n cb dz C z hz
      obtain ⟨q, hq, e1, e2, hmax⟩ := far2 C
      obtain ⟨q', hq', e1', e2'⟩ := ofS2 _ _ hz
      have := h2 q hq q' hq' hmax (by rw [e1, e1'])
      rw [← e2', this, e2]
  · -- the tilt side: far tops against far bottoms
    intro m ca cz m' ca' cz' n cb dz n' cb' dz' U1 L1 U2 L2
    obtain ⟨pU, hpU, aU, zU, mU⟩ := far1 U1
    obtain ⟨pL, hpL, aL, zL, mL⟩ := far1 L1
    obtain ⟨qU, hqU, bU, wU, nU⟩ := far2 U2
    obtain ⟨qL, hqL, bL, wL, nL⟩ := far2 L2
    have tb1 := topbot U1 L1
    have tb2 := topbot U2 L2
    rcases hone with h1 | h2
    · have e : pL = pU := h1 pU hpU pL hpL mU (by rw [aU, aL]; exact (U1.far_a_eq L1).symm)
      have hz : cz' m' = cz m := by rw [← zL, ← zU, e]
      have hne := hfarZ pU hpU qL hqL (pq pU hpU qL hqL mU) mU nL
      rw [zU, wL] at hne
      rcases lt_or_gt_of_ne hne with h | h
      · right; rw [hz]; linarith
      · left; exact h
    · have e : qL = qU := h2 qU hqU qL hqL nU (by rw [bU, bL]; exact (U2.far_a_eq L2).symm)
      have hw : dz' n' = dz n := by rw [← wL, ← wU, e]
      have hne := hfarZ pU hpU qL hqL (pq pU hpU qL hqL mU) mU nL
      rw [zU, wL] at hne
      rcases lt_or_gt_of_ne hne with h | h
      · right; rw [← hw]; linarith
      · left; exact h
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
    obtain ⟨p, hp, e1, -, hmax1⟩ := far1 C1
    obtain ⟨q, hq, f1, -, hmax2⟩ := far2 C2
    have le1 : a xa ≤ ca m := by rw [← e1]; exact hmax1 xa hxa
    have le2 : b xb ≤ cb n := by rw [← f1]; exact hmax2 xb hxb
    have k := hin' y hy' h1 h2
    have ha := ha2' y hy' h2
    have hb := hb1' y hy' h1
    have t1 : a y / ca m ≤ a y / a xa := div_le_div_of_nonneg_left ha.le hxa0 le1
    have t2 : b y / cb n ≤ b y / b xb := div_le_div_of_nonneg_left hb.le hxb0 le2
    have : a y / ca m + b y / cb n < 1 := by linarith
    rw [div_add_div _ _ hA.ne' hB.ne', div_lt_one (mul_pos hA hB)] at this
    linarith

set_option maxHeartbeats 4000000 in
/-- **Lemma T over a vertex, the planes vertical, segments parallel to the
view line allowed** (as `isRupert_facets_vertex_vertical` without `hpar`),
provided one facet has a single point where the other's functional is least
(Corollary T1's rectangle exception). -/
theorem isRupert_facets_vertex_vertical_par (V Q1 Q2 : Finset ℝ³) (v : ℝ³)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v}) (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ)
    (z1 : ∀ p ∈ Q1, f1 p = 0) (n1 : ∀ p ∈ V, p ∉ Q1 → f1 p < 0)
    (z2 : ∀ p ∈ Q2, f2 p = 0) (n2 : ∀ p ∈ V, p ∉ Q2 → f2 p < 0)
    (e1 : f1 (v + ez) = 0) (e2 : f2 (v + ez) = 0)
    (hne1 : ∃ p ∈ Q1, p ≠ v) (hne2 : ∃ p ∈ Q2, p ≠ v)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hfarZ : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
      p 2 ≠ q 2)
    (hone : (∀ p ∈ Q1, ∀ p' ∈ Q1, (∀ p'' ∈ Q1, f2 p ≤ f2 p'') → f2 p' = f2 p → p' = p) ∨
      (∀ q ∈ Q2, ∀ q' ∈ Q2, (∀ q'' ∈ Q2, f1 q ≤ f1 q'') → f1 q' = f1 q → q' = q))
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
  have hfar' : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, a p' ≤ a p) → (∀ q' ∈ Q2, b q' ≤ b q) →
      p 2 ≠ q 2 := fun p hp q hq hpq h1 h2 =>
    hfarZ p hp q hq hpq (fun p' hp' => by
        rw [G2 p, G2 p']; exact mul_le_mul_of_nonpos_right (h1 p' hp') m21.le)
      (fun q' hq' => by rw [G1 q, G1 q']; exact mul_le_mul_of_nonpos_right (h2 q' hq') m12.le)
  have hone' : (∀ p ∈ Q1, ∀ p' ∈ Q1, (∀ p'' ∈ Q1, a p'' ≤ a p) → a p' = a p → p' = p) ∨
      (∀ q ∈ Q2, ∀ q' ∈ Q2, (∀ q'' ∈ Q2, b q'' ≤ b q) → b q' = b q → q' = q) := by
    rcases hone with h | h
    · left; intro p hp p' hp' hmax e
      refine h p hp p' hp' (fun p'' hp'' => ?_) (by rw [G2 p', G2 p, e])
      rw [G2 p, G2 p'']; exact mul_le_mul_of_nonpos_right (hmax p'' hp'') m21.le
    · right; intro q hq q' hq' hmax e
      refine h q hq q' hq' (fun q'' hq'' => ?_) (by rw [G1 q', G1 q, e])
      rw [G1 q, G1 q'']; exact mul_le_mul_of_nonpos_right (hmax q'' hq'') m12.le
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
    refine isRupert_vertex_coords_par O r2 r1 hpos' V Q2 Q1 v b a (fun p _ => by rw [swap]; exact hy p)
      h2V h1V (by rw [Finset.inter_comm]; exact hint) ha2 ha2' hb1 hb1' ⟨p2, hp2, hp2v⟩
      ⟨p1, hp1, hp1v⟩ hcol
      (fun p hp q hq hpq h1 h2 => (hfar' q hq p hp (Ne.symm hpq) h2 h1).symm) hone'.symm ?_
    · obtain ⟨xa, hxa, xb, hxb, hxav, hxbv, h⟩ := hin'
      exact ⟨xb, hxb, xa, hxa, hxbv, hxav, fun y hy hy2 hy1 => by
        rw [add_comm]; exact h y hy hy1 hy2⟩
  · exact isRupert_vertex_coords_par O r1 r2 hpos V Q1 Q2 v a b (fun p _ => hy p) h1V h2V hint
      hb1 hb1' ha2 ha2' ⟨p1, hp1, hp1v⟩ ⟨p2, hp2, hp2v⟩ hcol hfar' hone' hin'

set_option maxHeartbeats 4000000 in
/-- **Lemma T over a vertex, any frame, segments parallel to the view line
allowed** (as `isRupert_facets_vertex` without `hpar`; one facet with a single
point where the other's functional is least). -/
theorem isRupert_facets_vertex_par (V Q1 Q2 : Finset ℝ³) (v : ℝ³)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v}) (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ)
    (z1 : ∀ p ∈ Q1, f1 p = 0) (n1 : ∀ p ∈ V, p ∉ Q1 → f1 p < 0)
    (z2 : ∀ p ∈ Q2, f2 p = 0) (n2 : ∀ p ∈ V, p ∉ Q2 → f2 p < 0)
    (e : ℝ³) (he : e ≠ 0) (e1 : f1 (v + e) = 0) (e2 : f2 (v + e) = 0)
    (hne1 : ∃ p ∈ Q1, p ≠ v) (hne2 : ∃ p ∈ Q2, p ≠ v)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hfarZ : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
      ⟪p, e⟫ ≠ ⟪q, e⟫)
    (hone : (∀ p ∈ Q1, ∀ p' ∈ Q1, (∀ p'' ∈ Q1, f2 p ≤ f2 p'') → f2 p' = f2 p → p' = p) ∨
      (∀ q ∈ Q2, ∀ q' ∈ Q2, (∀ q'' ∈ Q2, f1 q ≤ f1 q'') → f1 q' = f1 q → q' = q))
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
  refine isRupert_facets_vertex_vertical_par (V.image g) (Q1.image g) (Q2.image g) (g v)
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
  · refine allg Q1 _ (fun p hp => allg Q2 _ (fun q hq => ?_))
    intro hpq h1 h2 h
    simp only [hgz] at h
    refine hfarZ p hp q hq (fun e => hpq (by rw [e])) (fun p' hp' => ?_) (fun q' hq' => ?_)
      (by simpa [hr.ne'] using h)
    · have := h1 (g p') (Finset.mem_image_of_mem g hp'); rwa [tF2, tF2] at this
    · have := h2 (g q') (Finset.mem_image_of_mem g hq'); rwa [tF1, tF1] at this
  · rcases hone with h | h
    · left
      refine allg Q1 _ (fun p hp => allg Q1 _ (fun p' hp' => ?_))
      intro hmax e
      rw [h p hp p' hp' (fun p'' hp'' => by
        have := hmax (g p'') (Finset.mem_image_of_mem g hp''); rwa [tF2, tF2] at this)
        (by rwa [tF2, tF2] at e)]
    · right
      refine allg Q2 _ (fun q hq => allg Q2 _ (fun q' hq' => ?_))
      intro hmax e
      rw [h q hq q' hq' (fun q'' hq'' => by
        have := hmax (g q'') (Finset.mem_image_of_mem g hq''); rwa [tF1, tF1] at this)
        (by rwa [tF1, tF1] at e)]
  · obtain ⟨xa, hxa, xb, hxb, hxav, hxbv, h⟩ := hin
    refine ⟨g xa, Finset.mem_image_of_mem g hxa, g xb, Finset.mem_image_of_mem g hxb,
      fun e => hxav (hginj e), fun e => hxbv (hginj e), allg V _ (fun y hy hy1 hy2 => ?_)⟩
    rw [tF1, tF1, tF2, tF2]
    exact h y hy (fun h => hy1 ((memg Q1 y).mpr h)) (fun h => hy2 ((memg Q2 y).mpr h))


/-- General position for Lemma T at the line of the planes of two facets,
**segments parallel to the line allowed**: distinct depths at the far ends
(as `TriGenFar`) and one facet with a single point where the other's
functional is least (else Corollary T1's rectangle exception). -/
def TriGenFarP (V Q1 Q2 : Finset ℝ³) (v : ℝ³) : Prop :=
  ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ, (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
    (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
    ∀ e : ℝ³, e ≠ 0 → f1 (v + e) = 0 → f2 (v + e) = 0 →
      (∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
        ⟪p, e⟫ ≠ ⟪q, e⟫) ∧
      ((∀ p ∈ Q1, ∀ p' ∈ Q1, (∀ p'' ∈ Q1, f2 p ≤ f2 p'') → f2 p' = f2 p → p' = p) ∨
        (∀ q ∈ Q2, ∀ q' ∈ Q2, (∀ q'' ∈ Q2, f1 q ≤ f1 q'') → f1 q' = f1 q → q' = q))

set_option maxHeartbeats 4000000 in
/-- **Lemma T over a vertex, facet form, segments parallel to the view line
allowed** (`TriGenFarP` in place of `TriGenFar`). -/
theorem isRupert_of_facets_vertex_par (V : Finset ℝ³) (hgen : NoThreeCollinear V)
    (Q1 Q2 : Finset ℝ³) (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (h1f : IsFacet V Q1) (h2f : IsFacet V Q2)
    (v : ℝ³) (hint : Q1 ∩ Q2 = {v}) (hne1 : ∃ p ∈ Q1, p ≠ v) (hne2 : ∃ p ∈ Q2, p ≠ v)
    (hT : TriGenFarP V Q1 Q2 v)
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
  obtain ⟨hfarZ, hone⟩ := hT f1 f2 z1 n1 z2 n2 e hne e1 e2
  obtain ⟨xa, hxa, xb, hxb, hxav, hxbv, hin'⟩ := hin
  refine isRupert_facets_vertex_par V Q1 Q2 v h1V h2V hint f1 f2 z1 n1 z2 n2 e hne e1 e2
    ⟨p1, hp1, hp1v⟩ ⟨p2, hp2, hp2v⟩ ?_ hfarZ hone
    ⟨xa, hxa, xb, hxb, hxav, hxbv, hin' f1 f2 z1 n1 z2 n2⟩
  exact hgen


set_option maxHeartbeats 4000000 in
/-- **Lemma T over an edge in coordinates, segments parallel to the view line
allowed** (as `isRupert_edge_coords` without the injectivity hypotheses; one
face with a single vertex of largest `a`, resp. `b`). -/
theorem isRupert_edge_coords_par (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (V Q1 Q2 : Finset ℝ³)
    (v w : ℝ³) (hvw : v 2 < w 2) (a b : ℝ³ → ℝ)
    (hy : ∀ p ∈ V, p = oblPt O r1 r2 (a p) (b p) (p 2))
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v, w})
    (hb1 : ∀ p ∈ Q1, b p = 0) (hb1' : ∀ p ∈ V, p ∉ Q1 → 0 < b p)
    (ha2 : ∀ p ∈ Q2, a p = 0) (ha2' : ∀ p ∈ V, p ∉ Q2 → 0 < a p)
    (hne1 : ∃ p ∈ Q1, p ∉ Q2) (hne2 : ∃ p ∈ Q2, p ∉ Q1)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hfarZ : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, a p' ≤ a p) → (∀ q' ∈ Q2, b q' ≤ b q) →
      p 2 ≠ q 2)
    (hone : (∀ p ∈ Q1, ∀ p' ∈ Q1, (∀ p'' ∈ Q1, a p'' ≤ a p) → a p' = a p → p' = p) ∨
      (∀ q ∈ Q2, ∀ q' ∈ Q2, (∀ q'' ∈ Q2, b q'' ≤ b q) → b q' = b q → q' = q))
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ∉ Q2 ∧ xb ∉ Q1 ∧
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → a y / a xa + b y / b xb < 1) : IsRupert V := by
  classical
  have mem12 : ∀ p, p ∈ Q1 → p ∈ Q2 → p = v ∨ p = w := by
    intro p h1 h2
    have : p ∈ Q1 ∩ Q2 := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hint] at this; simpa using this
  have hvi : v ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hwi : w ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hv1 := (Finset.mem_inter.mp hvi).1; have hv2 := (Finset.mem_inter.mp hvi).2
  have hw1 := (Finset.mem_inter.mp hwi).1; have hw2 := (Finset.mem_inter.mp hwi).2
  have hav := ha2 v hv2; have haw := ha2 w hw2
  have hbv := hb1 v hv1; have hbw := hb1 w hw1
  have hvw' : v ≠ w := fun e => by rw [e] at hvw; exact lt_irrefl _ hvw
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
  have d1 : ∀ {r r' : ℝ × ℝ} {u u' : ℝ³}, r ≠ r' → a u = r.1 → u 2 = r.2 → a u' = r'.1 →
      u' 2 = r'.2 → u ≠ u' := by
    intro r r' u u' h h1 h2 h1' h2' hu; apply h
    exact Prod.ext (by rw [← h1, ← h1', hu]) (by rw [← h2, ← h2', hu])
  have d2 : ∀ {r r' : ℝ × ℝ} {u u' : ℝ³}, r ≠ r' → b u = r.1 → u 2 = r.2 → b u' = r'.1 →
      u' 2 = r'.2 → u ≠ u' := by
    intro r r' u u' h h1 h2 h1' h2' hu; apply h
    exact Prod.ext (by rw [← h1, ← h1', hu]) (by rw [← h2, ← h2', hu])
  -- chains of the first face
  have chains1 : ∀ (s : ℝ) (u u' : ℝ³), (s = 1 ∨ s = -1) → (u = v ∧ u' = w ∨ u = w ∧ u' = v) →
      s * u' 2 < s * u 2 → ∃ m ca cz, ChainOKc (fun x z => (x, z) ∈ S1) (u 2) s m ca cz := by
    intro s u u' hs huu hso
    have hu1 : u ∈ Q1 := by rcases huu with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
    have hau : a u = 0 := by rcases huu with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
    apply exists_chainOKc_edge S1 (u 2) (u' 2) s hs hso
      (by rw [hS1, Finset.mem_image]; exact ⟨u, hu1, by rw [hau]⟩)
    · intro q hq h0 h1
      obtain ⟨p, hp, e1, e2⟩ := ofS1 q.1 q.2 hq
      by_cases hp2 : p ∈ Q2
      · exfalso
        have hpe : p = u ∨ p = u' := by
          rcases mem12 p hp hp2 with rfl | rfl <;> rcases huu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
        rcases hpe with rfl | rfl
        · exact h0 (Prod.ext (by rw [← e1, hau]) (by rw [← e2]))
        · apply h1; refine Prod.ext ?_ (by rw [← e2])
          show q.1 = 0; rw [← e1]; exact ha2 p hp2
      · rw [← e1]; exact ha2' p (h1V hp) hp2
    · obtain ⟨p, hp, hp2⟩ := hne1
      exact ⟨(a p, p 2), Finset.mem_image_of_mem _ hp, ha2' p (h1V hp) hp2⟩
    · intro q hq q' hq' q'' hq'' n1 n2 n3
      obtain ⟨p, hp, e1, e2⟩ := ofS1 q.1 q.2 hq
      obtain ⟨p', hp', e1', e2'⟩ := ofS1 q'.1 q'.2 hq'
      obtain ⟨p'', hp'', e1'', e2''⟩ := ofS1 q''.1 q''.2 hq''
      have := orient_ne_of_frame1' (O := O) (r1 := r1) (r2 := r2) (ai := a p) (zi := p 2)
        (aj := a p') (zj := p' 2) (zk := p'' 2) (ak := a p'')
        (by rw [e1, e2, e1', e2']; exact n1) (by
          intro c; rw [← pt1 p hp, ← pt1 p' hp', ← pt1 p'' hp'']
          exact hcol p (h1V hp) p' (h1V hp') p'' (h1V hp'') (d1 n1 e1 e2 e1' e2')
            (d1 n2 e1 e2 e1'' e2'') (d1 n3 e1' e2' e1'' e2'') c)
      unfold orient2 at this; rwa [e1, e2, e1', e2', e1'', e2''] at this
  have chains2 : ∀ (s : ℝ) (u u' : ℝ³), (s = 1 ∨ s = -1) → (u = v ∧ u' = w ∨ u = w ∧ u' = v) →
      s * u' 2 < s * u 2 → ∃ m ca cz, ChainOKc (fun x z => (x, z) ∈ S2) (u 2) s m ca cz := by
    intro s u u' hs huu hso
    have hu2 : u ∈ Q2 := by rcases huu with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
    have hbu : b u = 0 := by rcases huu with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
    apply exists_chainOKc_edge S2 (u 2) (u' 2) s hs hso
      (by rw [hS2, Finset.mem_image]; exact ⟨u, hu2, by rw [hbu]⟩)
    · intro q hq h0 h1
      obtain ⟨p, hp, e1, e2⟩ := ofS2 q.1 q.2 hq
      by_cases hp1 : p ∈ Q1
      · exfalso
        have hpe : p = u ∨ p = u' := by
          rcases mem12 p hp1 hp with rfl | rfl <;> rcases huu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
        rcases hpe with rfl | rfl
        · exact h0 (Prod.ext (by rw [← e1, hbu]) (by rw [← e2]))
        · apply h1; refine Prod.ext ?_ (by rw [← e2])
          show q.1 = 0; rw [← e1]; exact hb1 p hp1
      · rw [← e1]; exact hb1' p (h2V hp) hp1
    · obtain ⟨p, hp, hp1⟩ := hne2
      exact ⟨(b p, p 2), Finset.mem_image_of_mem _ hp, hb1' p (h2V hp) hp1⟩
    · intro q hq q' hq' q'' hq'' n1 n2 n3
      obtain ⟨p, hp, e1, e2⟩ := ofS2 q.1 q.2 hq
      obtain ⟨p', hp', e1', e2'⟩ := ofS2 q'.1 q'.2 hq'
      obtain ⟨p'', hp'', e1'', e2''⟩ := ofS2 q''.1 q''.2 hq''
      have := orient_ne_of_frame2' (O := O) (r1 := r1) (r2 := r2) (bi := b p) (zi := p 2)
        (bj := b p') (zj := p' 2) (zk := p'' 2) (bk := b p'')
        (by rw [e1, e2, e1', e2']; exact n1) (by
          intro c; rw [← pt2 p hp, ← pt2 p' hp', ← pt2 p'' hp'']
          exact hcol p (h2V hp) p' (h2V hp') p'' (h2V hp'') (d2 n1 e1 e2 e1' e2')
            (d2 n2 e1 e2 e1'' e2'') (d2 n3 e1' e2' e1'' e2'') c)
      unfold orient2 at this; rwa [e1, e2, e1', e2', e1'', e2''] at this
  have up : (1 : ℝ) * v 2 < 1 * w 2 := by linarith
  have lo : (-1 : ℝ) * w 2 < -1 * v 2 := by linarith
  -- far points of the chains, and tops above bottoms
  have far1 : ∀ {s z0 : ℝ} {m : ℕ} {ca cz : ℕ → ℝ}, ChainOKc (fun x z => (x, z) ∈ S1) z0 s m ca cz →
      ∃ p ∈ Q1, a p = ca m ∧ p 2 = cz m ∧ ∀ p'' ∈ Q1, a p'' ≤ a p := by
    intro s z0 m ca cz C
    obtain ⟨p, hp, e1, e2⟩ := ofS1 _ _ (C.mem m le_rfl)
    refine ⟨p, hp, e1, e2, fun p'' hp'' => ?_⟩
    rw [e1]
    by_cases e : a p'' = ca m ∧ p'' 2 = cz m
    · exact e.1.le
    rcases C.far _ _ (Finset.mem_image_of_mem _ hp'') e with h | ⟨h, -⟩
    · exact h.le
    · exact h.le
  have far2 : ∀ {s z0 : ℝ} {n : ℕ} {cb dz : ℕ → ℝ}, ChainOKc (fun x z => (x, z) ∈ S2) z0 s n cb dz →
      ∃ q ∈ Q2, b q = cb n ∧ q 2 = dz n ∧ ∀ q'' ∈ Q2, b q'' ≤ b q := by
    intro s z0 n cb dz C
    obtain ⟨q, hq, e1, e2⟩ := ofS2 _ _ (C.mem n le_rfl)
    refine ⟨q, hq, e1, e2, fun q'' hq'' => ?_⟩
    rw [e1]
    by_cases e : b q'' = cb n ∧ q'' 2 = dz n
    · exact e.1.le
    rcases C.far _ _ (Finset.mem_image_of_mem (fun p => (b p, p 2)) hq'') e with h | ⟨h, -⟩
    · exact h.le
    · exact h.le
  have topbot : ∀ {Q : ℝ → ℝ → Prop} {z0 z0' : ℝ} {m m' : ℕ} {ca cz ca' cz' : ℕ → ℝ},
      ChainOKc Q z0 1 m ca cz → ChainOKc Q z0' (-1) m' ca' cz' → cz' m' ≤ cz m := by
    intro Q z0 z0' m m' ca cz ca' cz' U L
    have ea := U.far_a_eq L
    by_cases e : ca' m' = ca m ∧ cz' m' = cz m
    · exact e.2.le
    rcases U.far _ _ (L.mem m' le_rfl) e with h | ⟨-, h⟩
    · exact absurd ea (by linarith)
    · linarith
  have pq : ∀ p ∈ Q1, ∀ q ∈ Q2, (∀ p'' ∈ Q1, a p'' ≤ a p) → p ≠ q := by
    intro p hp q hq hmax e; subst e
    obtain ⟨p', hp', hp'2⟩ := hne1
    have := hmax p' hp'; rw [ha2 p hq] at this
    linarith [ha2' p' (h1V hp') hp'2]
  obtain ⟨xa, hxa, xb, hxb, hxa2, hxb1, hin'⟩ := hin
  refine isRupert_edge_frame_par O r1 r2 hρ (fun x z => (x, z) ∈ S1) (fun x z => (x, z) ∈ S2)
    (zx := v 2) (zx' := w 2) hvw
    (chains1 1 w v (Or.inl rfl) (Or.inr ⟨rfl, rfl⟩) up)
    (chains1 (-1) v w (Or.inr rfl) (Or.inl ⟨rfl, rfl⟩) lo)
    (chains2 1 w v (Or.inl rfl) (Or.inr ⟨rfl, rfl⟩) up)
    (chains2 (-1) v w (Or.inr rfl) (Or.inl ⟨rfl, rfl⟩) lo) ?_ ?_
    (Finset.mem_image.mpr ⟨v, hv1, by rw [hav]⟩) (Finset.mem_image.mpr ⟨w, hw1, by rw [haw]⟩)
    (Finset.mem_image.mpr ⟨v, hv2, by rw [hbv]⟩) (Finset.mem_image.mpr ⟨w, hw2, by rw [hbw]⟩)
    ?_ ?_ ?_ ?_ V ?_ ?_ ?_
  · intro z h
    obtain ⟨p, hp, e1, e2⟩ := ofS1 0 z h
    by_cases hp2 : p ∈ Q2
    · rcases mem12 p hp hp2 with rfl | rfl
      · exact Or.inl e2.symm
      · exact Or.inr e2.symm
    · linarith [ha2' p (h1V hp) hp2]
  · intro z h
    obtain ⟨p, hp, e1, e2⟩ := ofS2 0 z h
    by_cases hp1 : p ∈ Q1
    · rcases mem12 p hp1 hp with rfl | rfl
      · exact Or.inl e2.symm
      · exact Or.inr e2.symm
    · linarith [hb1' p (h2V hp) hp1]
  · intro x z h
    obtain ⟨p, hp, e1, e2⟩ := ofS1 x z h
    by_cases hp2 : p ∈ Q2
    · rw [← e1, ha2 p hp2]
    · rw [← e1]; exact (ha2' p (h1V hp) hp2).le
  · intro x z h
    obtain ⟨p, hp, e1, e2⟩ := ofS2 x z h
    by_cases hp1 : p ∈ Q1
    · rw [← e1, hb1 p hp1]
    · rw [← e1]; exact (hb1' p (h2V hp) hp1).le
  · rcases hone with h1 | h2
    · left; intro m ca cz C z hz
      obtain ⟨p, hp, e1, e2, hmax⟩ := far1 C
      obtain ⟨p', hp', e1', e2'⟩ := ofS1 _ _ hz
      have := h1 p hp p' hp' hmax (by rw [e1, e1'])
      rw [← e2', this, e2]
    · right; intro n cb dz C z hz
      obtain ⟨q, hq, e1, e2, hmax⟩ := far2 C
      obtain ⟨q', hq', e1', e2'⟩ := ofS2 _ _ hz
      have := h2 q hq q' hq' hmax (by rw [e1, e1'])
      rw [← e2', this, e2]
  · intro m ca cz m' ca' cz' n cb dz n' cb' dz' U1 L1 U2 L2
    obtain ⟨pU, hpU, aU, zU, mU⟩ := far1 U1
    obtain ⟨pL, hpL, aL, zL, mL⟩ := far1 L1
    obtain ⟨qU, hqU, bU, wU, nU⟩ := far2 U2
    obtain ⟨qL, hqL, bL, wL, nL⟩ := far2 L2
    have tb1 := topbot U1 L1
    have tb2 := topbot U2 L2
    rcases hone with h1 | h2
    · have e : pL = pU := h1 pU hpU pL hpL mU (by rw [aU, aL]; exact (U1.far_a_eq L1).symm)
      have hz : cz' m' = cz m := by rw [← zL, ← zU, e]
      have hne := hfarZ pU hpU qL hqL (pq pU hpU qL hqL mU) mU nL
      rw [zU, wL] at hne
      rcases lt_or_gt_of_ne hne with h | h
      · right; rw [hz]; linarith
      · left; exact h
    · have e : qL = qU := h2 qU hqU qL hqL nU (by rw [bU, bL]; exact (U2.far_a_eq L2).symm)
      have hw : dz' n' = dz n := by rw [← wL, ← wU, e]
      have hne := hfarZ pU hpU qL hqL (pq pU hpU qL hqL mU) mU nL
      rw [zU, wL] at hne
      rcases lt_or_gt_of_ne hne with h | h
      · right; rw [← hw]; linarith
      · left; exact h
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
    have hxa0 := ha2' xa (h1V hxa) hxa2
    have hxb0 := hb1' xb (h2V hxb) hxb1
    obtain ⟨p, hp, e1, -, hmax1⟩ := far1 C1
    obtain ⟨q, hq, f1, -, hmax2⟩ := far2 C2
    have le1 : a xa ≤ ca m := by rw [← e1]; exact hmax1 xa hxa
    have le2 : b xb ≤ cb n := by rw [← f1]; exact hmax2 xb hxb
    have k := hin' y hy' h1 h2
    have ha := ha2' y hy' h2
    have hb := hb1' y hy' h1
    have t1 : a y / ca m ≤ a y / a xa := div_le_div_of_nonneg_left ha.le hxa0 le1
    have t2 : b y / cb n ≤ b y / b xb := div_le_div_of_nonneg_left hb.le hxb0 le2
    have : a y / ca m + b y / cb n < 1 := by linarith
    rw [div_add_div _ _ hA.ne' hB.ne', div_lt_one (mul_pos hA hB)] at this
    linarith

set_option maxHeartbeats 4000000 in
/-- **Lemma T over an edge, the edge vertical (`v` below `w`), segments parallel
to it allowed** (as `isRupert_facets_edge_vertical_lt` without `hpar`; one facet
with a single point where the other's functional is least). -/
theorem isRupert_facets_edge_vertical_lt_par (V Q1 Q2 : Finset ℝ³) (v w : ℝ³) (hvw : v 2 < w 2)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v, w}) (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ)
    (z1 : ∀ p ∈ Q1, f1 p = 0) (n1 : ∀ p ∈ V, p ∉ Q1 → f1 p < 0)
    (z2 : ∀ p ∈ Q2, f2 p = 0) (n2 : ∀ p ∈ V, p ∉ Q2 → f2 p < 0)
    (e1 : f1 (v + ez) = 0) (e2 : f2 (v + ez) = 0)
    (hne1 : ∃ p ∈ Q1, p ∉ Q2) (hne2 : ∃ p ∈ Q2, p ∉ Q1)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hfarZ : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
      p 2 ≠ q 2)
    (hone : (∀ p ∈ Q1, ∀ p' ∈ Q1, (∀ p'' ∈ Q1, f2 p ≤ f2 p'') → f2 p' = f2 p → p' = p) ∨
      (∀ q ∈ Q2, ∀ q' ∈ Q2, (∀ q'' ∈ Q2, f1 q ≤ f1 q'') → f1 q' = f1 q → q' = q))
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ∉ Q2 ∧ xb ∉ Q1 ∧
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1) : IsRupert V := by
  classical
  have hvi : v ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hv1 := (Finset.mem_inter.mp hvi).1; have hv2 := (Finset.mem_inter.mp hvi).2
  obtain ⟨p1, hp1, hp12⟩ := hne1
  obtain ⟨p2, hp2, hp21⟩ := hne2
  have m21 : f2 p1 < 0 := n2 p1 (h1V hp1) hp12
  have m12 : f1 p2 < 0 := n1 p2 (h2V hp2) hp21
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
  have hfar' : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, a p' ≤ a p) → (∀ q' ∈ Q2, b q' ≤ b q) →
      p 2 ≠ q 2 := fun p hp q hq hpq h1 h2 =>
    hfarZ p hp q hq hpq (fun p' hp' => by
        rw [G2 p, G2 p']; exact mul_le_mul_of_nonpos_right (h1 p' hp') m21.le)
      (fun q' hq' => by rw [G1 q, G1 q']; exact mul_le_mul_of_nonpos_right (h2 q' hq') m12.le)
  have hone' : (∀ p ∈ Q1, ∀ p' ∈ Q1, (∀ p'' ∈ Q1, a p'' ≤ a p) → a p' = a p → p' = p) ∨
      (∀ q ∈ Q2, ∀ q' ∈ Q2, (∀ q'' ∈ Q2, b q'' ≤ b q) → b q' = b q → q' = q) := by
    rcases hone with h | h
    · left; intro p hp p' hp' hmax e
      refine h p hp p' hp' (fun p'' hp'' => ?_) (by rw [G2 p', G2 p, e])
      rw [G2 p, G2 p'']; exact mul_le_mul_of_nonpos_right (hmax p'' hp'') m21.le
    · right; intro q hq q' hq' hmax e
      refine h q hq q' hq' (fun q'' hq'' => ?_) (by rw [G1 q', G1 q, e])
      rw [G1 q, G1 q'']; exact mul_le_mul_of_nonpos_right (hmax q'' hq'') m12.le
  have hin' : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ∉ Q2 ∧ xb ∉ Q1 ∧
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → a y / a xa + b y / b xb < 1 := by
    obtain ⟨xa, hxa, xb, hxb, hxa2, hxb1, h⟩ := hin
    refine ⟨xa, hxa, xb, hxb, hxa2, hxb1, fun y hy hy1 hy2 => ?_⟩
    have k := h y hy hy1 hy2
    rw [G1 y, G1 xb, G2 y, G2 xa, mul_div_mul_right _ _ m21.ne, mul_div_mul_right _ _ m12.ne] at k
    exact k
  rcases lt_or_gt_of_ne hρ with hneg | hpos
  · have hpos' : 0 < cross2 r2 r1 := by
      have : cross2 r2 r1 = -cross2 r1 r2 := by unfold cross2; ring
      rw [this]; linarith
    have swap : ∀ p q z, oblPt O r2 r1 q p z = oblPt O r1 r2 p q z := by
      intro p q z; ext j; fin_cases j <;> simp [oblPt] <;> ring
    refine isRupert_edge_coords_par O r2 r1 hpos' V Q2 Q1 v w hvw b a
      (fun p _ => by rw [swap]; exact hy p) h2V h1V (by rw [Finset.inter_comm]; exact hint)
      ha2 ha2' hb1 hb1' ⟨p2, hp2, hp21⟩ ⟨p1, hp1, hp12⟩ hcol
      (fun p hp q hq hpq h1 h2 => (hfar' q hq p hp (Ne.symm hpq) h2 h1).symm) hone'.symm ?_
    · obtain ⟨xa, hxa, xb, hxb, hxa2, hxb1, h⟩ := hin'
      exact ⟨xb, hxb, xa, hxa, hxb1, hxa2, fun y hy hy2 hy1 => by
        rw [add_comm]; exact h y hy hy1 hy2⟩
  · exact isRupert_edge_coords_par O r1 r2 hpos V Q1 Q2 v w hvw a b (fun p _ => hy p) h1V h2V hint
      hb1 hb1' ha2 ha2' ⟨p1, hp1, hp12⟩ ⟨p2, hp2, hp21⟩ hcol hfar' hone' hin'

/-- **Lemma T over an edge, the edge vertical, segments parallel to it
allowed.** -/
theorem isRupert_facets_edge_vertical_par (V Q1 Q2 : Finset ℝ³) (v w : ℝ³) (hvw : v ≠ w)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v, w}) (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ)
    (z1 : ∀ p ∈ Q1, f1 p = 0) (n1 : ∀ p ∈ V, p ∉ Q1 → f1 p < 0)
    (z2 : ∀ p ∈ Q2, f2 p = 0) (n2 : ∀ p ∈ V, p ∉ Q2 → f2 p < 0)
    (e1 : f1 (v + ez) = 0) (e2 : f2 (v + ez) = 0)
    (hne1 : ∃ p ∈ Q1, p ∉ Q2) (hne2 : ∃ p ∈ Q2, p ∉ Q1)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hvw2 : v 2 ≠ w 2)
    (hfarZ : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
      p 2 ≠ q 2)
    (hone : (∀ p ∈ Q1, ∀ p' ∈ Q1, (∀ p'' ∈ Q1, f2 p ≤ f2 p'') → f2 p' = f2 p → p' = p) ∨
      (∀ q ∈ Q2, ∀ q' ∈ Q2, (∀ q'' ∈ Q2, f1 q ≤ f1 q'') → f1 q' = f1 q → q' = q))
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ∉ Q2 ∧ xb ∉ Q1 ∧
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1) : IsRupert V := by
  have hvi : v ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hwi : w ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hvV : v ∈ V := h1V (Finset.mem_inter.mp hvi).1
  have hwV : w ∈ V := h1V (Finset.mem_inter.mp hwi).1
  rcases lt_or_gt_of_ne hvw2 with hlt | hgt
  · exact isRupert_facets_edge_vertical_lt_par V Q1 Q2 v w hlt h1V h2V hint f1 f2 z1 n1 z2 n2 e1 e2
      hne1 hne2 hcol hfarZ hone hin
  · -- the line through `w` is the same vertical line
    have hw : ∀ (f : ℝ³ →ᵃ[ℝ] ℝ), f v = 0 → f (v + ez) = 0 → f w = 0 → f (w + ez) = 0 := by
      intro f h0 h1 hw0
      have k1 : f (v + ez) = f.linear ez + f v := by
        rw [show v + ez = ez +ᵥ v by rw [vadd_eq_add, add_comm]]; exact f.map_vadd v ez
      have k2 : f (w + ez) = f.linear ez + f w := by
        rw [show w + ez = ez +ᵥ w by rw [vadd_eq_add, add_comm]]; exact f.map_vadd w ez
      rw [k2, hw0]; rw [k1, h0] at h1; linarith
    have hv1 := (Finset.mem_inter.mp hvi).1; have hv2 := (Finset.mem_inter.mp hvi).2
    have hw1 := (Finset.mem_inter.mp hwi).1; have hw2 := (Finset.mem_inter.mp hwi).2
    refine isRupert_facets_edge_vertical_lt_par V Q1 Q2 w v hgt h1V h2V
      (by rw [Finset.pair_comm]; exact hint) f1 f2 z1 n1 z2 n2
      (hw f1 (z1 v hv1) e1 (z1 w hw1)) (hw f2 (z2 v hv2) e2 (z2 w hw2)) hne1 hne2 hcol
      hfarZ hone hin


set_option maxHeartbeats 4000000 in
/-- **Lemma T over an edge, any frame, segments parallel to the edge allowed**
(as `isRupert_facets_edge` without `hpar`). -/
theorem isRupert_facets_edge_par (V Q1 Q2 : Finset ℝ³) (v w : ℝ³) (hvw : v ≠ w)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v, w}) (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ)
    (z1 : ∀ p ∈ Q1, f1 p = 0) (n1 : ∀ p ∈ V, p ∉ Q1 → f1 p < 0)
    (z2 : ∀ p ∈ Q2, f2 p = 0) (n2 : ∀ p ∈ V, p ∉ Q2 → f2 p < 0)
    (hne1 : ∃ p ∈ Q1, p ∉ Q2) (hne2 : ∃ p ∈ Q2, p ∉ Q1)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hfarZ : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
      ⟪p, w - v⟫ ≠ ⟪q, w - v⟫)
    (hone : (∀ p ∈ Q1, ∀ p' ∈ Q1, (∀ p'' ∈ Q1, f2 p ≤ f2 p'') → f2 p' = f2 p → p' = p) ∨
      (∀ q ∈ Q2, ∀ q' ∈ Q2, (∀ q'' ∈ Q2, f1 q ≤ f1 q'') → f1 q' = f1 q → q' = q))
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ∉ Q2 ∧ xb ∉ Q1 ∧
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1) : IsRupert V := by
  classical
  have he : w - v ≠ 0 := sub_ne_zero.mpr hvw.symm
  obtain ⟨R, hR, r, hr, hRe⟩ := exists_rotation_to_ez_pos (w - v) he
  apply isRupert_of_isRupert_image_rotation R hR
  set g := R.toEuclideanLin with hg
  set I := so3Isometry hR with hI
  have hgI : ∀ p, g p = I p := fun p => rfl
  have hginj : Function.Injective g := I.injective
  have hgz : ∀ p, g p 2 = ⟪p, w - v⟫ / r := fun p => by
    have := inner_toEuclideanLin_SO3 hR p (w - v)
    rw [hRe, real_inner_smul_right, inner_ez] at this
    field_simp; linarith
  have hIe : I.symm ez = r⁻¹ • (w - v) := by
    apply I.injective
    rw [LinearIsometryEquiv.apply_symm_apply, map_smul, ← hgI, hRe, smul_smul,
      inv_mul_cancel₀ hr.ne', one_smul]
  set F1 := f1.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap with hF1
  set F2 := f2.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap with hF2
  have tF1 : ∀ p, F1 (g p) = f1 p := fun p => by simp [hF1, hgI]
  have tF2 : ∀ p, F2 (g p) = f2 p := fun p => by simp [hF2, hgI]
  have tz : ∀ f : ℝ³ →ᵃ[ℝ] ℝ, f v = 0 → f w = 0 →
      (f.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap) (g v + ez) = 0 := by
    intro f h0 h1
    have : (f.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap) (g v + ez) =
        f (v + r⁻¹ • (w - v)) := by
      simp [hgI, map_add, hIe]
    rw [this]; exact affine_zero_line f h0 (by rw [add_sub_cancel]; exact h1) _
  have hvi : v ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hwi : w ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hv1 := (Finset.mem_inter.mp hvi).1; have hv2 := (Finset.mem_inter.mp hvi).2
  have hw1 := (Finset.mem_inter.mp hwi).1; have hw2 := (Finset.mem_inter.mp hwi).2
  have memg : ∀ (S : Finset ℝ³) p, g p ∈ S.image g ↔ p ∈ S := fun S p =>
    ⟨fun h => by obtain ⟨q, hq, e⟩ := Finset.mem_image.mp h; rwa [← hginj e], Finset.mem_image_of_mem g⟩
  have allg : ∀ (S : Finset ℝ³) (P : ℝ³ → Prop), (∀ p ∈ S, P (g p)) → ∀ q ∈ S.image g, P q := by
    intro S P h q hq; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq; exact h p hp
  refine isRupert_facets_edge_vertical_par (V.image g) (Q1.image g) (Q2.image g) (g v) (g w)
    (fun h => hvw (hginj h))
    (Finset.image_subset_image h1V) (Finset.image_subset_image h2V)
    (by rw [← Finset.image_inter _ _ hginj, hint, Finset.image_insert, Finset.image_singleton]) F1 F2
    (allg Q1 _ (fun p hp => by rw [tF1]; exact z1 p hp))
    (allg V _ (fun p hp hq => by rw [tF1]; exact n1 p hp (fun h => hq ((memg Q1 p).mpr h))))
    (allg Q2 _ (fun p hp => by rw [tF2]; exact z2 p hp))
    (allg V _ (fun p hp hq => by rw [tF2]; exact n2 p hp (fun h => hq ((memg Q2 p).mpr h))))
    (tz f1 (z1 v hv1) (z1 w hw1)) (tz f2 (z2 v hv2) (z2 w hw2)) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · obtain ⟨p, hp, hp2⟩ := hne1
    exact ⟨g p, Finset.mem_image_of_mem g hp, fun h => hp2 ((memg Q2 p).mp h)⟩
  · obtain ⟨p, hp, hp1⟩ := hne2
    exact ⟨g p, Finset.mem_image_of_mem g hp, fun h => hp1 ((memg Q1 p).mp h)⟩
  · refine allg V _ (fun p hp => allg V _ (fun q hq => allg V _ (fun u hu => ?_)))
    intro hpq hpu hqu c h
    apply hcol p hp q hq u hu (fun e => hpq (by rw [e])) (fun e => hpu (by rw [e]))
      (fun e => hqu (by rw [e])) c
    apply hginj
    simp only [map_sub, map_smul] at h ⊢; exact h
  · rw [hgz, hgz]
    intro h
    have k : ⟪v, w - v⟫ = ⟪w, w - v⟫ := by simpa [hr.ne'] using h
    have : ⟪w - v, w - v⟫ = 0 := by rw [inner_sub_left]; linarith
    exact hvw (sub_eq_zero.mp (inner_self_eq_zero.mp this)).symm
  · refine allg Q1 _ (fun p hp => allg Q2 _ (fun q hq => ?_))
    intro hpq h1 h2 h
    simp only [hgz] at h
    refine hfarZ p hp q hq (fun e => hpq (by rw [e])) (fun p' hp' => ?_) (fun q' hq' => ?_)
      (by simpa [hr.ne'] using h)
    · have := h1 (g p') (Finset.mem_image_of_mem g hp'); rwa [tF2, tF2] at this
    · have := h2 (g q') (Finset.mem_image_of_mem g hq'); rwa [tF1, tF1] at this
  · rcases hone with h | h
    · left
      refine allg Q1 _ (fun p hp => allg Q1 _ (fun p' hp' => ?_))
      intro hmax e
      rw [h p hp p' hp' (fun p'' hp'' => by
        have := hmax (g p'') (Finset.mem_image_of_mem g hp''); rwa [tF2, tF2] at this)
        (by rwa [tF2, tF2] at e)]
    · right
      refine allg Q2 _ (fun q hq => allg Q2 _ (fun q' hq' => ?_))
      intro hmax e
      rw [h q hq q' hq' (fun q'' hq'' => by
        have := hmax (g q'') (Finset.mem_image_of_mem g hq''); rwa [tF1, tF1] at this)
        (by rwa [tF1, tF1] at e)]
  · obtain ⟨xa, hxa, xb, hxb, hxa2, hxb1, h⟩ := hin
    refine ⟨g xa, Finset.mem_image_of_mem g hxa, g xb, Finset.mem_image_of_mem g hxb,
      fun e => hxa2 ((memg Q2 xa).mp e), fun e => hxb1 ((memg Q1 xb).mp e),
      allg V _ (fun y hy hy1 hy2 => ?_)⟩
    rw [tF1, tF1, tF2, tF2]
    exact h y hy (fun h => hy1 ((memg Q1 y).mpr h)) (fun h => hy2 ((memg Q2 y).mpr h))

/-- General position for Lemma T along an edge, **segments parallel to the
edge allowed**: distinct far depths along it (as `EdgeFar`) and one facet with
a single point where the other's functional is least. -/
def EdgeFarP (V Q1 Q2 : Finset ℝ³) (v w : ℝ³) : Prop :=
  ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ, (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
    (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
    (∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
      ⟪p, w - v⟫ ≠ ⟪q, w - v⟫) ∧
    ((∀ p ∈ Q1, ∀ p' ∈ Q1, (∀ p'' ∈ Q1, f2 p ≤ f2 p'') → f2 p' = f2 p → p' = p) ∨
      (∀ q ∈ Q2, ∀ q' ∈ Q2, (∀ q'' ∈ Q2, f1 q ≤ f1 q'') → f1 q' = f1 q → q' = q))

set_option maxHeartbeats 4000000 in
/-- **Lemma T over an edge, facet form, segments parallel to the edge
allowed** (`EdgeFarP` in place of `EdgeFar`). -/
theorem isRupert_of_facets_edge_par (V : Finset ℝ³) (hgen : NoThreeCollinear V)
    (Q1 Q2 : Finset ℝ³) (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (h1f : IsFacet V Q1) (h2f : IsFacet V Q2)
    (v w : ℝ³) (hvw : v ≠ w) (hint : Q1 ∩ Q2 = {v, w})
    (hne1 : ∃ p ∈ Q1, p ∉ Q2) (hne2 : ∃ p ∈ Q2, p ∉ Q1)
    (hfarZ : EdgeFarP V Q1 Q2 v w)
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ∉ Q2 ∧ xb ∉ Q1 ∧ ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ,
      (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
      (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1) : IsRupert V := by
  classical
  obtain ⟨f1, z1, n1⟩ := h1f
  obtain ⟨f2, z2, n2⟩ := h2f
  obtain ⟨xa, hxa, xb, hxb, hxa2, hxb1, hin'⟩ := hin
  obtain ⟨hfar, hone⟩ := hfarZ f1 f2 z1 n1 z2 n2
  exact isRupert_facets_edge_par V Q1 Q2 v w hvw h1V h2V hint f1 f2 z1 n1 z2 n2 hne1 hne2 hgen
    hfar hone ⟨xa, hxa, xb, hxb, hxa2, hxb1, hin' f1 f2 z1 n1 z2 n2⟩

end Minimality

end
