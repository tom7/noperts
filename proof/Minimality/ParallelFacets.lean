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

end Minimality

end
