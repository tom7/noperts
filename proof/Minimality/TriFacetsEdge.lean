module

public import Minimality.TriFacets

@[expose] public section

/-!
# Lemma T for two facets sharing an edge

The edge analogue of `TriFacets.lean`: two facets `Q1`, `Q2` of `V` sharing the
edge `v w`, viewed along it.  If every point off both facets projects strictly
inside the triangle of the edge's shadow point and the far points of the two
facets, `V` is Rupert (the edge views of Theorems E–L of
`FEWER-FACES-PROOFS.md` §7).  The chains come from `exists_chainOK_edge`.
-/

namespace Minimality

open Finset Filter Topology
open scoped RealInnerProductSpace

/-- `orient_ne_of_frame1` for any two distinct points of the first ray's plane. -/
theorem orient_ne_of_frame1' {O r1 r2 : ℝ²} {ai zi aj zj ak zk : ℝ} (hij : (ai, zi) ≠ (aj, zj))
    (h : ∀ c : ℝ, oblPt O r1 r2 ak 0 zk - oblPt O r1 r2 ai 0 zi ≠
      c • (oblPt O r1 r2 aj 0 zj - oblPt O r1 r2 ai 0 zi)) :
    orient2 ai zi aj zj ak zk ≠ 0 := by
  by_cases ha : ai = aj
  · have hz : zj - zi ≠ 0 := fun e => hij (by rw [ha, show zi = zj by linarith])
    intro h0
    unfold orient2 at h0
    rw [ha, sub_self, zero_mul, zero_sub, neg_eq_zero] at h0
    have hk : ak = aj := by
      have := (mul_eq_zero.mp h0).resolve_left hz; linarith
    apply h ((zk - zi) / (zj - zi))
    rw [ha, hk]
    ext j; fin_cases j <;> simp [oblPt]
    field_simp
  · exact orient_ne_of_frame1 ha h

/-- The same on the second ray's plane. -/
theorem orient_ne_of_frame2' {O r1 r2 : ℝ²} {bi zi bj zj bk zk : ℝ} (hij : (bi, zi) ≠ (bj, zj))
    (h : ∀ c : ℝ, oblPt O r1 r2 0 bk zk - oblPt O r1 r2 0 bi zi ≠
      c • (oblPt O r1 r2 0 bj zj - oblPt O r1 r2 0 bi zi)) :
    orient2 bi zi bj zj bk zk ≠ 0 := by
  by_cases hb : bi = bj
  · have hz : zj - zi ≠ 0 := fun e => hij (by rw [hb, show zi = zj by linarith])
    intro h0
    unfold orient2 at h0
    rw [hb, sub_self, zero_mul, zero_sub, neg_eq_zero] at h0
    have hk : bk = bj := by
      have := (mul_eq_zero.mp h0).resolve_left hz; linarith
    apply h ((zk - zi) / (zj - zi))
    rw [hb, hk]
    ext j; fin_cases j <;> simp [oblPt]
    field_simp
  · exact orient_ne_of_frame2 hb h

set_option maxHeartbeats 4000000 in
/-- **Lemma T over an edge, in frame coordinates.**  The points of `V` are
`oblPt O r1 r2 (a p) (b p) (p 2)`; `Q1` lies on the ray `b = 0`, `Q2` on `a = 0`,
they share the vertical edge `v w`, every other point at `a, b > 0`. -/
theorem isRupert_edge_coords (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (V Q1 Q2 : Finset ℝ³)
    (v w : ℝ³) (hvw : v 2 < w 2) (a b : ℝ³ → ℝ)
    (hy : ∀ p ∈ V, p = oblPt O r1 r2 (a p) (b p) (p 2))
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v, w})
    (hb1 : ∀ p ∈ Q1, b p = 0) (hb1' : ∀ p ∈ V, p ∉ Q1 → 0 < b p)
    (ha2 : ∀ p ∈ Q2, a p = 0) (ha2' : ∀ p ∈ V, p ∉ Q2 → 0 < a p)
    (hne1 : ∃ p ∈ Q1, p ∉ Q2) (hne2 : ∃ p ∈ Q2, p ∉ Q1)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hinjv : Set.InjOn (fun p => (a p, b p)) ((V.erase v : Finset ℝ³) : Set ℝ³))
    (hinjw : Set.InjOn (fun p => (a p, b p)) ((V.erase w : Finset ℝ³) : Set ℝ³))
    (hfarZ : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, a p' ≤ a p) → (∀ q' ∈ Q2, b q' ≤ b q) →
      p 2 ≠ q 2)
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
      s * u' 2 < s * u 2 → ∃ m ca cz, ChainOK (fun x z => (x, z) ∈ S1) (u 2) s m ca cz := by
    intro s u u' hs huu hso
    have hu1 : u ∈ Q1 := by rcases huu with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
    have hau : a u = 0 := by rcases huu with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
    have hinj : Set.InjOn (fun p => (a p, b p)) ((V.erase u' : Finset ℝ³) : Set ℝ³) := by
      rcases huu with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact hinjw
      · exact hinjv
    apply exists_chainOK_edge S1 (u 2) (u' 2) s hs hso
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
    · intro q hq q' hq' e
      have hq0 := Finset.ne_of_mem_erase hq; have hq0' := Finset.ne_of_mem_erase hq'
      obtain ⟨p, hp, e1, e2⟩ := ofS1 q.1 q.2 (Finset.mem_of_mem_erase hq)
      obtain ⟨p', hp', e1', e2'⟩ := ofS1 q'.1 q'.2 (Finset.mem_of_mem_erase hq')
      have pu : p ≠ u' := fun h => hq0 (Prod.ext (by
        show q.1 = 0; rw [← e1, h]; rcases huu with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption)
        (by rw [← e2, h]))
      have pu' : p' ≠ u' := fun h => hq0' (Prod.ext (by
        show q'.1 = 0; rw [← e1', h]; rcases huu with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption)
        (by rw [← e2', h]))
      have : p = p' := hinj (Finset.mem_erase.mpr ⟨pu, h1V hp⟩) (Finset.mem_erase.mpr ⟨pu', h1V hp'⟩)
        (by simp only [Prod.mk.injEq]; rw [hb1 p hp, hb1 p' hp']; exact ⟨by rw [e1, e1']; exact e, rfl⟩)
      exact Prod.ext e (by rw [← e2, ← e2', this])
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
      s * u' 2 < s * u 2 → ∃ m ca cz, ChainOK (fun x z => (x, z) ∈ S2) (u 2) s m ca cz := by
    intro s u u' hs huu hso
    have hu2 : u ∈ Q2 := by rcases huu with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
    have hbu : b u = 0 := by rcases huu with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
    have hinj : Set.InjOn (fun p => (a p, b p)) ((V.erase u' : Finset ℝ³) : Set ℝ³) := by
      rcases huu with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact hinjw
      · exact hinjv
    apply exists_chainOK_edge S2 (u 2) (u' 2) s hs hso
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
    · intro q hq q' hq' e
      have hq0 := Finset.ne_of_mem_erase hq; have hq0' := Finset.ne_of_mem_erase hq'
      obtain ⟨p, hp, e1, e2⟩ := ofS2 q.1 q.2 (Finset.mem_of_mem_erase hq)
      obtain ⟨p', hp', e1', e2'⟩ := ofS2 q'.1 q'.2 (Finset.mem_of_mem_erase hq')
      have pu : p ≠ u' := fun h => hq0 (Prod.ext (by
        show q.1 = 0; rw [← e1, h]; rcases huu with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption)
        (by rw [← e2, h]))
      have pu' : p' ≠ u' := fun h => hq0' (Prod.ext (by
        show q'.1 = 0; rw [← e1', h]; rcases huu with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption)
        (by rw [← e2', h]))
      have : p = p' := hinj (Finset.mem_erase.mpr ⟨pu, h2V hp⟩) (Finset.mem_erase.mpr ⟨pu', h2V hp'⟩)
        (by simp only [Prod.mk.injEq]; rw [ha2 p hp, ha2 p' hp']; exact ⟨rfl, by rw [e1, e1']; exact e⟩)
      exact Prod.ext e (by rw [← e2, ← e2', this])
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
  obtain ⟨xa, hxa, xb, hxb, hxa2, hxb1, hin'⟩ := hin
  refine isRupert_edge_frame O r1 r2 hρ (fun x z => (x, z) ∈ S1) (fun x z => (x, z) ∈ S2)
    (zx := v 2) (zx' := w 2) hvw
    (chains1 1 w v (Or.inl rfl) (Or.inr ⟨rfl, rfl⟩) up)
    (chains1 (-1) v w (Or.inr rfl) (Or.inl ⟨rfl, rfl⟩) lo)
    (chains2 1 w v (Or.inl rfl) (Or.inr ⟨rfl, rfl⟩) up)
    (chains2 (-1) v w (Or.inr rfl) (Or.inl ⟨rfl, rfl⟩) lo) ?_ ?_
    (Finset.mem_image.mpr ⟨v, hv1, by rw [hav]⟩) (Finset.mem_image.mpr ⟨w, hw1, by rw [haw]⟩)
    (Finset.mem_image.mpr ⟨v, hv2, by rw [hbv]⟩) (Finset.mem_image.mpr ⟨w, hw2, by rw [hbw]⟩)
    ?_ ?_ V ?_ ?_ ?_ ?_
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
      have := C1.far_pos
      rw [← e1, ha2 p hq] at this; exact lt_irrefl _ this
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
/-- **Lemma T over an edge, the edge vertical**, with `v` below `w`. -/
theorem isRupert_facets_edge_vertical_lt (V Q1 Q2 : Finset ℝ³) (v w : ℝ³) (hvw : v 2 < w 2)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v, w}) (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ)
    (z1 : ∀ p ∈ Q1, f1 p = 0) (n1 : ∀ p ∈ V, p ∉ Q1 → f1 p < 0)
    (z2 : ∀ p ∈ Q2, f2 p = 0) (n2 : ∀ p ∈ V, p ∉ Q2 → f2 p < 0)
    (e1 : f1 (v + ez) = 0) (e2 : f2 (v + ez) = 0)
    (hne1 : ∃ p ∈ Q1, p ∉ Q2) (hne2 : ∃ p ∈ Q2, p ∉ Q1)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hpar : ∀ p ∈ V, ∀ q ∈ V, p ≠ q → ({p, q} : Finset ℝ³) ≠ {v, w} → p 0 ≠ q 0 ∨ p 1 ≠ q 1)
    (hfarZ : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
      p 2 ≠ q 2)
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
  have hinj : ∀ u ∈ ({v, w} : Finset ℝ³),
      Set.InjOn (fun p => (a p, b p)) ((V.erase u : Finset ℝ³) : Set ℝ³) := by
    intro u hu p hp q hq e
    simp only [Prod.mk.injEq] at e
    by_contra hpq
    have hp' := Finset.mem_erase.mp hp; have hq' := Finset.mem_erase.mp hq
    have hne : ({p, q} : Finset ℝ³) ≠ {v, w} := by
      intro h
      have : u ∈ ({p, q} : Finset ℝ³) := h ▸ hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl
      · exact hp'.1 rfl
      · exact hq'.1 rfl
    obtain ⟨c0, c1⟩ := hxy p; obtain ⟨d0, d1⟩ := hxy q
    rw [e.1, e.2] at c0 c1
    rcases hpar p hp'.2 q hq'.2 hpq hne with h | h <;> apply h <;> linarith
  have hinjv := hinj v (by simp)
  have hfar' : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, a p' ≤ a p) → (∀ q' ∈ Q2, b q' ≤ b q) →
      p 2 ≠ q 2 := fun p hp q hq hpq h1 h2 =>
    hfarZ p hp q hq hpq (fun p' hp' => by
        rw [G2 p, G2 p']; exact mul_le_mul_of_nonpos_right (h1 p' hp') m21.le)
      (fun q' hq' => by rw [G1 q, G1 q']; exact mul_le_mul_of_nonpos_right (h2 q' hq') m12.le)
  have hinjw := hinj w (by simp)
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
    refine isRupert_edge_coords O r2 r1 hpos' V Q2 Q1 v w hvw b a
      (fun p _ => by rw [swap]; exact hy p) h2V h1V (by rw [Finset.inter_comm]; exact hint)
      ha2 ha2' hb1 hb1' ⟨p2, hp2, hp21⟩ ⟨p1, hp1, hp12⟩ hcol ?_ ?_
      (fun p hp q hq hpq h1 h2 => (hfar' q hq p hp (Ne.symm hpq) h2 h1).symm) ?_
    · intro p hp q hq e
      simp only [Prod.mk.injEq] at e
      exact hinjv hp hq (by simp only [Prod.mk.injEq]; exact ⟨e.2, e.1⟩)
    · intro p hp q hq e
      simp only [Prod.mk.injEq] at e
      exact hinjw hp hq (by simp only [Prod.mk.injEq]; exact ⟨e.2, e.1⟩)
    · obtain ⟨xa, hxa, xb, hxb, hxa2, hxb1, h⟩ := hin'
      exact ⟨xb, hxb, xa, hxa, hxb1, hxa2, fun y hy hy2 hy1 => by
        rw [add_comm]; exact h y hy hy1 hy2⟩
  · exact isRupert_edge_coords O r1 r2 hpos V Q1 Q2 v w hvw a b (fun p _ => hy p) h1V h2V hint
      hb1 hb1' ha2 ha2' ⟨p1, hp1, hp12⟩ ⟨p2, hp2, hp21⟩ hcol hinjv hinjw hfar' hin'

/-- **Lemma T over an edge, the edge vertical.** -/
theorem isRupert_facets_edge_vertical (V Q1 Q2 : Finset ℝ³) (v w : ℝ³) (hvw : v ≠ w)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v, w}) (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ)
    (z1 : ∀ p ∈ Q1, f1 p = 0) (n1 : ∀ p ∈ V, p ∉ Q1 → f1 p < 0)
    (z2 : ∀ p ∈ Q2, f2 p = 0) (n2 : ∀ p ∈ V, p ∉ Q2 → f2 p < 0)
    (e1 : f1 (v + ez) = 0) (e2 : f2 (v + ez) = 0)
    (hne1 : ∃ p ∈ Q1, p ∉ Q2) (hne2 : ∃ p ∈ Q2, p ∉ Q1)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hpar : ∀ p ∈ V, ∀ q ∈ V, p ≠ q → ({p, q} : Finset ℝ³) ≠ {v, w} → p 0 ≠ q 0 ∨ p 1 ≠ q 1)
    (hvw2 : v 2 ≠ w 2)
    (hfarZ : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
      p 2 ≠ q 2)
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ∉ Q2 ∧ xb ∉ Q1 ∧
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1) : IsRupert V := by
  have hvi : v ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hwi : w ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hvV : v ∈ V := h1V (Finset.mem_inter.mp hvi).1
  have hwV : w ∈ V := h1V (Finset.mem_inter.mp hwi).1
  rcases lt_or_gt_of_ne hvw2 with hlt | hgt
  · exact isRupert_facets_edge_vertical_lt V Q1 Q2 v w hlt h1V h2V hint f1 f2 z1 n1 z2 n2 e1 e2
      hne1 hne2 hcol hpar hfarZ hin
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
    refine isRupert_facets_edge_vertical_lt V Q1 Q2 w v hgt h1V h2V
      (by rw [Finset.pair_comm]; exact hint) f1 f2 z1 n1 z2 n2
      (hw f1 (z1 v hv1) e1 (z1 w hw1)) (hw f2 (z2 v hv2) e2 (z2 w hw2)) hne1 hne2 hcol
      (fun p hp q hq hpq h => hpar p hp q hq hpq (by rw [Finset.pair_comm v w]; exact h)) hfarZ hin

set_option maxHeartbeats 4000000 in
/-- **Lemma T over an edge** for two facets `Q1`, `Q2` (functionals `f1`, `f2`)
sharing the edge `v w`, viewed along it: no three points collinear, no other
segment parallel to it, distinct far depths along it, and every point off both
facets inside the shadow triangle of the edge and some `xa ∈ Q1 \ Q2`,
`xb ∈ Q2 \ Q1`. -/
theorem isRupert_facets_edge (V Q1 Q2 : Finset ℝ³) (v w : ℝ³) (hvw : v ≠ w)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v, w}) (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ)
    (z1 : ∀ p ∈ Q1, f1 p = 0) (n1 : ∀ p ∈ V, p ∉ Q1 → f1 p < 0)
    (z2 : ∀ p ∈ Q2, f2 p = 0) (n2 : ∀ p ∈ V, p ∉ Q2 → f2 p < 0)
    (hne1 : ∃ p ∈ Q1, p ∉ Q2) (hne2 : ∃ p ∈ Q2, p ∉ Q1)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hpar : ∀ p ∈ V, ∀ q ∈ V, p ≠ q → ({p, q} : Finset ℝ³) ≠ {v, w} → ∀ c : ℝ, q - p ≠ c • (w - v))
    (hfarZ : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
      ⟪p, w - v⟫ ≠ ⟪q, w - v⟫)
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
  refine isRupert_facets_edge_vertical (V.image g) (Q1.image g) (Q2.image g) (g v) (g w)
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
  · refine allg V _ (fun p hp => allg V _ (fun q hq => ?_))
    intro hpq hpair
    by_contra h; push Not at h
    obtain ⟨h0, h1⟩ := h
    apply hpar p hp q hq (fun e => hpq (by rw [e])) (fun e => hpair (by
      rw [show ({g p, g q} : Finset ℝ³) = Finset.image g {p, q} by simp,
        show ({g v, g w} : Finset ℝ³) = Finset.image g {v, w} by simp, e]))
      ((g (q - p)) 2 / r)
    apply hginj
    rw [map_smul, hRe]
    ext k; fin_cases k
    · simp [ez, map_sub]; linarith
    · simp [ez, map_sub]; linarith
    · simp [ez]; field_simp
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
  · obtain ⟨xa, hxa, xb, hxb, hxa2, hxb1, h⟩ := hin
    refine ⟨g xa, Finset.mem_image_of_mem g hxa, g xb, Finset.mem_image_of_mem g hxb,
      fun e => hxa2 ((memg Q2 xa).mp e), fun e => hxb1 ((memg Q1 xb).mp e),
      allg V _ (fun y hy hy1 hy2 => ?_)⟩
    rw [tF1, tF1, tF2, tF2]
    exact h y hy (fun h => hy1 ((memg Q1 y).mpr h)) (fun h => hy2 ((memg Q2 y).mpr h))

/-- General position for Lemma T along an edge `v w` shared by two facets `Q1`,
`Q2`: the far ends of the two faces in the shadow (the point of `Q1` where `f2`
is least, that of `Q2` where `f1` is least) have distinct depths along the edge.
Weaker than distinct depths on all of `V` (`EdgeFar.of_injOn`). -/
def EdgeFar (V Q1 Q2 : Finset ℝ³) (v w : ℝ³) : Prop :=
  ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ, (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
    (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
    ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
      ⟪p, w - v⟫ ≠ ⟪q, w - v⟫

theorem EdgeFar.of_injOn {V Q1 Q2 : Finset ℝ³} {v w : ℝ³} (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V)
    (h : Set.InjOn (fun p : ℝ³ => ⟪p, w - v⟫) (V : Set ℝ³)) : EdgeFar V Q1 Q2 v w :=
  fun _ _ _ _ _ _ _ hp _ hq hpq _ _ hd => hpq (h (h1V hp) (h2V hq) hd)

set_option maxHeartbeats 4000000 in
/-- **Lemma T over an edge, facet form** (`FEWER-FACES-PROOFS.md` §7): two
facets `Q1`, `Q2` of `V` in general position sharing exactly the edge `v w`,
distinct depths along it at the far ends (`EdgeFar`), and every point off both
facets inside the shadow triangle of the edge and some `xa ∈ Q1 \ Q2`,
`xb ∈ Q2 \ Q1` (stated with any facet functionals `f1`, `f2`): Rupert. -/
theorem isRupert_of_facets_edge (V : Finset ℝ³) (hgen : GenPos V)
    (Q1 Q2 : Finset ℝ³) (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (h1f : IsFacet V Q1) (h2f : IsFacet V Q2)
    (v w : ℝ³) (hvw : v ≠ w) (hint : Q1 ∩ Q2 = {v, w})
    (hne1 : ∃ p ∈ Q1, p ∉ Q2) (hne2 : ∃ p ∈ Q2, p ∉ Q1)
    (hfarZ : EdgeFar V Q1 Q2 v w)
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ∉ Q2 ∧ xb ∉ Q1 ∧ ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ,
      (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
      (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1) : IsRupert V := by
  classical
  have hvi : v ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hwi : w ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hvV : v ∈ V := h1V (Finset.mem_inter.mp hvi).1
  have hwV : w ∈ V := h1V (Finset.mem_inter.mp hwi).1
  obtain ⟨f1, z1, n1⟩ := h1f
  obtain ⟨f2, z2, n2⟩ := h2f
  obtain ⟨xa, hxa, xb, hxb, hxa2, hxb1, hin'⟩ := hin
  refine isRupert_facets_edge V Q1 Q2 v w hvw h1V h2V hint f1 f2 z1 n1 z2 n2 hne1 hne2 ?_ ?_
    (hfarZ f1 f2 z1 n1 z2 n2)
    ⟨xa, hxa, xb, hxb, hxa2, hxb1, hin' f1 f2 z1 n1 z2 n2⟩
  · intro p hp q hq r hr hpq hpr hqr c
    exact (hgen p hp r hr p hp q hq hpr hpq (by
      intro h
      have : r ∈ ({p, q} : Finset ℝ³) := h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h' | h'
      · exact hpr h'.symm
      · exact hqr h'.symm)).1 c
  · intro p hp q hq hpq hpair c
    exact (hgen p hp q hq v hvV w hwV hpq hvw hpair).1 c

end Minimality

end
