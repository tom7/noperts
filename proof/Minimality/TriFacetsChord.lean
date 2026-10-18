module

public import Minimality.TriFacets
public import Minimality.TriFacesChord

@[expose] public section

/-!
# Lemma T′ at a vertex: frame coordinates

`isRupert_vertex_coords` with one off point `yc` allowed on the far side: its
barycentric value is `≤ 1` (all others `< 1`). If it is `< 1` for the far ends
the old argument applies; if it is `= 1`, `yc` lies on the chord and, not being
collinear with the far points, is hidden by the tilt (`isRupert_vertex_frame_chord`).
-/

namespace Minimality

open Finset Filter Topology
open scoped RealInnerProductSpace

set_option maxHeartbeats 8000000 in
/-- **Lemma T′ over a vertex, in frame coordinates.** -/
theorem isRupert_vertex_coords_chord (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (V Q1 Q2 : Finset ℝ³)
    (v : ℝ³) (a b : ℝ³ → ℝ) (hy : ∀ p ∈ V, p = oblPt O r1 r2 (a p) (b p) (p 2))
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v})
    (hb1 : ∀ p ∈ Q1, b p = 0) (hb1' : ∀ p ∈ V, p ∉ Q1 → 0 < b p)
    (ha2 : ∀ p ∈ Q2, a p = 0) (ha2' : ∀ p ∈ V, p ∉ Q2 → 0 < a p)
    (hne1 : ∃ p ∈ Q1, p ≠ v) (hne2 : ∃ p ∈ Q2, p ≠ v)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hinj : Set.InjOn (fun p => (a p, b p)) (V : Set ℝ³))
    (hZ : Set.InjOn (fun p : ℝ³ => p 2) (V : Set ℝ³))
    (xa xb : ℝ³) (hxa : xa ∈ Q1) (hxb : xb ∈ Q2) (hxav : xa ≠ v) (hxbv : xb ≠ v)
    (yc : ℝ³) (hycV : yc ∈ V) (hyc1 : yc ∉ Q1) (hyc2 : yc ∉ Q2)
    (hin' : ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → y ≠ yc → a y / a xa + b y / b xb < 1)
    (hyc : a yc / a xa + b yc / b xb ≤ 1) : IsRupert V := by
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
  -- the far ends, from the upper chains
  obtain ⟨m0, ca0, cz0, U1⟩ := chains1 1 (Or.inl rfl)
  obtain ⟨n0, cb0, dz0, U2⟩ := chains2 1 (Or.inl rfl)
  have hA := U1.far_pos
  have hB := U2.far_pos
  have hxa0 := apos xa hxa hxav
  have hxb0 := bpos xb hxb hxbv
  have hay := ha2' yc hycV hyc2
  have hby := hb1' yc hycV hyc1
  have le1 : a xa ≤ ca0 m0 := by
    by_cases e : a xa = ca0 m0 ∧ xa 2 = cz0 m0
    · exact e.1.le
    · exact (U1.far _ _ (Finset.mem_image_of_mem _ hxa) e).le
  have le2 : b xb ≤ cb0 n0 := by
    by_cases e : b xb = cb0 n0 ∧ xb 2 = dz0 n0
    · exact e.1.le
    · exact (U2.far _ _ (Finset.mem_image_of_mem (fun p => (b p, p 2)) hxb) e).le
  have hle : a yc * cb0 n0 + b yc * ca0 m0 ≤ ca0 m0 * cb0 n0 := by
    have t1 : a yc / ca0 m0 ≤ a yc / a xa := div_le_div_of_nonneg_left hay.le hxa0 le1
    have t2 : b yc / cb0 n0 ≤ b yc / b xb := div_le_div_of_nonneg_left hby.le hxb0 le2
    have : a yc / ca0 m0 + b yc / cb0 n0 ≤ 1 := by linarith
    rw [div_add_div _ _ hA.ne' hB.ne', div_le_one (mul_pos hA hB)] at this
    linarith
  -- the far points in `V`
  obtain ⟨pA, hpA, epA1, epA2⟩ := ofS1 _ _ (U1.mem m0 le_rfl)
  obtain ⟨pB, hpB, epB1, epB2⟩ := ofS2 _ _ (U2.mem n0 le_rfl)
  -- the point on the chord (or a dummy one when `yc` is strictly inside)
  obtain ⟨ac, bc, zc, hac, hbc, hch1, hch2, hspec⟩ : ∃ ac bc zc : ℝ, 0 < ac ∧ 0 < bc ∧
      ac * cb0 n0 + bc * ca0 m0 = ca0 m0 * cb0 n0 ∧
      cb0 n0 * (zc - cz0 m0) - bc * (dz0 n0 - cz0 m0) ≠ 0 ∧
      (a yc * cb0 n0 + b yc * ca0 m0 < ca0 m0 * cb0 n0 ∨ (a yc = ac ∧ b yc = bc ∧ yc 2 = zc)) := by
    by_cases hst : a yc * cb0 n0 + b yc * ca0 m0 < ca0 m0 * cb0 n0
    · refine ⟨ca0 m0 / 2, cb0 n0 / 2, (cz0 m0 + dz0 n0) / 2 + 1, by positivity, by positivity,
        by ring, ?_, Or.inl hst⟩
      have : cb0 n0 * ((cz0 m0 + dz0 n0) / 2 + 1 - cz0 m0) - cb0 n0 / 2 * (dz0 n0 - cz0 m0) =
          cb0 n0 := by ring
      rw [this]; exact hB.ne'
    · have heq : a yc * cb0 n0 + b yc * ca0 m0 = ca0 m0 * cb0 n0 := by linarith
      refine ⟨a yc, b yc, yc 2, hay, hby, by linarith, ?_, Or.inr ⟨rfl, rfl, rfl⟩⟩
      intro hD
      -- then `yc` lies on the segment of the far points
      have hpAv : pA ≠ v := fun h => by rw [h, hav] at epA1; linarith
      have hpBv : pB ≠ v := fun h => by rw [h, hbv] at epB1; linarith
      have hpAB : pA ≠ pB := fun h => hpAv (only pA hpA (h ▸ hpB))
      apply hcol pA (h1V hpA) pB (h2V hpB) yc hycV hpAB (fun h => hyc1 (h ▸ hpA))
        (fun h => hyc2 (h ▸ hpB)) (b yc / cb0 n0)
      have eA : pA = oblPt O r1 r2 (ca0 m0) 0 (cz0 m0) := by rw [← epA1, ← epA2]; exact pt1 pA hpA
      have eB : pB = oblPt O r1 r2 0 (cb0 n0) (dz0 n0) := by rw [← epB1, ← epB2]; exact pt2 pB hpB
      have key : oblPt O r1 r2 (a yc) (b yc) (yc 2) - oblPt O r1 r2 (ca0 m0) 0 (cz0 m0) =
          (b yc / cb0 n0) • (oblPt O r1 r2 0 (cb0 n0) (dz0 n0) - oblPt O r1 r2 (ca0 m0) 0 (cz0 m0)) := by
        set A := ca0 m0; set B := cb0 n0; set za := cz0 m0; set zb := dz0 n0
        set ay := a yc; set by' := b yc; set zy := yc 2
        ext j; fin_cases j <;> simp [oblPt] <;> field_simp
        · linear_combination (r1 0) * heq
        · linear_combination (r1 1) * heq
        · linear_combination hD
      rw [eA, eB]; conv_lhs => rw [hy yc hycV]
      exact key
  refine isRupert_vertex_frame_chord O r1 r2 hρ (fun x z => (x, z) ∈ S1) (fun x z => (x, z) ∈ S2)
    (z0 := v 2) ⟨m0, ca0, cz0, U1⟩ (chains1 (-1) (Or.inr rfl)) ⟨n0, cb0, dz0, U2⟩
    (chains2 (-1) (Or.inr rfl)) ?_ ?_ ?_ ?_ ac bc zc hac hbc ?_ V ?_ ?_ ?_ ?_ ?_
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
  · intro s1 s2 m ca cz n cb dz C1 C2
    obtain ⟨ea, ez⟩ := C1.far_eq U1
    obtain ⟨eb, ez2⟩ := C2.far_eq U2
    rw [ea, ez, eb, ez2]; exact ⟨hch1, hch2⟩
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
    by_cases hyy : y = yc
    · rcases hspec with hst | ⟨e1, e2, e3⟩
      · refine Or.inr (Or.inr (Or.inl ⟨ha2' y hy' h2, hb1' y hy' h1, ?_⟩))
        intro m ca cz n cb dz C1 C2
        obtain ⟨ea, -⟩ := C1.far_eq U1
        obtain ⟨eb, -⟩ := C2.far_eq U2
        rw [ea, eb, hyy]; exact hst
      · exact Or.inr (Or.inr (Or.inr ⟨by rw [hyy, e1], by rw [hyy, e2], by rw [hyy, e3]⟩))
    refine Or.inr (Or.inr (Or.inl ⟨ha2' y hy' h2, hb1' y hy' h1, ?_⟩))
    intro m ca cz n cb dz C1 C2
    have hA := C1.far_pos
    have hB := C2.far_pos
    have le1 : a xa ≤ ca m := by
      by_cases e : a xa = ca m ∧ xa 2 = cz m
      · exact e.1.le
      · exact (C1.far _ _ (Finset.mem_image_of_mem _ hxa) e).le
    have le2 : b xb ≤ cb n := by
      by_cases e : b xb = cb n ∧ xb 2 = dz n
      · exact e.1.le
      · exact (C2.far _ _ (Finset.mem_image_of_mem (fun p => (b p, p 2)) hxb) e).le
    have k := hin' y hy' h1 h2 hyy
    have ha := ha2' y hy' h2
    have hb := hb1' y hy' h1
    have t1 : a y / ca m ≤ a y / a xa := div_le_div_of_nonneg_left ha.le hxa0 le1
    have t2 : b y / cb n ≤ b y / b xb := div_le_div_of_nonneg_left hb.le hxb0 le2
    have : a y / ca m + b y / cb n < 1 := by linarith
    rw [div_add_div _ _ hA.ne' hB.ne', div_lt_one (mul_pos hA hB)] at this
    linarith
  · intro p hp q hq h
    simp only [inner_ez] at h
    exact hZ hp hq h
  · intro m ca cz n cb dz C1 C2 h
    obtain ⟨p, hp, e1, e2⟩ := ofS1 _ _ (C1.mem m le_rfl)
    obtain ⟨q, hq, f1, f2⟩ := ofS2 _ _ (C2.mem n le_rfl)
    have hpq : p ≠ q := by
      intro e; subst e
      have := only p hp hq; subst this
      linarith [C1.far_pos]
    exact hpq (hZ (h1V hp) (h2V hq) (by simp only; rw [e2, f2, h]))


end Minimality

end
