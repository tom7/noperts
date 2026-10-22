module

public import Minimality.TriFacetsEdge
public import Minimality.TriFacesChord

@[expose] public section

/-!
# Lemma T′ over an edge

The edge analogue of `TriFacetsChord.lean`: two facets `Q1`, `Q2` sharing the
edge `v w`, viewed along it, with one point `yc` off both facets allowed on the
far side of the shadow triangle (barycentric value `≤ 1`; every other off point
`< 1`). From the frame lemma `isRupert_edge_frame_chord`.

This is the reading of Lemma T′ at a corner of the shadow triangle that carries
a vertical edge (`FEWER-FACES-PROOFS.md` §23, Theorem 23.18): at the special
value of types 05, 10, 13, 17, 19, 23, 27, the forced edge parallel to the view
line is the apex of such a reading (`Type*.lean`).
-/

namespace Minimality

open Finset Filter Topology
open scoped RealInnerProductSpace

set_option maxHeartbeats 8000000 in
/-- **Lemma T′ over an edge, in frame coordinates.** As `isRupert_edge_coords`,
with one point `yc` off both faces allowed on the far side. -/
theorem isRupert_edge_coords_chord (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (V Q1 Q2 : Finset ℝ³)
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
    (xa xb : ℝ³) (hxa : xa ∈ Q1) (hxb : xb ∈ Q2) (hxa2 : xa ∉ Q2) (hxb1 : xb ∉ Q1)
    (yc : ℝ³) (hycV : yc ∈ V) (hyc1 : yc ∉ Q1) (hyc2 : yc ∉ Q2)
    (hin : ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → y ≠ yc → a y / a xa + b y / b xb < 1)
    (hyc : a yc / a xa + b yc / b xb ≤ 1) : IsRupert V := by
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
  -- the far ends, from the upper chains
  obtain ⟨m0, ca0, cz0, U1⟩ := chains1 1 w v (Or.inl rfl) (Or.inr ⟨rfl, rfl⟩) up
  obtain ⟨n0, cb0, dz0, U2⟩ := chains2 1 w v (Or.inl rfl) (Or.inr ⟨rfl, rfl⟩) up
  have hA := U1.far_pos
  have hB := U2.far_pos
  have hxa0 := ha2' xa (h1V hxa) hxa2
  have hxb0 := hb1' xb (h2V hxb) hxb1
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
    · have hle : a yc * cb0 n0 + b yc * ca0 m0 ≤ ca0 m0 * cb0 n0 := by
        have t1 : a yc / ca0 m0 ≤ a yc / a xa := div_le_div_of_nonneg_left hay.le hxa0 le1
        have t2 : b yc / cb0 n0 ≤ b yc / b xb := div_le_div_of_nonneg_left hby.le hxb0 le2
        have : a yc / ca0 m0 + b yc / cb0 n0 ≤ 1 := by linarith
        rw [div_add_div _ _ hA.ne' hB.ne', div_le_one (mul_pos hA hB)] at this
        linarith
      have heq : a yc * cb0 n0 + b yc * ca0 m0 = ca0 m0 * cb0 n0 := by linarith
      refine ⟨a yc, b yc, yc 2, hay, hby, by linarith, ?_, Or.inr ⟨rfl, rfl, rfl⟩⟩
      intro hD
      -- then `yc` lies on the segment of the far points
      have hpA2 : pA ∉ Q2 := fun h => by rw [ha2 pA h] at epA1; linarith
      have hpAB : pA ≠ pB := fun h => hpA2 (h ▸ hpB)
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
  refine isRupert_edge_frame_chord O r1 r2 hρ (fun x z => (x, z) ∈ S1) (fun x z => (x, z) ∈ S2)
    (zx := v 2) (zx' := w 2) hvw ⟨m0, ca0, cz0, U1⟩
    (chains1 (-1) v w (Or.inr rfl) (Or.inl ⟨rfl, rfl⟩) lo) ⟨n0, cb0, dz0, U2⟩
    (chains2 (-1) v w (Or.inr rfl) (Or.inl ⟨rfl, rfl⟩) lo) ?_ ?_
    (Finset.mem_image.mpr ⟨v, hv1, by rw [hav]⟩) (Finset.mem_image.mpr ⟨w, hw1, by rw [haw]⟩)
    (Finset.mem_image.mpr ⟨v, hv2, by rw [hbv]⟩) (Finset.mem_image.mpr ⟨w, hw2, by rw [hbw]⟩)
    ?_ ?_ ac bc zc hac hbc ?_ V ?_ ?_ ?_ ?_
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
  · intro z1 z2 s1 s2 m ca cz n cb dz C1 C2
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
    have k := hin y hy' h1 h2 hyy
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
/-- **Lemma T′ over an edge, the edge vertical**, with `v` below `w`. -/
theorem isRupert_facets_edge_vertical_lt_chord (V Q1 Q2 : Finset ℝ³) (v w : ℝ³) (hvw : v 2 < w 2)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v, w}) (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ)
    (z1 : ∀ p ∈ Q1, f1 p = 0) (n1 : ∀ p ∈ V, p ∉ Q1 → f1 p < 0)
    (z2 : ∀ p ∈ Q2, f2 p = 0) (n2 : ∀ p ∈ V, p ∉ Q2 → f2 p < 0)
    (e1 : f1 (v + ez) = 0) (e2 : f2 (v + ez) = 0)
    (hne1 : ∃ p ∈ Q1, p ∉ Q2) (hne2 : ∃ p ∈ Q2, p ∉ Q1)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hpar : ∀ p ∈ V, ∀ q ∈ V, p ≠ q → ({p, q} : Finset ℝ³) ≠ {v, w} → p 0 ≠ q 0 ∨ p 1 ≠ q 1)
    (hfarZ : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
      p 2 ≠ q 2)
    (xa xb : ℝ³) (hxa : xa ∈ Q1) (hxb : xb ∈ Q2) (hxa2 : xa ∉ Q2) (hxb1 : xb ∉ Q1)
    (yc : ℝ³) (hycV : yc ∈ V) (hyc1 : yc ∉ Q1) (hyc2 : yc ∉ Q2)
    (hin : ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → y ≠ yc → f2 y / f2 xa + f1 y / f1 xb < 1)
    (hyc : f2 yc / f2 xa + f1 yc / f1 xb ≤ 1) : IsRupert V := by
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
  have conv : ∀ y, f2 y / f2 xa + f1 y / f1 xb = a y / a xa + b y / b xb := fun y => by
    rw [G1 y, G1 xb, G2 y, G2 xa, mul_div_mul_right _ _ m21.ne, mul_div_mul_right _ _ m12.ne]
  rcases lt_or_gt_of_ne hρ with hneg | hpos
  · have hpos' : 0 < cross2 r2 r1 := by
      have : cross2 r2 r1 = -cross2 r1 r2 := by unfold cross2; ring
      rw [this]; linarith
    have swap : ∀ p q z, oblPt O r2 r1 q p z = oblPt O r1 r2 p q z := by
      intro p q z; ext j; fin_cases j <;> simp [oblPt] <;> ring
    refine isRupert_edge_coords_chord O r2 r1 hpos' V Q2 Q1 v w hvw b a
      (fun p _ => by rw [swap]; exact hy p) h2V h1V (by rw [Finset.inter_comm]; exact hint)
      ha2 ha2' hb1 hb1' ⟨p2, hp2, hp21⟩ ⟨p1, hp1, hp12⟩ hcol ?_ ?_
      (fun p hp q hq hpq h1 h2 => (hfar' q hq p hp (Ne.symm hpq) h2 h1).symm) xb xa hxb hxa hxb1 hxa2
      yc hycV hyc2 hyc1 (fun y hy h2 h1 hne => by rw [add_comm, ← conv]; exact hin y hy h1 h2 hne)
      (by rw [add_comm, ← conv]; exact hyc)
    · intro p hp q hq e
      simp only [Prod.mk.injEq] at e
      exact hinjv hp hq (by simp only [Prod.mk.injEq]; exact ⟨e.2, e.1⟩)
    · intro p hp q hq e
      simp only [Prod.mk.injEq] at e
      exact hinjw hp hq (by simp only [Prod.mk.injEq]; exact ⟨e.2, e.1⟩)
  · exact isRupert_edge_coords_chord O r1 r2 hpos V Q1 Q2 v w hvw a b (fun p _ => hy p) h1V h2V hint
      hb1 hb1' ha2 ha2' ⟨p1, hp1, hp12⟩ ⟨p2, hp2, hp21⟩ hcol hinjv hinjw hfar' xa xb hxa hxb hxa2 hxb1
      yc hycV hyc1 hyc2 (fun y hy h1 h2 hne => by rw [← conv]; exact hin y hy h1 h2 hne)
      (by rw [← conv]; exact hyc)

/-- **Lemma T′ over an edge, the edge vertical.** -/
theorem isRupert_facets_edge_vertical_chord (V Q1 Q2 : Finset ℝ³) (v w : ℝ³) (_hvw : v ≠ w)
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
    (xa xb : ℝ³) (hxa : xa ∈ Q1) (hxb : xb ∈ Q2) (hxa2 : xa ∉ Q2) (hxb1 : xb ∉ Q1)
    (yc : ℝ³) (hycV : yc ∈ V) (hyc1 : yc ∉ Q1) (hyc2 : yc ∉ Q2)
    (hin : ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → y ≠ yc → f2 y / f2 xa + f1 y / f1 xb < 1)
    (hyc : f2 yc / f2 xa + f1 yc / f1 xb ≤ 1) : IsRupert V := by
  have hvi : v ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hwi : w ∈ Q1 ∩ Q2 := by rw [hint]; simp
  rcases lt_or_gt_of_ne hvw2 with hlt | hgt
  · exact isRupert_facets_edge_vertical_lt_chord V Q1 Q2 v w hlt h1V h2V hint f1 f2 z1 n1 z2 n2
      e1 e2 hne1 hne2 hcol hpar hfarZ xa xb hxa hxb hxa2 hxb1 yc hycV hyc1 hyc2 hin hyc
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
    refine isRupert_facets_edge_vertical_lt_chord V Q1 Q2 w v hgt h1V h2V
      (by rw [Finset.pair_comm]; exact hint) f1 f2 z1 n1 z2 n2
      (hw f1 (z1 v hv1) e1 (z1 w hw1)) (hw f2 (z2 v hv2) e2 (z2 w hw2)) hne1 hne2 hcol
      (fun p hp q hq hpq h => hpar p hp q hq hpq (by rw [Finset.pair_comm v w]; exact h)) hfarZ
      xa xb hxa hxb hxa2 hxb1 yc hycV hyc1 hyc2 hin hyc


set_option maxHeartbeats 4000000 in
/-- **Lemma T′ over an edge** for two facets `Q1`, `Q2` (functionals `f1`,
`f2`) sharing the edge `v w`, viewed along it: as `isRupert_facets_edge`, except
that one point `yc` off both facets may lie on the far side `xa xb` of the
shadow triangle. -/
theorem isRupert_facets_edge_chord (V Q1 Q2 : Finset ℝ³) (v w : ℝ³) (hvw : v ≠ w)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v, w}) (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ)
    (z1 : ∀ p ∈ Q1, f1 p = 0) (n1 : ∀ p ∈ V, p ∉ Q1 → f1 p < 0)
    (z2 : ∀ p ∈ Q2, f2 p = 0) (n2 : ∀ p ∈ V, p ∉ Q2 → f2 p < 0)
    (hne1 : ∃ p ∈ Q1, p ∉ Q2) (hne2 : ∃ p ∈ Q2, p ∉ Q1)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hpar : ∀ p ∈ V, ∀ q ∈ V, p ≠ q → ({p, q} : Finset ℝ³) ≠ {v, w} → ∀ c : ℝ, q - p ≠ c • (w - v))
    (hfarZ : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
      ⟪p, w - v⟫ ≠ ⟪q, w - v⟫)
    (xa xb : ℝ³) (hxa : xa ∈ Q1) (hxb : xb ∈ Q2) (hxa2 : xa ∉ Q2) (hxb1 : xb ∉ Q1)
    (yc : ℝ³) (hycV : yc ∈ V) (hyc1 : yc ∉ Q1) (hyc2 : yc ∉ Q2)
    (hin : ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → y ≠ yc → f2 y / f2 xa + f1 y / f1 xb < 1)
    (hyc : f2 yc / f2 xa + f1 yc / f1 xb ≤ 1) : IsRupert V := by
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
  refine isRupert_facets_edge_vertical_chord (V.image g) (Q1.image g) (Q2.image g) (g v) (g w)
    (fun h => hvw (hginj h))
    (Finset.image_subset_image h1V) (Finset.image_subset_image h2V)
    (by rw [← Finset.image_inter _ _ hginj, hint, Finset.image_insert, Finset.image_singleton]) F1 F2
    (allg Q1 _ (fun p hp => by rw [tF1]; exact z1 p hp))
    (allg V _ (fun p hp hq => by rw [tF1]; exact n1 p hp (fun h => hq ((memg Q1 p).mpr h))))
    (allg Q2 _ (fun p hp => by rw [tF2]; exact z2 p hp))
    (allg V _ (fun p hp hq => by rw [tF2]; exact n2 p hp (fun h => hq ((memg Q2 p).mpr h))))
    (tz f1 (z1 v hv1) (z1 w hw1)) (tz f2 (z2 v hv2) (z2 w hw2)) ?_ ?_ ?_ ?_ ?_ ?_ (g xa) (g xb)
    (Finset.mem_image_of_mem g hxa) (Finset.mem_image_of_mem g hxb)
    (fun e => hxa2 ((memg Q2 xa).mp e)) (fun e => hxb1 ((memg Q1 xb).mp e)) (g yc)
    (Finset.mem_image_of_mem g hycV) (fun h => hyc1 ((memg Q1 yc).mp h))
    (fun h => hyc2 ((memg Q2 yc).mp h)) ?_ (by rw [tF1, tF1, tF2, tF2]; exact hyc)
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
  · refine allg V _ (fun y hy hy1 hy2 hne => ?_)
    rw [tF1, tF1, tF2, tF2]
    exact hin y hy (fun h => hy1 ((memg Q1 y).mpr h)) (fun h => hy2 ((memg Q2 y).mpr h))
      (fun e => hne (by rw [e]))

set_option maxHeartbeats 4000000 in
/-- **Lemma T′ over an edge, facet form** (`FEWER-FACES-PROOFS.md`, Lemma T′
with an edge apex, §23): as `isRupert_of_facets_edge`, except that one point
`yc` off both facets may lie on the far side `xa xb` of the shadow triangle
(barycentric value `≤ 1`); every other such point is strictly inside. -/
theorem isRupert_of_facets_edge_chord (V : Finset ℝ³) (hgen : NoThreeCollinear V)
    (Q1 Q2 : Finset ℝ³) (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (h1f : IsFacet V Q1) (h2f : IsFacet V Q2)
    (v w : ℝ³) (hvw : v ≠ w) (hint : Q1 ∩ Q2 = {v, w})
    (hfarZ : EdgeFar V Q1 Q2 v w)
    (xa xb : ℝ³) (hxa : xa ∈ Q1) (hxb : xb ∈ Q2) (hxa2 : xa ∉ Q2) (hxb1 : xb ∉ Q1)
    (yc : ℝ³) (hycV : yc ∈ V) (hyc1 : yc ∉ Q1) (hyc2 : yc ∉ Q2)
    (hin : ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ,
      (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
      (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
      (∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → y ≠ yc → f2 y / f2 xa + f1 y / f1 xb < 1) ∧
      f2 yc / f2 xa + f1 yc / f1 xb ≤ 1) : IsRupert V := by
  obtain ⟨f1, z1, n1⟩ := h1f
  obtain ⟨f2, z2, n2⟩ := h2f
  obtain ⟨hin', hyc⟩ := hin f1 f2 z1 n1 z2 n2
  exact isRupert_facets_edge_chord V Q1 Q2 v w hvw h1V h2V hint f1 f2 z1 n1 z2 n2
    ⟨xa, hxa, hxa2⟩ ⟨xb, hxb, hxb1⟩ hgen hfarZ.1 (hfarZ.2 f1 f2 z1 n1 z2 n2)
    xa xb hxa hxb hxa2 hxb1 yc hycV hyc1 hyc2 hin' hyc

end Minimality

end
