module

public import Minimality.SpecialFrame
public import Minimality.ParallelEdge

@[expose] public section

/-!
# The special value of Lemma T′ (`FEWER-FACES-PROOFS.md` Theorem 23.18, 24.13)

At the special value of the types 05, 10, 13, 17, 19, 23, 27 three faces are edge-on in
one view: `Q1`, `Q2` share the edge `v w`, which is parallel to the view, and the third
face `G` is a triangle `xa xb g` over the far side, with `xa ∈ Q1`, `xb ∈ Q2` and `g` on
the far side of the shadow triangle. Each corner gives a reading of Lemma T′:

- the corner of `v w` (Lemma T′ over the edge, `EdgeChord.lean`), which works unless the
  far ends `xa`, `xb` tie;
- the corners `xa`, `xb` (Lemma T′ at a vertex with the vertical edge `v w` over a far
  corner, the Extension of §7 as corrected in §23), whose mixed sectors are
  `isRupert_vertex_coords_parc` (one end of `v w` hidden);
- at a tie of the far ends, Lemma T′ over the edge still works when `xa` is the strict top
  or bottom of `Q1` (`isRupert_edge_coords_mode_chord`).

`isRupert_special_coords` combines them: if every face has at most one vertex besides
its corners, `K` is Rupert unless the far ends tie with an end of `v w` (the triple tie).
So two ties that are not a triple are allowed (24.13), and any single tie (23.18).
-/

namespace Minimality

open Finset Filter Topology
open scoped RealInnerProductSpace

theorem cross2_R2 (r1 r2 : ℝ²) : cross2 (r2 - r1) (-r1) = cross2 r1 r2 := by
  unfold cross2; simp; ring

theorem cross2_R3 (r1 r2 : ℝ²) : cross2 (-r2) (r1 - r2) = cross2 r1 r2 := by
  unfold cross2; simp; ring

/-- The oblique frame at the corner `O + r1`, rays toward `O + r2` and `O`. -/
theorem oblPt_R2 (O r1 r2 : ℝ²) (a b z : ℝ) :
    oblPt (O + r1) (r2 - r1) (-r1) b (1 - a - b) z = oblPt O r1 r2 a b z := by
  ext j; fin_cases j <;> simp [oblPt] <;> ring

/-- The oblique frame at the corner `O + r2`, rays toward `O` and `O + r1`. -/
theorem oblPt_R3 (O r1 r2 : ℝ²) (a b z : ℝ) :
    oblPt (O + r2) (-r2) (r1 - r2) (1 - a - b) a z = oblPt O r1 r2 a b z := by
  ext j; fin_cases j <;> simp [oblPt] <;> ring

/-- Three points with collinear frame coordinates are collinear. -/
theorem oblPt_sub_smul (O r1 r2 : ℝ²) {a1 b1 z1 a2 b2 z2 a3 b3 z3 t : ℝ}
    (ha : a3 - a1 = t * (a2 - a1)) (hb : b3 - b1 = t * (b2 - b1)) (hz : z3 - z1 = t * (z2 - z1)) :
    oblPt O r1 r2 a3 b3 z3 - oblPt O r1 r2 a1 b1 z1 =
      t • (oblPt O r1 r2 a2 b2 z2 - oblPt O r1 r2 a1 b1 z1) := by
  ext j; fin_cases j <;> simp [oblPt]
  · linear_combination (r1 0) * ha + (r2 0) * hb
  · linear_combination (r1 1) * ha + (r2 1) * hb
  · linear_combination hz

set_option maxHeartbeats 16000000 in
/-- **The special value of Lemma T′ in frame coordinates** (Theorems 23.18 and 24.13). In
the oblique frame of the edge view (`isRupert_edge_coords_chord`, normalized so that the
far ends are `xa = (1, 0)`, `xb = (0, 1)`), the third face `G = {xa, xb, g}` lies on the
far side `a + b = 1` and every other point strictly inside; `Q1`, `Q2` have at most one
vertex besides `v`, `w` and their far end. Then `V` is Rupert unless `xa`, `xb` and an
end of the edge are at one depth. -/
theorem isRupert_special_coords (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (V Q1 Q2 G : Finset ℝ³)
    (v w : ℝ³) (hvw : v 2 < w 2) (a b : ℝ³ → ℝ)
    (hy : ∀ p ∈ V, p = oblPt O r1 r2 (a p) (b p) (p 2))
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hGV : G ⊆ V) (hint : Q1 ∩ Q2 = {v, w})
    (hb1 : ∀ p ∈ Q1, b p = 0) (hb1' : ∀ p ∈ V, p ∉ Q1 → 0 < b p)
    (ha2 : ∀ p ∈ Q2, a p = 0) (ha2' : ∀ p ∈ V, p ∉ Q2 → 0 < a p)
    (hG1 : ∀ p ∈ G, a p + b p = 1) (hG1' : ∀ p ∈ V, p ∉ G → a p + b p < 1)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hinjv : Set.InjOn (fun p => (a p, b p)) ((V.erase v : Finset ℝ³) : Set ℝ³))
    (hinjw : Set.InjOn (fun p => (a p, b p)) ((V.erase w : Finset ℝ³) : Set ℝ³))
    (xa xb g m1 m2 : ℝ³) (hxa : xa ∈ Q1) (hxb : xb ∈ Q2) (hxaG : xa ∈ G) (hxbG : xb ∈ G)
    (hgG : g ∈ G) (hxa2 : xa ∉ Q2) (hxb1 : xb ∉ Q1) (hg1 : g ∉ Q1) (hg2 : g ∉ Q2)
    (hGm : ∀ p ∈ G, p = xa ∨ p = xb ∨ p = g)
    (hQ1m : ∀ p ∈ Q1, p = v ∨ p = w ∨ p = xa ∨ p = m1)
    (hQ2m : ∀ p ∈ Q2, p = v ∨ p = w ∨ p = xb ∨ p = m2)
    (htri : ¬ (xa 2 = xb 2 ∧ (v 2 = xa 2 ∨ w 2 = xa 2))) : IsRupert V := by
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
  have hgV := hGV hgG
  have hxaV := h1V hxa
  have hxbV := h2V hxb
  have hAx : a xa = 1 := by have := hG1 xa hxaG; rw [hb1 xa hxa] at this; linarith
  have hBx : b xb = 1 := by have := hG1 xb hxbG; rw [ha2 xb hxb] at this; linarith
  have hbxa := hb1 xa hxa
  have haxb := ha2 xb hxb
  have ha0 : ∀ p ∈ V, 0 ≤ a p := fun p hp => by
    by_cases h : p ∈ Q2
    · rw [ha2 p h]
    · exact (ha2' p hp h).le
  have hb0 : ∀ p ∈ V, 0 ≤ b p := fun p hp => by
    by_cases h : p ∈ Q1
    · rw [hb1 p h]
    · exact (hb1' p hp h).le
  have hGQ1 : G ∩ Q1 = {xa} := by
    ext p; simp only [Finset.mem_inter, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      rcases hGm p h1 with rfl | rfl | rfl
      · rfl
      · exact absurd h2 hxb1
      · exact absurd h2 hg1
    · rintro rfl; exact ⟨hxaG, hxa⟩
  have hQ2G : Q2 ∩ G = {xb} := by
    ext p; simp only [Finset.mem_inter, Finset.mem_singleton]
    constructor
    · rintro ⟨h2, h1⟩
      rcases hGm p h1 with rfl | rfl | rfl
      · exact absurd h2 hxa2
      · rfl
      · exact absurd h2 hg2
    · rintro rfl; exact ⟨hxb, hxbG⟩
  have hxaxb : xa ≠ xb := fun e => hxb1 (e ▸ hxa)
  have hvxa : v ≠ xa := fun e => hxa2 (e ▸ hv2)
  have hwxa : w ≠ xa := fun e => hxa2 (e ▸ hw2)
  have hvxb : v ≠ xb := fun e => hxb1 (e ▸ hv1)
  have hwxb : w ≠ xb := fun e => hxb1 (e ▸ hw1)
  -- the far side is not on the line of the far ends
  have hgline : g 2 - xa 2 - b g * (xb 2 - xa 2) ≠ 0 := by
    intro h
    have hag : a g = 1 - b g := by have := hG1 g hgG; linarith
    apply hcol xa hxaV xb hxbV g hgV hxaxb (fun e => hg1 (e ▸ hxa)) (fun e => hg2 (e ▸ hxb)) (b g)
    have key := oblPt_sub_smul O r1 r2 (a1 := a xa) (b1 := b xa) (z1 := xa 2) (a2 := a xb)
      (b2 := b xb) (z2 := xb 2) (a3 := a g) (b3 := b g) (z3 := g 2) (t := b g)
      (by rw [hag, hAx, haxb]; ring) (by rw [hbxa, hBx]; ring) (by linarith)
    rw [← hy g hgV, ← hy xa hxaV, ← hy xb hxbV] at key
    exact key
  -- the reading at the edge (`isRupert_edge_coords_mode_chord`), for a sign `s` and a mode
  have edgeR : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      (s * xb 2 < s * xa 2 ∨ ∀ p ∈ Q1, p ≠ xa → s * p 2 < s * xa 2) → IsRupert V := by
    intro s hs hmode
    set D := g 2 - xa 2 - b g * (xb 2 - xa 2) with hD
    obtain ⟨σ, hσ, hσD⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ 0 < σ * s * D := by
      have hsD : s * D ≠ 0 := mul_ne_zero (by rcases hs with rfl | rfl <;> norm_num) hgline
      rcases lt_or_gt_of_ne hsD with h | h
      · exact ⟨-1, Or.inr rfl, by nlinarith⟩
      · exact ⟨1, Or.inl rfl, by nlinarith⟩
    refine isRupert_edge_coords_mode_chord O r1 r2 hρ V Q1 Q2 v w hvw a b hy h1V h2V hint hb1 hb1'
      ha2 ha2' ⟨xa, hxa, hxa2⟩ ⟨xb, hxb, hxb1⟩ hcol hinjv hinjw xa xb hxa hxb hxa2 hxb1 ?_ ?_ s hs
      hmode σ hσ ?_
    · intro p hp
      rw [hAx]
      by_cases hpG : p ∈ G
      · rcases hGm p hpG with rfl | rfl | rfl
        · rw [hAx]
        · exact absurd hp hxb1
        · exact absurd hp hg1
      · have := hG1' p (h1V hp) hpG; rw [hb1 p hp] at this; linarith
    · intro q hq
      rw [hBx]
      by_cases hqG : q ∈ G
      · rcases hGm q hqG with rfl | rfl | rfl
        · exact absurd hq hxa2
        · rw [hBx]
        · exact absurd hq hg2
      · have := hG1' q (h2V hq) hqG; rw [ha2 q hq] at this; linarith
    · intro y hy' h1 h2
      rw [hAx, hBx, div_one, div_one]
      by_cases hyG : y ∈ G
      · rcases hGm y hyG with rfl | rfl | rfl
        · exact absurd hxa h1
        · exact absurd hxb h2
        · right; refine ⟨hG1 y hgG, ?_⟩
          rw [one_mul]; exact hσD
      · exact Or.inl (hG1' y hy' hyG)
  -- the far depths differ: the edge view
  by_cases hne : xa 2 = xb 2
  swap
  · rcases lt_or_gt_of_ne hne with h | h
    · exact edgeR (-1) (Or.inr rfl) (Or.inl (by linarith))
    · exact edgeR 1 (Or.inl rfl) (Or.inl (by linarith))
  set c := xa 2 with hc
  have hvc : v 2 ≠ c := fun h => htri ⟨hne, Or.inl h⟩
  have hwc : w 2 ≠ c := fun h => htri ⟨hne, Or.inr h⟩
  -- the reading at the corner `xa` (apex `xa`, faces `G` and `Q1`, `v w` over a far corner)
  have R2 : ∀ (s : ℝ) (u : ℝ³), (s = 1 ∧ u = v ∨ s = -1 ∧ u = w) → s * u 2 < s * c →
      (∀ y ∈ Q2, y ∉ Q1 → y ∉ G → 0 < s * ((y 2 - c) - (1 - b y) * (u 2 - c))) → IsRupert V := by
    intro s u hsu hAB hside
    have hs : s = 1 ∨ s = -1 := by rcases hsu with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
    have hu1 : u ∈ Q1 := by rcases hsu with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
    have hau : a u = 0 := by rcases hsu with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
    have hbu : b u = 0 := by rcases hsu with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
    refine isRupert_vertex_coords_parc (O + r1) (r2 - r1) (-r1) (by rw [cross2_R2]; exact hρ) V G Q1
      xa b (fun p => 1 - a p - b p) (fun p hp => by rw [oblPt_R2]; exact hy p hp) hGV h1V hGQ1
      (fun p hp => by have := hG1 p hp; show 1 - a p - b p = 0; linarith)
      (fun p hp hpG => by have := hG1' p hp hpG; show 0 < 1 - a p - b p; linarith) hb1 hb1'
      ⟨xb, hxbG, hxaxb.symm⟩ ⟨v, hv1, hvxa⟩ hcol s hs xb u hxbG hu1 ?_ ?_ ?_ ?_
      (by rw [← hne]; exact hAB) 1 (Or.inl rfl) ?_ (fun _ => rfl) ?_
    · intro p hp; rw [hBx]; have := hG1 p hp; linarith [ha0 p (hGV hp)]
    · intro q hq; show 1 - a q - b q ≤ 1 - a u - b u
      rw [hau, hbu]; linarith [ha0 q (h1V hq), hb1 q hq]
    · intro p hp hpb hpx
      exfalso; apply hpx
      have hap : a p = 0 := by have := hG1 p hp; rw [hpb, hBx] at this; linarith
      have hp2 : p ∈ Q2 := by
        by_contra h; linarith [ha2' p (hGV hp) h]
      have : p ∈ Q2 ∩ G := Finset.mem_inter.mpr ⟨hp2, hp⟩
      rw [hQ2G] at this; simpa using this
    · intro q hq hqb hqu
      have hqb' : 1 - a q - b q = 1 - a u - b u := hqb
      have haq : a q = 0 := by rw [hau, hbu, hb1 q hq] at hqb'; linarith
      have hq2 : q ∈ Q2 := by
        by_contra h; linarith [ha2' q (h1V hq) h]
      rcases mem12 q hq hq2 with rfl | rfl <;> rcases hsu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd rfl hqu
      · linarith
      · linarith
      · exact absurd rfl hqu
    · rintro ⟨p, hp, hpb, hpx⟩
      exfalso; apply hpx
      have hap : a p = 0 := by have := hG1 p hp; rw [hpb, hBx] at this; linarith
      have hp2 : p ∈ Q2 := by
        by_contra h; linarith [ha2' p (hGV hp) h]
      have : p ∈ Q2 ∩ G := Finset.mem_inter.mpr ⟨hp2, hp⟩
      rw [hQ2G] at this; simpa using this
    · intro y hy' hyG hy1
      have e1 : (1 - a u - b u) = 1 := by rw [hau, hbu]; ring
      show b y / b xb + (1 - a y - b y) / (1 - a u - b u) < 1 ∨
        (b y / b xb + (1 - a y - b y) / (1 - a u - b u) = 1 ∧
          0 < 1 * s * ((1 - a u - b u) * (y 2 - xb 2) - (1 - a y - b y) * (u 2 - xb 2)))
      rw [hBx, e1, div_one, div_one]
      by_cases hy2 : y ∈ Q2
      · right
        have hay := ha2 y hy2
        refine ⟨by rw [hay]; ring, ?_⟩
        have := hside y hy2 hy1 hyG
        rw [← hne, hay]
        have e : 1 * s * (1 * (y 2 - c) - (1 - 0 - b y) * (u 2 - c)) =
            s * ((y 2 - c) - (1 - b y) * (u 2 - c)) := by ring
        rw [e]; exact this
      · left; linarith [ha2' y hy' hy2]
  -- the reading at the corner `xb` (apex `xb`, faces `Q2` and `G`)
  have R3 : ∀ (s : ℝ) (u : ℝ³), (s = 1 ∧ u = w ∨ s = -1 ∧ u = v) → s * c < s * u 2 →
      (∀ y ∈ Q1, y ∉ Q2 → y ∉ G → s * ((y 2 - u 2) - a y * (c - u 2)) < 0) → IsRupert V := by
    intro s u hsu hAB hside
    have hs : s = 1 ∨ s = -1 := by rcases hsu with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
    have hu2 : u ∈ Q2 := by rcases hsu with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
    have hau : a u = 0 := by rcases hsu with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
    have hbu : b u = 0 := by rcases hsu with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
    refine isRupert_vertex_coords_parc (O + r2) (-r2) (r1 - r2) (by rw [cross2_R3]; exact hρ) V Q2 G
      xb (fun p => 1 - a p - b p) a (fun p hp => by rw [oblPt_R3]; exact hy p hp) h2V hGV hQ2G
      ha2 ha2' (fun p hp => by have := hG1 p hp; show 1 - a p - b p = 0; linarith)
      (fun p hp hpG => by have := hG1' p hp hpG; show 0 < 1 - a p - b p; linarith)
      ⟨v, hv2, hvxb⟩ ⟨xa, hxaG, hxaxb⟩ hcol s hs u xa hu2 hxaG ?_ ?_ ?_ ?_
      (by rw [hc] at hAB; exact hAB) (-1) (Or.inr rfl) (fun _ => rfl) ?_ ?_
    · intro q hq; show 1 - a q - b q ≤ 1 - a u - b u
      rw [hau, hbu]; linarith [hb0 q (h2V hq), ha2 q hq]
    · intro p hp; rw [hAx]; have := hG1 p hp; linarith [hb0 p (hGV hp)]
    · intro p hp hpa hpu
      have hpa' : 1 - a p - b p = 1 - a u - b u := hpa
      have hbp : b p = 0 := by rw [hau, hbu, ha2 p hp] at hpa'; linarith
      have hp1 : p ∈ Q1 := by
        by_contra h; linarith [hb1' p (h2V hp) h]
      rcases mem12 p hp1 hp with rfl | rfl <;> rcases hsu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · linarith
      · exact absurd rfl hpu
      · exact absurd rfl hpu
      · linarith
    · intro q hq hqa hqx
      exfalso; apply hqx
      have hbq : b q = 0 := by have := hG1 q hq; rw [hqa, hAx] at this; linarith
      have hq1 : q ∈ Q1 := by
        by_contra h; linarith [hb1' q (hGV hq) h]
      have : q ∈ G ∩ Q1 := Finset.mem_inter.mpr ⟨hq, hq1⟩
      rw [hGQ1] at this; simpa using this
    · rintro ⟨q, hq, hqa, hqx⟩
      exfalso; apply hqx
      have hbq : b q = 0 := by have := hG1 q hq; rw [hqa, hAx] at this; linarith
      have hq1 : q ∈ Q1 := by
        by_contra h; linarith [hb1' q (hGV hq) h]
      have : q ∈ G ∩ Q1 := Finset.mem_inter.mpr ⟨hq, hq1⟩
      rw [hGQ1] at this; simpa using this
    · intro y hy' hy2 hyG
      have e1 : (1 - a u - b u) = 1 := by rw [hau, hbu]; ring
      show (1 - a y - b y) / (1 - a u - b u) + a y / a xa < 1 ∨
        ((1 - a y - b y) / (1 - a u - b u) + a y / a xa = 1 ∧
          0 < -1 * s * (a xa * (y 2 - u 2) - a y * (xa 2 - u 2)))
      rw [hAx, e1, div_one, div_one]
      by_cases hy1 : y ∈ Q1
      · right
        have hby := hb1 y hy1
        refine ⟨by rw [hby]; ring, ?_⟩
        have := hside y hy1 hy2 hyG
        rw [← hc]
        have e : -1 * s * (1 * (y 2 - u 2) - a y * (c - u 2)) =
            -(s * ((y 2 - u 2) - a y * (c - u 2))) := by ring
        rw [e]; linarith
      · left; linarith [hb1' y hy' hy1]
  -- the middles of `Q1`, `Q2`: at most one each
  have mid1 : ∀ y ∈ Q1, y ∉ Q2 → y ∉ G → y = m1 := by
    intro y hy h2 hG
    rcases hQ1m y hy with rfl | rfl | rfl | rfl
    · exact absurd hv2 h2
    · exact absurd hw2 h2
    · exact absurd hxaG hG
    · rfl
  have mid2 : ∀ y ∈ Q2, y ∉ Q1 → y ∉ G → y = m2 := by
    intro y hy h1 hG
    rcases hQ2m y hy with rfl | rfl | rfl | rfl
    · exact absurd hv1 h1
    · exact absurd hw1 h1
    · exact absurd hxbG hG
    · rfl
  have ab1 : ∀ y ∈ Q1, y ∉ Q2 → y ∉ G → 0 < a y ∧ a y < 1 := by
    intro y hy h2 hG
    refine ⟨ha2' y (h1V hy) h2, ?_⟩
    have := hG1' y (h1V hy) hG; rw [hb1 y hy] at this; linarith
  have ab2 : ∀ y ∈ Q2, y ∉ Q1 → y ∉ G → 0 < b y ∧ b y < 1 := by
    intro y hy h1 hG
    refine ⟨hb1' y (h2V hy) h1, ?_⟩
    have := hG1' y (h2V hy) hG; rw [ha2 y hy] at this; linarith
  rcases lt_or_gt_of_ne hvc with hvlt | hvgt
  · rcases lt_or_gt_of_ne hwc with hwlt | hwgt
    · -- both ends of the edge below the far ends
      by_cases hA : ∀ y ∈ Q2, y ∉ Q1 → y ∉ G → 0 < 1 * ((y 2 - c) - (1 - b y) * (v 2 - c))
      · exact R2 1 v (Or.inl ⟨rfl, rfl⟩) (by linarith) hA
      by_cases hB : ∀ y ∈ Q1, y ∉ Q2 → y ∉ G → -1 * ((y 2 - v 2) - a y * (c - v 2)) < 0
      · exact R3 (-1) v (Or.inr ⟨rfl, rfl⟩) (by linarith) hB
      push Not at hB
      obtain ⟨y1, hy1, hy12, hy1G, hy1s⟩ := hB
      -- `xa` is the strict top of `Q1`
      refine edgeR 1 (Or.inl rfl) (Or.inr fun p hp hpx => ?_)
      rcases hQ1m p hp with rfl | rfl | rfl | rfl
      · linarith
      · linarith
      · exact absurd rfl hpx
      · have e := mid1 y1 hy1 hy12 hy1G
        subst e
        have := ab1 y1 hy1 hy12 hy1G
        nlinarith
    · -- `v` below, `w` above the far ends
      by_cases hA : ∀ y ∈ Q2, y ∉ Q1 → y ∉ G → 0 < -1 * ((y 2 - c) - (1 - b y) * (w 2 - c))
      · exact R2 (-1) w (Or.inr ⟨rfl, rfl⟩) (by linarith) hA
      push Not at hA
      obtain ⟨y2, hy2, hy21, hy2G, hy2s⟩ := hA
      refine R2 1 v (Or.inl ⟨rfl, rfl⟩) (by linarith) fun y hy h1 hG => ?_
      have e1 := mid2 y hy h1 hG
      have e2 := mid2 y2 hy2 hy21 hy2G
      rw [e1, ← e2]
      have := ab2 y2 hy2 hy21 hy2G
      nlinarith
  · -- both ends of the edge above the far ends
    have hwgt : c < w 2 := by linarith
    by_cases hA : ∀ y ∈ Q2, y ∉ Q1 → y ∉ G → 0 < -1 * ((y 2 - c) - (1 - b y) * (w 2 - c))
    · exact R2 (-1) w (Or.inr ⟨rfl, rfl⟩) (by linarith) hA
    by_cases hB : ∀ y ∈ Q1, y ∉ Q2 → y ∉ G → 1 * ((y 2 - w 2) - a y * (c - w 2)) < 0
    · exact R3 1 w (Or.inl ⟨rfl, rfl⟩) (by linarith) hB
    push Not at hB
    obtain ⟨y1, hy1, hy12, hy1G, hy1s⟩ := hB
    -- `xa` is the strict bottom of `Q1`
    refine edgeR (-1) (Or.inr rfl) (Or.inr fun p hp hpx => ?_)
    rcases hQ1m p hp with rfl | rfl | rfl | rfl
    · linarith
    · linarith
    · exact absurd rfl hpx
    · have e := mid1 y1 hy1 hy12 hy1G
      subst e
      have := ab1 y1 hy1 hy12 hy1G
      nlinarith

set_option maxHeartbeats 8000000 in
/-- **The special value, the edge vertical**, with `v` below `w`: the faces `Q1`, `Q2`
(functionals `f1`, `f2`) contain the vertical line through `v`, and the plane of the third
face `G` is parallel to the edge `v w` (`fG w = fG v`). -/
theorem isRupert_special_vertical_lt (V Q1 Q2 G : Finset ℝ³) (v w : ℝ³) (hvw : v 2 < w 2)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hGV : G ⊆ V) (hint : Q1 ∩ Q2 = {v, w})
    (f1 f2 fG : ℝ³ →ᵃ[ℝ] ℝ)
    (z1 : ∀ p ∈ Q1, f1 p = 0) (n1 : ∀ p ∈ V, p ∉ Q1 → f1 p < 0)
    (z2 : ∀ p ∈ Q2, f2 p = 0) (n2 : ∀ p ∈ V, p ∉ Q2 → f2 p < 0)
    (zG : ∀ p ∈ G, fG p = 0) (nG : ∀ p ∈ V, p ∉ G → fG p < 0)
    (e1 : f1 (v + ez) = 0) (e2 : f2 (v + ez) = 0) (hspec : fG w = fG v)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hpar : ∀ p ∈ V, ∀ q ∈ V, p ≠ q → ({p, q} : Finset ℝ³) ≠ {v, w} → p 0 ≠ q 0 ∨ p 1 ≠ q 1)
    (xa xb g m1 m2 : ℝ³) (hxa : xa ∈ Q1) (hxb : xb ∈ Q2) (hxaG : xa ∈ G) (hxbG : xb ∈ G)
    (hgG : g ∈ G) (hxa2 : xa ∉ Q2) (hxb1 : xb ∉ Q1) (hg1 : g ∉ Q1) (hg2 : g ∉ Q2)
    (hGm : ∀ p ∈ G, p = xa ∨ p = xb ∨ p = g)
    (hQ1m : ∀ p ∈ Q1, p = v ∨ p = w ∨ p = xa ∨ p = m1)
    (hQ2m : ∀ p ∈ Q2, p = v ∨ p = w ∨ p = xb ∨ p = m2)
    (htri : ¬ (xa 2 = xb 2 ∧ (v 2 = xa 2 ∨ w 2 = xa 2))) : IsRupert V := by
  classical
  have hvi : v ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hwi : w ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hv1 := (Finset.mem_inter.mp hvi).1; have hv2 := (Finset.mem_inter.mp hvi).2
  have hw1 := (Finset.mem_inter.mp hwi).1; have hw2 := (Finset.mem_inter.mp hwi).2
  have m21 : f2 xa < 0 := n2 xa (h1V hxa) hxa2
  have m12 : f1 xb < 0 := n1 xb (h2V hxb) hxb1
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
  set r1 : ℝ² := !₂[xa 0 - v 0, xa 1 - v 1] with hr1
  set r2 : ℝ² := !₂[xb 0 - v 0, xb 1 - v 1] with hr2
  have q11 : α1 * (xa 0 - v 0) + β1 * (xa 1 - v 1) = 0 := by rw [← g1]; exact z1 xa hxa
  have q22 : α2 * (xb 0 - v 0) + β2 * (xb 1 - v 1) = 0 := by rw [← g2]; exact z2 xb hxb
  have hρ : cross2 r1 r2 ≠ 0 := by
    intro hρ0
    simp only [hr1, hr2, cross2] at hρ0
    simp at hρ0
    have k0 : f1 xb * (xa 0 - v 0) = 0 := by
      rw [g1]; linear_combination (xb 0 - v 0) * q11 + β1 * hρ0
    have k1 : f1 xb * (xa 1 - v 1) = 0 := by
      rw [g1]; linear_combination (xb 1 - v 1) * q11 - α1 * hρ0
    have r10 := (mul_eq_zero.mp k0).resolve_left m12.ne
    have r11 := (mul_eq_zero.mp k1).resolve_left m12.ne
    have := g2 xa; rw [r10, r11] at this; linarith
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
  have r10 : r1 0 = xa 0 - v 0 := by simp [hr1]
  have r11 : r1 1 = xa 1 - v 1 := by simp [hr1]
  have r20 : r2 0 = xb 0 - v 0 := by simp [hr2]
  have r21 : r2 1 = xb 1 - v 1 := by simp [hr2]
  have G1 : ∀ p, f1 p = b p * f1 xb := by
    intro p; rw [g1 p, g1 xb, (hxy p).1, (hxy p).2, r10, r11, r20, r21]
    linear_combination a p * q11
  have G2 : ∀ p, f2 p = a p * f2 xa := by
    intro p; rw [g2 p, g2 xa, (hxy p).1, (hxy p).2, r10, r11, r20, r21]
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
  have hAx : a xa = 1 := by
    have k : (a xa - 1) * f2 xa = 0 := by linear_combination -(G2 xa)
    linarith [(mul_eq_zero.mp k).resolve_right m21.ne]
  have hBx : b xb = 1 := by
    have k : (b xb - 1) * f1 xb = 0 := by linear_combination -(G1 xb)
    linarith [(mul_eq_zero.mp k).resolve_right m12.ne]
  -- the third face is vertical: `fG = fG v (1 - a - b)`
  have hw01 : w 0 = v 0 ∧ w 1 = v 1 := by
    obtain ⟨c0, c1⟩ := hxy w
    rw [ha2 w hw2, hb1 w hw1] at c0 c1
    constructor <;> linarith
  obtain ⟨KG, αG, βG, γG, hG⟩ := affine_xyz fG
  have hγG : γG = 0 := by
    rw [hG, hG] at hspec
    rw [hw01.1, hw01.2] at hspec
    have : γG * (w 2 - v 2) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right (by linarith)
  have GG : ∀ p, fG p = fG v * (1 - a p - b p) := by
    intro p
    have ka := zG xa hxaG; have kb := zG xb hxbG
    rw [hG] at ka kb; rw [hG p, hG v]
    obtain ⟨c0, c1⟩ := hxy p
    rw [r10, r20] at c0; rw [r11, r21] at c1
    rw [hγG] at ka kb ⊢
    linear_combination αG * c0 + βG * c1 + a p * ka + b p * kb
  have hvG : v ∉ G := by
    intro h
    rcases hGm v h with rfl | rfl | rfl
    · exact hxa2 hv2
    · exact hxb1 hv1
    · exact hg1 hv1
  have hfv : fG v < 0 := nG v (h1V hv1) hvG
  have hG1 : ∀ p ∈ G, a p + b p = 1 := by
    intro p hp
    have := GG p; rw [zG p hp] at this
    have := (mul_eq_zero.mp this.symm).resolve_left hfv.ne
    linarith
  have hG1' : ∀ p ∈ V, p ∉ G → a p + b p < 1 := by
    intro p hp hpG
    have := nG p hp hpG; rw [GG p] at this
    nlinarith
  rcases lt_or_gt_of_ne hρ with hneg | hpos
  · have hpos' : 0 < cross2 r2 r1 := by
      have : cross2 r2 r1 = -cross2 r1 r2 := by unfold cross2; ring
      rw [this]; linarith
    have swap : ∀ p q z, oblPt O r2 r1 q p z = oblPt O r1 r2 p q z := by
      intro p q z; ext j; fin_cases j <;> simp [oblPt] <;> ring
    refine isRupert_special_coords O r2 r1 hpos' V Q2 Q1 G v w hvw b a
      (fun p _ => by rw [swap]; exact hy p) h2V h1V hGV (by rw [Finset.inter_comm]; exact hint)
      ha2 ha2' hb1 hb1' (fun p hp => by rw [add_comm]; exact hG1 p hp)
      (fun p hp hpG => by rw [add_comm]; exact hG1' p hp hpG) hcol ?_ ?_ xb xa g m2 m1 hxb hxa hxbG
      hxaG hgG hxb1 hxa2 hg2 hg1 (fun p hp => by rcases hGm p hp with h | h | h <;> simp [h])
      hQ2m hQ1m ?_
    · intro p hp q hq e
      simp only [Prod.mk.injEq] at e
      exact (hinj v (by simp)) hp hq (by simp only [Prod.mk.injEq]; exact ⟨e.2, e.1⟩)
    · intro p hp q hq e
      simp only [Prod.mk.injEq] at e
      exact (hinj w (by simp)) hp hq (by simp only [Prod.mk.injEq]; exact ⟨e.2, e.1⟩)
    · rintro ⟨h1, h2⟩
      apply htri
      refine ⟨h1.symm, ?_⟩
      rcases h2 with h | h
      · exact Or.inl (h.trans h1)
      · exact Or.inr (h.trans h1)
  · exact isRupert_special_coords O r1 r2 hpos V Q1 Q2 G v w hvw a b (fun p _ => hy p) h1V h2V hGV
      hint hb1 hb1' ha2 ha2' hG1 hG1' hcol (hinj v (by simp)) (hinj w (by simp)) xa xb g m1 m2
      hxa hxb hxaG hxbG hgG hxa2 hxb1 hg1 hg2 hGm hQ1m hQ2m htri

/-- **The special value, the edge vertical** (either end of the edge below). -/
theorem isRupert_special_vertical (V Q1 Q2 G : Finset ℝ³) (v w : ℝ³) (hvw2 : v 2 ≠ w 2)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hGV : G ⊆ V) (hint : Q1 ∩ Q2 = {v, w})
    (f1 f2 fG : ℝ³ →ᵃ[ℝ] ℝ)
    (z1 : ∀ p ∈ Q1, f1 p = 0) (n1 : ∀ p ∈ V, p ∉ Q1 → f1 p < 0)
    (z2 : ∀ p ∈ Q2, f2 p = 0) (n2 : ∀ p ∈ V, p ∉ Q2 → f2 p < 0)
    (zG : ∀ p ∈ G, fG p = 0) (nG : ∀ p ∈ V, p ∉ G → fG p < 0)
    (e1 : f1 (v + ez) = 0) (e2 : f2 (v + ez) = 0) (hspec : fG w = fG v)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hpar : ∀ p ∈ V, ∀ q ∈ V, p ≠ q → ({p, q} : Finset ℝ³) ≠ {v, w} → p 0 ≠ q 0 ∨ p 1 ≠ q 1)
    (xa xb g m1 m2 : ℝ³) (hxa : xa ∈ Q1) (hxb : xb ∈ Q2) (hxaG : xa ∈ G) (hxbG : xb ∈ G)
    (hgG : g ∈ G) (hxa2 : xa ∉ Q2) (hxb1 : xb ∉ Q1) (hg1 : g ∉ Q1) (hg2 : g ∉ Q2)
    (hGm : ∀ p ∈ G, p = xa ∨ p = xb ∨ p = g)
    (hQ1m : ∀ p ∈ Q1, p = v ∨ p = w ∨ p = xa ∨ p = m1)
    (hQ2m : ∀ p ∈ Q2, p = v ∨ p = w ∨ p = xb ∨ p = m2)
    (htri : ¬ (xa 2 = xb 2 ∧ (v 2 = xa 2 ∨ w 2 = xa 2))) : IsRupert V := by
  have hvi : v ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hwi : w ∈ Q1 ∩ Q2 := by rw [hint]; simp
  rcases lt_or_gt_of_ne hvw2 with hlt | hgt
  · exact isRupert_special_vertical_lt V Q1 Q2 G v w hlt h1V h2V hGV hint f1 f2 fG z1 n1 z2 n2 zG nG
      e1 e2 hspec hcol hpar xa xb g m1 m2 hxa hxb hxaG hxbG hgG hxa2 hxb1 hg1 hg2 hGm hQ1m hQ2m htri
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
    refine isRupert_special_vertical_lt V Q1 Q2 G w v hgt h1V h2V hGV
      (by rw [Finset.pair_comm]; exact hint) f1 f2 fG z1 n1 z2 n2 zG nG
      (hw f1 (z1 v hv1) e1 (z1 w hw1)) (hw f2 (z2 v hv2) e2 (z2 w hw2)) hspec.symm hcol
      (fun p hp q hq hpq h => hpar p hp q hq hpq (by rw [Finset.pair_comm v w]; exact h))
      xa xb g m1 m2 hxa hxb hxaG hxbG hgG hxa2 hxb1 hg1 hg2 hGm
      (fun p hp => by rcases hQ1m p hp with h | h | h | h <;> simp [h])
      (fun p hp => by rcases hQ2m p hp with h | h | h | h <;> simp [h])
      (fun ⟨h1, h2⟩ => htri ⟨h1, h2.symm⟩)

/-- The triple tie at the special value: the far ends `xa`, `xb` and an end of the edge
`v w` at one depth along `w - v`. -/
def SpecTriple (v w xa xb : ℝ³) : Prop :=
  ⟪xa, w - v⟫ = ⟪xb, w - v⟫ ∧ (⟪v, w - v⟫ = ⟪xa, w - v⟫ ∨ ⟪w, w - v⟫ = ⟪xa, w - v⟫)

set_option maxHeartbeats 8000000 in
/-- **The special value of Lemma T′** (`FEWER-FACES-PROOFS.md` Theorems 23.18 and 24.13,
facet form). Three facets: `Q1`, `Q2` (functionals `f1`, `f2`) share exactly the edge `v w`,
and the plane of the third, `G = {xa, xb, g}` (functional `fG`), is parallel to that edge
(`fG w = fG v`, the special value), with `G ∩ Q1 = {xa}`, `G ∩ Q2 = {xb}`. Each of `Q1`,
`Q2` has at most one vertex besides `v`, `w` and `xa` (resp. `xb`), and no segment of `V`
other than `v w` is parallel to `v w`. Then `V` is Rupert unless `xa`, `xb` and `v` or `w`
are at one depth along `w - v` (the triple tie): any other ties are allowed. -/
theorem isRupert_special (V Q1 Q2 G : Finset ℝ³) (v w : ℝ³) (hvw : v ≠ w)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hGV : G ⊆ V) (hint : Q1 ∩ Q2 = {v, w})
    (f1 f2 fG : ℝ³ →ᵃ[ℝ] ℝ)
    (z1 : ∀ p ∈ Q1, f1 p = 0) (n1 : ∀ p ∈ V, p ∉ Q1 → f1 p < 0)
    (z2 : ∀ p ∈ Q2, f2 p = 0) (n2 : ∀ p ∈ V, p ∉ Q2 → f2 p < 0)
    (zG : ∀ p ∈ G, fG p = 0) (nG : ∀ p ∈ V, p ∉ G → fG p < 0) (hspec : fG w = fG v)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hpar : EdgePar V v w)
    (xa xb g m1 m2 : ℝ³) (hxa : xa ∈ Q1) (hxb : xb ∈ Q2) (hxaG : xa ∈ G) (hxbG : xb ∈ G)
    (hgG : g ∈ G) (hxa2 : xa ∉ Q2) (hxb1 : xb ∉ Q1) (hg1 : g ∉ Q1) (hg2 : g ∉ Q2)
    (hGm : ∀ p ∈ G, p = xa ∨ p = xb ∨ p = g)
    (hQ1m : ∀ p ∈ Q1, p = v ∨ p = w ∨ p = xa ∨ p = m1)
    (hQ2m : ∀ p ∈ Q2, p = v ∨ p = w ∨ p = xb ∨ p = m2)
    (htri : ¬ SpecTriple v w xa xb) : IsRupert V := by
  classical
  have he : w - v ≠ 0 := sub_ne_zero.mpr hvw.symm
  obtain ⟨R, hR, r, hr, hRe⟩ := exists_rotation_to_ez_pos (w - v) he
  apply isRupert_of_isRupert_image_rotation R hR
  set gr := R.toEuclideanLin with hgr
  set I := so3Isometry hR with hI
  have hgI : ∀ p, gr p = I p := fun p => rfl
  have hginj : Function.Injective gr := I.injective
  have hgz : ∀ p, gr p 2 = ⟪p, w - v⟫ / r := fun p => by
    have := inner_toEuclideanLin_SO3 hR p (w - v)
    rw [hRe, real_inner_smul_right, inner_ez] at this
    field_simp; linarith
  have hIe : I.symm ez = r⁻¹ • (w - v) := by
    apply I.injective
    rw [LinearIsometryEquiv.apply_symm_apply, map_smul, ← hgI, hRe, smul_smul,
      inv_mul_cancel₀ hr.ne', one_smul]
  set F1 := f1.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap with hF1
  set F2 := f2.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap with hF2
  set FG := fG.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap with hFG
  have tF1 : ∀ p, F1 (gr p) = f1 p := fun p => by simp [hF1, hgI]
  have tF2 : ∀ p, F2 (gr p) = f2 p := fun p => by simp [hF2, hgI]
  have tFG : ∀ p, FG (gr p) = fG p := fun p => by simp [hFG, hgI]
  have tz : ∀ f : ℝ³ →ᵃ[ℝ] ℝ, f v = 0 → f w = 0 →
      (f.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap) (gr v + ez) = 0 := by
    intro f h0 h1
    have : (f.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap) (gr v + ez) =
        f (v + r⁻¹ • (w - v)) := by
      simp [hgI, map_add, hIe]
    rw [this]; exact affine_zero_line f h0 (by rw [add_sub_cancel]; exact h1) _
  have hvi : v ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hwi : w ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hv1 := (Finset.mem_inter.mp hvi).1; have hv2 := (Finset.mem_inter.mp hvi).2
  have hw1 := (Finset.mem_inter.mp hwi).1; have hw2 := (Finset.mem_inter.mp hwi).2
  have memg : ∀ (S : Finset ℝ³) p, gr p ∈ S.image gr ↔ p ∈ S := fun S p =>
    ⟨fun h => by obtain ⟨q, hq, e⟩ := Finset.mem_image.mp h; rwa [← hginj e],
      Finset.mem_image_of_mem gr⟩
  have allg : ∀ (S : Finset ℝ³) (P : ℝ³ → Prop), (∀ p ∈ S, P (gr p)) → ∀ q ∈ S.image gr, P q := by
    intro S P h q hq; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq; exact h p hp
  have hdiv : ∀ p q : ℝ³, ⟪p, w - v⟫ / r = ⟪q, w - v⟫ / r → ⟪p, w - v⟫ = ⟪q, w - v⟫ := by
    intro p q h; field_simp at h; exact h
  refine isRupert_special_vertical (V.image gr) (Q1.image gr) (Q2.image gr) (G.image gr) (gr v) (gr w)
    ?_ (Finset.image_subset_image h1V) (Finset.image_subset_image h2V)
    (Finset.image_subset_image hGV)
    (by rw [← Finset.image_inter _ _ hginj, hint, Finset.image_insert, Finset.image_singleton])
    F1 F2 FG
    (allg Q1 _ (fun p hp => by rw [tF1]; exact z1 p hp))
    (allg V _ (fun p hp hq => by rw [tF1]; exact n1 p hp (fun h => hq ((memg Q1 p).mpr h))))
    (allg Q2 _ (fun p hp => by rw [tF2]; exact z2 p hp))
    (allg V _ (fun p hp hq => by rw [tF2]; exact n2 p hp (fun h => hq ((memg Q2 p).mpr h))))
    (allg G _ (fun p hp => by rw [tFG]; exact zG p hp))
    (allg V _ (fun p hp hq => by rw [tFG]; exact nG p hp (fun h => hq ((memg G p).mpr h))))
    (tz f1 (z1 v hv1) (z1 w hw1)) (tz f2 (z2 v hv2) (z2 w hw2)) (by rw [tFG, tFG]; exact hspec)
    ?_ ?_ (gr xa) (gr xb) (gr g) (gr m1) (gr m2)
    (Finset.mem_image_of_mem gr hxa) (Finset.mem_image_of_mem gr hxb)
    (Finset.mem_image_of_mem gr hxaG) (Finset.mem_image_of_mem gr hxbG)
    (Finset.mem_image_of_mem gr hgG)
    (fun h => hxa2 ((memg Q2 xa).mp h)) (fun h => hxb1 ((memg Q1 xb).mp h))
    (fun h => hg1 ((memg Q1 g).mp h)) (fun h => hg2 ((memg Q2 g).mp h))
    (allg G _ (fun p hp => by rcases hGm p hp with rfl | rfl | rfl <;> simp))
    (allg Q1 _ (fun p hp => by rcases hQ1m p hp with rfl | rfl | rfl | rfl <;> simp))
    (allg Q2 _ (fun p hp => by rcases hQ2m p hp with rfl | rfl | rfl | rfl <;> simp)) ?_
  · rw [hgz, hgz]
    intro h
    have k : ⟪v, w - v⟫ = ⟪w, w - v⟫ := hdiv v w h
    have : ⟪w - v, w - v⟫ = 0 := by rw [inner_sub_left]; linarith
    exact hvw (sub_eq_zero.mp (inner_self_eq_zero.mp this)).symm
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
      rw [show ({gr p, gr q} : Finset ℝ³) = Finset.image gr {p, q} by simp,
        show ({gr v, gr w} : Finset ℝ³) = Finset.image gr {v, w} by simp, e]))
      ((gr (q - p)) 2 / r)
    apply hginj
    rw [map_smul, hRe]
    ext k; fin_cases k
    · simp [ez, map_sub]; linarith
    · simp [ez, map_sub]; linarith
    · simp [ez]; field_simp
  · rw [hgz, hgz, hgz, hgz]
    rintro ⟨h1, h2⟩
    apply htri
    refine ⟨hdiv _ _ h1, ?_⟩
    rcases h2 with h | h
    · exact Or.inl (hdiv _ _ h)
    · exact Or.inr (hdiv _ _ h)

/-- No other segment is parallel to the edge `v w` when the faces `Q1`, `Q2` (through the
edge) and `G` (parallel to it) separate every other pair of points: a segment parallel to
`v w` has equal values of the three functionals at its ends. -/
theorem edgePar_of_cover {V Q1 Q2 G : Finset ℝ³} {v w : ℝ³} (f1 f2 fG : ℝ³ →ᵃ[ℝ] ℝ)
    (z1 : ∀ p ∈ Q1, f1 p = 0) (n1 : ∀ p ∈ V, p ∉ Q1 → f1 p < 0)
    (z2 : ∀ p ∈ Q2, f2 p = 0) (n2 : ∀ p ∈ V, p ∉ Q2 → f2 p < 0)
    (zG : ∀ p ∈ G, fG p = 0) (nG : ∀ p ∈ V, p ∉ G → fG p < 0)
    (hv1 : v ∈ Q1) (hw1 : w ∈ Q1) (hv2 : v ∈ Q2) (hw2 : w ∈ Q2) (hspec : fG w = fG v)
    (hsep : ∀ p ∈ V, ∀ q ∈ V, p ≠ q → (p ∈ Q1 ↔ q ∈ Q1) → (p ∈ Q2 ↔ q ∈ Q2) →
      (p ∈ G ↔ q ∈ G) → (p = v ∧ q = w) ∨ (p = w ∧ q = v)) : EdgePar V v w := by
  intro p hp q hq hpq hpair c hc
  have shift : ∀ f : ℝ³ →ᵃ[ℝ] ℝ, f w = f v → f q = f p := by
    intro f hf
    obtain ⟨K, α, β, γ, h⟩ := affine_xyz f
    have hq' : q = p + c • (w - v) := by rw [← hc]; abel
    rw [h, h] at hf ⊢; rw [hq']; simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
      smul_eq_mul]
    linear_combination c * hf
  have key : ∀ (Q : Finset ℝ³) (f : ℝ³ →ᵃ[ℝ] ℝ), (∀ p ∈ Q, f p = 0) →
      (∀ p ∈ V, p ∉ Q → f p < 0) → f w = f v → (p ∈ Q ↔ q ∈ Q) := by
    intro Q f zf nf hf
    have e := shift f hf
    constructor
    · intro h; by_contra h'; have := nf q hq h'; rw [e, zf p h] at this; exact lt_irrefl _ this
    · intro h; by_contra h'; have := nf p hp h'; rw [← e, zf q h] at this; exact lt_irrefl _ this
  rcases hsep p hp q hq hpq (key Q1 f1 z1 n1 (by rw [z1 w hw1, z1 v hv1]))
    (key Q2 f2 z2 n2 (by rw [z2 w hw2, z2 v hv2])) (key G fG zG nG hspec) with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hpair rfl
  · exact hpair (Finset.pair_comm _ _)

/-- `edgePar_of_cover`'s separation hypothesis for labelled points, from its index form
(decidable). -/
theorem sep_of_index {x : Fin 7 → ℝ³} (hx : Function.Injective x) (A B C : Finset (Fin 7))
    (i0 i1 : Fin 7)
    (h : ∀ i j : Fin 7, i ≠ j → (i ∈ A ↔ j ∈ A) → (i ∈ B ↔ j ∈ B) → (i ∈ C ↔ j ∈ C) →
      (i = i0 ∧ j = i1) ∨ (i = i1 ∧ j = i0)) :
    ∀ p ∈ univ.image x, ∀ q ∈ univ.image x, p ≠ q → (p ∈ A.image x ↔ q ∈ A.image x) →
      (p ∈ B.image x ↔ q ∈ B.image x) → (p ∈ C.image x ↔ q ∈ C.image x) →
      (p = x i0 ∧ q = x i1) ∨ (p = x i1 ∧ q = x i0) := by
  intro p hp q hq hpq h1 h2 h3
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hq
  rw [hx.mem_finset_image, hx.mem_finset_image] at h1 h2 h3
  rcases h i j (fun e => hpq (by rw [e])) h1 h2 h3 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

/-- **The special value for seven labelled points** (`isRupert_special` with `edgePar_of_cover`):
facets `A`, `B` through the edge `i0 i1`, the triangle `C = {ia, ib, ig}` with `fC` equal at
`i0`, `i1`, at most one more vertex `j1` of `A` and `j2` of `B`, and the three faces
separating every pair of labels but `i0`, `i1` (decidable). Rupert unless the triple tie. -/
theorem isRupert_special_index (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (hgen : NoThreeCollinear (univ.image x)) (A B C : Finset (Fin 7)) (fA fB fC : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ A → fA (x i) = 0) ∧ (i ∉ A → fA (x i) < 0))
    (hB : ∀ i, (i ∈ B → fB (x i) = 0) ∧ (i ∉ B → fB (x i) < 0))
    (hC : ∀ i, (i ∈ C → fC (x i) = 0) ∧ (i ∉ C → fC (x i) < 0))
    (i0 i1 ia ib ig j1 j2 : Fin 7) (h01 : i0 ≠ i1) (hAB : A ∩ B = {i0, i1})
    (hspec : fC (x i1) = fC (x i0))
    (hia : ia ∈ A ∧ ia ∈ C ∧ ia ∉ B) (hib : ib ∈ B ∧ ib ∈ C ∧ ib ∉ A) (hig : ig ∈ C ∧ ig ∉ A ∧ ig ∉ B)
    (hCm : ∀ i ∈ C, i = ia ∨ i = ib ∨ i = ig) (hAm : ∀ i ∈ A, i = i0 ∨ i = i1 ∨ i = ia ∨ i = j1)
    (hBm : ∀ i ∈ B, i = i0 ∨ i = i1 ∨ i = ib ∨ i = j2)
    (hsep : ∀ i j : Fin 7, i ≠ j → (i ∈ A ↔ j ∈ A) → (i ∈ B ↔ j ∈ B) → (i ∈ C ↔ j ∈ C) →
      (i = i0 ∧ j = i1) ∨ (i = i1 ∧ j = i0))
    (htri : ¬ SpecTriple (x i0) (x i1) (x ia) (x ib)) : IsRupert (univ.image x) := by
  classical
  have memQ : ∀ (P : Finset (Fin 7)) i, x i ∈ P.image x ↔ i ∈ P := fun P i => hx.mem_finset_image
  have sub : ∀ P : Finset (Fin 7), P.image x ⊆ univ.image x := fun P =>
    Finset.image_subset_image (Finset.subset_univ P)
  have i01A : i0 ∈ A ∧ i1 ∈ A ∧ i0 ∈ B ∧ i1 ∈ B := by
    have h0 : i0 ∈ A ∩ B := by rw [hAB]; simp
    have h1 : i1 ∈ A ∩ B := by rw [hAB]; simp
    exact ⟨(Finset.mem_inter.mp h0).1, (Finset.mem_inter.mp h1).1, (Finset.mem_inter.mp h0).2,
      (Finset.mem_inter.mp h1).2⟩
  refine isRupert_special (univ.image x) (A.image x) (B.image x) (C.image x) (x i0) (x i1)
    (fun h => h01 (hx h)) (sub A) (sub B) (sub C)
    (by rw [← Finset.image_inter A B hx, hAB, Finset.image_insert, Finset.image_singleton])
    fA fB fC (facet_zero_of_index hA) (facet_neg_of_index hA) (facet_zero_of_index hB)
    (facet_neg_of_index hB) (facet_zero_of_index hC) (facet_neg_of_index hC) hspec hgen
    (edgePar_of_cover fA fB fC (facet_zero_of_index hA) (facet_neg_of_index hA)
      (facet_zero_of_index hB) (facet_neg_of_index hB) (facet_zero_of_index hC)
      (facet_neg_of_index hC) ((memQ A i0).mpr i01A.1) ((memQ A i1).mpr i01A.2.1)
      ((memQ B i0).mpr i01A.2.2.1) ((memQ B i1).mpr i01A.2.2.2) hspec
      (sep_of_index hx A B C i0 i1 hsep))
    (x ia) (x ib) (x ig) (x j1) (x j2) ((memQ A ia).mpr hia.1) ((memQ B ib).mpr hib.1)
    ((memQ C ia).mpr hia.2.1) ((memQ C ib).mpr hib.2.1) ((memQ C ig).mpr hig.1)
    (fun h => hia.2.2 ((memQ B ia).mp h)) (fun h => hib.2.2 ((memQ A ib).mp h))
    (fun h => hig.2.1 ((memQ A ig).mp h)) (fun h => hig.2.2 ((memQ B ig).mp h)) ?_ ?_ ?_ htri
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    rcases hCm i hi with rfl | rfl | rfl <;> simp
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    rcases hAm i hi with rfl | rfl | rfl | rfl <;> simp
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    rcases hBm i hi with rfl | rfl | rfl | rfl <;> simp

/-! ### Three single corners (types 12, 22, 28)

At the special value of types 12, 22, 28 the three edge-on faces meet in single vertices
at the corners of the shadow triangle. The reading of Lemma T′ at the apex `v` works
unless the far corners `xa`, `xb` tie, the reading at `xa` unless `v` and `xb` tie; so
only the triple tie is left (Theorem 23.18 with 24.13). -/

set_option maxHeartbeats 16000000 in
/-- **The special value with three single corners, in frame coordinates.** As
`isRupert_special_coords`, with the apex a single vertex `v` and `Q2` having at most one
vertex besides `v` and `xb` (or `Q1` besides `v` and `xa`; the other face is arbitrary).
Rupert unless `v`, `xa`, `xb` are at one depth. No condition on segments parallel to the
view. -/
theorem isRupert_special3_coords (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (V Q1 Q2 G : Finset ℝ³)
    (v : ℝ³) (a b : ℝ³ → ℝ) (hy : ∀ p ∈ V, p = oblPt O r1 r2 (a p) (b p) (p 2))
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hGV : G ⊆ V) (hint : Q1 ∩ Q2 = {v})
    (hb1 : ∀ p ∈ Q1, b p = 0) (hb1' : ∀ p ∈ V, p ∉ Q1 → 0 < b p)
    (ha2 : ∀ p ∈ Q2, a p = 0) (ha2' : ∀ p ∈ V, p ∉ Q2 → 0 < a p)
    (hG1 : ∀ p ∈ G, a p + b p = 1) (hG1' : ∀ p ∈ V, p ∉ G → a p + b p < 1)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (xa xb g m2 : ℝ³) (hxa : xa ∈ Q1) (hxb : xb ∈ Q2) (hxaG : xa ∈ G) (hxbG : xb ∈ G)
    (hgG : g ∈ G) (hg1 : g ∉ Q1) (hg2 : g ∉ Q2)
    (hGm : ∀ p ∈ G, p = xa ∨ p = xb ∨ p = g)
    (hQm : (∀ p ∈ Q2, p = v ∨ p = xb ∨ p = m2) ∨ (∀ p ∈ Q1, p = v ∨ p = xa ∨ p = m2))
    (htri : ¬ (xa 2 = xb 2 ∧ v 2 = xa 2)) : IsRupert V := by
  classical
  have hv1 : v ∈ Q1 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).1
  have hv2 : v ∈ Q2 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).2
  have only : ∀ p ∈ Q1, p ∈ Q2 → p = v := by
    intro p h1 h2
    have : p ∈ Q1 ∩ Q2 := Finset.mem_inter.mpr ⟨h1, h2⟩
    rwa [hint, Finset.mem_singleton] at this
  have hav := ha2 v hv2; have hbv := hb1 v hv1
  have hgV := hGV hgG
  have hxaV := h1V hxa
  have hxbV := h2V hxb
  have hvV := h1V hv1
  have hAx : a xa = 1 := by have := hG1 xa hxaG; rw [hb1 xa hxa] at this; linarith
  have hBx : b xb = 1 := by have := hG1 xb hxbG; rw [ha2 xb hxb] at this; linarith
  have hbxa := hb1 xa hxa
  have haxb := ha2 xb hxb
  have hxa2 : xa ∉ Q2 := fun h => by have := ha2 xa h; linarith
  have hxb1 : xb ∉ Q1 := fun h => by have := hb1 xb h; linarith
  have hxav : xa ≠ v := fun e => hxa2 (e ▸ hv2)
  have hxbv : xb ≠ v := fun e => hxb1 (e ▸ hv1)
  have hxaxb : xa ≠ xb := fun e => hxb1 (e ▸ hxa)
  have ha0 : ∀ p ∈ V, 0 ≤ a p := fun p hp => by
    by_cases h : p ∈ Q2
    · rw [ha2 p h]
    · exact (ha2' p hp h).le
  have hb0 : ∀ p ∈ V, 0 ≤ b p := fun p hp => by
    by_cases h : p ∈ Q1
    · rw [hb1 p h]
    · exact (hb1' p hp h).le
  have hGQ1 : G ∩ Q1 = {xa} := by
    ext p; simp only [Finset.mem_inter, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      rcases hGm p h1 with rfl | rfl | rfl
      · rfl
      · exact absurd h2 hxb1
      · exact absurd h2 hg1
    · rintro rfl; exact ⟨hxaG, hxa⟩
  have hQ2G : Q2 ∩ G = {xb} := by
    ext p; simp only [Finset.mem_inter, Finset.mem_singleton]
    constructor
    · rintro ⟨h2, h1⟩
      rcases hGm p h1 with rfl | rfl | rfl
      · exact absurd h2 hxa2
      · rfl
      · exact absurd h2 hg2
    · rintro rfl; exact ⟨hxb, hxbG⟩
  -- points of `Q1` over the far corner `xa`, of `G` over `xb`, of `Q1` over `v`
  have onlyxa : ∀ p ∈ Q1, a p = a xa → p = xa := by
    intro p hp hpa
    have hpG : p ∈ G := by
      by_contra h; have := hG1' p (h1V hp) h; rw [hb1 p hp, hpa, hAx] at this; linarith
    have : p ∈ G ∩ Q1 := Finset.mem_inter.mpr ⟨hpG, hp⟩
    rw [hGQ1] at this; simpa using this
  have onlyxb : ∀ p ∈ Q2, b p = b xb → p = xb := by
    intro p hp hpb
    have hpG : p ∈ G := by
      by_contra h; have := hG1' p (h2V hp) h; rw [ha2 p hp, hpb, hBx] at this; linarith
    have : p ∈ Q2 ∩ G := Finset.mem_inter.mpr ⟨hp, hpG⟩
    rw [hQ2G] at this; simpa using this
  have onlyxbG : ∀ p ∈ G, b p = 1 → p = xb := by
    intro p hp hpb
    have hap : a p = 0 := by have := hG1 p hp; linarith
    have hp2 : p ∈ Q2 := by by_contra h; linarith [ha2' p (hGV hp) h]
    have : p ∈ Q2 ∩ G := Finset.mem_inter.mpr ⟨hp2, hp⟩
    rw [hQ2G] at this; simpa using this
  have onlyv : ∀ p ∈ Q1, a p = 0 → p = v := by
    intro p hp hpa
    have hp2 : p ∈ Q2 := by by_contra h; linarith [ha2' p (h1V hp) h]
    exact only p hp hp2
  -- the far side of the apex reading is not on the line of the far corners
  have hgline : g 2 - xa 2 - b g * (xb 2 - xa 2) ≠ 0 := by
    intro h
    have hag : a g = 1 - b g := by have := hG1 g hgG; linarith
    apply hcol xa hxaV xb hxbV g hgV hxaxb (fun e => hg1 (e ▸ hxa)) (fun e => hg2 (e ▸ hxb)) (b g)
    have key := oblPt_sub_smul O r1 r2 (a1 := a xa) (b1 := b xa) (z1 := xa 2) (a2 := a xb)
      (b2 := b xb) (z2 := xb 2) (a3 := a g) (b3 := b g) (z3 := g 2) (t := b g)
      (by rw [hag, hAx, haxb]; ring) (by rw [hbxa, hBx]; ring) (by linarith)
    rw [← hy g hgV, ← hy xa hxaV, ← hy xb hxbV] at key
    exact key
  -- the reading at the apex `v`
  have readX : ∀ s : ℝ, (s = 1 ∨ s = -1) → s * xb 2 < s * xa 2 → IsRupert V := by
    intro s hs hAB
    obtain ⟨σ, hσ, hσD⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
        0 < σ * s * (g 2 - xa 2 - b g * (xb 2 - xa 2)) := by
      have hsD : s * (g 2 - xa 2 - b g * (xb 2 - xa 2)) ≠ 0 :=
        mul_ne_zero (by rcases hs with rfl | rfl <;> norm_num) hgline
      rcases lt_or_gt_of_ne hsD with h | h
      · exact ⟨-1, Or.inr rfl, by nlinarith⟩
      · exact ⟨1, Or.inl rfl, by nlinarith⟩
    refine isRupert_vertex_coords_parc O r1 r2 hρ V Q1 Q2 v a b hy h1V h2V hint hb1 hb1' ha2 ha2'
      ⟨xa, hxa, hxav⟩ ⟨xb, hxb, hxbv⟩ hcol s hs xa xb hxa hxb ?_ ?_
      (fun p hp hpa hpx => absurd (onlyxa p hp hpa) hpx)
      (fun q hq hqb hqx => absurd (onlyxb q hq hqb) hqx) hAB σ hσ
      (fun ⟨p, hp, hpa, hpx⟩ => absurd (onlyxa p hp hpa) hpx)
      (fun ⟨q, hq, hqb, hqx⟩ => absurd (onlyxb q hq hqb) hqx) ?_
    · intro p hp; rw [hAx]
      by_cases hpG : p ∈ G
      · rcases hGm p hpG with rfl | rfl | rfl
        · rw [hAx]
        · exact absurd hp hxb1
        · exact absurd hp hg1
      · have := hG1' p (h1V hp) hpG; rw [hb1 p hp] at this; linarith
    · intro q hq; rw [hBx]
      by_cases hqG : q ∈ G
      · rcases hGm q hqG with rfl | rfl | rfl
        · exact absurd hq hxa2
        · rw [hBx]
        · exact absurd hq hg2
      · have := hG1' q (h2V hq) hqG; rw [ha2 q hq] at this; linarith
    · intro y hy' h1 h2
      rw [hAx, hBx, div_one, div_one]
      by_cases hyG : y ∈ G
      · rcases hGm y hyG with rfl | rfl | rfl
        · exact absurd hxa h1
        · exact absurd hxb h2
        · right; refine ⟨hG1 y hgG, ?_⟩
          rw [one_mul]; exact hσD
      · exact Or.inl (hG1' y hy' hyG)
  -- the reading at the far corner `xa` (apex `xa`, faces `G` and `Q1`, far face `Q2`)
  have readY : (∀ p ∈ Q2, p = v ∨ p = xb ∨ p = m2) → ∀ s : ℝ, (s = 1 ∨ s = -1) →
      s * v 2 < s * xb 2 → IsRupert V := by
    intro hQ2m s hs hAB
    -- the side of the middle of `Q2`
    obtain ⟨σ, hσ, hσD⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ y ∈ Q2, y ∉ Q1 → y ∉ G →
        0 < σ * s * ((y 2 - xb 2) - (1 - b y) * (v 2 - xb 2)) := by
      by_cases hm : m2 ∈ Q2 ∧ m2 ∉ Q1 ∧ m2 ∉ G
      · have hm2V := h2V hm.1
        have hline : (m2 2 - xb 2) - (1 - b m2) * (v 2 - xb 2) ≠ 0 := by
          intro h
          apply hcol xb hxbV v hvV m2 hm2V hxbv (fun e => hm.2.2 (e ▸ hxbG))
            (fun e => hm.2.1 (e ▸ hv1)) (1 - b m2)
          have key := oblPt_sub_smul O r1 r2 (a1 := a xb) (b1 := b xb) (z1 := xb 2) (a2 := a v)
            (b2 := b v) (z2 := v 2) (a3 := a m2) (b3 := b m2) (z3 := m2 2) (t := 1 - b m2)
            (by rw [haxb, hav, ha2 m2 hm.1]; ring) (by rw [hBx, hbv]; ring) (by linarith)
          rw [← hy m2 hm2V, ← hy xb hxbV, ← hy v hvV] at key
          exact key
        have hsD : s * ((m2 2 - xb 2) - (1 - b m2) * (v 2 - xb 2)) ≠ 0 :=
          mul_ne_zero (by rcases hs with rfl | rfl <;> norm_num) hline
        have only2 : ∀ y ∈ Q2, y ∉ Q1 → y ∉ G → y = m2 := by
          intro y hy h1 hG
          rcases hQ2m y hy with rfl | rfl | rfl
          · exact absurd hv1 h1
          · exact absurd hxbG hG
          · rfl
        rcases lt_or_gt_of_ne hsD with h | h
        · exact ⟨-1, Or.inr rfl, fun y hy h1 hG => by rw [only2 y hy h1 hG]; nlinarith⟩
        · exact ⟨1, Or.inl rfl, fun y hy h1 hG => by rw [only2 y hy h1 hG]; nlinarith⟩
      · refine ⟨1, Or.inl rfl, fun y hy h1 hG => ?_⟩
        exfalso
        rcases hQ2m y hy with rfl | rfl | rfl
        · exact h1 hv1
        · exact hG hxbG
        · exact hm ⟨hy, h1, hG⟩
    refine isRupert_vertex_coords_parc (O + r1) (r2 - r1) (-r1) (by rw [cross2_R2]; exact hρ) V G Q1
      xa b (fun p => 1 - a p - b p) (fun p hp => by rw [oblPt_R2]; exact hy p hp) hGV h1V hGQ1
      (fun p hp => by have := hG1 p hp; show 1 - a p - b p = 0; linarith)
      (fun p hp hpG => by have := hG1' p hp hpG; show 0 < 1 - a p - b p; linarith) hb1 hb1'
      ⟨xb, hxbG, hxaxb.symm⟩ ⟨v, hv1, hxav.symm⟩ hcol s hs xb v hxbG hv1 ?_ ?_
      (fun p hp hpb hpx => absurd (onlyxbG p hp (by rw [hpb, hBx])) hpx) ?_ hAB σ hσ
      (fun ⟨p, hp, hpb, hpx⟩ => absurd (onlyxbG p hp (by rw [hpb, hBx])) hpx) ?_ ?_
    · intro p hp; rw [hBx]; have := hG1 p hp; linarith [ha0 p (hGV hp)]
    · intro q hq; show 1 - a q - b q ≤ 1 - a v - b v
      rw [hav, hbv]; linarith [ha0 q (h1V hq), hb1 q hq]
    · intro q hq hqb hqv
      have hqb' : 1 - a q - b q = 1 - a v - b v := hqb
      exact absurd (onlyv q hq (by rw [hav, hbv, hb1 q hq] at hqb'; linarith)) hqv
    · rintro ⟨q, hq, hqb, hqv⟩
      have hqb' : 1 - a q - b q = 1 - a v - b v := hqb
      exact absurd (onlyv q hq (by rw [hav, hbv, hb1 q hq] at hqb'; linarith)) hqv
    · intro y hy' hyG hy1
      have e1 : (1 - a v - b v) = 1 := by rw [hav, hbv]; ring
      show b y / b xb + (1 - a y - b y) / (1 - a v - b v) < 1 ∨
        (b y / b xb + (1 - a y - b y) / (1 - a v - b v) = 1 ∧
          0 < σ * s * ((1 - a v - b v) * (y 2 - xb 2) - (1 - a y - b y) * (v 2 - xb 2)))
      rw [hBx, e1, div_one, div_one]
      by_cases hy2 : y ∈ Q2
      · right
        have hay := ha2 y hy2
        refine ⟨by rw [hay]; ring, ?_⟩
        have := hσD y hy2 hy1 hyG
        rw [hay]
        have e : σ * s * (1 * (y 2 - xb 2) - (1 - 0 - b y) * (v 2 - xb 2)) =
            σ * s * ((y 2 - xb 2) - (1 - b y) * (v 2 - xb 2)) := by ring
        rw [e]; exact this
      · left; linarith [ha2' y hy' hy2]
  -- the reading at the far corner `xb` (apex `xb`, faces `Q2` and `G`, far face `Q1`)
  have readZ : (∀ p ∈ Q1, p = v ∨ p = xa ∨ p = m2) → ∀ s : ℝ, (s = 1 ∨ s = -1) →
      s * xa 2 < s * v 2 → IsRupert V := by
    intro hQ1m s hs hAB
    obtain ⟨σ, hσ, hσD⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ y ∈ Q1, y ∉ Q2 → y ∉ G →
        0 < σ * s * ((y 2 - v 2) - a y * (xa 2 - v 2)) := by
      by_cases hm : m2 ∈ Q1 ∧ m2 ∉ Q2 ∧ m2 ∉ G
      · have hm1V := h1V hm.1
        have hline : (m2 2 - v 2) - a m2 * (xa 2 - v 2) ≠ 0 := by
          intro h
          apply hcol v hvV xa hxaV m2 hm1V hxav.symm (fun e => hm.2.1 (e ▸ hv2))
            (fun e => hm.2.2 (e ▸ hxaG)) (a m2)
          have key := oblPt_sub_smul O r1 r2 (a1 := a v) (b1 := b v) (z1 := v 2) (a2 := a xa)
            (b2 := b xa) (z2 := xa 2) (a3 := a m2) (b3 := b m2) (z3 := m2 2) (t := a m2)
            (by rw [hav, hAx]; ring) (by rw [hbv, hbxa, hb1 m2 hm.1]; ring) (by linarith)
          rw [← hy m2 hm1V, ← hy xa hxaV, ← hy v hvV] at key
          exact key
        have hsD : s * ((m2 2 - v 2) - a m2 * (xa 2 - v 2)) ≠ 0 :=
          mul_ne_zero (by rcases hs with rfl | rfl <;> norm_num) hline
        have only1 : ∀ y ∈ Q1, y ∉ Q2 → y ∉ G → y = m2 := by
          intro y hy h2 hG
          rcases hQ1m y hy with rfl | rfl | rfl
          · exact absurd hv2 h2
          · exact absurd hxaG hG
          · rfl
        rcases lt_or_gt_of_ne hsD with h | h
        · exact ⟨-1, Or.inr rfl, fun y hy h2 hG => by rw [only1 y hy h2 hG]; nlinarith⟩
        · exact ⟨1, Or.inl rfl, fun y hy h2 hG => by rw [only1 y hy h2 hG]; nlinarith⟩
      · refine ⟨1, Or.inl rfl, fun y hy h2 hG => ?_⟩
        exfalso
        rcases hQ1m y hy with rfl | rfl | rfl
        · exact h2 hv2
        · exact hG hxaG
        · exact hm ⟨hy, h2, hG⟩
    have onlyxaG : ∀ p ∈ G, a p = 1 → p = xa := by
      intro p hp hpa
      have hbp : b p = 0 := by have := hG1 p hp; linarith
      have hp1 : p ∈ Q1 := by by_contra h; linarith [hb1' p (hGV hp) h]
      have : p ∈ G ∩ Q1 := Finset.mem_inter.mpr ⟨hp, hp1⟩
      rw [hGQ1] at this; simpa using this
    have onlyv2 : ∀ p ∈ Q2, b p = 0 → p = v := by
      intro p hp hpb
      have hp1 : p ∈ Q1 := by by_contra h; linarith [hb1' p (h2V hp) h]
      exact only p hp1 hp
    refine isRupert_vertex_coords_parc (O + r2) (-r2) (r1 - r2) (by rw [cross2_R3]; exact hρ) V Q2 G
      xb (fun p => 1 - a p - b p) a (fun p hp => by rw [oblPt_R3]; exact hy p hp) h2V hGV hQ2G
      ha2 ha2' (fun p hp => by have := hG1 p hp; show 1 - a p - b p = 0; linarith)
      (fun p hp hpG => by have := hG1' p hp hpG; show 0 < 1 - a p - b p; linarith)
      ⟨v, hv2, hxbv.symm⟩ ⟨xa, hxaG, hxaxb⟩ hcol s hs v xa hv2 hxaG ?_ ?_ ?_
      (fun q hq hqa hqx => absurd (onlyxaG q hq (by rw [hqa, hAx])) hqx) hAB σ hσ ?_
      (fun ⟨q, hq, hqa, hqx⟩ => absurd (onlyxaG q hq (by rw [hqa, hAx])) hqx) ?_
    · intro q hq; show 1 - a q - b q ≤ 1 - a v - b v
      rw [hav, hbv]; linarith [hb0 q (h2V hq), ha2 q hq]
    · intro p hp; rw [hAx]; have := hG1 p hp; linarith [hb0 p (hGV hp)]
    · intro p hp hpa hpv
      have hpa' : 1 - a p - b p = 1 - a v - b v := hpa
      exact absurd (onlyv2 p hp (by rw [hav, hbv, ha2 p hp] at hpa'; linarith)) hpv
    · rintro ⟨p, hp, hpa, hpv⟩
      have hpa' : 1 - a p - b p = 1 - a v - b v := hpa
      exact absurd (onlyv2 p hp (by rw [hav, hbv, ha2 p hp] at hpa'; linarith)) hpv
    · intro y hy' hy2 hyG
      have e1 : (1 - a v - b v) = 1 := by rw [hav, hbv]; ring
      show (1 - a y - b y) / (1 - a v - b v) + a y / a xa < 1 ∨
        ((1 - a y - b y) / (1 - a v - b v) + a y / a xa = 1 ∧
          0 < σ * s * (a xa * (y 2 - v 2) - a y * (xa 2 - v 2)))
      rw [hAx, e1, div_one, div_one]
      by_cases hy1 : y ∈ Q1
      · right
        have hby := hb1 y hy1
        refine ⟨by rw [hby]; ring, ?_⟩
        have := hσD y hy1 hy2 hyG
        rw [one_mul]; exact this
      · left; linarith [hb1' y hy' hy1]
  by_cases hne : xa 2 = xb 2
  · have hv : v 2 ≠ xb 2 := fun h => htri ⟨hne, h.trans hne.symm⟩
    rcases hQm with hQ2m | hQ1m
    · rcases lt_or_gt_of_ne hv with h | h
      · exact readY hQ2m 1 (Or.inl rfl) (by linarith)
      · exact readY hQ2m (-1) (Or.inr rfl) (by linarith)
    · rcases lt_or_gt_of_ne hv with h | h
      · exact readZ hQ1m (-1) (Or.inr rfl) (by linarith)
      · exact readZ hQ1m 1 (Or.inl rfl) (by linarith)
  · rcases lt_or_gt_of_ne hne with h | h
    · exact readX (-1) (Or.inr rfl) (by linarith)
    · exact readX 1 (Or.inl rfl) (by linarith)

set_option maxHeartbeats 8000000 in
/-- **The special value with three single corners, the planes vertical.** `Q1`, `Q2`
(functionals `f1`, `f2`) contain the vertical line through `v`, and the third face `G`
contains `xa`, `xb` and the point `g` whose barycentric value in the view is 1. -/
theorem isRupert_special3_vertical (V Q1 Q2 G : Finset ℝ³) (v : ℝ³)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hGV : G ⊆ V) (hint : Q1 ∩ Q2 = {v})
    (f1 f2 fG : ℝ³ →ᵃ[ℝ] ℝ)
    (z1 : ∀ p ∈ Q1, f1 p = 0) (n1 : ∀ p ∈ V, p ∉ Q1 → f1 p < 0)
    (z2 : ∀ p ∈ Q2, f2 p = 0) (n2 : ∀ p ∈ V, p ∉ Q2 → f2 p < 0)
    (zG : ∀ p ∈ G, fG p = 0) (nG : ∀ p ∈ V, p ∉ G → fG p < 0)
    (e1 : f1 (v + ez) = 0) (e2 : f2 (v + ez) = 0)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (xa xb g m : ℝ³) (hxa : xa ∈ Q1) (hxb : xb ∈ Q2) (hxaG : xa ∈ G) (hxbG : xb ∈ G)
    (hgG : g ∈ G) (hxav : xa ≠ v) (hxbv : xb ≠ v) (hg1 : g ∉ Q1) (hg2 : g ∉ Q2)
    (hGm : ∀ p ∈ G, p = xa ∨ p = xb ∨ p = g)
    (hQm : (∀ p ∈ Q2, p = v ∨ p = xb ∨ p = m) ∨ (∀ p ∈ Q1, p = v ∨ p = xa ∨ p = m))
    (hgb : f2 g / f2 xa + f1 g / f1 xb = 1)
    (htri : ¬ (xa 2 = xb 2 ∧ v 2 = xa 2)) : IsRupert V := by
  classical
  have hv1 : v ∈ Q1 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).1
  have hv2 : v ∈ Q2 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).2
  have only : ∀ p ∈ Q1, p ∈ Q2 → p = v := by
    intro p h1 h2
    have : p ∈ Q1 ∩ Q2 := Finset.mem_inter.mpr ⟨h1, h2⟩
    rwa [hint, Finset.mem_singleton] at this
  have hxa2 : xa ∉ Q2 := fun h => hxav (only xa hxa h)
  have hxb1 : xb ∉ Q1 := fun h => hxbv (only xb h hxb)
  have m21 : f2 xa < 0 := n2 xa (h1V hxa) hxa2
  have m12 : f1 xb < 0 := n1 xb (h2V hxb) hxb1
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
  set r1 : ℝ² := !₂[xa 0 - v 0, xa 1 - v 1] with hr1
  set r2 : ℝ² := !₂[xb 0 - v 0, xb 1 - v 1] with hr2
  have q11 : α1 * (xa 0 - v 0) + β1 * (xa 1 - v 1) = 0 := by rw [← g1]; exact z1 xa hxa
  have q22 : α2 * (xb 0 - v 0) + β2 * (xb 1 - v 1) = 0 := by rw [← g2]; exact z2 xb hxb
  have hρ : cross2 r1 r2 ≠ 0 := by
    intro hρ0
    simp only [hr1, hr2, cross2] at hρ0
    simp at hρ0
    have k0 : f1 xb * (xa 0 - v 0) = 0 := by
      rw [g1]; linear_combination (xb 0 - v 0) * q11 + β1 * hρ0
    have k1 : f1 xb * (xa 1 - v 1) = 0 := by
      rw [g1]; linear_combination (xb 1 - v 1) * q11 - α1 * hρ0
    have r10 := (mul_eq_zero.mp k0).resolve_left m12.ne
    have r11 := (mul_eq_zero.mp k1).resolve_left m12.ne
    have := g2 xa; rw [r10, r11] at this; linarith
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
  have r10 : r1 0 = xa 0 - v 0 := by simp [hr1]
  have r11 : r1 1 = xa 1 - v 1 := by simp [hr1]
  have r20 : r2 0 = xb 0 - v 0 := by simp [hr2]
  have r21 : r2 1 = xb 1 - v 1 := by simp [hr2]
  have G1 : ∀ p, f1 p = b p * f1 xb := by
    intro p; rw [g1 p, g1 xb, (hxy p).1, (hxy p).2, r10, r11, r20, r21]
    linear_combination a p * q11
  have G2 : ∀ p, f2 p = a p * f2 xa := by
    intro p; rw [g2 p, g2 xa, (hxy p).1, (hxy p).2, r10, r11, r20, r21]
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
  have hAx : a xa = 1 := by
    have k : (a xa - 1) * f2 xa = 0 := by linear_combination -(G2 xa)
    linarith [(mul_eq_zero.mp k).resolve_right m21.ne]
  have hBx : b xb = 1 := by
    have k : (b xb - 1) * f1 xb = 0 := by linear_combination -(G1 xb)
    linarith [(mul_eq_zero.mp k).resolve_right m12.ne]
  have hbxa := hb1 xa hxa
  have haxb := ha2 xb hxb
  -- the point `g` on the far side
  have hgab : a g + b g = 1 := by
    rw [G2 g, G1 g, mul_div_assoc, mul_div_assoc, div_self m21.ne, div_self m12.ne] at hgb
    linarith
  -- the third face is vertical: `fG = fG v (1 - a - b)`
  obtain ⟨KG, αG, βG, γG, hG⟩ := affine_xyz fG
  have hgV := hGV hgG
  have hγG : γG = 0 := by
    have kg := zG g hgG; have ka := zG xa hxaG; have kb := zG xb hxbG
    rw [hG] at kg ka kb
    obtain ⟨c0, c1⟩ := hxy g
    rw [r10, r20] at c0; rw [r11, r21] at c1
    have hz : γG * (g 2 - a g * xa 2 - b g * xb 2) = 0 := by
      linear_combination kg - a g * ka - b g * kb - αG * c0 - βG * c1 +
        (KG + αG * v 0 + βG * v 1) * hgab
    rcases mul_eq_zero.mp hz with h | h
    · exact h
    · exfalso
      apply hcol xa (h1V hxa) xb (h2V hxb) g hgV (fun e => hxb1 (e ▸ hxa))
        (fun e => hg1 (e ▸ hxa)) (fun e => hg2 (e ▸ hxb)) (b g)
      have key := oblPt_sub_smul O r1 r2 (a1 := a xa) (b1 := b xa) (z1 := xa 2) (a2 := a xb)
        (b2 := b xb) (z2 := xb 2) (a3 := a g) (b3 := b g) (z3 := g 2) (t := b g)
        (by rw [hAx, haxb]; linarith) (by rw [hbxa, hBx]; ring) (by
          have : a g = 1 - b g := by linarith
          rw [this] at h; linarith)
      rw [← hy g, ← hy xa, ← hy xb] at key
      exact key
  have GG : ∀ p, fG p = fG v * (1 - a p - b p) := by
    intro p
    have ka := zG xa hxaG; have kb := zG xb hxbG
    rw [hG] at ka kb; rw [hG p, hG v]
    obtain ⟨c0, c1⟩ := hxy p
    rw [r10, r20] at c0; rw [r11, r21] at c1
    rw [hγG] at ka kb ⊢
    linear_combination αG * c0 + βG * c1 + a p * ka + b p * kb
  have hvG : v ∉ G := by
    intro h
    rcases hGm v h with h' | h' | h'
    · exact hxav h'.symm
    · exact hxbv h'.symm
    · exact hg1 (h' ▸ hv1)
  have hfv : fG v < 0 := nG v (h1V hv1) hvG
  have hG1 : ∀ p ∈ G, a p + b p = 1 := by
    intro p hp
    have := GG p; rw [zG p hp] at this
    have := (mul_eq_zero.mp this.symm).resolve_left hfv.ne
    linarith
  have hG1' : ∀ p ∈ V, p ∉ G → a p + b p < 1 := by
    intro p hp hpG
    have := nG p hp hpG; rw [GG p] at this
    nlinarith
  rcases lt_or_gt_of_ne hρ with hneg | hpos
  · have hpos' : 0 < cross2 r2 r1 := by
      have : cross2 r2 r1 = -cross2 r1 r2 := by unfold cross2; ring
      rw [this]; linarith
    have swap : ∀ p q z, oblPt O r2 r1 q p z = oblPt O r1 r2 p q z := by
      intro p q z; ext j; fin_cases j <;> simp [oblPt] <;> ring
    exact isRupert_special3_coords O r2 r1 hpos' V Q2 Q1 G v b a
      (fun p _ => by rw [swap]; exact hy p) h2V h1V hGV (by rw [Finset.inter_comm]; exact hint)
      ha2 ha2' hb1 hb1' (fun p hp => by rw [add_comm]; exact hG1 p hp)
      (fun p hp hpG => by rw [add_comm]; exact hG1' p hp hpG) hcol xb xa g m hxb hxa hxbG hxaG hgG
      hg2 hg1 (fun p hp => by rcases hGm p hp with h | h | h <;> simp [h]) hQm.symm
      (fun ⟨h1, h2⟩ => htri ⟨h1.symm, h2.trans h1⟩)
  · exact isRupert_special3_coords O r1 r2 hpos V Q1 Q2 G v a b (fun p _ => hy p) h1V h2V hGV
      hint hb1 hb1' ha2 ha2' hG1 hG1' hcol xa xb g m hxa hxb hxaG hxbG hgG hg1 hg2 hGm hQm htri

/-- The triple tie in the view along the line of the planes of `f1` and `f2` through `v`:
`v`, `xa`, `xb` at one depth. -/
def ViewTriple (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ) (v xa xb : ℝ³) : Prop :=
  ∃ e : ℝ³, e ≠ 0 ∧ f1 (v + e) = 0 ∧ f2 (v + e) = 0 ∧ ⟪xa, e⟫ = ⟪xb, e⟫ ∧ ⟪v, e⟫ = ⟪xa, e⟫

set_option maxHeartbeats 8000000 in
/-- **The special value with three single corners** (`FEWER-FACES-PROOFS.md` Theorems 23.18
and 24.13 for types 12, 22, 28, facet form). Facets `Q1`, `Q2` (functionals `f1`, `f2`)
meet in the single vertex `v`; the third facet `G` is the triangle `xa xb g` with
`xa ∈ Q1`, `xb ∈ Q2`, and `g` has barycentric value 1 in the view along the line of the
planes of `Q1`, `Q2` (Lemma T′'s special value); `Q2` has at most one vertex besides `v`,
`xb` (or `Q1` besides `v`, `xa`). Then `V` is Rupert unless `v`, `xa`, `xb` are at one
depth in that view. No condition on segments parallel to the view. -/
theorem isRupert_special3 (V Q1 Q2 G : Finset ℝ³) (v : ℝ³)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hGV : G ⊆ V) (hint : Q1 ∩ Q2 = {v})
    (f1 f2 fG : ℝ³ →ᵃ[ℝ] ℝ)
    (z1 : ∀ p ∈ Q1, f1 p = 0) (n1 : ∀ p ∈ V, p ∉ Q1 → f1 p < 0)
    (z2 : ∀ p ∈ Q2, f2 p = 0) (n2 : ∀ p ∈ V, p ∉ Q2 → f2 p < 0)
    (zG : ∀ p ∈ G, fG p = 0) (nG : ∀ p ∈ V, p ∉ G → fG p < 0)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (xa xb g m : ℝ³) (hxa : xa ∈ Q1) (hxb : xb ∈ Q2) (hxaG : xa ∈ G) (hxbG : xb ∈ G)
    (hgG : g ∈ G) (hxav : xa ≠ v) (hxbv : xb ≠ v) (hg1 : g ∉ Q1) (hg2 : g ∉ Q2)
    (hGm : ∀ p ∈ G, p = xa ∨ p = xb ∨ p = g)
    (hQm : (∀ p ∈ Q2, p = v ∨ p = xb ∨ p = m) ∨ (∀ p ∈ Q1, p = v ∨ p = xa ∨ p = m))
    (hgb : f2 g / f2 xa + f1 g / f1 xb = 1)
    (htri : ¬ ViewTriple f1 f2 v xa xb) : IsRupert V := by
  classical
  have hv1 : v ∈ Q1 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).1
  have hv2 : v ∈ Q2 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).2
  have only : ∀ p ∈ Q1, p ∈ Q2 → p = v := by
    intro p h1 h2
    have : p ∈ Q1 ∩ Q2 := Finset.mem_inter.mpr ⟨h1, h2⟩
    rwa [hint, Finset.mem_singleton] at this
  -- the line of the two planes
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
  have hxa2 : xa ∉ Q2 := fun h => hxav (only xa hxa h)
  have hxb1 : xb ∉ Q1 := fun h => hxbv (only xb h hxb)
  have hn1 : f1 xb < 0 := n1 xb (h2V hxb) hxb1
  have hn2 : f2 xa < 0 := n2 xa (h1V hxa) hxa2
  have hne : e ≠ 0 := by
    intro h0
    have c0 := congrArg (fun p : ℝ³ => p 0) h0
    have c1 := congrArg (fun p : ℝ³ => p 1) h0
    have c2 := congrArg (fun p : ℝ³ => p 2) h0
    simp [he] at c0 c1 c2
    have d14 := dif f1 K1 α1 β1 γ1 hf1 v xb
    have d21 := dif f2 K2 α2 β2 γ2 hf2 v xa
    have d11 := dif f1 K1 α1 β1 γ1 hf1 v xa
    rw [z1 v hv1, sub_zero] at d14
    rw [z1 v hv1, z1 xa hxa, sub_zero] at d11
    rw [z2 v hv2, sub_zero] at d21
    have key : (f1 xb) * (f2 xa) = 0 := by
      rw [d14, d21]
      have := d11
      linear_combination (α2 * (xb 0 - v 0) + β2 * (xb 1 - v 1) + γ2 * (xb 2 - v 2)) * this.symm +
        ((xa 1 - v 1) * (xb 0 - v 0) - (xa 0 - v 0) * (xb 1 - v 1)) * c2 +
        ((xa 2 - v 2) * (xb 1 - v 1) - (xa 1 - v 1) * (xb 2 - v 2)) * c0 +
        ((xa 0 - v 0) * (xb 2 - v 2) - (xa 2 - v 2) * (xb 0 - v 0)) * c1
    nlinarith
  -- rotate the line to the vertical
  obtain ⟨R, hR, r, hr, hRe⟩ := exists_rotation_to_ez_pos e hne
  apply isRupert_of_isRupert_image_rotation R hR
  set gr := R.toEuclideanLin with hgr
  set I := so3Isometry hR with hI
  have hgI : ∀ p, gr p = I p := fun p => rfl
  have hginj : Function.Injective gr := I.injective
  have hgz : ∀ p, gr p 2 = ⟪p, e⟫ / r := fun p => by
    have := inner_toEuclideanLin_SO3 hR p e
    rw [hRe, real_inner_smul_right, inner_ez] at this
    field_simp; linarith
  have hIe : I.symm ez = r⁻¹ • e := by
    apply I.injective
    rw [LinearIsometryEquiv.apply_symm_apply, map_smul, ← hgI, hRe, smul_smul,
      inv_mul_cancel₀ hr.ne', one_smul]
  set F1 := f1.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap with hF1
  set F2 := f2.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap with hF2
  set FG := fG.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap with hFG
  have tF1 : ∀ p, F1 (gr p) = f1 p := fun p => by simp [hF1, hgI]
  have tF2 : ∀ p, F2 (gr p) = f2 p := fun p => by simp [hF2, hgI]
  have tFG : ∀ p, FG (gr p) = fG p := fun p => by simp [hFG, hgI]
  have tz : ∀ f : ℝ³ →ᵃ[ℝ] ℝ, f v = 0 → f (v + e) = 0 →
      (f.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap) (gr v + ez) = 0 := by
    intro f h0 h1
    have : (f.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap) (gr v + ez) =
        f (v + r⁻¹ • e) := by
      simp [hgI, map_add, hIe]
    rw [this]; exact affine_zero_line f h0 h1 _
  have memg : ∀ (S : Finset ℝ³) p, gr p ∈ S.image gr ↔ p ∈ S := fun S p =>
    ⟨fun h => by obtain ⟨q, hq, e⟩ := Finset.mem_image.mp h; rwa [← hginj e],
      Finset.mem_image_of_mem gr⟩
  have allg : ∀ (S : Finset ℝ³) (P : ℝ³ → Prop), (∀ p ∈ S, P (gr p)) → ∀ q ∈ S.image gr, P q := by
    intro S P h q hq; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq; exact h p hp
  refine isRupert_special3_vertical (V.image gr) (Q1.image gr) (Q2.image gr) (G.image gr) (gr v)
    (Finset.image_subset_image h1V) (Finset.image_subset_image h2V)
    (Finset.image_subset_image hGV)
    (by rw [← Finset.image_inter _ _ hginj, hint, Finset.image_singleton]) F1 F2 FG
    (allg Q1 _ (fun p hp => by rw [tF1]; exact z1 p hp))
    (allg V _ (fun p hp hq => by rw [tF1]; exact n1 p hp (fun h => hq ((memg Q1 p).mpr h))))
    (allg Q2 _ (fun p hp => by rw [tF2]; exact z2 p hp))
    (allg V _ (fun p hp hq => by rw [tF2]; exact n2 p hp (fun h => hq ((memg Q2 p).mpr h))))
    (allg G _ (fun p hp => by rw [tFG]; exact zG p hp))
    (allg V _ (fun p hp hq => by rw [tFG]; exact nG p hp (fun h => hq ((memg G p).mpr h))))
    (tz f1 (z1 v hv1) e1) (tz f2 (z2 v hv2) e2) ?_ (gr xa) (gr xb) (gr g) (gr m)
    (Finset.mem_image_of_mem gr hxa) (Finset.mem_image_of_mem gr hxb)
    (Finset.mem_image_of_mem gr hxaG) (Finset.mem_image_of_mem gr hxbG)
    (Finset.mem_image_of_mem gr hgG) (fun h => hxav (hginj h)) (fun h => hxbv (hginj h))
    (fun h => hg1 ((memg Q1 g).mp h)) (fun h => hg2 ((memg Q2 g).mp h))
    (allg G _ (fun p hp => by rcases hGm p hp with rfl | rfl | rfl <;> simp)) ?_
    (by rw [tF1, tF1, tF2, tF2]; exact hgb) ?_
  · refine allg V _ (fun p hp => allg V _ (fun q hq => allg V _ (fun u hu => ?_)))
    intro hpq hpu hqu c h
    apply hcol p hp q hq u hu (fun e => hpq (by rw [e])) (fun e => hpu (by rw [e]))
      (fun e => hqu (by rw [e])) c
    apply hginj
    simp only [map_sub, map_smul] at h ⊢; exact h
  · rcases hQm with h | h
    · exact Or.inl (allg Q2 _ (fun p hp => by rcases h p hp with rfl | rfl | rfl <;> simp))
    · exact Or.inr (allg Q1 _ (fun p hp => by rcases h p hp with rfl | rfl | rfl <;> simp))
  · rw [hgz, hgz, hgz]
    rintro ⟨h1, h2⟩
    apply htri
    refine ⟨e, hne, e1, e2, ?_, ?_⟩
    · field_simp at h1; exact h1
    · field_simp at h2; exact h2

/-- **`isRupert_special3` for seven labelled points**: facets `A`, `B` meeting in `iv`, the
triangle `C = {ia, ib, ig}` with `ig` at barycentric value 1 in the view of `A`, `B`, at most
one more vertex `j` of `B` (or of `A`). Rupert unless `iv`, `ia`, `ib` tie in that view. -/
theorem isRupert_special3_index (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (hgen : NoThreeCollinear (univ.image x)) (A B C : Finset (Fin 7)) (fA fB fC : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ A → fA (x i) = 0) ∧ (i ∉ A → fA (x i) < 0))
    (hB : ∀ i, (i ∈ B → fB (x i) = 0) ∧ (i ∉ B → fB (x i) < 0))
    (hC : ∀ i, (i ∈ C → fC (x i) = 0) ∧ (i ∉ C → fC (x i) < 0))
    (iv ia ib ig j : Fin 7) (hAB : A ∩ B = {iv})
    (hia : ia ∈ A ∧ ia ∈ C ∧ ia ≠ iv) (hib : ib ∈ B ∧ ib ∈ C ∧ ib ≠ iv)
    (hig : ig ∈ C ∧ ig ∉ A ∧ ig ∉ B) (hCm : ∀ i ∈ C, i = ia ∨ i = ib ∨ i = ig)
    (hm : (∀ i ∈ B, i = iv ∨ i = ib ∨ i = j) ∨ (∀ i ∈ A, i = iv ∨ i = ia ∨ i = j))
    (hgb : fB (x ig) / fB (x ia) + fA (x ig) / fA (x ib) = 1)
    (htri : ¬ ViewTriple fA fB (x iv) (x ia) (x ib)) : IsRupert (univ.image x) := by
  classical
  have memQ : ∀ (P : Finset (Fin 7)) i, x i ∈ P.image x ↔ i ∈ P := fun P i => hx.mem_finset_image
  have sub : ∀ P : Finset (Fin 7), P.image x ⊆ univ.image x := fun P =>
    Finset.image_subset_image (Finset.subset_univ P)
  refine isRupert_special3 (univ.image x) (A.image x) (B.image x) (C.image x) (x iv) (sub A) (sub B)
    (sub C) (by rw [← Finset.image_inter A B hx, hAB, Finset.image_singleton])
    fA fB fC (facet_zero_of_index hA) (facet_neg_of_index hA) (facet_zero_of_index hB)
    (facet_neg_of_index hB) (facet_zero_of_index hC) (facet_neg_of_index hC) hgen
    (x ia) (x ib) (x ig) (x j) ((memQ A ia).mpr hia.1) ((memQ B ib).mpr hib.1)
    ((memQ C ia).mpr hia.2.1) ((memQ C ib).mpr hib.2.1) ((memQ C ig).mpr hig.1)
    (fun h => hia.2.2 (hx h)) (fun h => hib.2.2 (hx h))
    (fun h => hig.2.1 ((memQ A ig).mp h)) (fun h => hig.2.2 ((memQ B ig).mp h)) ?_ ?_ hgb htri
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    rcases hCm i hi with rfl | rfl | rfl <;> simp
  · rcases hm with h | h
    · left; intro p hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      rcases h i hi with rfl | rfl | rfl <;> simp
    · right; intro p hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      rcases h i hi with rfl | rfl | rfl <;> simp

end Minimality

end
