module

public import Minimality.Type24
public import Minimality.Type24Corner

@[expose] public section

/-!
# Type 24: the quad triangles (Proposition 20.31)

`FEWER-FACES-PROOFS.md` §20, continued (5), §50 (subagent cu16 and its referee, 2026-10-22):
**Proposition 20.31 (quad triangles)**.

Part (a), the crossing rule, in the form the Rupert certificate needs.  Two faces `F₁`, `F₂`
share exactly the vertex `x`, `V = F₁ ∪ F₂ ∪ {y}`; the view `u` is parallel to both faces.  The
faces project onto the sides `[P x, P f₁]`, `[P x, P f₂]` (`f₁`, `f₂` the far ends; the other
vertices of the faces are the *middles*, over the open sides), so the rim is `(x, f₁, y, f₂)`
if `y` is a corner of the shadow and the triangle `(x, f₁, f₂)` otherwise.

* **`exists_hull_gt`** (the hidden-vertex step): if the polytope `K = conv V` is the intersection
  of the facet half-spaces `f i ≤ 0` (`hK`), and `y` is a vertex whose active facets all have
  `N i · w < 0` for one direction `w`, then for every `μ ≠ 0` with `μ · w = 0` the hull has a
  point with `μ · z > μ · y`: `y` is not on the boundary of the shadow along `w`.
* **`triHidden_of_facets`** (the paper's "`y` is hidden iff the numbers `n_f · d` of the faces at
  `y` are all of one strict sign", the direction used): `y` is strictly inside the shadow
  triangle `(p, q, r)`.
* **`isRupert_quadTriangle_of_facets`** (the crossing rule, hidden `y` ⇒ triangle rim ⇒ Rupert):
  with the triangle `(p, q, r)` of distinct depths and every other point a middle over an open
  side, `V` is Rupert unless the triangle has a horizontal double normal at the view
  (`isRupert_vertexTri` = Proposition 8.8 with Theorem 7.3).

The facets enter through functionals `f i` with linear parts `N i` (`Face16` style), and the
hypothesis `hK` that these are *all* the facets (`K` is the intersection of the half-spaces).
This is the paper's tacit "the faces of the polytope are the listed ones"; it is not derivable
from fewer faces.

Part (b), the three type-24 instances (`Q = 0345`, `G = 235`, `H = 346` the three facets beyond
`Type24`; `ω3 > 0`; `w · d0 = ⟪N_Q, viewT62⟫` and `w · d_h = ⟪N_Q, viewT26⟫` up to the
positive factor `−f_Q(x 1)`):

* **`isRupert_type24_quad016`** (`016/0345`, `y = 2`): `w · d0 < 0`.  The faces at `2` have
  `N_f · d < 0` for `012, 126, 236, 025` (`qView6_signs`), and for `235` off special position
  (`inner_235_neg`: `N_235 · d ≠ 0` and `P0 ∉ {P3, P5}`, through two functionals `≥ 0` on `K`).
* **`isRupert_type24_quad012`** (`012/0345`, `y = 6`): `w · d_h < 0`, the mirror
  (`qView2_signs`, `inner_346_neg`).
* **`isRupert_type24_quad236`** (`236/0345`, `y = 1`): `(w · d0)(w · d_h) < 0`; the faces at
  `1` are the cap faces (`qView3`).
* The converse directions of Proposition 20.31 (if `w · d0 > 0`, `2` is a corner) and part (i)
  are not formalized.

The rim data (the far ends and that the other vertices of the faces are middles over the open
sides) and `hK` are hypotheses; the special positions are `N_235 · d ≠ 0`, `N_346 · d ≠ 0`, the
non-collinear triangle, distinct corner depths, and `NoHDNAt` of the triangle.
-/

namespace Minimality

open Finset Filter
open scoped RealInnerProductSpace Topology

/-! ### The hidden-vertex step -/

/-- **A vertex whose active facets all face away from `w` is not on the shadow boundary along
`w`.**  `K = conv V` is the intersection of the half-spaces `f i ≤ 0` (`hK`).  If every facet
`i` through `y` has `⟪N i, w⟫ < 0`, then for every `μ ≠ 0` with `⟪μ, w⟫ = 0` the hull contains a
point `z = y + ε (μ + L w)` with `⟪μ, z⟫ > ⟪μ, y⟫`. -/
theorem exists_hull_gt {ι : Type*} [Fintype ι] (f : ι → ℝ³ → ℝ) (N : ι → ℝ³)
    (hN : ∀ i a b, f i a - f i b = ⟪N i, a - b⟫) (V : Finset ℝ³)
    (hK : ∀ z, (∀ i, f i z ≤ 0) → z ∈ convexHull ℝ (V : Set ℝ³)) {y w : ℝ³}
    (hyf : ∀ i, f i y ≤ 0) (hw : ∀ i, f i y = 0 → ⟪N i, w⟫ < 0) {μ : ℝ³} (hμ : μ ≠ 0)
    (hμw : ⟪μ, w⟫ = 0) : ∃ z ∈ convexHull ℝ (V : Set ℝ³), ⟪μ, y⟫ < ⟪μ, z⟫ := by
  classical
  set L : ℝ := ∑ i, |⟪N i, μ⟫| / |⟪N i, w⟫| with hL
  set v : ℝ³ := μ + L • w with hv
  have hfv : ∀ i (ε : ℝ), f i (y + ε • v) = f i y + ε * ⟪N i, v⟫ := by
    intro i ε
    have := hN i (y + ε • v) y
    rw [add_sub_cancel_left, inner_smul_right] at this
    linarith
  have hact : ∀ i, f i y = 0 → ⟪N i, v⟫ ≤ 0 := by
    intro i hi
    have hneg := hw i hi
    have hle : |⟪N i, μ⟫| / |⟪N i, w⟫| ≤ L :=
      Finset.single_le_sum (f := fun j => |⟪N j, μ⟫| / |⟪N j, w⟫|)
        (fun j _ => by positivity) (Finset.mem_univ i)
    have habs : |⟪N i, w⟫| = -⟪N i, w⟫ := abs_of_neg hneg
    have hpos : 0 < |⟪N i, w⟫| := by rw [habs]; linarith
    rw [div_le_iff₀ hpos] at hle
    have : ⟪N i, v⟫ = ⟪N i, μ⟫ + L * ⟪N i, w⟫ := by
      rw [hv, inner_add_right, inner_smul_right]
    rw [this]
    rw [habs] at hle
    have := le_abs_self ⟪N i, μ⟫
    linarith
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i, f i (y + ε • v) ≤ 0 := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : f i y = 0
    · refine hpos.mono fun ε he => ?_
      rw [hfv, hi, zero_add]
      nlinarith [hact i hi]
    · have hneg : f i y < 0 := lt_of_le_of_ne (hyf i) hi
      have ht : Tendsto (fun ε : ℝ => f i y + ε * ⟪N i, v⟫) (𝓝 0) (𝓝 (f i y)) := by
        have : Continuous fun ε : ℝ => f i y + ε * ⟪N i, v⟫ := by fun_prop
        simpa using this.tendsto 0
      exact ((ht.eventually_lt_const hneg).filter_mono nhdsWithin_le_nhds).mono fun ε h => by
        rw [hfv]; exact h.le
  obtain ⟨ε, hε, hεpos⟩ := (hev.and hpos).exists
  refine ⟨y + ε • v, hK _ hε, ?_⟩
  rw [inner_add_right, inner_smul_right, hv, inner_add_right, inner_smul_right, hμw]
  have : 0 < ⟪μ, μ⟫ := real_inner_self_pos.mpr hμ
  nlinarith

/-! ### A hidden vertex is strictly inside the triangle -/

/-- A *middle* of the triangle `(p, q, r)` at the view `u`: a point over an open side, at a
nonzero depth offset (the vertices of the two faces other than the common vertex and the far
ends). -/
def QuadMid (u p q r m : ℝ³) : Prop :=
  ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
    (m = p + s • (q - p) + δ • u ∨ m = q + s • (r - q) + δ • u ∨ m = r + s • (p - r) + δ • u)

/-- A functional `μ ⊥ u` bounded by `c` on the corners is bounded by `c` on the middles. -/
theorem QuadMid.inner_le {u p q r m μ : ℝ³} (h : QuadMid u p q r m) (hμu : ⟪μ, u⟫ = 0) {c : ℝ}
    (hp : ⟪μ, p⟫ ≤ c) (hq : ⟪μ, q⟫ ≤ c) (hr : ⟪μ, r⟫ ≤ c) : ⟪μ, m⟫ ≤ c := by
  obtain ⟨s, δ, hs0, hs1, -, h | h | h⟩ := h <;>
  · simp only [h, inner_add_right, inner_smul_right, inner_sub_right, hμu]
    nlinarith

/-- The outward edge functional of the edge `a → b` of a counterclockwise triangle. -/
theorem edge_vals {u a b c : ℝ³} (hdet : 0 < det3 (b - a) (c - a) u) :
    ⟪-(cross u (b - a)), b⟫ = ⟪-(cross u (b - a)), a⟫ ∧
      ⟪-(cross u (b - a)), c⟫ < ⟪-(cross u (b - a)), a⟫ := by
  have h1 : ⟪cross u (b - a), b - a⟫ = 0 := inner_cross_right _ _
  have h2 := det3_eq_inner_cross (b - a) (c - a) u
  rw [h2] at hdet
  simp only [inner_neg_left, inner_sub_right] at h1 hdet ⊢
  constructor <;> linarith

theorem edge_hidden {ι : Type*} [Fintype ι] (f : ι → ℝ³ → ℝ) (N : ι → ℝ³)
    (hN : ∀ i a b, f i a - f i b = ⟪N i, a - b⟫) (V : Finset ℝ³)
    (hK : ∀ z, (∀ i, f i z ≤ 0) → z ∈ convexHull ℝ (V : Set ℝ³)) {y u : ℝ³}
    (hyf : ∀ i, f i y ≤ 0)
    (hw : ∃ w, (w = u ∨ w = -u) ∧ ∀ i, f i y = 0 → ⟪N i, w⟫ < 0) {a b c : ℝ³}
    (hdet : 0 < det3 (b - a) (c - a) u)
    (hmax : ∀ v ∈ V, v ≠ y → ⟪-(cross u (b - a)), v⟫ ≤ ⟪-(cross u (b - a)), a⟫) :
    0 < det3 (b - a) (y - a) u := by
  set μ : ℝ³ := -(cross u (b - a)) with hμdef
  have hμu : ⟪μ, u⟫ = 0 := by rw [hμdef, inner_neg_left, inner_cross_left, neg_zero]
  have hμ0 : μ ≠ 0 := by
    intro h0
    have h2 := det3_eq_inner_cross (b - a) (c - a) u
    rw [h2] at hdet
    have : cross u (b - a) = 0 := by rw [hμdef] at h0; exact neg_eq_zero.mp h0
    rw [this, inner_zero_left] at hdet
    exact lt_irrefl _ hdet
  obtain ⟨w, hwu, hwN⟩ := hw
  have hμw : ⟪μ, w⟫ = 0 := by
    rcases hwu with rfl | rfl
    · exact hμu
    · rw [inner_neg_right, hμu, neg_zero]
  have hdy : det3 (b - a) (y - a) u = -⟪μ, y - a⟫ := by
    rw [det3_eq_inner_cross, hμdef, inner_neg_left, neg_neg]
  rw [hdy]
  by_contra hcon
  have hya : ⟪μ, a⟫ ≤ ⟪μ, y⟫ := by
    rw [inner_sub_right] at hcon; linarith
  have hbd : ∀ v ∈ V, ⟪μ, v⟫ ≤ ⟪μ, y⟫ := by
    intro v hv
    by_cases hvy : v = y
    · rw [hvy]
    · exact (hmax v hv hvy).trans hya
  have hconv : Convex ℝ {z : ℝ³ | ⟪μ, z⟫ ≤ ⟪μ, y⟫} :=
    convex_halfSpace_le (innerSL ℝ μ).toLinearMap.isLinear _
  have hsub : convexHull ℝ (V : Set ℝ³) ⊆ {z : ℝ³ | ⟪μ, z⟫ ≤ ⟪μ, y⟫} :=
    convexHull_min (fun v hv => hbd v hv) hconv
  obtain ⟨z, hz, hlt⟩ := exists_hull_gt f N hN V hK hyf hwN hμ0 hμw
  exact absurd (hsub hz) (not_le.mpr hlt)

/-- **Proposition 20.31, the crossing rule: a hidden `y` lies strictly inside the triangle.**
The triangle `(p, q, r)` is counterclockwise at the view `u` (`det3 (q − p) (r − p) u > 0`);
every point of `V` is `y`, a corner or a middle over an open side; `K = conv V` is the
intersection of the facet half-spaces `f i ≤ 0`; and the facets through `y` have the numbers
`N i · u` all of one strict sign (all `< 0` or all `> 0`).  Then `y` is strictly inside the
shadow triangle (`TriHidden`). -/
theorem triHidden_of_facets {ι : Type*} [Fintype ι] (f : ι → ℝ³ → ℝ) (N : ι → ℝ³)
    (hN : ∀ i a b, f i a - f i b = ⟪N i, a - b⟫) (V : Finset ℝ³)
    (hK : ∀ z, (∀ i, f i z ≤ 0) → z ∈ convexHull ℝ (V : Set ℝ³)) {y u p q r : ℝ³}
    (hyf : ∀ i, f i y ≤ 0)
    (hsign : (∀ i, f i y = 0 → ⟪N i, u⟫ < 0) ∨ (∀ i, f i y = 0 → 0 < ⟪N i, u⟫))
    (hT : 0 < det3 (q - p) (r - p) u)
    (hcover : ∀ z ∈ V, z = y ∨ z = p ∨ z = q ∨ z = r ∨ QuadMid u p q r z) :
    TriHidden u p q r y := by
  have hw : ∃ w, (w = u ∨ w = -u) ∧ ∀ i, f i y = 0 → ⟪N i, w⟫ < 0 := by
    rcases hsign with h | h
    · exact ⟨u, Or.inl rfl, h⟩
    · exact ⟨-u, Or.inr rfl, fun i hi => by rw [inner_neg_right]; linarith [h i hi]⟩
  have i1 : det3 (r - q) (p - q) u = det3 (q - p) (r - p) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i2 : det3 (p - r) (q - r) u = det3 (q - p) (r - p) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have hμ : ∀ {a b c : ℝ³}, 0 < det3 (b - a) (c - a) u →
      (∀ v ∈ V, v ≠ y → v = p ∨ v = q ∨ v = r ∨ QuadMid u p q r v) → 
      ⟪-(cross u (b - a)), p⟫ ≤ ⟪-(cross u (b - a)), a⟫ →
      ⟪-(cross u (b - a)), q⟫ ≤ ⟪-(cross u (b - a)), a⟫ →
      ⟪-(cross u (b - a)), r⟫ ≤ ⟪-(cross u (b - a)), a⟫ →
      0 < det3 (b - a) (y - a) u := by
    intro a b c hdet hc hp hq hr
    refine edge_hidden f N hN V hK hyf hw hdet fun v hv hvy => ?_
    have hμu : ⟪-(cross u (b - a)), u⟫ = 0 := by
      rw [inner_neg_left, inner_cross_left, neg_zero]
    rcases hc v hv hvy with rfl | rfl | rfl | hm
    exacts [hp, hq, hr, hm.inner_le hμu hp hq hr]
  have hc : ∀ v ∈ V, v ≠ y → v = p ∨ v = q ∨ v = r ∨ QuadMid u p q r v := by
    intro v hv hvy
    rcases hcover v hv with h | h
    · exact absurd h hvy
    · exact h
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨e1, e2⟩ := edge_vals hT
    exact hμ hT hc le_rfl e1.le e2.le
  · obtain ⟨e1, e2⟩ := edge_vals (a := q) (b := r) (c := p) (by rw [i1]; exact hT)
    exact hμ (a := q) (b := r) (c := p) (by rw [i1]; exact hT) hc e2.le le_rfl e1.le
  · obtain ⟨e1, e2⟩ := edge_vals (a := r) (b := p) (c := q) (by rw [i2]; exact hT)
    exact hμ (a := r) (b := p) (c := q) (by rw [i2]; exact hT) hc e1.le e2.le le_rfl

/-! ### The crossing rule: triangle rim ⇒ Rupert -/

/-- **Proposition 20.31, the crossing rule (counterclockwise form).**  The triangle
`(p, q, r)` of points of `V` is counterclockwise at the view `u`, with distinct depths; every
other point of `V` is `y` or a middle over an open side; `K = conv V` is the intersection of
the facet half-spaces `f i ≤ 0`, and the facets through `y` have `N i · u` of one strict sign
(so `y` is hidden).  Then the rim is the triangle, which is unimodal, and `V` is Rupert unless
the triangle has a horizontal double normal at the view (`isRupert_vertexTri`). -/
theorem isRupert_quadTriangle_ccw {ι : Type*} [Fintype ι] (f : ι → ℝ³ → ℝ) (N : ι → ℝ³)
    (hN : ∀ i a b, f i a - f i b = ⟪N i, a - b⟫) (V : Finset ℝ³)
    (hK : ∀ z, (∀ i, f i z ≤ 0) → z ∈ convexHull ℝ (V : Set ℝ³)) {y u p q r : ℝ³}
    (hpV : p ∈ V) (hqV : q ∈ V) (hrV : r ∈ V) (hyf : ∀ i, f i y ≤ 0)
    (hsign : (∀ i, f i y = 0 → ⟪N i, u⟫ < 0) ∨ (∀ i, f i y = 0 → 0 < ⟪N i, u⟫))
    (hT : 0 < det3 (q - p) (r - p) u)
    (hz : [⟪p, u⟫, ⟪q, u⟫, ⟪r, u⟫].Nodup)
    (hcover : ∀ z ∈ V, z = y ∨ z = p ∨ z = q ∨ z = r ∨ QuadMid u p q r z)
    (hnd : NoHDNAt {p, q, r} u) : IsRupert V := by
  classical
  have hH := triHidden_of_facets f N hN V hK hyf hsign hT hcover
  refine isRupert_vertexTri V (V.filter fun m => m ≠ p ∧ m ≠ q ∧ m ≠ r ∧ QuadMid u p q r m)
    u hpV hqV hrV ?_ ?_ ?_ hT hz ?_ ?_ hnd
  · simp
  · simp
  · simp
  · intro z hz' hzM hzp hzq hzr
    rcases hcover z hz' with rfl | h | h | h | h
    · exact hH
    · exact absurd h hzp
    · exact absurd h hzq
    · exact absurd h hzr
    · exact absurd (Finset.mem_filter.mpr ⟨hz', hzp, hzq, hzr, h⟩) hzM
  · intro m hm
    obtain ⟨-, -, -, -, s, δ, hs0, hs1, hδ, h⟩ := Finset.mem_filter.mp hm
    exact ⟨s, δ, hs0, hs1, hδ, h⟩

/-- A point over an open side of the two far-end sides `[x, f₁]`, `[x, f₂]` of the triangle
`(x, f₁, f₂)` (the vertices of the faces `F₁`, `F₂` at `x` other than `x` and the far ends):
it lies over `x + s (f_i − x)`, `0 < s < 1`, at a nonzero depth offset. -/
def QuadSide (u x f₁ f₂ m : ℝ³) : Prop :=
  ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
    (m = x + s • (f₁ - x) + δ • u ∨ m = x + s • (f₂ - x) + δ • u)

theorem QuadSide.mid_ccw {u x f₁ f₂ m : ℝ³} (h : QuadSide u x f₁ f₂ m) :
    QuadMid u x f₁ f₂ m := by
  obtain ⟨s, δ, hs0, hs1, hδ, h | h⟩ := h
  · exact ⟨s, δ, hs0, hs1, hδ, Or.inl h⟩
  · refine ⟨1 - s, δ, by linarith, by linarith, hδ, Or.inr (Or.inr ?_)⟩
    rw [h]; module

theorem QuadSide.mid_cw {u x f₁ f₂ m : ℝ³} (h : QuadSide u x f₁ f₂ m) :
    QuadMid u x f₂ f₁ m := by
  obtain ⟨s, δ, hs0, hs1, hδ, h | h⟩ := h
  · refine ⟨1 - s, δ, by linarith, by linarith, hδ, Or.inr (Or.inr ?_)⟩
    rw [h]; module
  · exact ⟨s, δ, hs0, hs1, hδ, Or.inl h⟩

/-- **Proposition 20.31, the crossing rule.**  Two faces `F₁`, `F₂` of the polytope `K = conv V`
meet in exactly the vertex `x`; `V = F₁ ∪ F₂ ∪ {y}`; the view `u` is parallel to both faces, whose
far ends are `f₁`, `f₂` and whose other vertices are middles over the open sides `[x, f_i]`
(`QuadSide`: nonzero depth offset, `0 < s < 1`).  The facets of `K` are `f i ≤ 0` (`hK`: `K` is
their intersection).  If the numbers `N i · u` of the facets through `y` are all of one strict
sign, then `y` is hidden, the rim is the triangle `(x, f₁, f₂)`, and `V` is Rupert, unless
the corner depths coincide, `x, f₁, f₂` project to collinear points (`det3 = 0`: special
position), or the triangle has a horizontal double normal at the view. -/
theorem isRupert_quadTriangle {ι : Type*} [Fintype ι] (f : ι → ℝ³ → ℝ) (N : ι → ℝ³)
    (hN : ∀ i a b, f i a - f i b = ⟪N i, a - b⟫) (V : Finset ℝ³)
    (hK : ∀ z, (∀ i, f i z ≤ 0) → z ∈ convexHull ℝ (V : Set ℝ³)) {y u x f₁ f₂ : ℝ³}
    (hxV : x ∈ V) (h1V : f₁ ∈ V) (h2V : f₂ ∈ V) (hyf : ∀ i, f i y ≤ 0)
    (hsign : (∀ i, f i y = 0 → ⟪N i, u⟫ < 0) ∨ (∀ i, f i y = 0 → 0 < ⟪N i, u⟫))
    (hdet : det3 (f₁ - x) (f₂ - x) u ≠ 0)
    (hd12 : ⟪x, u⟫ ≠ ⟪f₁, u⟫) (hd1x : ⟪x, u⟫ ≠ ⟪f₂, u⟫) (hd2 : ⟪f₁, u⟫ ≠ ⟪f₂, u⟫)
    (hcover : ∀ z ∈ V, z = y ∨ z = x ∨ z = f₁ ∨ z = f₂ ∨ QuadSide u x f₁ f₂ z)
    (hnd : NoHDNAt {x, f₁, f₂} u) : IsRupert V := by
  rcases lt_or_gt_of_ne hdet with hneg | hpos
  · -- clockwise: use the triangle `(x, f₂, f₁)`
    have hT : 0 < det3 (f₂ - x) (f₁ - x) u := by
      have : det3 (f₂ - x) (f₁ - x) u = -det3 (f₁ - x) (f₂ - x) u := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      linarith
    refine isRupert_quadTriangle_ccw f N hN V hK hxV h2V h1V hyf hsign hT ?_
      (fun z hz => ?_) ?_
    · exact nodup3.mpr ⟨hd1x, hd12, fun h => hd2 h.symm⟩
    · rcases hcover z hz with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h.mid_cw)))
    · have : ({x, f₂, f₁} : Finset ℝ³) = {x, f₁, f₂} := by
        ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
      rw [this]; exact hnd
  · refine isRupert_quadTriangle_ccw f N hN V hK hxV h1V h2V hyf hsign hpos ?_
      (fun z hz => ?_) hnd
    · exact nodup3.mpr ⟨hd12, hd1x, hd2⟩
    · rcases hcover z hz with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h.mid_ccw)))

/-! ### Type 24: the crossing 016/0345 (hidden vertex `2`) -/

/-- The face value over a point `x₀ + s (x_b − x₀) + δ u`: the functional is affine, and the
view contributes `δ ⟪N, u⟫`. -/
theorem Face16.f_over {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (F : Face16 x S) {z x₀ x_b u : ℝ³}
    {s δ : ℝ} (h : z = x₀ + s • (x_b - x₀) + δ • u) :
    F.f z = F.f x₀ + s * (F.f x_b - F.f x₀) + δ * ⟪F.N, u⟫ := by
  have h1 := F.hN z x₀
  have h2 := F.hN x_b x₀
  have : z - x₀ = s • (x_b - x₀) + δ • u := by rw [h]; abel
  rw [this, inner_add_right, inner_smul_right, inner_smul_right, ← h2] at h1
  linarith

/-- **The far end is on both faces** (the algebra of the special-position step of the
proof of Proposition 20.31, `016/0345`): if `β > 0` and `α < 0` and two nonpositive values
`d, g` at the far end of a point `d = 0 = g` over `[x₀, x_b]` at `0 < s ≤ 1` come from the
functionals `-β D + α G`, both vanish at `x_b`. -/
theorem far_zero {β α d0 db g0 gb s : ℝ} (hβ : 0 < β) (hα : α < 0) (hd0 : d0 ≤ 0)
    (hdb : db ≤ 0) (hg0 : g0 ≤ 0) (hgb : gb ≤ 0) (hs : 0 < s) (hs1 : s ≤ 1)
    (h : -β * ((1 - s) * d0 + s * db) + α * ((1 - s) * g0 + s * gb) = 0) : db = 0 ∧ gb = 0 := by
  have t1 : 0 ≤ (1 - s) * (-β * d0) := mul_nonneg (by linarith) (by nlinarith)
  have t2 : 0 ≤ s * (-β * db) := mul_nonneg hs.le (by nlinarith)
  have t3 : 0 ≤ (1 - s) * (α * g0) := mul_nonneg (by linarith) (by nlinarith)
  have t4 : 0 ≤ s * (α * gb) := mul_nonneg hs.le (by nlinarith)
  have e2 : s * (-β * db) = 0 := by nlinarith
  have e4 : s * (α * gb) = 0 := by nlinarith
  have : db = 0 := by
    rcases mul_eq_zero.mp e2 with h' | h'
    · exact absurd h' hs.ne'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · linarith
      · exact h''
  have : gb = 0 := by
    rcases mul_eq_zero.mp e4 with h' | h'
    · exact absurd h' hs.ne'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · linarith
      · exact h''
  exact ⟨by assumption, by assumption⟩

namespace Type24

variable {x : Fin 7 → ℝ³} (T : Type24 x)
include T

/-- The apex `3` fixes `ω3`: `f₂₃₆(x 0) − f₂₃₆(x 1) = ω3 f₂₃₆(x 1)`. -/
theorem D0 : T.t236.f (x 0) - T.t236.f (x 1) = omega3 x * T.t236.f (x 1) := by
  have e3 := T.eval T.t236 3
  rw [T.t236.zero 2 (by decide), T.t236.zero 6 (by decide)] at e3
  rw [T.t236.zero 3 (by decide)] at e3
  have h3 := T.eq3
  have hX := T.X0_pos (v := 3) (by decide)
  have k : (T.t236.f (x 0) - T.t236.f (x 1) - omega3 x * T.t236.f (x 1)) * oblX0 x 3 = 0 := by
    linear_combination -e3 + T.t236.f (x 1) * h3
  rcases mul_eq_zero.mp k with h | h
  · linarith
  · exact absurd h hX.ne'

/-- The apex `5` fixes `ω5`: `f₀₂₅(x 6) − f₀₂₅(x 1) = ω5 f₀₂₅(x 1)`. -/
theorem F6 : T.t025.f (x 6) - T.t025.f (x 1) = omega5 x * T.t025.f (x 1) := by
  have e5 := T.eval T.t025 5
  rw [T.t025.zero 0 (by decide), T.t025.zero 2 (by decide)] at e5
  rw [T.t025.zero 5 (by decide)] at e5
  have h5 := T.eq5
  have hX := T.X6_pos (v := 5) (by decide)
  have k : (T.t025.f (x 6) - T.t025.f (x 1) - omega5 x * T.t025.f (x 1)) * oblX6 x 5 = 0 := by
    linear_combination -e5 + T.t025.f (x 1) * h5
  rcases mul_eq_zero.mp k with h | h
  · linarith
  · exact absurd h hX.ne'

end Type24

/-- The view of the crossing `016/0345`: parallel to `016` and to the quad `0345`,
`(f_Q(x 1) − f_Q(x 6)) (x 0 − x 1) − f_Q(x 1) (x 6 − x 1)`; in the oblique coordinates of §15
this is a positive multiple of `(1, 0, −1/w_c)` when `w_c < 0` (§50). -/
noncomputable def qView6 {x : Fin 7 → ℝ³} (Q : Face16 x {0, 3, 4, 5}) : ℝ³ :=
  (Q.f (x 1) - Q.f (x 6)) • (x 0 - x 1) + (-Q.f (x 1)) • (x 6 - x 1)

theorem Face16.inner_qView6 {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (Q : Face16 x {0, 3, 4, 5})
    (F : Face16 x S) :
    ⟪F.N, qView6 Q⟫ = (Q.f (x 1) - Q.f (x 6)) * (F.f (x 0) - F.f (x 1)) +
      (-Q.f (x 1)) * (F.f (x 6) - F.f (x 1)) := by
  rw [qView6, inner_add_right, inner_smul_right, inner_smul_right, ← F.hN, ← F.hN]

theorem inner_qView6_Q {x : Fin 7 → ℝ³} (Q : Face16 x {0, 3, 4, 5}) : ⟪Q.N, qView6 Q⟫ = 0 := by
  rw [Face16.inner_qView6, Q.zero 0 (by decide)]
  ring

/-- The quad covector against the view `d0` of `T′(6,2)`: `w · d0 = 1 + ω3 w_c`, up to the
positive factor `−f_Q(x 1)`. -/
theorem inner_viewT62 {x : Fin 7 → ℝ³} (Q : Face16 x {0, 3, 4, 5}) :
    ⟪Q.N, viewT62 x⟫ = (-Q.f (x 1)) + omega3 x * (Q.f (x 6) - Q.f (x 1)) := by
  rw [viewT62, inner_add_right, inner_smul_right, ← Q.hN, ← Q.hN, Q.zero 0 (by decide)]
  ring

/-- **The numbers `N_f · d` of the faces at `2` for the crossing `016/0345`**: the four faces
`012`, `126`, `236`, `025` at the vertex `2` face away from the view `qView6` exactly when
the quad faces away from `d0` (`w · d0 < 0`, with `ω3 > 0`); the fifth face `235` is treated by
`inner_235_neg`.  The paper's "first four numbers" of the proof of Proposition 20.31. -/
theorem qView6_signs {x : Fin 7 → ℝ³} (T : Type24 x) (Q : Face16 x {0, 3, 4, 5})
    (hω3 : 0 < omega3 x) (hw : ⟪Q.N, viewT62 x⟫ < 0) :
    ⟪T.t012.N, qView6 Q⟫ < 0 ∧ ⟪T.t126.N, qView6 Q⟫ < 0 ∧ ⟪T.t236.N, qView6 Q⟫ < 0 ∧
      ⟪T.t025.N, qView6 Q⟫ < 0 := by
  rw [inner_viewT62] at hw
  have hκ : 0 < -Q.f (x 1) := by linarith [Q.neg 1 (by decide)]
  have hl6 : Q.f (x 6) - Q.f (x 1) < 0 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hl6' : 0 < Q.f (x 1) - Q.f (x 6) := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Face16.inner_qView6, T.t012.zero 0 (by decide), T.t012.zero 1 (by decide)]
    have := T.t012.neg 6 (by decide)
    nlinarith
  · rw [Face16.inner_qView6, T.t126.zero 1 (by decide), T.t126.zero 6 (by decide)]
    have := T.t126.neg 0 (by decide)
    nlinarith
  · rw [Face16.inner_qView6, T.t236.zero 6 (by decide)]
    have h0 := T.D0
    have h1 := T.t236.neg 1 (by decide)
    nlinarith
  · rw [Face16.inner_qView6, T.t025.zero 0 (by decide)]
    have h6 := T.F6
    have h1 := T.t025.neg 1 (by decide)
    -- `λ6 + κ ω5 > 0` from the vertex `5` on the quad and on `025`
    have e := T.eval Q 5
    rw [Q.zero 5 (by decide), Q.zero 0 (by decide)] at e
    have e5 := T.eq5
    have hb := T.X2_pos (v := 5) (by decide)
    have hc := T.X6_pos (v := 5) (by decide)
    have h2 := Q.neg 2 (by decide)
    have key : 0 < omega5 x * (-Q.f (x 1)) + (Q.f (x 6) - Q.f (x 1)) := by
      have hprod : oblX6 x 5 * (omega5 x * (-Q.f (x 1)) + (Q.f (x 6) - Q.f (x 1))) =
          oblX2 x 5 * (-Q.f (x 2)) := by
        have ha5 : oblX0 x 5 = 1 - oblX2 x 5 + omega5 x * oblX6 x 5 := by linarith
        rw [ha5] at e
        linear_combination -e
      have : 0 < oblX6 x 5 * (omega5 x * (-Q.f (x 1)) + (Q.f (x 6) - Q.f (x 1))) := by
        rw [hprod]; exact mul_pos hb (by linarith)
      exact pos_of_mul_pos_right this hc.le
    nlinarith

/-- **The face `235` also faces away from the view** (the special-position step of the proof of
Proposition 20.31, `016/0345`): if `N_235 · u ≠ 0`, `N_236 · u < 0`, `N_025 · u < 0`, and the
quad vertices `3` and `5` lie over the open-or-closed side `(x 0, x_b]` (`x_b` the far end of the
quad, `0 < s ≤ 1`), then `N_235 · u < 0`.  Otherwise the functionals `−β f₂₃₆ + α f₂₃₅` and
`−β f₀₂₅ + α′ f₂₃₅` (nonnegative on `K`, gradients `⊥ u`) would vanish at the far end, which lies
on none of the two pairs of faces.  (The paper: "`25` and `23` silhouette edges force
`P0 ∈ {P3, P5}`: special position".) -/
theorem inner_235_neg {x : Fin 7 → ℝ³} (T : Type24 x) (G : Face16 x {2, 3, 5}) {u : ℝ³}
    (hD : ⟪T.t236.N, u⟫ < 0) (hF : ⟪T.t025.N, u⟫ < 0) (hG : ⟪G.N, u⟫ ≠ 0) {b : Fin 7}
    (hb : b = 3 ∨ b = 4 ∨ b = 5)
    (h3 : ∃ s δ : ℝ, 0 < s ∧ s ≤ 1 ∧ x 3 = x 0 + s • (x b - x 0) + δ • u)
    (h5 : ∃ s δ : ℝ, 0 < s ∧ s ≤ 1 ∧ x 5 = x 0 + s • (x b - x 0) + δ • u) :
    ⟪G.N, u⟫ < 0 := by
  by_contra hcon
  have hβ : 0 < ⟪G.N, u⟫ := lt_of_le_of_ne (not_lt.mp hcon) (Ne.symm hG)
  obtain ⟨s3, δ3, hs3, hs31, e3⟩ := h3
  obtain ⟨s5, δ5, hs5, hs51, e5⟩ := h5
  have hDb : T.t236.f (x b) = 0 := by
    have eD := T.t236.f_over e3
    have eG := G.f_over e3
    rw [T.t236.zero 3 (by decide)] at eD
    rw [G.zero 3 (by decide)] at eG
    have := far_zero hβ hD (Type24.f_le T.t236 0) (Type24.f_le T.t236 b) (Type24.f_le G 0)
      (Type24.f_le G b) hs3 hs31
      (by linear_combination (-⟪G.N, u⟫) * (-eD) + ⟪T.t236.N, u⟫ * (-eG))
    exact this.1
  have hb3 : b = 3 := by
    rcases hb with h | h | h
    · exact h
    · subst h; have := T.t236.neg 4 (by decide); linarith
    · subst h; have := T.t236.neg 5 (by decide); linarith
  subst hb3
  have eF := T.t025.f_over e5
  have eG := G.f_over e5
  rw [T.t025.zero 5 (by decide)] at eF
  rw [G.zero 5 (by decide)] at eG
  have hz := far_zero hβ hF (Type24.f_le T.t025 0) (Type24.f_le T.t025 3) (Type24.f_le G 0)
    (Type24.f_le G 3) hs5 hs51
    (by linear_combination (-⟪G.N, u⟫) * (-eF) + ⟪T.t025.N, u⟫ * (-eG))
  have := T.t025.neg 3 (by decide)
  linarith [hz.1]

/-- **Proposition 20.31 (ii), the crossing `016/0345` (at `0`; `y = 2`).**  Let `x` be of type 24
(`T`: the cap faces and the side faces; `Q = 0345`, `G = 235`, `H = 346` the other three
facets), `K = conv (x i)` the intersection of the nine facet half-spaces (`hK`), `ω3 > 0`
(the case `C̄`).  If the quad faces away from the view `d0` of `T′(6,2)` (`w · d0 < 0`,
written `⟪N_Q, d0⟫ < 0`; `viewT62`), then the crossing `016/0345`, at its view `qView6` (parallel to
`016` and to the quad), has the triangle `(0, f₁, f₂)` as rim, and `K` is Rupert, off special
position.  The crossing data are the far ends `f₁ = x a` (`a ∈ {1, 6}`) and `f₂ = x b`
(`b ∈ {3, 4, 5}`), the other vertices of the faces `016`, `0345` being middles over the open
sides `(x 0, x a)`, `(x 0, x b)` (`hmA`, `hmB`).

The special positions are explicit: `N_235 · u ≠ 0` (`hG`: the face `235` is not parallel to
the view), the triangle `(0, f₁, f₂)` is non-collinear in the shadow (`hdet`), has distinct depths
(`hd1`–`hd3`), and no horizontal double normal (`hnd`).  Beyond the paper: `hK` (the nine
faces are all the facets), the rim data `a`, `b` and the middles (the paper's "(8.8)": the
faces project onto the sides `[P0, P f_i]`; they are determined by the geometry but
not derived here), and the strictness `s < 1`, `δ ≠ 0` of the middles. -/
theorem isRupert_type24_quad016 {x : Fin 7 → ℝ³} (T : Type24 x) (Q : Face16 x {0, 3, 4, 5})
    (G : Face16 x {2, 3, 5}) (H : Face16 x {3, 4, 6})
    (hK : ∀ z, T.t012.f z ≤ 0 → T.t016.f z ≤ 0 → T.t126.f z ≤ 0 → T.t236.f z ≤ 0 →
      T.t046.f z ≤ 0 → T.t025.f z ≤ 0 → Q.f z ≤ 0 → G.f z ≤ 0 → H.f z ≤ 0 →
      z ∈ convexHull ℝ (↑(univ.image x) : Set ℝ³))
    (hω3 : 0 < omega3 x) (hw : ⟪Q.N, viewT62 x⟫ < 0)
    {a b : Fin 7} (_ha : a = 1 ∨ a = 6) (hb : b = 3 ∨ b = 4 ∨ b = 5)
    (hmA : ∀ i, (i = 1 ∨ i = 6) → i ≠ a →
      ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧ x i = x 0 + s • (x a - x 0) + δ • qView6 Q)
    (hmB : ∀ i, (i = 3 ∨ i = 4 ∨ i = 5) → i ≠ b →
      ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧ x i = x 0 + s • (x b - x 0) + δ • qView6 Q)
    (hG : ⟪G.N, qView6 Q⟫ ≠ 0)
    (hdet : det3 (x a - x 0) (x b - x 0) (qView6 Q) ≠ 0)
    (hd1 : ⟪x 0, qView6 Q⟫ ≠ ⟪x a, qView6 Q⟫) (hd2 : ⟪x 0, qView6 Q⟫ ≠ ⟪x b, qView6 Q⟫)
    (hd3 : ⟪x a, qView6 Q⟫ ≠ ⟪x b, qView6 Q⟫)
    (hnd : NoHDNAt {x 0, x a, x b} (qView6 Q)) : IsRupert (univ.image x) := by
  classical
  set u : ℝ³ := qView6 Q with hu
  obtain ⟨sA, sC, sD, sF⟩ := qView6_signs T Q hω3 hw
  have hover : ∀ i, (i = 3 ∨ i = 4 ∨ i = 5) →
      ∃ s δ : ℝ, 0 < s ∧ s ≤ 1 ∧ x i = x 0 + s • (x b - x 0) + δ • u := by
    intro i hi
    by_cases h : i = b
    · subst h; exact ⟨1, 0, one_pos, le_rfl, by simp⟩
    · obtain ⟨s, δ, h0, h1, -, he⟩ := hmB i hi h
      exact ⟨s, δ, h0, h1.le, he⟩
  have sG := inner_235_neg T G sD sF hG hb (hover 3 (Or.inl rfl)) (hover 5 (Or.inr (Or.inr rfl)))
  -- the nine facets
  let f : Fin 9 → ℝ³ → ℝ :=
    ![T.t012.f, T.t016.f, T.t126.f, T.t236.f, T.t046.f, T.t025.f, Q.f, G.f, H.f]
  let N : Fin 9 → ℝ³ :=
    ![T.t012.N, T.t016.N, T.t126.N, T.t236.N, T.t046.N, T.t025.N, Q.N, G.N, H.N]
  have hN : ∀ i a b, f i a - f i b = ⟪N i, a - b⟫ := by
    intro i; fin_cases i
    exacts [T.t012.hN, T.t016.hN, T.t126.hN, T.t236.hN, T.t046.hN, T.t025.hN, Q.hN, G.hN, H.hN]
  have hKf : ∀ z, (∀ i, f i z ≤ 0) → z ∈ convexHull ℝ (↑(univ.image x) : Set ℝ³) :=
    fun z h => hK z (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7) (h 8)
  have hyf : ∀ i, f i (x 2) ≤ 0 := by
    intro i; fin_cases i
    exacts [Type24.f_le T.t012 2, Type24.f_le T.t016 2, Type24.f_le T.t126 2,
      Type24.f_le T.t236 2, Type24.f_le T.t046 2, Type24.f_le T.t025 2, Type24.f_le Q 2,
      Type24.f_le G 2, Type24.f_le H 2]
  have hsign : ∀ i, f i (x 2) = 0 → ⟪N i, u⟫ < 0 := by
    intro i hi; fin_cases i
    · exact sA
    · exact absurd hi (T.t016.neg 2 (by decide)).ne
    · exact sC
    · exact sD
    · exact absurd hi (T.t046.neg 2 (by decide)).ne
    · exact sF
    · exact absurd hi (Q.neg 2 (by decide)).ne
    · exact sG
    · exact absurd hi (H.neg 2 (by decide)).ne
  have mem : ∀ i, x i ∈ univ.image x := fun i => mem_image_of_mem x (mem_univ i)
  refine isRupert_quadTriangle f N hN _ hKf (mem 0) (mem a) (mem b) hyf (Or.inl hsign) hdet hd1
    hd2 hd3 ?_ hnd
  intro z hz
  obtain ⟨i, -, rfl⟩ := mem_image.mp hz
  by_cases h2 : i = 2
  · exact Or.inl (by rw [h2])
  by_cases h0 : i = 0
  · exact Or.inr (Or.inl (by rw [h0]))
  by_cases hia : i = a
  · exact Or.inr (Or.inr (Or.inl (by rw [hia])))
  by_cases hib : i = b
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [hib]))))
  have hcases : ∀ i : Fin 7, i ≠ 2 → i ≠ 0 → i = 1 ∨ i = 6 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by decide
  refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
  rcases hcases i h2 h0 with h | h | h | h | h
  · obtain ⟨s, δ, h0, h1, hδ, he⟩ := hmA i (Or.inl h) hia
    exact ⟨s, δ, h0, h1, hδ, Or.inl he⟩
  · obtain ⟨s, δ, h0, h1, hδ, he⟩ := hmA i (Or.inr h) hia
    exact ⟨s, δ, h0, h1, hδ, Or.inl he⟩
  · obtain ⟨s, δ, h0, h1, hδ, he⟩ := hmB i (Or.inl h) hib
    exact ⟨s, δ, h0, h1, hδ, Or.inr he⟩
  · obtain ⟨s, δ, h0, h1, hδ, he⟩ := hmB i (Or.inr (Or.inl h)) hib
    exact ⟨s, δ, h0, h1, hδ, Or.inr he⟩
  · obtain ⟨s, δ, h0, h1, hδ, he⟩ := hmB i (Or.inr (Or.inr h)) hib
    exact ⟨s, δ, h0, h1, hδ, Or.inr he⟩

/-! ### Type 24: the crossing 012/0345 (hidden vertex `6`), the mirror `2 ↔ 6`, `4 ↔ 5` -/

namespace Type24

variable {x : Fin 7 → ℝ³} (T : Type24 x)
include T

/-- The apex `4` fixes `ω4`: `f₀₄₆(x 2) − f₀₄₆(x 1) = ω4 f₀₄₆(x 1)`. -/
theorem E2 : T.t046.f (x 2) - T.t046.f (x 1) = omega4 x * T.t046.f (x 1) := by
  have e4 := T.eval T.t046 4
  rw [T.t046.zero 0 (by decide), T.t046.zero 6 (by decide)] at e4
  rw [T.t046.zero 4 (by decide)] at e4
  have h4 := T.eq4
  have hX := T.X2_pos (v := 4) (by decide)
  have k : (T.t046.f (x 2) - T.t046.f (x 1) - omega4 x * T.t046.f (x 1)) * oblX2 x 4 = 0 := by
    linear_combination -e4 + T.t046.f (x 1) * h4
  rcases mul_eq_zero.mp k with h | h
  · linarith
  · exact absurd h hX.ne'

end Type24

/-- The view of the crossing `012/0345`: parallel to `012` and to the quad `0345`,
`(f_Q(x 1) − f_Q(x 2)) (x 0 − x 1) − f_Q(x 1) (x 2 − x 1)`; a positive multiple of
`(1, −1/w_b, 0)` when `w_b < 0` (the mirror of `qView6`). -/
noncomputable def qView2 {x : Fin 7 → ℝ³} (Q : Face16 x {0, 3, 4, 5}) : ℝ³ :=
  (Q.f (x 1) - Q.f (x 2)) • (x 0 - x 1) + (-Q.f (x 1)) • (x 2 - x 1)

theorem Face16.inner_qView2 {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (Q : Face16 x {0, 3, 4, 5})
    (F : Face16 x S) :
    ⟪F.N, qView2 Q⟫ = (Q.f (x 1) - Q.f (x 2)) * (F.f (x 0) - F.f (x 1)) +
      (-Q.f (x 1)) * (F.f (x 2) - F.f (x 1)) := by
  rw [qView2, inner_add_right, inner_smul_right, inner_smul_right, ← F.hN, ← F.hN]

/-- The quad covector against the view `d_h` of `T′(2,6)`: `w · d_h = 1 + ω3 w_b`, up to the
positive factor `−f_Q(x 1)`. -/
theorem inner_viewT26 {x : Fin 7 → ℝ³} (Q : Face16 x {0, 3, 4, 5}) :
    ⟪Q.N, viewT26 x⟫ = (-Q.f (x 1)) + omega3 x * (Q.f (x 2) - Q.f (x 1)) := by
  rw [viewT26, inner_add_right, inner_smul_right, ← Q.hN, ← Q.hN, Q.zero 0 (by decide)]
  ring

/-- **The numbers `N_f · d` of the faces at `6` for the crossing `012/0345`** (the mirror of
`qView6_signs`): `016`, `126`, `236`, `046` face away from `qView2` iff `w · d_h < 0`; the fifth
face `346` is `inner_346_neg`. -/
theorem qView2_signs {x : Fin 7 → ℝ³} (T : Type24 x) (Q : Face16 x {0, 3, 4, 5})
    (hω3 : 0 < omega3 x) (hw : ⟪Q.N, viewT26 x⟫ < 0) :
    ⟪T.t016.N, qView2 Q⟫ < 0 ∧ ⟪T.t126.N, qView2 Q⟫ < 0 ∧ ⟪T.t236.N, qView2 Q⟫ < 0 ∧
      ⟪T.t046.N, qView2 Q⟫ < 0 := by
  rw [inner_viewT26] at hw
  have hκ : 0 < -Q.f (x 1) := by linarith [Q.neg 1 (by decide)]
  have hl2 : Q.f (x 2) - Q.f (x 1) < 0 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hl2' : 0 < Q.f (x 1) - Q.f (x 2) := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Face16.inner_qView2, T.t016.zero 0 (by decide), T.t016.zero 1 (by decide)]
    have := T.t016.neg 2 (by decide)
    nlinarith
  · rw [Face16.inner_qView2, T.t126.zero 1 (by decide), T.t126.zero 2 (by decide)]
    have := T.t126.neg 0 (by decide)
    nlinarith
  · rw [Face16.inner_qView2, T.t236.zero 2 (by decide)]
    have h0 := T.D0
    have h1 := T.t236.neg 1 (by decide)
    nlinarith
  · rw [Face16.inner_qView2, T.t046.zero 0 (by decide)]
    have h2 := T.E2
    have h1 := T.t046.neg 1 (by decide)
    have e := T.eval Q 4
    rw [Q.zero 4 (by decide), Q.zero 0 (by decide)] at e
    have e4 := T.eq4
    have hb := T.X2_pos (v := 4) (by decide)
    have hc := T.X6_pos (v := 4) (by decide)
    have h6 := Q.neg 6 (by decide)
    have key : 0 < omega4 x * (-Q.f (x 1)) + (Q.f (x 2) - Q.f (x 1)) := by
      have hprod : oblX2 x 4 * (omega4 x * (-Q.f (x 1)) + (Q.f (x 2) - Q.f (x 1))) =
          oblX6 x 4 * (-Q.f (x 6)) := by
        have ha4 : oblX0 x 4 = 1 - oblX6 x 4 + omega4 x * oblX2 x 4 := by linarith
        rw [ha4] at e
        linear_combination -e
      have : 0 < oblX2 x 4 * (omega4 x * (-Q.f (x 1)) + (Q.f (x 2) - Q.f (x 1))) := by
        rw [hprod]; exact mul_pos hc (by linarith)
      exact pos_of_mul_pos_right this hb.le
    nlinarith

/-- **The face `346` also faces away from the view** (the mirror of `inner_235_neg`; the
special-position step of the proof of Proposition 20.31, `012/0345`): if `N_346 · u ≠ 0`,
`N_236 · u < 0`, `N_046 · u < 0`, and the quad vertices `3` and `4` lie over `(x 0, x_b]`, then
`N_346 · u < 0`. -/
theorem inner_346_neg {x : Fin 7 → ℝ³} (T : Type24 x) (H : Face16 x {3, 4, 6}) {u : ℝ³}
    (hD : ⟪T.t236.N, u⟫ < 0) (hE : ⟪T.t046.N, u⟫ < 0) (hH : ⟪H.N, u⟫ ≠ 0) {b : Fin 7}
    (hb : b = 3 ∨ b = 4 ∨ b = 5)
    (h3 : ∃ s δ : ℝ, 0 < s ∧ s ≤ 1 ∧ x 3 = x 0 + s • (x b - x 0) + δ • u)
    (h4 : ∃ s δ : ℝ, 0 < s ∧ s ≤ 1 ∧ x 4 = x 0 + s • (x b - x 0) + δ • u) :
    ⟪H.N, u⟫ < 0 := by
  by_contra hcon
  have hβ : 0 < ⟪H.N, u⟫ := lt_of_le_of_ne (not_lt.mp hcon) (Ne.symm hH)
  obtain ⟨s3, δ3, hs3, hs31, e3⟩ := h3
  obtain ⟨s4, δ4, hs4, hs41, e4⟩ := h4
  have hDb : T.t236.f (x b) = 0 := by
    have eD := T.t236.f_over e3
    have eH := H.f_over e3
    rw [T.t236.zero 3 (by decide)] at eD
    rw [H.zero 3 (by decide)] at eH
    have := far_zero hβ hD (Type24.f_le T.t236 0) (Type24.f_le T.t236 b) (Type24.f_le H 0)
      (Type24.f_le H b) hs3 hs31
      (by linear_combination (-⟪H.N, u⟫) * (-eD) + ⟪T.t236.N, u⟫ * (-eH))
    exact this.1
  have hb3 : b = 3 := by
    rcases hb with h | h | h
    · exact h
    · subst h; have := T.t236.neg 4 (by decide); linarith
    · subst h; have := T.t236.neg 5 (by decide); linarith
  subst hb3
  have eE := T.t046.f_over e4
  have eH := H.f_over e4
  rw [T.t046.zero 4 (by decide)] at eE
  rw [H.zero 4 (by decide)] at eH
  have hz := far_zero hβ hE (Type24.f_le T.t046 0) (Type24.f_le T.t046 3) (Type24.f_le H 0)
    (Type24.f_le H 3) hs4 hs41
    (by linear_combination (-⟪H.N, u⟫) * (-eE) + ⟪T.t046.N, u⟫ * (-eH))
  have := T.t046.neg 3 (by decide)
  linarith [hz.1]

/-- **Proposition 20.31 (ii), the crossing `012/0345` (at `0`; `y = 6`).**  The mirror
(`2 ↔ 6`, `4 ↔ 5`) of `isRupert_type24_quad016`: if the quad faces away from the view `d_h` of
`T′(2,6)` (`w · d_h < 0`, `⟪N_Q, viewT26⟫ < 0`), then the crossing `012/0345` at its view
`qView2` has the triangle `(0, f₁, f₂)` as rim (`f₁ = x a`, `a ∈ {1, 2}`; `f₂ = x b`,
`b ∈ {3, 4, 5}`) and `K` is Rupert, off special position (`hH : N_346 · u ≠ 0`, `hdet`,
`hd1`–`hd3`, `hnd`).  Same extra hypotheses as `isRupert_type24_quad016` (`hK`, rim data and
middles). -/
theorem isRupert_type24_quad012 {x : Fin 7 → ℝ³} (T : Type24 x) (Q : Face16 x {0, 3, 4, 5})
    (G : Face16 x {2, 3, 5}) (H : Face16 x {3, 4, 6})
    (hK : ∀ z, T.t012.f z ≤ 0 → T.t016.f z ≤ 0 → T.t126.f z ≤ 0 → T.t236.f z ≤ 0 →
      T.t046.f z ≤ 0 → T.t025.f z ≤ 0 → Q.f z ≤ 0 → G.f z ≤ 0 → H.f z ≤ 0 →
      z ∈ convexHull ℝ (↑(univ.image x) : Set ℝ³))
    (hω3 : 0 < omega3 x) (hw : ⟪Q.N, viewT26 x⟫ < 0)
    {a b : Fin 7} (_ha : a = 1 ∨ a = 2) (hb : b = 3 ∨ b = 4 ∨ b = 5)
    (hmA : ∀ i, (i = 1 ∨ i = 2) → i ≠ a →
      ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧ x i = x 0 + s • (x a - x 0) + δ • qView2 Q)
    (hmB : ∀ i, (i = 3 ∨ i = 4 ∨ i = 5) → i ≠ b →
      ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧ x i = x 0 + s • (x b - x 0) + δ • qView2 Q)
    (hH : ⟪H.N, qView2 Q⟫ ≠ 0)
    (hdet : det3 (x a - x 0) (x b - x 0) (qView2 Q) ≠ 0)
    (hd1 : ⟪x 0, qView2 Q⟫ ≠ ⟪x a, qView2 Q⟫) (hd2 : ⟪x 0, qView2 Q⟫ ≠ ⟪x b, qView2 Q⟫)
    (hd3 : ⟪x a, qView2 Q⟫ ≠ ⟪x b, qView2 Q⟫)
    (hnd : NoHDNAt {x 0, x a, x b} (qView2 Q)) : IsRupert (univ.image x) := by
  classical
  set u : ℝ³ := qView2 Q with hu
  obtain ⟨sB, sC, sD, sE⟩ := qView2_signs T Q hω3 hw
  have hover : ∀ i, (i = 3 ∨ i = 4 ∨ i = 5) →
      ∃ s δ : ℝ, 0 < s ∧ s ≤ 1 ∧ x i = x 0 + s • (x b - x 0) + δ • u := by
    intro i hi
    by_cases h : i = b
    · subst h; exact ⟨1, 0, one_pos, le_rfl, by simp⟩
    · obtain ⟨s, δ, h0, h1, -, he⟩ := hmB i hi h
      exact ⟨s, δ, h0, h1.le, he⟩
  have sH := inner_346_neg T H sD sE hH hb (hover 3 (Or.inl rfl)) (hover 4 (Or.inr (Or.inl rfl)))
  let f : Fin 9 → ℝ³ → ℝ :=
    ![T.t012.f, T.t016.f, T.t126.f, T.t236.f, T.t046.f, T.t025.f, Q.f, G.f, H.f]
  let N : Fin 9 → ℝ³ :=
    ![T.t012.N, T.t016.N, T.t126.N, T.t236.N, T.t046.N, T.t025.N, Q.N, G.N, H.N]
  have hN : ∀ i a b, f i a - f i b = ⟪N i, a - b⟫ := by
    intro i; fin_cases i
    exacts [T.t012.hN, T.t016.hN, T.t126.hN, T.t236.hN, T.t046.hN, T.t025.hN, Q.hN, G.hN, H.hN]
  have hKf : ∀ z, (∀ i, f i z ≤ 0) → z ∈ convexHull ℝ (↑(univ.image x) : Set ℝ³) :=
    fun z h => hK z (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7) (h 8)
  have hyf : ∀ i, f i (x 6) ≤ 0 := by
    intro i; fin_cases i
    exacts [Type24.f_le T.t012 6, Type24.f_le T.t016 6, Type24.f_le T.t126 6,
      Type24.f_le T.t236 6, Type24.f_le T.t046 6, Type24.f_le T.t025 6, Type24.f_le Q 6,
      Type24.f_le G 6, Type24.f_le H 6]
  have hsign : ∀ i, f i (x 6) = 0 → ⟪N i, u⟫ < 0 := by
    intro i hi; fin_cases i
    · exact absurd hi (T.t012.neg 6 (by decide)).ne
    · exact sB
    · exact sC
    · exact sD
    · exact sE
    · exact absurd hi (T.t025.neg 6 (by decide)).ne
    · exact absurd hi (Q.neg 6 (by decide)).ne
    · exact absurd hi (G.neg 6 (by decide)).ne
    · exact sH
  have mem : ∀ i, x i ∈ univ.image x := fun i => mem_image_of_mem x (mem_univ i)
  refine isRupert_quadTriangle f N hN _ hKf (mem 0) (mem a) (mem b) hyf (Or.inl hsign) hdet hd1
    hd2 hd3 ?_ hnd
  intro z hz
  obtain ⟨i, -, rfl⟩ := mem_image.mp hz
  by_cases h6 : i = 6
  · exact Or.inl (by rw [h6])
  by_cases h0 : i = 0
  · exact Or.inr (Or.inl (by rw [h0]))
  by_cases hia : i = a
  · exact Or.inr (Or.inr (Or.inl (by rw [hia])))
  by_cases hib : i = b
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [hib]))))
  have hcases : ∀ i : Fin 7, i ≠ 6 → i ≠ 0 → i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by decide
  refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
  rcases hcases i h6 h0 with h | h | h | h | h
  · obtain ⟨s, δ, h0, h1, hδ, he⟩ := hmA i (Or.inl h) hia
    exact ⟨s, δ, h0, h1, hδ, Or.inl he⟩
  · obtain ⟨s, δ, h0, h1, hδ, he⟩ := hmA i (Or.inr h) hia
    exact ⟨s, δ, h0, h1, hδ, Or.inl he⟩
  · obtain ⟨s, δ, h0, h1, hδ, he⟩ := hmB i (Or.inl h) hib
    exact ⟨s, δ, h0, h1, hδ, Or.inr he⟩
  · obtain ⟨s, δ, h0, h1, hδ, he⟩ := hmB i (Or.inr (Or.inl h)) hib
    exact ⟨s, δ, h0, h1, hδ, Or.inr he⟩
  · obtain ⟨s, δ, h0, h1, hδ, he⟩ := hmB i (Or.inr (Or.inr h)) hib
    exact ⟨s, δ, h0, h1, hδ, Or.inr he⟩

/-! ### Type 24: the crossing 236/0345 (hidden vertex `1`) -/

/-- A facet functional against a combination of the frame vectors at `1`. -/
theorem Face16.inner_frame {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (F : Face16 x S) (α β γ : ℝ) :
    ⟪F.N, α • (x 0 - x 1) + β • (x 2 - x 1) + γ • (x 6 - x 1)⟫ =
      α * (F.f (x 0) - F.f (x 1)) + β * (F.f (x 2) - F.f (x 1)) +
        γ * (F.f (x 6) - F.f (x 1)) := by
  rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right, inner_smul_right,
    ← F.hN, ← F.hN, ← F.hN]

/-- The view of the crossing `236/0345`: parallel to `236` and to the quad `0345`,
`(w_c − w_b, w · d0, −w · d_h)` in the oblique coordinates of §15, up to the positive factor
`−f_Q(x 1)`: `d = n_236 × w` (§50). -/
noncomputable def qView3 {x : Fin 7 → ℝ³} (Q : Face16 x {0, 3, 4, 5}) : ℝ³ :=
  (Q.f (x 6) - Q.f (x 2)) • (x 0 - x 1) + ⟪Q.N, viewT62 x⟫ • (x 2 - x 1) +
    (-⟪Q.N, viewT26 x⟫) • (x 6 - x 1)

/-- The view `qView3` is parallel to the quad. -/
theorem inner_qView3_Q {x : Fin 7 → ℝ³} (Q : Face16 x {0, 3, 4, 5}) : ⟪Q.N, qView3 Q⟫ = 0 := by
  rw [qView3, Face16.inner_frame, inner_viewT62, inner_viewT26, Q.zero 0 (by decide)]
  ring

/-- The view `qView3` is parallel to the face `236`. -/
theorem inner_qView3_D {x : Fin 7 → ℝ³} (T : Type24 x) (Q : Face16 x {0, 3, 4, 5}) :
    ⟪T.t236.N, qView3 Q⟫ = 0 := by
  rw [qView3, Face16.inner_frame, inner_viewT62, inner_viewT26, T.t236.zero 2 (by decide),
    T.t236.zero 6 (by decide)]
  have h0 := T.D0
  have : T.t236.f (x 0) = T.t236.f (x 1) + omega3 x * T.t236.f (x 1) := by linarith
  rw [this]
  ring

/-- **Proposition 20.31 (ii), the crossing `236/0345` (at `3`; `y = 1`).**  If
`(w · d0)(w · d_h) < 0` (`⟪N_Q, viewT62⟫ · ⟪N_Q, viewT26⟫ < 0`, with `ω3 > 0`), the crossing
`236/0345` at its view `qView3` (parallel to `236` and to the quad) has the triangle
`(3, f₁, f₂)` as rim, and `K` is Rupert, off special position.  The faces at the hidden vertex
`1` are the cap faces `012`, `016`, `126`; their numbers `N_f · d` are
`−w · d_h · f₀₁₂(x 6)`, `w · d0 · f₀₁₆(x 2)`, `(f_Q(x 6) − f_Q(x 2)) f₁₂₆(x 0)`, all of one strict
sign exactly when `w · d0` and `w · d_h` have opposite signs (the sign of
`f_Q(x 6) − f_Q(x 2) = (w_c − w_b)·(−f_Q(x 1))` then follows from `ω3 > 0`).  The far ends are
`f₁ = x a` (`a ∈ {2, 6}`, the face `236`) and `f₂ = x b` (`b ∈ {0, 4, 5}`, the quad), the other
vertices of the faces being middles over the open sides (`hmA`, `hmB`).  Hypotheses beyond the
paper: `hK`, the rim data and the strictness of the middles, as in `isRupert_type24_quad016`. -/
theorem isRupert_type24_quad236 {x : Fin 7 → ℝ³} (T : Type24 x) (Q : Face16 x {0, 3, 4, 5})
    (G : Face16 x {2, 3, 5}) (H : Face16 x {3, 4, 6})
    (hK : ∀ z, T.t012.f z ≤ 0 → T.t016.f z ≤ 0 → T.t126.f z ≤ 0 → T.t236.f z ≤ 0 →
      T.t046.f z ≤ 0 → T.t025.f z ≤ 0 → Q.f z ≤ 0 → G.f z ≤ 0 → H.f z ≤ 0 →
      z ∈ convexHull ℝ (↑(univ.image x) : Set ℝ³))
    (hω3 : 0 < omega3 x) (hw : ⟪Q.N, viewT62 x⟫ * ⟪Q.N, viewT26 x⟫ < 0)
    {a b : Fin 7} (_ha : a = 2 ∨ a = 6) (_hb : b = 0 ∨ b = 4 ∨ b = 5)
    (hmA : ∀ i, (i = 2 ∨ i = 6) → i ≠ a →
      ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧ x i = x 3 + s • (x a - x 3) + δ • qView3 Q)
    (hmB : ∀ i, (i = 0 ∨ i = 4 ∨ i = 5) → i ≠ b →
      ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧ x i = x 3 + s • (x b - x 3) + δ • qView3 Q)
    (hdet : det3 (x a - x 3) (x b - x 3) (qView3 Q) ≠ 0)
    (hd1 : ⟪x 3, qView3 Q⟫ ≠ ⟪x a, qView3 Q⟫) (hd2 : ⟪x 3, qView3 Q⟫ ≠ ⟪x b, qView3 Q⟫)
    (hd3 : ⟪x a, qView3 Q⟫ ≠ ⟪x b, qView3 Q⟫)
    (hnd : NoHDNAt {x 3, x a, x b} (qView3 Q)) : IsRupert (univ.image x) := by
  classical
  set u : ℝ³ := qView3 Q with hu
  have hκ : 0 < -Q.f (x 1) := by linarith [Q.neg 1 (by decide)]
  have nA : ⟪T.t012.N, u⟫ = (-⟪Q.N, viewT26 x⟫) * T.t012.f (x 6) := by
    rw [hu, qView3, Face16.inner_frame, T.t012.zero 0 (by decide), T.t012.zero 1 (by decide),
      T.t012.zero 2 (by decide)]
    ring
  have nB : ⟪T.t016.N, u⟫ = ⟪Q.N, viewT62 x⟫ * T.t016.f (x 2) := by
    rw [hu, qView3, Face16.inner_frame, T.t016.zero 0 (by decide), T.t016.zero 1 (by decide),
      T.t016.zero 6 (by decide)]
    ring
  have nC : ⟪T.t126.N, u⟫ = (Q.f (x 6) - Q.f (x 2)) * T.t126.f (x 0) := by
    rw [hu, qView3, Face16.inner_frame, T.t126.zero 1 (by decide), T.t126.zero 2 (by decide),
      T.t126.zero 6 (by decide)]
    ring
  have hA6 := T.t012.neg 6 (by decide)
  have hB2 := T.t016.neg 2 (by decide)
  have hC0 := T.t126.neg 0 (by decide)
  have hα : ⟪Q.N, viewT62 x⟫ = (-Q.f (x 1)) + omega3 x * (Q.f (x 6) - Q.f (x 1)) :=
    inner_viewT62 Q
  have hα' : ⟪Q.N, viewT26 x⟫ = (-Q.f (x 1)) + omega3 x * (Q.f (x 2) - Q.f (x 1)) :=
    inner_viewT26 Q
  have hdiff : ⟪Q.N, viewT62 x⟫ - ⟪Q.N, viewT26 x⟫ = omega3 x * (Q.f (x 6) - Q.f (x 2)) := by
    rw [hα, hα']; ring
  set P0 := ⟪Q.N, viewT62 x⟫ with hP0
  set Ph := ⟪Q.N, viewT26 x⟫ with hPh
  have hsignAll : (∀ i : Fin 9, ![T.t012.f, T.t016.f, T.t126.f, T.t236.f, T.t046.f, T.t025.f,
        Q.f, G.f, H.f] i (x 1) = 0 → ⟪![T.t012.N, T.t016.N, T.t126.N, T.t236.N, T.t046.N,
        T.t025.N, Q.N, G.N, H.N] i, u⟫ < 0) ∨
      (∀ i : Fin 9, ![T.t012.f, T.t016.f, T.t126.f, T.t236.f, T.t046.f, T.t025.f,
        Q.f, G.f, H.f] i (x 1) = 0 → 0 < ⟪![T.t012.N, T.t016.N, T.t126.N, T.t236.N, T.t046.N,
        T.t025.N, Q.N, G.N, H.N] i, u⟫) := by
    rcases mul_neg_iff.mp hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- `w · d0 > 0 > w · d_h`: all three numbers negative
      have hαpos : 0 < Q.f (x 6) - Q.f (x 2) := by
        by_contra hcon
        push Not at hcon
        nlinarith
      left
      intro i hi; fin_cases i
      · show ⟪T.t012.N, u⟫ < 0
        rw [nA]; nlinarith
      · show ⟪T.t016.N, u⟫ < 0
        rw [nB]; nlinarith
      · show ⟪T.t126.N, u⟫ < 0
        rw [nC]; nlinarith
      · exact absurd hi (T.t236.neg 1 (by decide)).ne
      · exact absurd hi (T.t046.neg 1 (by decide)).ne
      · exact absurd hi (T.t025.neg 1 (by decide)).ne
      · exact absurd hi (Q.neg 1 (by decide)).ne
      · exact absurd hi (G.neg 1 (by decide)).ne
      · exact absurd hi (H.neg 1 (by decide)).ne
    · -- `w · d0 < 0 < w · d_h`: all three numbers positive
      have hαneg : Q.f (x 6) - Q.f (x 2) < 0 := by
        by_contra hcon
        push Not at hcon
        nlinarith
      right
      intro i hi; fin_cases i
      · show 0 < ⟪T.t012.N, u⟫
        rw [nA]; nlinarith
      · show 0 < ⟪T.t016.N, u⟫
        rw [nB]; nlinarith
      · show 0 < ⟪T.t126.N, u⟫
        rw [nC]; nlinarith
      · exact absurd hi (T.t236.neg 1 (by decide)).ne
      · exact absurd hi (T.t046.neg 1 (by decide)).ne
      · exact absurd hi (T.t025.neg 1 (by decide)).ne
      · exact absurd hi (Q.neg 1 (by decide)).ne
      · exact absurd hi (G.neg 1 (by decide)).ne
      · exact absurd hi (H.neg 1 (by decide)).ne
  let f : Fin 9 → ℝ³ → ℝ :=
    ![T.t012.f, T.t016.f, T.t126.f, T.t236.f, T.t046.f, T.t025.f, Q.f, G.f, H.f]
  let N : Fin 9 → ℝ³ :=
    ![T.t012.N, T.t016.N, T.t126.N, T.t236.N, T.t046.N, T.t025.N, Q.N, G.N, H.N]
  have hN : ∀ i a b, f i a - f i b = ⟪N i, a - b⟫ := by
    intro i; fin_cases i
    exacts [T.t012.hN, T.t016.hN, T.t126.hN, T.t236.hN, T.t046.hN, T.t025.hN, Q.hN, G.hN, H.hN]
  have hKf : ∀ z, (∀ i, f i z ≤ 0) → z ∈ convexHull ℝ (↑(univ.image x) : Set ℝ³) :=
    fun z h => hK z (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7) (h 8)
  have hyf : ∀ i, f i (x 1) ≤ 0 := by
    intro i; fin_cases i
    exacts [Type24.f_le T.t012 1, Type24.f_le T.t016 1, Type24.f_le T.t126 1,
      Type24.f_le T.t236 1, Type24.f_le T.t046 1, Type24.f_le T.t025 1, Type24.f_le Q 1,
      Type24.f_le G 1, Type24.f_le H 1]
  have mem : ∀ i, x i ∈ univ.image x := fun i => mem_image_of_mem x (mem_univ i)
  refine isRupert_quadTriangle f N hN _ hKf (mem 3) (mem a) (mem b) hyf hsignAll hdet hd1
    hd2 hd3 ?_ hnd
  intro z hz
  obtain ⟨i, -, rfl⟩ := mem_image.mp hz
  by_cases h1 : i = 1
  · exact Or.inl (by rw [h1])
  by_cases h3 : i = 3
  · exact Or.inr (Or.inl (by rw [h3]))
  by_cases hia : i = a
  · exact Or.inr (Or.inr (Or.inl (by rw [hia])))
  by_cases hib : i = b
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [hib]))))
  have hcases : ∀ i : Fin 7, i ≠ 1 → i ≠ 3 → i = 2 ∨ i = 6 ∨ i = 0 ∨ i = 4 ∨ i = 5 := by decide
  refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
  rcases hcases i h1 h3 with h | h | h | h | h
  · obtain ⟨s, δ, h0, h1, hδ, he⟩ := hmA i (Or.inl h) hia
    exact ⟨s, δ, h0, h1, hδ, Or.inl he⟩
  · obtain ⟨s, δ, h0, h1, hδ, he⟩ := hmA i (Or.inr h) hia
    exact ⟨s, δ, h0, h1, hδ, Or.inl he⟩
  · obtain ⟨s, δ, h0, h1, hδ, he⟩ := hmB i (Or.inl h) hib
    exact ⟨s, δ, h0, h1, hδ, Or.inr he⟩
  · obtain ⟨s, δ, h0, h1, hδ, he⟩ := hmB i (Or.inr (Or.inl h)) hib
    exact ⟨s, δ, h0, h1, hδ, Or.inr he⟩
  · obtain ⟨s, δ, h0, h1, hδ, he⟩ := hmB i (Or.inr (Or.inr h)) hib
    exact ⟨s, δ, h0, h1, hδ, Or.inr he⟩

end Minimality

end
