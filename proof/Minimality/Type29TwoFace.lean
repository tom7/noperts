module

public import Minimality.Type29HDN
public import Minimality.Type21Vtx

@[expose] public section

/-!
# Type 29: two face circles at the quadrilateral-triangle views (§22.2, §28.5)

Proposition 22.2 for a labelled rim at a vertex line (or an edge) where a triangle `S_T` and a
quadrilateral `S_Q` are seen edge-on and the closing is realized on both circles (§28.5): `V`
(035/1456), `V′` (1456/234), `T2` with the rim `(4, 3, 6)` and `Y2` (46).  At the limit the
shape is Rupert whatever its horizontal double normals if (G1) holds at the view (no segment
parallel to it, distinct depths).

* `TwoGen29`, `TwoEdgeGen29`: the codimension-2 conditions at a vertex line, resp. an edge.
* `twoFace_sides29`: the side signs of the two faces from the rim's sides (a triangle side and
  a quadrilateral side, an edge of the quad with its adjacent facet).
* `isRupert_twoFaceVtx29`, `isRupert_twoFaceEdge29`: the limit statements.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

variable {x : Fin 7 → ℝ³}

/-! ### The conditions -/

/-- **(G1) at a vertex line seen along two faces** (§22.4): no segment is parallel to the view,
every point over a support line lies on one of the two faces with the line's ends, and the
depths are distinct. -/
structure TwoGen29 (V : Finset ℝ³) (u : ℝ³) (SA SB : Finset ℝ³) : Prop where
  par : NoParAt V u
  g1 : G1At V u SA SB
  dist : ∀ y ∈ V, ∀ y' ∈ V, y ≠ y' → ⟪y, u⟫ ≠ ⟪y', u⟫

/-- **(G1) at an edge view** (§22.4): only the axle `v w` is seen end-on, (G1), and distinct
depths. -/
structure TwoEdgeGen29 (V : Finset ℝ³) (u v w : ℝ³) (SA SB : Finset ℝ³) : Prop where
  par : ParOnly V u v w
  g1 : G1At V u SA SB
  dist : ∀ y ∈ V, ∀ y' ∈ V, y ≠ y' → ⟪y, u⟫ ≠ ⟪y', u⟫

theorem G1At.sign {V : Finset ℝ³} {u : ℝ³} {SA SB : Finset ℝ³} (h : G1At V u SA SB) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) : G1At V (ε • u) SA SB := by
  rcases hε with rfl | rfl
  · rwa [one_smul]
  · rw [neg_one_smul]; exact G1At.swapF (EdgeConf.G1At.neg h)

theorem TwoGen29.sign {V : Finset ℝ³} {u : ℝ³} {SA SB : Finset ℝ³} (h : TwoGen29 V u SA SB)
    {ε : ℝ} (hε : ε = 1 ∨ ε = -1) : TwoGen29 V (ε • u) SA SB where
  par := fun y hy y' hy' hne => by
    rw [cross_smul_right']
    exact smul_ne_zero (by rcases hε with rfl | rfl <;> norm_num) (h.par y hy y' hy' hne)
  g1 := h.g1.sign hε
  dist := fun y hy y' hy' hne e => by
    rw [real_inner_smul_right, real_inner_smul_right] at e
    exact h.dist y hy y' hy' hne
      (mul_left_cancel₀ (by rcases hε with rfl | rfl <;> norm_num) e)

theorem TwoEdgeGen29.sign {V : Finset ℝ³} {u v w : ℝ³} {SA SB : Finset ℝ³}
    (h : TwoEdgeGen29 V u v w SA SB) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    TwoEdgeGen29 V (ε • u) v w SA SB where
  par := h.par.smul (by rcases hε with rfl | rfl <;> norm_num)
  g1 := h.g1.sign hε
  dist := fun y hy y' hy' hne e => by
    rw [real_inner_smul_right, real_inner_smul_right] at e
    exact h.dist y hy y' hy' hne
      (mul_left_cancel₀ (by rcases hε with rfl | rfl <;> norm_num) e)

/-! ### The side signs -/

/-- A face's side sign from an adjacent facet (`side_pos21` for `Facets29`). -/
theorem side_pos29 (T : Facets29 x) {S SO : Finset (Fin 7)} (F : Face16 x S)
    (FO : Face16 x SO) {p q m₀ m : Fin 7} (hp : p ∈ S) (hq : q ∈ S) (hm₀ : m₀ ∈ S) (hm : m ∈ S)
    (hpO : p ∈ SO) (hqO : q ∈ SO) (hm₀O : m₀ ∉ SO) (hmO : m ∉ SO) (hpq : p ≠ q) (hpm₀ : p ≠ m₀)
    (hqm₀ : q ≠ m₀) {j₀ : Fin 7} (hj₀ : j₀ ∉ S) :
    0 < det3 (x q - x p) (x m₀ - x p) F.N * det3 (x q - x p) (x m - x p) F.N := by
  have adj := FO.adj (p := p) (q := q) (r := m₀) (s := m) hpO hqO hm₀O hmO
  have := side_sign_of_adj (N := F.N) (NG := FO.N) (p := x p) (q := x q) (m₀ := x m₀) (m := x m)
    (F.inner_sub hq hp) (F.inner_sub hm₀ hp) (F.inner_sub hm hp)
    (cross_ne_zero_of_noSeg T.inj T.noSeg hpq hpm₀ hqm₀) (F.N_ne hp hj₀) adj.1 adj.2.1 adj.2.2
  linarith [mul_comm (det3 (x q - x p) (x m - x p) F.N) (det3 (x q - x p) (x m₀ - x p) F.N)]

/-- **The side signs of the two faces seen edge-on** (the rim has one side `a → b` on the triangle
`S_T ∋ a, b, c` and one side `p → q` on the quadrilateral `S_Q ∋ p, q, q₁, q₂`, an edge of the
quad with the adjacent facet `S_O`): nonzero `σ_T`, `σ_Q` with the signs of `hsa`, `hsb` of
`isRupert_twoFace`, and the normals are not parallel when a point `v` of `S_T ∩ S_Q` is joined to
a point `e` of `S_T` off `S_Q`. -/
theorem twoFace_sides29 (T : Facets29 x) {k : ℕ} [NeZero k] (lab : ZMod k → Fin 7)
    {ST SQ SO : Finset (Fin 7)} (FT : Face16 x ST) (FQ : Face16 x SQ) (FO : Face16 x SO)
    {a b c p q q₁ q₂ v e jT jQ : Fin 7}
    (hT : a ∈ ST ∧ b ∈ ST ∧ c ∈ ST ∧ jT ∉ ST) (hQ : p ∈ SQ ∧ q ∈ SQ ∧ q₁ ∈ SQ ∧ q₂ ∈ SQ ∧ jQ ∉ SQ)
    (hO : p ∈ SO ∧ q ∈ SO ∧ q₁ ∉ SO ∧ q₂ ∉ SO)
    (hne : a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ p ≠ q ∧ p ≠ q₁ ∧ q ≠ q₁)
    (hv : v ∈ ST ∧ v ∈ SQ ∧ e ∈ ST ∧ e ∉ SQ)
    (hsideT : ∀ i m', lab i ∈ ST → lab (i + 1) ∈ ST → m' ∈ ST → m' ≠ lab i → m' ≠ lab (i + 1) →
      lab i = a ∧ lab (i + 1) = b ∧ m' = c)
    (hsideQ : ∀ i m', lab i ∈ SQ → lab (i + 1) ∈ SQ → m' ∈ SQ → m' ≠ lab i → m' ≠ lab (i + 1) →
      lab i = p ∧ lab (i + 1) = q ∧ (m' = q₁ ∨ m' = q₂)) :
    cross FT.N FQ.N ≠ 0 ∧ ∃ σT σQ : ℝ, σT ≠ 0 ∧ σQ ≠ 0 ∧
      (∀ i m, lab i ∈ ST → lab (i + 1) ∈ ST → m ∈ ST → m ≠ lab i → m ≠ lab (i + 1) →
        0 < σT * det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) FT.N) ∧
      (∀ i m, lab i ∈ SQ → lab (i + 1) ∈ SQ → m ∈ SQ → m ≠ lab i → m ≠ lab (i + 1) →
        0 < σQ * det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) FQ.N) := by
  obtain ⟨haT, hbT, hcT, hjT⟩ := hT
  obtain ⟨hpQ, hqQ, hq₁Q, hq₂Q, hjQ⟩ := hQ
  obtain ⟨hpO, hqO, hq₁O, hq₂O⟩ := hO
  obtain ⟨hab, hac, hbc, hpq, hpq₁, hqq₁⟩ := hne
  obtain ⟨hvT, hvQ, heT, heQ⟩ := hv
  have hσT : det3 (x b - x a) (x c - x a) FT.N ≠ 0 :=
    FT.det3_normal_ne haT hbT hcT hjT (cross_ne_zero_of_noSeg T.inj T.noSeg hab hac hbc)
  have hσQ : det3 (x q - x p) (x q₁ - x p) FQ.N ≠ 0 :=
    FQ.det3_normal_ne hpQ hqQ hq₁Q hjQ (cross_ne_zero_of_noSeg T.inj T.noSeg hpq hpq₁ hqq₁)
  have hq₂ : 0 < det3 (x q - x p) (x q₁ - x p) FQ.N * det3 (x q - x p) (x q₂ - x p) FQ.N :=
    side_pos29 T FQ FO hpQ hqQ hq₁Q hq₂Q hpO hqO hq₁O hq₂O hpq hpq₁ hqq₁ hjQ
  refine ⟨?_, _, _, hσT, hσQ, fun i m h1 h2 h3 h4 h5 => ?_, fun i m h1 h2 h3 h4 h5 => ?_⟩
  · refine cross_normals_ne (FT.N_ne hvT hjT) (FT.inner_sub heT hvT) ?_
    rw [← FQ.hN, FQ.zero v hvQ, sub_zero]; exact FQ.neg e heQ
  · obtain ⟨hi, hi1, rfl⟩ := hsideT i m h1 h2 h3 h4 h5
    rw [hi, hi1]; exact mul_self_pos.mpr hσT
  · obtain ⟨hi, hi1, hm'⟩ := hsideQ i m h1 h2 h3 h4 h5
    rw [hi, hi1]
    rcases hm' with rfl | rfl
    · exact mul_self_pos.mpr hσQ
    · exact hq₂

/-! ### The limit statements -/

/-- **Proposition 22.2 at a vertex line with a triangle and a quadrilateral** (`V`, `V′`, `T2`
with the rim `(4, 3, 6)`): the rim has one side `a → b` on the triangle and one side `p → q` on
the quadrilateral (an edge with the adjacent facet `S_O`); with (G1) at the view the limit is
Rupert, whatever its horizontal double normals. -/
theorem isRupert_twoFaceVtx29 (N : NF29 x) {k : ℕ} [NeZero k] (v : View29)
    (hv0 : view29 x v ≠ 0) (ε : Bool) (lab : ZMod k → Fin 7)
    {ST SQ SO : Finset (Fin 7)} (FT : Face16 x ST) (FQ : Face16 x SQ) (FO : Face16 x SO)
    {a b c p q q₁ q₂ vv e jT jQ : Fin 7}
    (hT : a ∈ ST ∧ b ∈ ST ∧ c ∈ ST ∧ jT ∉ ST)
    (hQ : p ∈ SQ ∧ q ∈ SQ ∧ q₁ ∈ SQ ∧ q₂ ∈ SQ ∧ jQ ∉ SQ)
    (hO : p ∈ SO ∧ q ∈ SO ∧ q₁ ∉ SO ∧ q₂ ∉ SO)
    (hne : a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ p ≠ q ∧ p ≠ q₁ ∧ q ≠ q₁)
    (hvv : vv ∈ ST ∧ vv ∈ SQ ∧ e ∈ ST ∧ e ∉ SQ)
    (hsideT : ∀ i m', lab i ∈ ST → lab (i + 1) ∈ ST → m' ∈ ST → m' ≠ lab i → m' ≠ lab (i + 1) →
      lab i = a ∧ lab (i + 1) = b ∧ m' = c)
    (hsideQ : ∀ i m', lab i ∈ SQ → lab (i + 1) ∈ SQ → m' ∈ SQ → m' ≠ lab i → m' ≠ lab (i + 1) →
      lab i = p ∧ lab (i + 1) = q ∧ (m' = q₁ ∨ m' = q₂))
    (K : ℕ → Fin 7 → ℝ³) (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)))
    (hgen : TwoGen29 (univ.image x) (view29 x v) (ST.image x) (SQ.image x))
    (hc : ∃ᶠ n in atTop, RimCertAt (K n) (sgnB ε • view29 (K n) v) lab ∧ TiesAt29 x (K n)) :
    IsRupert (univ.image x) := by
  obtain ⟨n₀, hn₀, -⟩ := hc.exists
  have hs := sgnB_ne_zero ε
  obtain ⟨hab, σT, σQ, hσT, hσQ, hsa, hsb⟩ := twoFace_sides29 N.facets lab FT FQ FO hT hQ hO hne
    hvv hsideT hsideQ
  have hg := hgen.sign (sgnB_cases ε)
  exact isRupert_vtxTwoFace_limit hn₀.three x N.inj lab hn₀.lab_injective (smul_ne_zero hs hv0)
    (fun n => sgnB ε • view29 (K n) v) ((tendsto_view29 hK v).const_smul _) K hK
    (hc.mono fun n hn => hn.1.toPts) (fun i hi => ((FT.hf hT.1) i).1 hi)
    (fun i hi => ((FQ.hf hQ.1) i).1 hi) hab hg.par hg.g1 hg.dist hσT hσQ hsa hsb

/-- **Proposition 22.2 at an edge view with a triangle and a quadrilateral through the axle**
(`Y2` at `46`): as `isRupert_twoFaceVtx29`, with `ParOnly` (only the axle seen end-on). -/
theorem isRupert_twoFaceEdge29 (N : NF29 x) {k : ℕ} [NeZero k] {v w : Fin 7} (hvw : v ≠ w)
    (ε : Bool) (lab : ZMod k → Fin 7)
    {ST SQ SO : Finset (Fin 7)} (FT : Face16 x ST) (FQ : Face16 x SQ) (FO : Face16 x SO)
    {a b c p q q₁ q₂ vv e jT jQ : Fin 7}
    (hT : a ∈ ST ∧ b ∈ ST ∧ c ∈ ST ∧ jT ∉ ST)
    (hQ : p ∈ SQ ∧ q ∈ SQ ∧ q₁ ∈ SQ ∧ q₂ ∈ SQ ∧ jQ ∉ SQ)
    (hO : p ∈ SO ∧ q ∈ SO ∧ q₁ ∉ SO ∧ q₂ ∉ SO)
    (hne : a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ p ≠ q ∧ p ≠ q₁ ∧ q ≠ q₁)
    (hvv : vv ∈ ST ∧ vv ∈ SQ ∧ e ∈ ST ∧ e ∉ SQ)
    (hsideT : ∀ i m', lab i ∈ ST → lab (i + 1) ∈ ST → m' ∈ ST → m' ≠ lab i → m' ≠ lab (i + 1) →
      lab i = a ∧ lab (i + 1) = b ∧ m' = c)
    (hsideQ : ∀ i m', lab i ∈ SQ → lab (i + 1) ∈ SQ → m' ∈ SQ → m' ≠ lab i → m' ≠ lab (i + 1) →
      lab i = p ∧ lab (i + 1) = q ∧ (m' = q₁ ∨ m' = q₂))
    (K : ℕ → Fin 7 → ℝ³) (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)))
    (hgen : TwoEdgeGen29 (univ.image x) (x w - x v) (x v) (x w) (ST.image x) (SQ.image x))
    (hc : ∃ᶠ n in atTop, RimCertAt (K n) (sgnB ε • view29 (K n) (.inl (v, w))) lab ∧
      TiesAt29 x (K n)) : IsRupert (univ.image x) := by
  obtain ⟨hab, σT, σQ, hσT, hσQ, hsa, hsb⟩ := twoFace_sides29 N.facets lab FT FQ FO hT hQ hO hne
    hvv hsideT hsideQ
  exact isRupert_twoFace_limit x N.inj lab hvw (sgnB ε) (sgnB_cases ε) K hK
    (hc.mono fun n hn => hn.1) (fun i hi => ((FT.hf hT.1) i).1 hi)
    (fun i hi => ((FQ.hf hQ.1) i).1 hi) hab hgen.par hgen.g1 hgen.dist hσT hσQ hsa hsb

end Minimality

end
