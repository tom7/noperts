module

public import Minimality.Type29K3
public import Minimality.Type21F2

@[expose] public section

/-!
# Type 29: certificates (`FEWER-FACES-PROOFS.md` §28, §18.2, §21)

The named views of type 29 and the certificate `Cert29` that every step of the K3a / K4a covers
ends in (the analogue of type 16's `Cert16`, `Type16NF.lean`):

* `view29`: the 21 segments and the 7 vertex lines `012/145`, `234/145`, `035/145`, `015/124`,
  `015/356`, `124/346`, `035/234` (`vtxLines29`), as functions of the shape `x` alone.
  `NF29.vtxView29_t`: `view29 x (.inr t) = κ_t D • N.v..` (`D` the frame determinant,
  `κ_t = ±1`), so the labelled view of a test is `c • view29 x v` with `c ≠ 0`
  (`namedAt_of_eq`, as type 16's `namedAt_vA`).
* `Cert29 x`: a labelled rim certificate (`RimCertPts` at `c • view29 x v`, a quadrilateral, a
  pentagon or a triangle of the whitelists `quadLabels29`, …) with closed region facts (`Ex29`),
  or an edge pair of Lemma E (`EPairData`).
* `OneTie29`: at most one tied pair at each nonzero named view (the hypothesis of the tie-tolerant
  tests); the pair cores `pair_core` (Corollary 13.3 with ties; the partner is preferred and the
  other test carries `⟪u, v⟫ ≤ 0`, as `VQuadCone`) and `robust_of_view_nhds`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- The view index: a segment `x j − x i` or one of the seven vertex lines. -/
abbrev View29 := (Fin 7 × Fin 7) ⊕ Fin 7

/-- The vertex lines of type 29, each by three labels on either plane
(`012/145`, `234/145`, `035/145`, `015/124`, `015/356`, `124/346`, `035/234`). -/
def vtxLines29 : Fin 7 → (Fin 7 × Fin 7 × Fin 7) × (Fin 7 × Fin 7 × Fin 7) :=
  ![((0, 1, 2), (1, 4, 5)), ((2, 3, 4), (1, 4, 5)), ((0, 3, 5), (1, 4, 5)),
    ((0, 1, 5), (1, 2, 4)), ((0, 1, 5), (3, 5, 6)), ((1, 2, 4), (3, 4, 6)),
    ((0, 3, 5), (2, 3, 4))]

/-- The direction of the line of two planes of `x` (`vtxLines29`). -/
noncomputable def vtxView29 (x : Fin 7 → ℝ³) (t : Fin 7) : ℝ³ :=
  planeLine (x (vtxLines29 t).1.1) (x (vtxLines29 t).1.2.1) (x (vtxLines29 t).1.2.2)
    (x (vtxLines29 t).2.1) (x (vtxLines29 t).2.2.1) (x (vtxLines29 t).2.2.2)

/-- **The named views** of a type-29 shape. -/
noncomputable def view29 (x : Fin 7 → ℝ³) : View29 → ℝ³
  | .inl (i, j) => x j - x i
  | .inr t => vtxView29 x t

/-- **At most one tied pair at each nonzero named view** (the codimension-2 hypothesis of the
tie-tolerant tests: a second tied pair is a second equation on the shape). -/
def OneTie29 (x : Fin 7 → ℝ³) : Prop :=
  ∀ v : View29, view29 x v ≠ 0 → OneTieAt (univ.image x) (view29 x v)

/-! ### Labelled views of a normal form -/

/-- A view `u = v'` positively or negatively proportional to a named view: `σ • v' = c • w`. -/
theorem namedAt_of_eq {D κ : ℝ} (hD : D ≠ 0) (hκ : κ ≠ 0) {v' w : ℝ³} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (h : w = (κ * D) • v') : ∃ c : ℝ, c ≠ 0 ∧ σ • v' = c • w := by
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have hκD : κ * D ≠ 0 := mul_ne_zero hκ hD
  refine ⟨σ * (κ * D)⁻¹, mul_ne_zero hσ0 (inv_ne_zero hκD), ?_⟩
  rw [h, smul_smul, mul_assoc, inv_mul_cancel₀ hκD, mul_one]

theorem namedAt_seg {x : Fin 7 → ℝ³} (i j : Fin 7) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ∃ c : ℝ, c ≠ 0 ∧ σ • (x j - x i) = c • view29 x (.inl (i, j)) :=
  ⟨σ, by rcases hσ with rfl | rfl <;> norm_num, rfl⟩

variable {x : Fin 7 → ℝ³}

theorem NF29.vtxView29_0 (N : NF29 x) : vtxView29 x 0 = ((1 : ℝ) * N.D) • N.vT1 := by
  show planeLine (x 0) (x 1) (x 2) (x 1) (x 4) (x 5) = _
  simp only [planeLine, NF29.vT1, NF29.D]
  nf29_simp N
  ext k
  simp only [nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul,
    det3c]
  ring

theorem NF29.vtxView29_1 (N : NF29 x) : vtxView29 x 1 = ((-1 : ℝ) * N.D) • N.vT2 := by
  show planeLine (x 2) (x 3) (x 4) (x 1) (x 4) (x 5) = _
  simp only [planeLine, NF29.vT2, NF29.D]
  nf29_simp N
  ext k
  simp only [nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul,
    det3c]
  ring

theorem NF29.vtxView29_2 (N : NF29 x) : vtxView29 x 2 = ((-1 : ℝ) * N.D) • N.vV := by
  show planeLine (x 0) (x 3) (x 5) (x 1) (x 4) (x 5) = _
  simp only [planeLine, NF29.vV, NF29.D]
  nf29_simp N
  ext k
  simp only [nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul,
    det3c]
  ring

theorem NF29.vtxView29_3 (N : NF29 x) : vtxView29 x 3 = ((1 : ℝ) * N.D) • N.vT3 := by
  show planeLine (x 0) (x 1) (x 5) (x 1) (x 2) (x 4) = _
  simp only [planeLine, NF29.vT3, NF29.D]
  nf29_simp N
  ext k
  simp only [nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul,
    det3c]
  ring

theorem NF29.vtxView29_4 (N : NF29 x) : vtxView29 x 4 = ((-1 : ℝ) * N.D) • N.vY1 := by
  show planeLine (x 0) (x 1) (x 5) (x 3) (x 5) (x 6) = _
  simp only [planeLine, NF29.vY1, NF29.D]
  nf29_simp N
  ext k
  simp only [nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul,
    det3c]
  ring

theorem NF29.vtxView29_6 (N : NF29 x) : vtxView29 x 6 = ((1 : ℝ) * N.D) • N.vZ := by
  show planeLine (x 0) (x 3) (x 5) (x 2) (x 3) (x 4) = _
  simp only [planeLine, NF29.vZ, NF29.D]
  nf29_simp N
  ext k
  simp only [nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul,
    det3c]
  ring

theorem NF29.namedAt_vT1 (N : NF29 x) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ∃ c : ℝ, c ≠ 0 ∧ σ • N.vT1 = c • view29 x (.inr 0) :=
  namedAt_of_eq N.hD (by norm_num) hσ (N.vtxView29_0)

theorem NF29.namedAt_vT2 (N : NF29 x) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ∃ c : ℝ, c ≠ 0 ∧ σ • N.vT2 = c • view29 x (.inr 1) :=
  namedAt_of_eq N.hD (by norm_num) hσ (N.vtxView29_1)

theorem NF29.namedAt_vV (N : NF29 x) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ∃ c : ℝ, c ≠ 0 ∧ σ • N.vV = c • view29 x (.inr 2) :=
  namedAt_of_eq N.hD (by norm_num) hσ (N.vtxView29_2)

theorem NF29.namedAt_vT3 (N : NF29 x) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ∃ c : ℝ, c ≠ 0 ∧ σ • N.vT3 = c • view29 x (.inr 3) :=
  namedAt_of_eq N.hD (by norm_num) hσ (N.vtxView29_3)

theorem NF29.namedAt_vY1 (N : NF29 x) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ∃ c : ℝ, c ≠ 0 ∧ σ • N.vY1 = c • view29 x (.inr 4) :=
  namedAt_of_eq N.hD (by norm_num) hσ (N.vtxView29_4)

theorem NF29.namedAt_vZ (N : NF29 x) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ∃ c : ℝ, c ≠ 0 ∧ σ • N.vZ = c • view29 x (.inr 6) :=
  namedAt_of_eq N.hD (by norm_num) hσ (N.vtxView29_6)

/-- The vertex views as multiples of the named views (`κ = ±1`): `N.vT1 = D⁻¹ w₀`,
`N.vT2 = −D⁻¹ w₁`, `N.vV = −D⁻¹ w₂`, `N.vT3 = D⁻¹ w₃`, `N.vY1 = −D⁻¹ w₄`, `N.vZ = D⁻¹ w₆`. -/
theorem NF29.vT1_eq (N : NF29 x) : N.vT1 = N.D⁻¹ • view29 x (.inr 0) := by
  show _ = _ • vtxView29 x 0
  rw [N.vtxView29_0, smul_smul, one_mul, inv_mul_cancel₀ (show N.D ≠ 0 from N.hD), one_smul]

theorem NF29.vT2_eq (N : NF29 x) : N.vT2 = (-N.D)⁻¹ • view29 x (.inr 1) := by
  show _ = _ • vtxView29 x 1
  have h : (-N.D) ≠ 0 := neg_ne_zero.mpr N.hD
  rw [N.vtxView29_1, smul_smul, neg_one_mul, inv_mul_cancel₀ h, one_smul]

theorem NF29.vV_eq (N : NF29 x) : N.vV = (-N.D)⁻¹ • view29 x (.inr 2) := by
  show _ = _ • vtxView29 x 2
  have h : (-N.D) ≠ 0 := neg_ne_zero.mpr N.hD
  rw [N.vtxView29_2, smul_smul, neg_one_mul, inv_mul_cancel₀ h, one_smul]

theorem NF29.vT3_eq (N : NF29 x) : N.vT3 = N.D⁻¹ • view29 x (.inr 3) := by
  show _ = _ • vtxView29 x 3
  rw [N.vtxView29_3, smul_smul, one_mul, inv_mul_cancel₀ (show N.D ≠ 0 from N.hD), one_smul]

theorem NF29.vY1_eq (N : NF29 x) : N.vY1 = (-N.D)⁻¹ • view29 x (.inr 4) := by
  show _ = _ • vtxView29 x 4
  have h : (-N.D) ≠ 0 := neg_ne_zero.mpr N.hD
  rw [N.vtxView29_4, smul_smul, neg_one_mul, inv_mul_cancel₀ h, one_smul]

theorem NF29.vZ_eq (N : NF29 x) : N.vZ = N.D⁻¹ • view29 x (.inr 6) := by
  show _ = _ • vtxView29 x 6
  rw [N.vtxView29_6, smul_smul, one_mul, inv_mul_cancel₀ (show N.D ≠ 0 from N.hD), one_smul]

/-! ### The certificate -/

/-- **Closed region facts carried by a certificate** (§22: what the limit argument needs at the
tests whose view can degenerate).  `t1`: `T1` of `P14` (`θ ≥ α`, `h2 ≤ 1`, and the partner `T2`
failing gives `⟪vT1, vT2⟫ ≤ 0`, i.e. `⟪w₀, w₁⟫ ≥ 0` for the named views); `t1o`: `T1` of `P11`
(`1 ≤ h2`, `⟪vT1, vT3⟫ ≤ 0`, i.e. `⟪w₀, w₃⟫ ≤ 0`); `t2`: `T2` of the region `h2 < 1`
(`h0 ≤ h2 ≤ 1`); `t2o`: `T2` of the region `1 < h2` (`h0 ≤ 1 ≤ h2`). -/
inductive Ex29 | none | t1 | t1o | t2 | t2o
  deriving DecidableEq

/-- The facts of an `Ex29` tag (existentially in a normal form of `x`). -/
def Ex29.facts (x : Fin 7 → ℝ³) : Ex29 → Prop
  | .none => True
  | .t1 => (∃ N : NF29 x, 0 ≤ -N.a2 * N.t + N.b2 * N.s ∧ N.h2 ≤ 1) ∧
      0 ≤ ⟪view29 x (.inr 0), view29 x (.inr 1)⟫
  | .t1o => (∃ N : NF29 x, 0 ≤ -N.a2 * N.t + N.b2 * N.s ∧ 1 ≤ N.h2) ∧
      ⟪view29 x (.inr 0), view29 x (.inr 3)⟫ ≤ 0
  | .t2 => ∃ N : NF29 x, N.h0 ≤ N.h2 ∧ N.h2 ≤ 1
  | .t2o => ∃ N : NF29 x, N.h0 ≤ 1 ∧ 1 ≤ N.h2

/-- The labelled four-corner rims of the K3a / K4a covers: view, rim, region tag (the last entry
is `V' = 1456/234`, the `σ`-image of `V`, tier (B1)). -/
def quadLabels29 : Finset (View29 × (Fin 7 × Fin 7 × Fin 7 × Fin 7) × Ex29) :=
  {(.inr 0, (1, 2, 3, 6), .t1), (.inr 0, (1, 2, 3, 6), .t1o), (.inr 1, (4, 3, 0, 5), .t2),
    (.inr 1, (4, 2, 0, 5), .t2o), (.inr 3, (1, 4, 3, 0), .none), (.inr 3, (1, 4, 6, 5), .none),
    (.inr 3, (1, 4, 3, 5), .none), (.inl (0, 5), (5, 1, 4, 3), .none),
    (.inr 4, (1, 4, 6, 5), .none), (.inr 4, (5, 1, 4, 3), .none),
    (.inr 2, (5, 1, 2, 3), .none), (.inl (0, 3), (3, 5, 1, 2), .none),
    (.inr 6, (3, 0, 1, 4), .none), (.inr 1, (4, 1, 0, 3), .none)}

/-- The labelled five-corner rims: `Y2` (`1456/346-4`), `Y = 035/356-3` and `Y' = 234/346-3`
(the `σ`-image of `Y`, tier (B1)). -/
def quintLabels29 : Finset (View29 × (Fin 7 × Fin 7 × Fin 7 × Fin 7 × Fin 7)) :=
  {(.inl (4, 6), (6, 3, 2, 0, 5)), (.inl (3, 5), (5, 0, 1, 4, 6)),
    (.inl (3, 4), (4, 2, 1, 5, 6))}

/-- The labelled triangular rims: `T2` with `0` or `1`-side hidden (region `h2 < 1`). -/
def triLabels29 : Finset (View29 × (Fin 7 × Fin 7 × Fin 7) × Ex29) :=
  {(.inr 1, (4, 3, 5), .t2), (.inr 1, (4, 3, 6), .t2)}

/-- The labelled edge pairs `(v, w, a, b, c)` of Lemma E (C1 tier and `6 ∉ R`). -/
def ePairLabels29 : Finset (Fin 7 × Fin 7 × Fin 7 × Fin 7 × Fin 7) :=
  {(0, 5, 1, 3, 2), (2, 4, 3, 1, 0), (4, 1, 5, 2, 3), (4, 1, 6, 2, 3), (1, 5, 4, 0, 2),
    (5, 1, 0, 4, 3), (5, 1, 0, 6, 3), (0, 3, 5, 2, 1), (1, 4, 2, 5, 0), (6, 5, 3, 1, 2),
    (4, 6, 3, 1, 2)}

/-- A four-corner certificate: a rim of `quadLabels29` as `RimCertPts` at `c • view29 x v`. -/
def CertQ29 (x : Fin 7 → ℝ³) : Prop :=
  ∃ (v : View29) (i₀ i₁ i₂ i₃ : Fin 7) (e : Ex29),
    (v, (i₀, i₁, i₂, i₃), e) ∈ quadLabels29 ∧ e.facts x ∧
      ∃ c : ℝ, c ≠ 0 ∧
        RimCertPts (univ.image x) (c • view29 x v) (quad (x i₀) (x i₁) (x i₂) (x i₃))

/-- A five-corner certificate. -/
def CertQ5_29 (x : Fin 7 → ℝ³) : Prop :=
  ∃ (v : View29) (i₀ i₁ i₂ i₃ i₄ : Fin 7), (v, (i₀, i₁, i₂, i₃, i₄)) ∈ quintLabels29 ∧
    ∃ c : ℝ, c ≠ 0 ∧
      RimCertPts (univ.image x) (c • view29 x v) (quint (x i₀) (x i₁) (x i₂) (x i₃) (x i₄))

/-- A triangular certificate. -/
def CertT29 (x : Fin 7 → ℝ³) : Prop :=
  ∃ (v : View29) (i₀ i₁ i₂ : Fin 7) (e : Ex29), (v, (i₀, i₁, i₂), e) ∈ triLabels29 ∧
    e.facts x ∧ ∃ c : ℝ, c ≠ 0 ∧
      RimCertPts (univ.image x) (c • view29 x v) (tri (x i₀) (x i₁) (x i₂))

/-- An edge-pair certificate (Lemma E with ties, Corollary 14.1): the data of
`rimCert_edgePairσ_robust`, including the Lemma E inequality `hE`. -/
def CertE29 (x : Fin 7 → ℝ³) : Prop :=
  ∃ v w a b c : Fin 7, (v, w, a, b, c) ∈ ePairLabels29 ∧
    ∃ σ : ℝ, EPairData (univ.image x) σ (x v) (x w) (x a) (x b) (x c)

/-- **A type-29 certificate**: a labelled rim certificate at a named view (with its region
facts), or an edge pair of Lemma E.  Every step of the K3a / K4a covers ends in one. -/
def Cert29 (x : Fin 7 → ℝ³) : Prop := CertQ29 x ∨ CertQ5_29 x ∨ CertT29 x ∨ CertE29 x

theorem Cert29.ofQuad {v : View29} (i₀ i₁ i₂ i₃ : Fin 7) (e : Ex29)
    (hm : (v, (i₀, i₁, i₂, i₃), e) ∈ quadLabels29) (hx : e.facts x) {u : ℝ³}
    (hn : ∃ c : ℝ, c ≠ 0 ∧ u = c • view29 x v)
    (h : RimCertPts (univ.image x) u (quad (x i₀) (x i₁) (x i₂) (x i₃))) : Cert29 x := by
  obtain ⟨c, hc, rfl⟩ := hn
  exact Or.inl ⟨v, i₀, i₁, i₂, i₃, e, hm, hx, c, hc, h⟩

theorem Cert29.ofQuint {v : View29} (i₀ i₁ i₂ i₃ i₄ : Fin 7)
    (hm : (v, (i₀, i₁, i₂, i₃, i₄)) ∈ quintLabels29) {u : ℝ³}
    (hn : ∃ c : ℝ, c ≠ 0 ∧ u = c • view29 x v)
    (h : RimCertPts (univ.image x) u (quint (x i₀) (x i₁) (x i₂) (x i₃) (x i₄))) : Cert29 x := by
  obtain ⟨c, hc, rfl⟩ := hn
  exact Or.inr (Or.inl ⟨v, i₀, i₁, i₂, i₃, i₄, hm, c, hc, h⟩)

theorem Cert29.ofTri {v : View29} (i₀ i₁ i₂ : Fin 7) (e : Ex29)
    (hm : (v, (i₀, i₁, i₂), e) ∈ triLabels29) (hx : e.facts x) {u : ℝ³}
    (hn : ∃ c : ℝ, c ≠ 0 ∧ u = c • view29 x v)
    (h : RimCertPts (univ.image x) u (tri (x i₀) (x i₁) (x i₂))) : Cert29 x := by
  obtain ⟨c, hc, rfl⟩ := hn
  exact Or.inr (Or.inr (Or.inl ⟨v, i₀, i₁, i₂, e, hm, hx, c, hc, h⟩))

theorem Cert29.ofEPair (v w a b c : Fin 7) (hm : (v, w, a, b, c) ∈ ePairLabels29) {σ : ℝ}
    (h : EPairData (univ.image x) σ (x v) (x w) (x a) (x b) (x c)) : Cert29 x :=
  Or.inr (Or.inr (Or.inr ⟨v, w, a, b, c, hm, σ, h⟩))

/-- The tier (A) certificate `V = 035/1456` (rim `(5, 1, 2, 3)`). -/
def CertV29 (x : Fin 7 → ℝ³) : Prop :=
  ∃ c : ℝ, c ≠ 0 ∧
    RimCertPts (univ.image x) (c • view29 x (.inr 2)) (quad (x 5) (x 1) (x 2) (x 3))

/-- The tier (A) certificate `Y = 035/356-3` (rim `(5, 0, 1, 4, 6)`). -/
def CertY29 (x : Fin 7 → ℝ³) : Prop :=
  ∃ c : ℝ, c ≠ 0 ∧
    RimCertPts (univ.image x) (c • view29 x (.inl (3, 5))) (quint (x 5) (x 0) (x 1) (x 4) (x 6))

theorem Cert29.ofV (h : CertV29 x) : Cert29 x := by
  obtain ⟨c, hc, h⟩ := h
  exact Or.inl ⟨.inr 2, 5, 1, 2, 3, .none, by decide, trivial, c, hc, h⟩

theorem Cert29.ofY (h : CertY29 x) : Cert29 x := by
  obtain ⟨c, hc, h⟩ := h
  exact Or.inr (Or.inl ⟨.inl (3, 5), 5, 0, 1, 4, 6, by decide, c, hc, h⟩)

theorem view29_sigma_inr2 (x : Fin 7 → ℝ³) :
    view29 (x ∘ sigma29) (.inr 2) = -view29 x (.inr 1) := by
  show planeLine (x 2) (x 3) (x 4) (x 1) (x 5) (x 4) = -planeLine (x 2) (x 3) (x 4) (x 1) (x 4) (x
      5)
  ext k
  simp only [planeLine, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
    PiLp.neg_apply, smul_eq_mul]
  ring

/-- **The `σ`-image of tier (A)** (tier (B1) of K4a): a tier (A) certificate of `x ∘ σ` is a
certificate of `x` (`V' = 1456/234`, rim `(4, 1, 0, 3)`; `Y' = 234/346-3`, rim `(4, 2, 1, 5, 6)`),
`σ = (0 2)(4 5)`. -/
theorem Cert29.ofSigmaA (h : CertV29 (x ∘ sigma29) ∨ CertY29 (x ∘ sigma29)) : Cert29 x := by
  rw [CertV29, CertY29, image_sigma29] at h
  rcases h with ⟨c, hc, h⟩ | ⟨c, hc, h⟩
  · rw [view29_sigma_inr2, smul_neg, ← neg_smul] at h
    exact Or.inl ⟨.inr 1, 4, 1, 0, 3, .none, by decide, trivial, -c, neg_ne_zero.mpr hc, h⟩
  · exact Or.inr (Or.inl ⟨.inl (3, 4), 4, 2, 1, 5, 6, by decide, c, hc, h⟩)

/-- Every type-29 certificate is a rim certificate at (a multiple of) a named view. -/
theorem Cert29.rimCert (h : Cert29 x) :
    ∃ (v : View29) (c : ℝ), c ≠ 0 ∧ RimCert (univ.image x) (c • view29 x v) := by
  rcases h with ⟨v, i₀, i₁, i₂, i₃, e, -, -, c, hc, hr⟩ | ⟨v, i₀, i₁, i₂, i₃, i₄, -, c, hc, hr⟩ |
    ⟨v, i₀, i₁, i₂, e, -, -, c, hc, hr⟩ | ⟨v, w, a, b, c, -, σ, hσ, q₁, q₂, q₃, q₄, hE, h3, hV⟩
  · exact ⟨v, c, hc, hr.rimCert4⟩
  · exact ⟨v, c, hc, hr.rimCert5⟩
  · exact ⟨v, c, hc, hr.rimCert3⟩
  · exact ⟨.inl (v, w), 1, one_ne_zero, by
      rw [one_smul]
      exact rimCert_edgePairσ_robust _ hσ (img29 v) (img29 w) (img29 a) (img29 b) (img29 c)
        q₁ q₂ q₃ q₄ hE h3 hV⟩

end Minimality

end
