module

public import Minimality.Type16

@[expose] public section

/-!
# Type 16: Theorem M, the octahedral region (`FEWER-FACES-PROOFS.md` §11)

On the *octahedral region* `O = K − 5` is an octahedron: `12` is an edge of `conv O`,
with the faces `123`, `124` (`Oct16`).  Its opposite pairs are `(1, 0)`, `(2, 6)`,
`(3, 4)`; `Oct16.facets` bundles its eight facet functions (`OctFacets` with the labels
`a, a', b, b', c, c' = 1, 0, 2, 6, 3, 4` of §10, the cap face `{1, 2, 3}`).

* **Lemma 11.1** (`Oct16.five_beyond`, `Oct16.isCap`): `5` lies strictly beyond the
  planes of `123` and `124`, so the line `ℓ = 35` meets the plane `124` in a point
  `5* = 3 + λ (5 − 3)`, `0 < λ < 1` (`Oct16.star`), and `O ∪ {5*}` is a type-08 point
  set with the cap `5*` (`IsCap`).
* **Lemma 11.4 with §10's Lemma 7** (`isRupert_type16_N2`, the case N2 of S1 at the
  view along `ℓ`): in J's labelling `(a, b, c) = (1, 3, 2)` (`κ_1, κ_3 > 0`,
  `[3 2] < 0`), if the far end of `0235` along `35` is `0`, then `0 → 2` is a quad edge
  of `O` that is not bad, `5` is a middle at its view (it lies beneath `024`, on `023`,
  beyond `123`), and Lemma 9.3 with a middle applies.  By `σ = (0 6)(1 2)`:
  `isRupert_type16_N2σ` (test `61`).
* **Lemma 11.3 (a)** (`type16_not_bad35_thirdQuad`): far ends `2` and `1`: the plane
  quadrilateral `5*, 1, 4, 2` (on the plane `124`) has no saddle and `z 3 < z 5*`, so
  `35` is not bad (Lemma 11.U then gives the test at `35`).
* **Lemma 11.3 (b)** (`type16_not_bad35_T4`, `type16_not_bad35_T4σ`): far ends `0`, `1`
  with `[1 3] [2 6] > 0` (resp. `2`, `6` with `[2 3] [1 0] > 0`): §10's T4 argument for
  `K* = O ∪ {5*}` at its edge `5* 3` (Lemmas 9.7, 4, 3; `t4_not_bad'`, where `κ_b` need
  only be nonzero) shows `35` is not bad.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### The octahedral region -/

/-- A facet of the octahedron `O = K − 5` with index set `S`: vanishing on `S`,
negative at the other points of `O` (no condition at `5`). -/
structure FaceO (x : Fin 7 → ℝ³) (S : Finset (Fin 7)) where
  f : ℝ³ → ℝ
  N : ℝ³
  hN : ∀ y z, f y - f z = ⟪N, y - z⟫
  zero : ∀ i ∈ S, f (x i) = 0
  neg : ∀ i ∉ S, i ≠ 5 → f (x i) < 0

/-- **The octahedral region** of type 16: `12` is an edge of `conv (K − 5)`, with the
faces `123` and `124`. -/
structure Oct16 (x : Fin 7 → ℝ³) where
  t123 : FaceO x {1, 2, 3}
  t124 : FaceO x {1, 2, 4}

/-- Relabel a facet of `O` by `σ` (fixing `5`). -/
def FaceO.comp {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (F : FaceO x S) (σ : Fin 7 → Fin 7)
    (S' : Finset (Fin 7)) (hS : ∀ i, i ∈ S' ↔ σ i ∈ S) (h5 : ∀ i, i ≠ 5 → σ i ≠ 5) :
    FaceO (x ∘ σ) S' :=
  ⟨F.f, F.N, F.hN, fun i hi => F.zero (σ i) ((hS i).mp hi),
    fun i hi h5' => F.neg (σ i) (fun h => hi ((hS i).mpr h)) (h5 i h5')⟩

/-- The octahedral region is invariant under `σ = (0 6)(1 2)`. -/
def Oct16.sigma {x : Fin 7 → ℝ³} (O : Oct16 x) : Oct16 (x ∘ sigma16) :=
  ⟨O.t123.comp sigma16 _ (by decide) (by decide), O.t124.comp sigma16 _ (by decide) (by decide)⟩

/-- Coordinates of a point in a frame read off three affine functions with a
nonsingular value matrix, and the value of a fourth affine function there. -/
theorem affine_eval_frame {f₀ f₁ f₂ g : ℝ³ → ℝ} {N₀ N₁ N₂ M : ℝ³}
    (h₀ : ∀ y z, f₀ y - f₀ z = ⟪N₀, y - z⟫) (h₁ : ∀ y z, f₁ y - f₁ z = ⟪N₁, y - z⟫)
    (h₂ : ∀ y z, f₂ y - f₂ z = ⟪N₂, y - z⟫) (hg : ∀ y z, g y - g z = ⟪M, y - z⟫)
    (o e₀ e₁ e₂ w : ℝ³) (α β γ : ℝ)
    (hdet : (f₀ e₀ - f₀ o) * ((f₁ e₁ - f₁ o) * (f₂ e₂ - f₂ o) - (f₁ e₂ - f₁ o) * (f₂ e₁ - f₂ o)) -
      (f₀ e₁ - f₀ o) * ((f₁ e₀ - f₁ o) * (f₂ e₂ - f₂ o) - (f₁ e₂ - f₁ o) * (f₂ e₀ - f₂ o)) +
      (f₀ e₂ - f₀ o) * ((f₁ e₀ - f₁ o) * (f₂ e₁ - f₂ o) - (f₁ e₁ - f₁ o) * (f₂ e₀ - f₂ o)) ≠ 0)
    (h0w : f₀ w = f₀ o + α * (f₀ e₀ - f₀ o) + β * (f₀ e₁ - f₀ o) + γ * (f₀ e₂ - f₀ o))
    (h1w : f₁ w = f₁ o + α * (f₁ e₀ - f₁ o) + β * (f₁ e₁ - f₁ o) + γ * (f₁ e₂ - f₁ o))
    (h2w : f₂ w = f₂ o + α * (f₂ e₀ - f₂ o) + β * (f₂ e₁ - f₂ o) + γ * (f₂ e₂ - f₂ o)) :
    g w = g o + α * (g e₀ - g o) + β * (g e₁ - g o) + γ * (g e₂ - g o) := by
  have e := eq_of_affine3 h₀ h₁ h₂ o e₀ e₁ e₂ hdet (w := w)
    (w' := o + α • (e₀ - o) + β • (e₁ - o) + γ • (e₂ - o))
    (by rw [affine_frame3 h₀]; exact h0w) (by rw [affine_frame3 h₁]; exact h1w)
    (by rw [affine_frame3 h₂]; exact h2w)
  rw [e, affine_frame3 hg]

/-- **Lemma 11.1 (5 beyond `123` and `124`).**  In the octahedral region, `5` lies
strictly beyond the planes of the faces `123` and `124` of `O` (otherwise they would be
faces of `K`, but `12` is not an edge of `K`). -/
theorem Oct16.five_beyond {x : Fin 7 → ℝ³} (T : Type16 x) (O : Oct16 x) :
    0 < O.t123.f (x 5) ∧ 0 < O.t124.f (x 5) := by
  constructor
  · -- the frame `3; 1, 2, 0` with the faces `0235`, `1356`, `036`
    have A0 := T.q0235.zero 0 (by decide); have A2 := T.q0235.zero 2 (by decide)
    have A3 := T.q0235.zero 3 (by decide); have A5 := T.q0235.zero 5 (by decide)
    have A1 := T.q0235.neg 1 (by decide)
    have B1 := T.q1356.zero 1 (by decide); have B3 := T.q1356.zero 3 (by decide)
    have B5 := T.q1356.zero 5 (by decide); have B0 := T.q1356.neg 0 (by decide)
    have B2 := T.q1356.neg 2 (by decide)
    have D0 := T.t036.zero 0 (by decide); have D3 := T.t036.zero 3 (by decide)
    have D2 := T.t036.neg 2 (by decide); have D5 := T.t036.neg 5 (by decide)
    have g1 := O.t123.zero 1 (by decide); have g2 := O.t123.zero 2 (by decide)
    have g3 := O.t123.zero 3 (by decide); have g0 := O.t123.neg 0 (by decide) (by decide)
    set β := T.t036.f (x 5) / T.t036.f (x 2)
    set γ := -β * T.q1356.f (x 2) / T.q1356.f (x 0)
    have hβ : 0 < β := div_pos_of_neg_of_neg D5 D2
    have hγ : γ < 0 := by
      simp only [γ, neg_mul, neg_div]
      exact neg_neg_of_pos (div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hβ B2) B0)
    have e := affine_eval_frame T.q0235.hN T.q1356.hN T.t036.hN O.t123.hN (x 3) (x 1) (x 2)
      (x 0) (x 5) 0 β γ ?_ ?_ ?_ ?_
    · rw [e, g1, g2, g3]; nlinarith
    · rw [A0, A2, A3, B1, B3, D0, D3]
      have := mul_ne_zero A1.ne (mul_ne_zero B0.ne D2.ne)
      intro h; apply this; linarith
    · rw [A0, A2, A3, A5]; ring
    · have := B0.ne; rw [B1, B3, B5]; simp only [γ]; field_simp; ring
    · have := D2.ne; rw [D0, D3]; simp only [β]; field_simp; ring
  · -- the frame `4; 1, 2, 0` with the faces `245`, `145`, `024`
    have H2 := T.t245.zero 2 (by decide); have H4 := T.t245.zero 4 (by decide)
    have H5 := T.t245.zero 5 (by decide); have H1 := T.t245.neg 1 (by decide)
    have H0 := T.t245.neg 0 (by decide)
    have F1 := T.t145.zero 1 (by decide); have F4 := T.t145.zero 4 (by decide)
    have F5 := T.t145.zero 5 (by decide); have F2 := T.t145.neg 2 (by decide)
    have F0 := T.t145.neg 0 (by decide)
    have C0 := T.t024.zero 0 (by decide); have C2 := T.t024.zero 2 (by decide)
    have C4 := T.t024.zero 4 (by decide); have C1 := T.t024.neg 1 (by decide)
    have C5 := T.t024.neg 5 (by decide)
    have g1 := O.t124.zero 1 (by decide); have g2 := O.t124.zero 2 (by decide)
    have g4 := O.t124.zero 4 (by decide); have g0 := O.t124.neg 0 (by decide) (by decide)
    set α := T.t024.f (x 5) / T.t024.f (x 1)
    set γ := -α * T.t245.f (x 1) / T.t245.f (x 0)
    set β := -γ * T.t145.f (x 0) / T.t145.f (x 2)
    have hα : 0 < α := div_pos_of_neg_of_neg C5 C1
    have hγ : γ < 0 := by
      simp only [γ, neg_mul, neg_div]
      exact neg_neg_of_pos (div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hα H1) H0)
    have e := affine_eval_frame T.t245.hN T.t145.hN T.t024.hN O.t124.hN (x 4) (x 1) (x 2)
      (x 0) (x 5) α β γ ?_ ?_ ?_ ?_
    · rw [e, g1, g2, g4]; nlinarith
    · rw [H2, H4, F1, F4, C0, C2, C4]
      have := mul_ne_zero H0.ne (mul_ne_zero F2.ne C1.ne)
      intro h; apply this; linarith
    · have := H0.ne; rw [H2, H4, H5]; simp only [γ]; field_simp; ring
    · have := F2.ne; rw [F1, F4, F5]; simp only [β]; field_simp; ring
    · have := C1.ne; rw [C0, C2, C4]; simp only [α]; field_simp; ring

/-- An affine function on the line `o + λ (v − o)`. -/
theorem affine_line {f : ℝ³ → ℝ} {N : ℝ³} (hf : ∀ y z, f y - f z = ⟪N, y - z⟫) (o v : ℝ³)
    (l : ℝ) : f (o + l • (v - o)) = (1 - l) * f o + l * f v := by
  have h := hf (o + l • (v - o)) o
  rw [add_sub_cancel_left, real_inner_smul_right, ← hf] at h
  linarith

/-- The parameter of `5* = 3 + λ (5 − 3)` on the plane `124`. -/
noncomputable def Oct16.lam {x : Fin 7 → ℝ³} (O : Oct16 x) : ℝ :=
  O.t124.f (x 3) / (O.t124.f (x 3) - O.t124.f (x 5))

/-- The virtual cap `5*` of Lemma 11.1: the point of `ℓ = 35` on the plane `124`. -/
noncomputable def Oct16.star {x : Fin 7 → ℝ³} (O : Oct16 x) : ℝ³ :=
  x 3 + O.lam • (x 5 - x 3)

theorem Oct16.lam_pos {x : Fin 7 → ℝ³} (T : Type16 x) (O : Oct16 x) :
    0 < O.lam ∧ O.lam < 1 := by
  have g3 := O.t124.neg 3 (by decide) (by decide)
  have g5 := (O.five_beyond T).2
  refine ⟨div_pos_of_neg_of_neg g3 (by linarith), ?_⟩
  rw [Oct16.lam, div_lt_one_of_neg (by linarith)]; linarith

/-- Any affine function at `5*`. -/
theorem Oct16.star_eval {x : Fin 7 → ℝ³} (O : Oct16 x) {f : ℝ³ → ℝ} {N : ℝ³}
    (hf : ∀ y z, f y - f z = ⟪N, y - z⟫) :
    f O.star = (1 - O.lam) * f (x 3) + O.lam * f (x 5) :=
  affine_line hf (x 3) (x 5) O.lam

theorem Oct16.t124_star {x : Fin 7 → ℝ³} (T : Type16 x) (O : Oct16 x) :
    O.t124.f O.star = 0 := by
  have g3 := O.t124.neg 3 (by decide) (by decide)
  have g5 := (O.five_beyond T).2
  have hne : O.t124.f (x 3) - O.t124.f (x 5) ≠ 0 := by linarith
  rw [O.star_eval O.t124.hN, Oct16.lam]
  field_simp
  ring

/-- A negative value at `3` and a nonpositive one at `5` give a negative value at `5*`. -/
theorem Oct16.star_neg {x : Fin 7 → ℝ³} (T : Type16 x) (O : Oct16 x) {f : ℝ³ → ℝ} {N : ℝ³}
    (hf : ∀ y z, f y - f z = ⟪N, y - z⟫) (h3 : f (x 3) < 0) (h5 : f (x 5) ≤ 0) :
    f O.star < 0 := by
  obtain ⟨l0, l1⟩ := O.lam_pos T
  rw [O.star_eval hf]
  nlinarith

/-- A facet function of `O` from a facet of `K`. -/
noncomputable def Face16.toO {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (F : Face16 x S)
    (i j k : Fin 7) (hi : i ∈ S) (hj : j ∈ S) (hk : k ∈ S)
    (hI : ∀ l ∈ ({1, 0, 2, 6, 3, 4} : Finset (Fin 7)), l ≠ i → l ≠ j → l ≠ k → l ∉ S) :
    FacetFn {x 1, x 0, x 2, x 6, x 3, x 4} (x i) (x j) (x k) :=
  ⟨F.f, F.N, F.hN, F.zero i hi, F.zero j hj, F.zero k hk, fun w hw h1 h2 h3 => by
    have key : ∀ l ∈ ({1, 0, 2, 6, 3, 4} : Finset (Fin 7)), w = x l → F.f w < 0 := by
      rintro l hl rfl
      exact F.neg l (hI l hl (fun h => h1 (by rw [h])) (fun h => h2 (by rw [h]))
        (fun h => h3 (by rw [h])))
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with h | h | h | h | h | h
    exacts [key 1 (by decide) h, key 0 (by decide) h, key 2 (by decide) h, key 6 (by decide) h,
      key 3 (by decide) h, key 4 (by decide) h]⟩

/-- A facet function of `O` from a facet of the octahedral region. -/
noncomputable def FaceO.toO {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (F : FaceO x S)
    (i j k : Fin 7) (hi : i ∈ S) (hj : j ∈ S) (hk : k ∈ S)
    (hI : ∀ l ∈ ({1, 0, 2, 6, 3, 4} : Finset (Fin 7)), l ≠ i → l ≠ j → l ≠ k → l ∉ S ∧ l ≠ 5) :
    FacetFn {x 1, x 0, x 2, x 6, x 3, x 4} (x i) (x j) (x k) :=
  ⟨F.f, F.N, F.hN, F.zero i hi, F.zero j hj, F.zero k hk, fun w hw h1 h2 h3 => by
    have key : ∀ l ∈ ({1, 0, 2, 6, 3, 4} : Finset (Fin 7)), w = x l → F.f w < 0 := by
      rintro l hl rfl
      obtain ⟨h4, h5⟩ := hI l hl (fun h => h1 (by rw [h])) (fun h => h2 (by rw [h]))
        (fun h => h3 (by rw [h]))
      exact F.neg l h4 h5
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with h | h | h | h | h | h
    exacts [key 1 (by decide) h, key 0 (by decide) h, key 2 (by decide) h, key 6 (by decide) h,
      key 3 (by decide) h, key 4 (by decide) h]⟩

/-- **The octahedron `O = K − 5`** with opposite pairs `(1, 0)`, `(2, 6)`, `(3, 4)`: its
eight facets are `123`, `124` (`Oct16`), the halves `136`, `023` of `K`'s
quadrilaterals, and `K`'s triangles `146`, `024`, `036`, `046`. -/
noncomputable def Oct16.facets {x : Fin 7 → ℝ³} (T : Type16 x) (O : Oct16 x) :
    OctFacets (x 1) (x 0) (x 2) (x 6) (x 3) (x 4) :=
  ⟨List.Nodup.map (l := [1, 0, 2, 6, 3, 4]) T.inj (by decide),
    O.t123.toO 1 2 3 (by decide) (by decide) (by decide) (by decide),
    O.t124.toO 1 2 4 (by decide) (by decide) (by decide) (by decide),
    T.q1356.toO 1 6 3 (by decide) (by decide) (by decide) (by decide),
    T.t146.toO 1 6 4 (by decide) (by decide) (by decide) (by decide),
    T.q0235.toO 0 2 3 (by decide) (by decide) (by decide) (by decide),
    T.t024.toO 0 2 4 (by decide) (by decide) (by decide) (by decide),
    T.t036.toO 0 6 3 (by decide) (by decide) (by decide) (by decide),
    T.t046.toO 0 6 4 (by decide) (by decide) (by decide) (by decide)⟩

/-- **Lemma 11.1 (the virtual shape `K*`).**  `5*` is a type-08 cap over `O`: on the
planes of `124`, `136`, `023`, beyond `123`, beneath `146`, `024`, `036`, `046`. -/
theorem Oct16.isCap {x : Fin 7 → ℝ³} (T : Type16 x) (O : Oct16 x) :
    IsCap (O.facets T) O.star := by
  obtain ⟨l0, l1⟩ := O.lam_pos T
  have hz : ∀ {f : ℝ³ → ℝ} {N : ℝ³}, (∀ y z, f y - f z = ⟪N, y - z⟫) → f (x 3) = 0 →
      f (x 5) = 0 → f O.star = 0 := by
    intro f N hf h3 h5; rw [O.star_eval hf, h3, h5]; ring
  refine ⟨O.t124_star T, hz T.q1356.hN (T.q1356.zero 3 (by decide)) (T.q1356.zero 5 (by decide)),
    hz T.q0235.hN (T.q0235.zero 3 (by decide)) (T.q0235.zero 5 (by decide)), ?_,
    O.star_neg T T.t146.hN (T.t146.neg 3 (by decide)) (T.t146.neg 5 (by decide)).le,
    O.star_neg T T.t024.hN (T.t024.neg 3 (by decide)) (T.t024.neg 5 (by decide)).le,
    ?_, O.star_neg T T.t046.hN (T.t046.neg 3 (by decide)) (T.t046.neg 5 (by decide)).le⟩
  · show 0 < O.t123.f O.star
    rw [O.star_eval O.t123.hN, O.t123.zero 3 (by decide)]
    nlinarith [(O.five_beyond T).1]
  · show T.t036.f O.star < 0
    rw [O.star_eval T.t036.hN, T.t036.zero 3 (by decide)]
    nlinarith [T.t036.neg 5 (by decide)]

/-! ### The case N2 of S1: the test at `02` -/

/-- **Lemma 2 of §10 for a point that is not the cap** (Lemma 11.4): a point `d` on the
planes of `a'bc` and `abc'`, beneath `a'b'c` and beyond `abc` is a middle of the quad
edge `a' → c` (given Lemma 9.1 (a) with the face `abc'`, `hfar`).  For type 16 this is
`5`, on the planes `0235` and `1356`. -/
theorem middle_Qbc_of {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (h1 : F.a'bc.f d = 0) (h2 : F.a'b'c.f d < 0) (h3 : 0 < F.abc.f d) (h4 : F.abc'.f d = 0)
    (hfar : F.abc'.f a' < F.abc'.f c) :
    ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ 0 < δ ∧ d = c + s • (b - c) + δ • (c - a') := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have n1 := F.a'bc.neg a (by simp) haa' hab hac
  have n2 := F.a'b'c.neg b (by simp) (Ne.symm ha'b) hbb' hbc
  have n3 := F.abc.neg a' (by simp) (Ne.symm haa') ha'b ha'c
  have hco := coords_of_affine3 F.a'bc.hN F.a'b'c.hN F.abc.hN F.a'bc.hR F.a'bc.hQ F.a'bc.hP
    h1 n1.ne F.a'b'c.hR F.a'b'c.hP n2.ne F.abc.hR F.abc.hQ n3.ne
  set s := F.a'b'c.f d / F.a'b'c.f b
  set t := F.abc.f d / F.abc.f a'
  have hs : 0 < s := div_pos_of_neg_of_neg h2 n2
  have ht : t < 0 := div_neg_of_pos_of_neg h3 n3
  refine ⟨s, -t, hs, ?_, by linarith, ?_⟩
  · have hf := affine_frame F.abc'.hN c b a' s t
    rw [← hco, h4, F.abc'.hQ] at hf
    nlinarith [mul_pos_of_neg_of_neg ht (show F.abc'.f a' - F.abc'.f c < 0 by linarith),
      F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc']
  · rw [hco]; module

/-- `univ.image (x ∘ σ) = univ.image x`. -/
theorem image_sigma16 (x : Fin 7 → ℝ³) : univ.image (x ∘ sigma16) = univ.image x := by
  ext z
  simp only [mem_image, mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨_, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨sigma16 i, congrArg x (by fin_cases i <;> rfl)⟩

/-- `univ.image x` as `5` inserted into `O`. -/
theorem image_insert5 (x : Fin 7 → ℝ³) :
    univ.image x = insert (x 5) ({x 0, x 1, x 2, x 6, x 3, x 4} : Finset ℝ³) := by
  ext z
  simp only [mem_image, mem_univ, true_and, mem_insert, mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> exact ⟨_, rfl⟩

/-- **The case N2 of Theorem M's S1 (test `02`).**  In the octahedral region, with
Gale data of `O` in J's labelling `(a, b, c) = (1, 3, 2)` (`κ_1, κ_3 > 0`,
`[3 2] < 0`, `κ_2 ≠ 0`), if the far end of `0235` along `35` is `0` (`2` a middle), then
`0 → 2` is a quad edge of `O` that is not bad (§10's Lemma 7), `5` is a middle at its
view (Lemma 11.4), and Lemma 9.3 with a middle gives a passage (general position, no
horizontal double normals). -/
theorem isRupert_type16_N2 {x : Fin 7 → ℝ³} (T : Type16 x) (O : Oct16 x)
    (G : GaleData (x 1) (x 0) (x 3) (x 4) (x 2) (x 6))
    (hκa : 0 < galeD G.l G.m (x 1) (x 0)) (hκb : 0 < galeD G.l G.m (x 3) (x 4))
    (hκc : galeD G.l G.m (x 2) (x 6) ≠ 0) (hU : galeD G.l G.m (x 3) (x 2) < 0)
    (hfar : MidOf (x 3) (x 5) (x 0) (x 2)) (hgen : GenPos (univ.image x))
    (hnd : ∀ v ∈ univ.image x, ∀ w ∈ univ.image x, v ≠ w →
      NoHDNAt ((univ.image x).erase w) (w - v)) : IsRupert (univ.image x) := by
  classical
  have memV : ∀ i, x i ∈ univ.image x := fun i => mem_image_of_mem x (mem_univ i)
  set F := (O.facets T).perm₂₃ with hF
  have hfar' : F.abc'.f (x 0) < F.abc'.f (x 2) :=
    hfar.lt T.q1356.hN (T.q1356.zero 3 (by decide)) (T.q1356.zero 5 (by decide))
      (T.q1356.neg 0 (by decide))
  obtain ⟨hq₂, hgood⟩ := type08_lemma7 F G hκa hκb hκc hU hfar'
  obtain ⟨s, δ, hs0, hs1, hδ, hmid⟩ := middle_Qbc_of F (d := x 5) (T.q0235.zero 5 (by decide))
    (T.t024.neg 5 (by decide)) (O.five_beyond T).1 (T.q1356.zero 5 (by decide)) hfar'
  have e := image_insert5 x
  have := isRupert_quad_edge_middle (m := x 5) F.swap₁.perm₂₃ hfar' hq₂ hgood
    ⟨s, δ, hs0, hs1, hδ, Or.inl hmid⟩
    ⟨T.inj.ne (by decide), T.inj.ne (by decide), T.inj.ne (by decide), T.inj.ne (by decide),
      T.inj.ne (by decide), T.inj.ne (by decide)⟩
    (fun s t hs ht hst => by
      have hsV : s ∈ univ.image x := by
        rcases hs with rfl | rfl | rfl | rfl | rfl <;> exact memV _
      have htV : t ∈ univ.image x := by rcases ht with rfl | rfl | rfl <;> exact memV _
      refine hgen.inner_ne_of_ne hsV htV (memV 0) (memV 2) hst (T.inj.ne (by decide)) (Or.inl ?_)
      rcases ht with rfl | rfl | rfl <;> exact ⟨T.inj.ne (by decide), T.inj.ne (by decide)⟩)
    (by
      rw [← e]
      refine ⟨?_, hnd (x 0) (memV 0) (x 2) (memV 2) (T.inj.ne (by decide))⟩
      have := (hnd (x 2) (memV 2) (x 0) (memV 0) (T.inj.ne (by decide))).neg
      rwa [neg_sub] at this)
  rwa [← e] at this

/-- **The case N2 of S1 by `σ` (test `61`).**  With Gale data in J's labelling
`(a, b, c) = (2, 3, 1)` (`κ_2, κ_3 > 0`, `[3 1] < 0`, `κ_1 ≠ 0`), if the far end of
`1356` along `35` is `6` (`1` a middle), the test at `61` gives a passage. -/
theorem isRupert_type16_N2σ {x : Fin 7 → ℝ³} (T : Type16 x) (O : Oct16 x)
    (G : GaleData (x 2) (x 6) (x 3) (x 4) (x 1) (x 0))
    (hκa : 0 < galeD G.l G.m (x 2) (x 6)) (hκb : 0 < galeD G.l G.m (x 3) (x 4))
    (hκc : galeD G.l G.m (x 1) (x 0) ≠ 0) (hU : galeD G.l G.m (x 3) (x 1) < 0)
    (hfar : MidOf (x 3) (x 5) (x 6) (x 1)) (hgen : GenPos (univ.image x))
    (hnd : ∀ v ∈ univ.image x, ∀ w ∈ univ.image x, v ≠ w →
      NoHDNAt ((univ.image x).erase w) (w - v)) : IsRupert (univ.image x) := by
  rw [← image_sigma16] at hgen hnd ⊢
  exact isRupert_type16_N2 T.sigma O.sigma G hκa hκb hκc hU hfar hgen hnd

/-! ### Lemma 11.3 (a): the third quadrilateral -/

/-- The far end of `0235` is unique. -/
theorem Type16.far0235_unique {x : Fin 7 → ℝ³} (T : Type16 x) (h : MidOf (x 3) (x 5) (x 0) (x 2))
    (h' : MidOf (x 3) (x 5) (x 2) (x 0)) : False := by
  have := h.lt T.q1356.hN (T.q1356.zero 3 (by decide)) (T.q1356.zero 5 (by decide))
    (T.q1356.neg 0 (by decide))
  have := h'.lt T.q1356.hN (T.q1356.zero 3 (by decide)) (T.q1356.zero 5 (by decide))
    (T.q1356.neg 2 (by decide))
  linarith

/-- The far end of `1356` is unique. -/
theorem Type16.far1356_unique {x : Fin 7 → ℝ³} (T : Type16 x) (h : MidOf (x 3) (x 5) (x 1) (x 6))
    (h' : MidOf (x 3) (x 5) (x 6) (x 1)) : False := by
  have := h.lt T.q0235.hN (T.q0235.zero 3 (by decide)) (T.q0235.zero 5 (by decide))
    (T.q0235.neg 1 (by decide))
  have := h'.lt T.q0235.hN (T.q0235.zero 3 (by decide)) (T.q0235.zero 5 (by decide))
    (T.q0235.neg 6 (by decide))
  linarith

/-- `z 3 < z 5*`. -/
theorem Oct16.z_star {x : Fin 7 → ℝ³} (T : Type16 x) (O : Oct16 x) :
    ⟪x 3, x 5 - x 3⟫ < ⟪O.star, x 5 - x 3⟫ := by
  obtain ⟨l0, -⟩ := O.lam_pos T
  have hov : x 3 ≠ x 5 := T.inj.ne (by decide)
  have hU := real_inner_self_pos.mpr (sub_ne_zero.mpr (Ne.symm hov))
  simp only [Oct16.star, inner_add_left, real_inner_smul_left]
  nlinarith

/-- **Lemma 11.3 (a) (third quadrilateral).**  In the octahedral region, if the far
ends along `35` are `2` and `1`, then `35` is not bad: `5*, 1, 4, 2` is a convex plane
quadrilateral (on the plane `124`), so `min (z 5*, z 4) < max (z 1, z 2)`, and
`z 3 < z 5*`. -/
theorem type16_not_bad35_thirdQuad {x : Fin 7 → ℝ³} (T : Type16 x) (O : Oct16 x)
    (h2 : MidOf (x 3) (x 5) (x 2) (x 0)) (h1 : MidOf (x 3) (x 5) (x 1) (x 6)) :
    ¬ Type16Bad35 x := by
  rintro ⟨A, m, B, m', hA, hB, hmA, hmB, -, hlt⟩
  rcases hA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact T.far0235_unique hmA h2
  rcases hB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  swap
  · exact T.far1356_unique h1 hmB
  have hz : ∀ {f : ℝ³ → ℝ} {N : ℝ³}, (∀ y z, f y - f z = ⟪N, y - z⟫) → f (x 3) = 0 →
      f (x 5) = 0 → f O.star = 0 := by
    intro f N hf h3 h5; rw [O.star_eval hf, h3, h5]; ring
  obtain ⟨hα, hβ, hαβ, h4⟩ := plane_quad_coords O.t124.hN T.q0235.hN T.q1356.hN T.t245.hN
    (o := O.star) (p := x 1) (q := x 2) (w := x 4) (Z := x 3)
    (O.t124_star T) (O.t124.zero 1 (by decide)) (O.t124.zero 2 (by decide))
    (O.t124.zero 4 (by decide)) (O.t124.neg 3 (by decide) (by decide)).ne
    (hz T.q0235.hN (T.q0235.zero 3 (by decide)) (T.q0235.zero 5 (by decide)))
    (T.q0235.zero 2 (by decide)) (T.q0235.neg 1 (by decide)) (T.q0235.neg 4 (by decide))
    (hz T.q1356.hN (T.q1356.zero 3 (by decide)) (T.q1356.zero 5 (by decide)))
    (T.q1356.zero 1 (by decide)) (T.q1356.neg 2 (by decide)) (T.q1356.neg 4 (by decide))
    (T.t245.zero 4 (by decide)) (T.t245.zero 2 (by decide))
    (O.star_neg T T.t245.hN (T.t245.neg 3 (by decide)) (T.t245.zero 5 (by decide)).le)
    (T.t245.neg 1 (by decide))
  set α := T.q0235.f (x 4) / T.q0235.f (x 1)
  set β := T.q1356.f (x 4) / T.q1356.f (x 2)
  have hz4 : ⟪x 4, x 5 - x 3⟫ = ⟪O.star, x 5 - x 3⟫ + α * (⟪x 1, x 5 - x 3⟫ - ⟪O.star, x 5 - x 3⟫) +
      β * (⟪x 2, x 5 - x 3⟫ - ⟪O.star, x 5 - x 3⟫) := by
    conv_lhs => rw [h4]
    simp only [inner_add_left, inner_sub_left, real_inner_smul_left]
  have hs := O.z_star T
  simp only [max_lt_iff, lt_min_iff] at hlt
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := hlt
  set z1 := ⟪x 1, x 5 - x 3⟫
  set z2 := ⟪x 2, x 5 - x 3⟫
  set zd := ⟪O.star, x 5 - x 3⟫
  have hp : 0 < zd - z1 := by linarith
  have hq : 0 < zd - z2 := by linarith
  have I1 : 0 < (1 - α) * (zd - z1) - β * (zd - z2) := by nlinarith
  have I2 : 0 < (1 - β) * (zd - z2) - α * (zd - z1) := by nlinarith
  rcases lt_or_ge α 1 with hα1 | hα1
  · nlinarith [mul_pos hα I1, mul_pos (sub_pos.mpr hα1) I2, mul_pos (sub_pos.mpr hαβ) hq]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hα1) hp.le, mul_pos hβ hq]

/-! ### Lemma 11.3 (b): §10's T4 case in `K*` -/

/-- **§10's "the T4 edge is not bad"** (`type08_t4_not_bad`) with `κ_b` only nonzero:
the signs `[a' b], [a' b'] < 0` it uses follow from `κ_a > 0`, `[b c] < 0` and the pole
signs (G3) of `b` and `a'`. -/
theorem t4_not_bad' {a a' b b' c c' d : ℝ³} (h : IsOctahedron a a' b b' c c')
    (F : OctFacets a a' b b' c c') (hd : IsCap F d) (G : GaleData a a' b b' c c')
    (hκa : 0 < galeD G.l G.m a a') (hκb : galeD G.l G.m b b' ≠ 0)
    (hU : galeD G.l G.m b c < 0)
    (hopp : det3 (b - d) (b' - d) (c - d) * det3 (b - d) (b' - d) (c' - d) < 0) :
    ¬ max ⟪b, b - d⟫ ⟪b', b - d⟫ ≤ min ⟪c, b - d⟫ ⟪c', b - d⟫ := by
  have anti := galeD_anti G.l G.m
  obtain ⟨b1, -, b3⟩ := pole_signs F.perm₁₂ (G.hl.galeD G.hm b).perm₁₂ (galeD_self _ _ b) hκb
  have hba : 0 < galeD G.l G.m b a := pos_of_mul_neg_neg b3 hU
  have hba' : 0 < galeD G.l G.m b a' := pos_of_mul_pos_pos b1 hba
  have ha'b : galeD G.l G.m a' b < 0 := by rw [anti]; linarith
  obtain ⟨e1, -, -⟩ := pole_signs F.swap₁ (G.hl.galeD G.hm a').swap₁ (galeD_self _ _ a')
    (by rw [anti]; linarith)
  have ha'b' : galeD G.l G.m a' b' < 0 := neg_of_mul_pos_neg e1 ha'b
  obtain ⟨e, he, sab, sba', -, sb'a⟩ := axis_quad_signs h
  obtain ⟨hBCD, -⟩ := inTri_of_dep (G.hl.galeD G.hm a') (galeD_self _ _ a')
    (by rw [galeD_anti]; linarith) ha'b ha'b' he sab
  obtain ⟨-, hii, hiii⟩ := hd.axis_facts e (by rw [det3_swap12]; linarith) sba'.ne'
  obtain ⟨h1, h2, h3⟩ := inTri_cap_BD sba' sb'a hii hiii hBCD
  refine not_bad_of_inTri (g := fun X => det3 (b - d) (b' - d) (X - d))
    (N := cross (b - d) (b' - d)) (fun s t => by simp only [det3, ← inner_sub_right]; abel_nf)
    (by simp only [sub_self]; simp [det3_expand]) (by simp only [det3_expand]; ring)
    (by simp only [det3_expand]; ring) hopp (hd.ne.2.2.1) ?_
  rcases he with rfl | rfl
  · exact Or.inl ⟨h2, h3, h1⟩
  · right
    simp only [show c - c' = -(c' - c) by abel, det3_neg_right] at h1 h2 h3
    exact ⟨by linarith, by linarith, by linarith⟩

/-- The orientation from the axle point `o` in the plane `o P X`, seen from a point
`d = o + l u` of the axle. -/
theorem det3_axle_star (o P X u : ℝ³) (l : ℝ) :
    det3 (o - (o + l • u)) (P - (o + l • u)) (X - (o + l • u)) = -l * det3 (P - o) (X - o) u := by
  simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- **Lemma 11.3 (b) (J's T4 case in `K*`).**  In the octahedral region, with Gale
data of `O` in the labelling `(a, b, c) = (2, 3, 1)` with `κ_2 > 0`, `[3 1] < 0`
(`[1 3] [2 6] > 0` after mirroring) and `κ_3 ≠ 0`, if the far ends along `35` are `0`
and `1`, then `35` is not bad: §10's T4 edge `5* → 3` of `K*` is not bad
(Lemmas 9.7, 4, 3), and its depth is `−λ` times that along `35`. -/
theorem type16_not_bad35_T4 {x : Fin 7 → ℝ³} (T : Type16 x) (O : Oct16 x)
    (G : GaleData (x 2) (x 6) (x 3) (x 4) (x 1) (x 0))
    (hκa : 0 < galeD G.l G.m (x 2) (x 6)) (hκb : galeD G.l G.m (x 3) (x 4) ≠ 0)
    (hU : galeD G.l G.m (x 3) (x 1) < 0)
    (h0 : MidOf (x 3) (x 5) (x 0) (x 2)) (h1 : MidOf (x 3) (x 5) (x 1) (x 6)) :
    ¬ Type16Bad35 x := by
  set F := (O.facets T).perm₁₂.perm₂₃
  have hd : IsCap F O.star := (O.isCap T).perm₁₂.perm₂₃
  obtain ⟨l0, -⟩ := O.lam_pos T
  have hov : x 3 ≠ x 5 := T.inj.ne (by decide)
  -- the screen coordinates of `4` in the frame `3; 0, 1` of the view along `35`
  obtain ⟨τ, h4⟩ := frame_coords T.q0235.hN T.q1356.hN (o := x 3) (v := x 5) (A := x 0) (B := x 1)
    (T.q0235.zero 3 (by decide)) (T.q0235.zero 5 (by decide)) (T.q0235.zero 0 (by decide))
    (T.q0235.neg 1 (by decide)).ne (T.q1356.zero 3 (by decide)) (T.q1356.zero 5 (by decide))
    (T.q1356.zero 1 (by decide)) (T.q1356.neg 0 (by decide)).ne hov (x 4)
  have hE := frame16_det_ne T.q0235.hN T.q1356.hN (o := x 3) (v := x 5) (A := x 0) (B := x 1)
    (T.q0235.zero 3 (by decide)) (T.q0235.zero 5 (by decide)) (T.q0235.zero 0 (by decide))
    (T.q0235.neg 1 (by decide)).ne (T.q1356.zero 3 (by decide)) (T.q1356.zero 5 (by decide))
    (T.q1356.zero 1 (by decide)) (T.q1356.neg 0 (by decide)).ne hov
  set r := T.q1356.f (x 4) / T.q1356.f (x 0)
  set q := T.q0235.f (x 4) / T.q0235.f (x 1)
  have hr : 0 < r := div_pos_of_neg_of_neg (T.q1356.neg 4 (by decide)) (T.q1356.neg 0 (by decide))
  have hq : 0 < q := div_pos_of_neg_of_neg (T.q0235.neg 4 (by decide)) (T.q0235.neg 1 (by decide))
  set u := x 5 - x 3
  have c3 : x 3 = x 3 + (0 : ℝ) • (x 0 - x 3) + (0 : ℝ) • (x 1 - x 3) + (0 : ℝ) • u := by simp
  have c0 : x 0 = x 3 + (1 : ℝ) • (x 0 - x 3) + (0 : ℝ) • (x 1 - x 3) + (0 : ℝ) • u := by
    simp only [zero_smul, add_zero, one_smul]; abel
  have c1 : x 1 = x 3 + (0 : ℝ) • (x 0 - x 3) + (1 : ℝ) • (x 1 - x 3) + (0 : ℝ) • u := by
    simp only [zero_smul, add_zero, one_smul]; abel
  have d1 := det3_frame (x 3) (x 0 - x 3) (x 1 - x 3) u (x 3) (x 4) (x 1) 0 0 0 r q τ 0 1 0 c3 h4 c1
  have d0 := det3_frame (x 3) (x 0 - x 3) (x 1 - x 3) u (x 3) (x 4) (x 0) 0 0 0 r q τ 1 0 0 c3 h4 c0
  have hopp : det3 (x 3 - O.star) (x 4 - O.star) (x 1 - O.star) *
      det3 (x 3 - O.star) (x 4 - O.star) (x 0 - O.star) < 0 := by
    simp only [Oct16.star]
    rw [det3_axle_star, det3_axle_star, d1, d0]
    have := mul_self_pos.mpr hE
    have := mul_pos l0 l0
    nlinarith [mul_pos (mul_pos hr hq) (mul_pos (mul_pos l0 l0) (mul_self_pos.mpr hE))]
  have nb := t4_not_bad' F.isOctahedron F hd G hκa hκb hU hopp
  rintro ⟨A, m, B, m', hA, hB, hmA, hmB, -, hlt⟩
  rcases hA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  swap
  · exact T.far0235_unique h0 hmA
  rcases hB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  swap
  · exact T.far1356_unique h1 hmB
  apply nb
  have e : x 3 - O.star = -O.lam • u := by simp only [Oct16.star, u]; module
  simp only [e, real_inner_smul_right, max_le_iff, le_min_iff]
  simp only [max_lt_iff, lt_min_iff] at hlt
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := hlt
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith

/-- "35 is bad" is invariant under `σ = (0 6)(1 2)`. -/
theorem Type16Bad35.sigma {x : Fin 7 → ℝ³} (h : Type16Bad35 x) : Type16Bad35 (x ∘ sigma16) := by
  obtain ⟨A, m, B, m', hA, hB, hmA, hmB, hc, hlt⟩ := h
  refine ⟨B, m', A, m, ?_, ?_, hmB, hmA, ?_, ?_⟩
  · rcases hB with h | h
    exacts [Or.inr h, Or.inl h]
  · rcases hA with h | h
    exacts [Or.inr h, Or.inl h]
  · show det3 (A - B) (x 4 - B) (x 5 - x 3) * det3 (A - B) (x 3 - B) (x 5 - x 3) < 0
    have e : det3 (A - B) (x 4 - B) (x 5 - x 3) * det3 (A - B) (x 3 - B) (x 5 - x 3) =
        det3 (B - A) (x 4 - A) (x 5 - x 3) * det3 (B - A) (x 3 - A) (x 5 - x 3) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [e]; exact hc
  · show max ⟪B, x 5 - x 3⟫ ⟪A, x 5 - x 3⟫ < min ⟪x 3, x 5 - x 3⟫ ⟪x 4, x 5 - x 3⟫
    rwa [max_comm]

/-- **Lemma 11.3 (b) by `σ`**: far ends `2` and `6`, `κ_1 > 0`, `[3 2] < 0`
(`[2 3] [1 0] > 0` after mirroring), `κ_3 ≠ 0`. -/
theorem type16_not_bad35_T4σ {x : Fin 7 → ℝ³} (T : Type16 x) (O : Oct16 x)
    (G : GaleData (x 1) (x 0) (x 3) (x 4) (x 2) (x 6))
    (hκa : 0 < galeD G.l G.m (x 1) (x 0)) (hκb : galeD G.l G.m (x 3) (x 4) ≠ 0)
    (hU : galeD G.l G.m (x 3) (x 2) < 0)
    (h2 : MidOf (x 3) (x 5) (x 2) (x 0)) (h6 : MidOf (x 3) (x 5) (x 6) (x 1)) :
    ¬ Type16Bad35 x :=
  fun h => type16_not_bad35_T4 T.sigma O.sigma G hκa hκb hU h6 h2 h.sigma

/-! ### Mirror-invariant forms, in the Gale data of `O` -/

/-- Gale data of `O`, or its mirror, with `[1 0]`, … read with a sign `ε = ±1`. -/
theorem exists_gale_sign {a a' b b' c c' : ℝ³} (G : GaleData a a' b b' c c') {s t : ℝ³}
    (hst : galeD G.l G.m s t ≠ 0) :
    ∃ G' : GaleData a a' b b' c c', 0 < galeD G'.l G'.m s t ∧
      ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ p q, galeD G'.l G'.m p q = ε * galeD G.l G.m p q := by
  rcases lt_or_gt_of_ne hst with h | h
  · exact ⟨G.mirror, by rw [G.galeD_mirror]; linarith, -1, Or.inr rfl,
      fun p q => by rw [G.galeD_mirror]; ring⟩
  · exact ⟨G, h, 1, Or.inl rfl, fun p q => by ring⟩

/-- **S1, N2 at `02`, Gale form**: `[2 3] κ_1 > 0`, `κ_1 κ_3 > 0`, `κ_2 ≠ 0` (any Gale
data of `O`), the far end of `0235` along `35` is `0`. -/
theorem isRupert_type16_N2' {x : Fin 7 → ℝ³} (T : Type16 x) (O : Oct16 x)
    (G : GaleData (x 1) (x 0) (x 2) (x 6) (x 3) (x 4))
    (h1 : 0 < galeD G.l G.m (x 2) (x 3) * galeD G.l G.m (x 1) (x 0))
    (h2 : 0 < galeD G.l G.m (x 1) (x 0) * galeD G.l G.m (x 3) (x 4))
    (hκ : galeD G.l G.m (x 2) (x 6) ≠ 0)
    (hfar : MidOf (x 3) (x 5) (x 0) (x 2)) (hgen : GenPos (univ.image x))
    (hnd : ∀ v ∈ univ.image x, ∀ w ∈ univ.image x, v ≠ w →
      NoHDNAt ((univ.image x).erase w) (w - v)) : IsRupert (univ.image x) := by
  obtain ⟨G', hpos, ε, hε, hG'⟩ := exists_gale_sign G (s := x 1) (t := x 0)
    (fun h0 => by rw [h0, zero_mul] at h2; exact lt_irrefl _ h2)
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  rw [hG'] at hpos
  have anti := galeD_anti G.l G.m
  refine isRupert_type16_N2 T O G'.perm₂₃ ?_ ?_ ?_ ?_ hfar hgen hnd
  · show 0 < galeD G'.l G'.m (x 1) (x 0); rw [hG']; exact hpos
  · show 0 < galeD G'.l G'.m (x 3) (x 4); rw [hG']
    nlinarith [mul_pos hpos h2]
  · show galeD G'.l G'.m (x 2) (x 6) ≠ 0; rw [hG']
    exact mul_ne_zero (by rcases hε with rfl | rfl <;> norm_num) hκ
  · show galeD G'.l G'.m (x 3) (x 2) < 0; rw [hG', anti]
    nlinarith [mul_pos hpos h1]

/-- **S1, N2 at `61`, Gale form**: `[1 3] κ_2 > 0`, `κ_2 κ_3 > 0`, `κ_1 ≠ 0`, the far
end of `1356` along `35` is `6`. -/
theorem isRupert_type16_N2σ' {x : Fin 7 → ℝ³} (T : Type16 x) (O : Oct16 x)
    (G : GaleData (x 1) (x 0) (x 2) (x 6) (x 3) (x 4))
    (h1 : 0 < galeD G.l G.m (x 1) (x 3) * galeD G.l G.m (x 2) (x 6))
    (h2 : 0 < galeD G.l G.m (x 2) (x 6) * galeD G.l G.m (x 3) (x 4))
    (hκ : galeD G.l G.m (x 1) (x 0) ≠ 0)
    (hfar : MidOf (x 3) (x 5) (x 6) (x 1)) (hgen : GenPos (univ.image x))
    (hnd : ∀ v ∈ univ.image x, ∀ w ∈ univ.image x, v ≠ w →
      NoHDNAt ((univ.image x).erase w) (w - v)) : IsRupert (univ.image x) := by
  obtain ⟨G', hpos, ε, hε, hG'⟩ := exists_gale_sign G (s := x 2) (t := x 6)
    (fun h0 => by rw [h0, zero_mul] at h2; exact lt_irrefl _ h2)
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  rw [hG'] at hpos
  have anti := galeD_anti G.l G.m
  refine isRupert_type16_N2σ T O G'.perm₁₂.perm₂₃ ?_ ?_ ?_ ?_ hfar hgen hnd
  · show 0 < galeD G'.l G'.m (x 2) (x 6); rw [hG']; exact hpos
  · show 0 < galeD G'.l G'.m (x 3) (x 4); rw [hG']
    nlinarith [mul_pos hpos h2]
  · show galeD G'.l G'.m (x 1) (x 0) ≠ 0; rw [hG']
    exact mul_ne_zero (by rcases hε with rfl | rfl <;> norm_num) hκ
  · show galeD G'.l G'.m (x 3) (x 1) < 0; rw [hG', anti]
    nlinarith [mul_pos hpos h1]

/-- **Lemma 11.3 (b), Gale form**: far ends `0`, `1`, `[1 3] [2 6] > 0`, `κ_3 ≠ 0`. -/
theorem type16_not_bad35_T4' {x : Fin 7 → ℝ³} (T : Type16 x) (O : Oct16 x)
    (G : GaleData (x 1) (x 0) (x 2) (x 6) (x 3) (x 4))
    (h : 0 < galeD G.l G.m (x 1) (x 3) * galeD G.l G.m (x 2) (x 6))
    (hκ : galeD G.l G.m (x 3) (x 4) ≠ 0)
    (h0 : MidOf (x 3) (x 5) (x 0) (x 2)) (h1 : MidOf (x 3) (x 5) (x 1) (x 6)) :
    ¬ Type16Bad35 x := by
  obtain ⟨G', hpos, ε, hε, hG'⟩ := exists_gale_sign G (s := x 2) (t := x 6)
    (fun h0 => by rw [h0, mul_zero] at h; exact lt_irrefl _ h)
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  rw [hG'] at hpos
  have anti := galeD_anti G.l G.m
  refine type16_not_bad35_T4 T O G'.perm₁₂.perm₂₃ ?_ ?_ ?_ h0 h1
  · show 0 < galeD G'.l G'.m (x 2) (x 6); rw [hG']; exact hpos
  · show galeD G'.l G'.m (x 3) (x 4) ≠ 0; rw [hG']
    exact mul_ne_zero (by rcases hε with rfl | rfl <;> norm_num) hκ
  · show galeD G'.l G'.m (x 3) (x 1) < 0; rw [hG', anti]
    nlinarith [mul_pos hpos h]

/-- **Lemma 11.3 (b) by `σ`, Gale form**: far ends `2`, `6`, `[2 3] [1 0] > 0`,
`κ_3 ≠ 0`. -/
theorem type16_not_bad35_T4σ' {x : Fin 7 → ℝ³} (T : Type16 x) (O : Oct16 x)
    (G : GaleData (x 1) (x 0) (x 2) (x 6) (x 3) (x 4))
    (h : 0 < galeD G.l G.m (x 2) (x 3) * galeD G.l G.m (x 1) (x 0))
    (hκ : galeD G.l G.m (x 3) (x 4) ≠ 0)
    (h2 : MidOf (x 3) (x 5) (x 2) (x 0)) (h6 : MidOf (x 3) (x 5) (x 6) (x 1)) :
    ¬ Type16Bad35 x := by
  obtain ⟨G', hpos, ε, hε, hG'⟩ := exists_gale_sign G (s := x 1) (t := x 0)
    (fun h0 => by rw [h0, mul_zero] at h; exact lt_irrefl _ h)
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  rw [hG'] at hpos
  have anti := galeD_anti G.l G.m
  refine type16_not_bad35_T4σ T O G'.perm₂₃ ?_ ?_ ?_ h2 h6
  · show 0 < galeD G'.l G'.m (x 1) (x 0); rw [hG']; exact hpos
  · show galeD G'.l G'.m (x 3) (x 4) ≠ 0; rw [hG']
    exact mul_ne_zero (by rcases hε with rfl | rfl <;> norm_num) hκ
  · show galeD G'.l G'.m (x 3) (x 2) < 0; rw [hG', anti]
    nlinarith [mul_pos hpos h]

/-! ### Proposition 11.V: Lemma 8 (the bonus edge `2 → 4`), R1, R2 -/

/-- `isRupert_quad_rim` with extra points strictly inside the rim. -/
theorem isRupert_quad_rim_int (V M : Finset ℝ³) (u : ℝ³) (hu : u ≠ 0) {w y y' A B : ℝ³}
    (h : ℝ) (hh : h ≠ 0) (hw : w = y - h • u) (hwV : w ∈ V) (hyV : y ∈ V) (hy'V : y' ∈ V)
    (hAV : A ∈ V) (hBV : B ∈ V) (hyM : y ∉ M) (hAM : A ∉ M) (hy'M : y' ∉ M) (hBM : B ∉ M)
    (t1 : 0 < det3 (A - y) (y' - y) u) (t2 : 0 < det3 (A - y) (B - y) u)
    (t3 : 0 < det3 (y' - A) (B - A) u) (t4 : 0 < det3 (y' - A) (y - A) u)
    (t5 : 0 < det3 (B - y') (y - y') u) (t6 : 0 < det3 (B - y') (A - y') u)
    (t7 : 0 < det3 (y - B) (A - B) u) (t8 : 0 < det3 (y - B) (y' - B) u)
    (hrest : ∀ z ∈ V, z ∉ M → z ≠ w → z ≠ y → z ≠ A → z ≠ y' → z ≠ B →
      0 < det3 (A - y) (z - y) u ∧ 0 < det3 (y' - A) (z - A) u ∧
      0 < det3 (B - y') (z - y') u ∧ 0 < det3 (y - B) (z - B) u)
    (hinj : Function.Injective (quad ⟪y, u⟫ ⟪A, u⟫ ⟪y', u⟫ ⟪B, u⟫))
    (hN : NWS4 (quad ⟪y, u⟫ ⟪A, u⟫ ⟪y', u⟫ ⟪B, u⟫))
    (hM : ∀ m ∈ M, EdgeMiddle u y w A B h m) (hnd : NoHDNAt (V.erase w) u) : IsRupert V := by
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  refine isRupert_of_edgeView V M u hu (k := 4) (by norm_num) (quad y A y' B) 0 w h hwV
    (by simp only [quad_0]; exact hw) hh ?_ ?_ ?_ ?_ ?_ hnd ?_
  · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
    exacts [hyV, hAV, hy'V, hBV]
  · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
    exacts [hyM, hAM, hy'M, hBM]
  · intro i j hi hj
    rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
    exacts [t1, t2, t3, t4, t5, t6, t7, t8]
  · intro z hz hzM hzw hzx i
    obtain ⟨r1, r2, r3, r4⟩ := hrest z hz hzM hzw (hzx 0) (hzx 1) (hzx 2) (hzx 3)
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
    exacts [r1, r2, r3, r4]
  · rw [quad_inner]; exact isCyclicUnimodal_of_NWS4 hinj hN
  · rw [zmod4_zero_add_one, zmod4_zero_sub_one]
    simpa only [quad_0, quad_1, quad_3] using hM

/-- **An edge view whose rim is a convex plane quadrilateral**, in screen coordinates:
the view along `o v`, the rim `o, A, y', B` with `y' = o + r₃ (A − o) + q₃ (B − o)`
(`r₃, q₃ > 0`, `r₃ + q₃ > 1`), every other point except `v` strictly inside
(coordinates `r, q > 0` on the inner side of the sides `A y'` and `y' B`), no middles,
distinct depths, a non-saddle rim: Rupert. -/
theorem isRupert_quad_rim_coords (V : Finset ℝ³) {o v A y' B : ℝ³} {r3 q3 : ℝ}
    (hr3 : 0 < r3) (hq3 : 0 < q3) (hrq3 : 1 < r3 + q3)
    (c3 : y' = o + r3 • (A - o) + q3 • (B - o)) (hE : det3 (A - o) (B - o) (v - o) ≠ 0)
    (hov : o ≠ v) (hvV : v ∈ V) (hoV : o ∈ V) (hAV : A ∈ V) (hy'V : y' ∈ V) (hBV : B ∈ V)
    (hrest : ∀ z ∈ V, z ≠ v → z ≠ o → z ≠ A → z ≠ y' → z ≠ B →
      ∃ rX qX τ : ℝ, z = o + rX • (A - o) + qX • (B - o) + τ • (v - o) ∧ 0 < rX ∧ 0 < qX ∧
        0 < (r3 - 1) * qX - q3 * (rX - 1) ∧ 0 < r3 * (1 - qX) - rX * (1 - q3))
    (hd : ⟪o, v - o⟫ ≠ ⟪A, v - o⟫ ∧ ⟪o, v - o⟫ ≠ ⟪y', v - o⟫ ∧ ⟪o, v - o⟫ ≠ ⟪B, v - o⟫ ∧
      ⟪A, v - o⟫ ≠ ⟪y', v - o⟫ ∧ ⟪A, v - o⟫ ≠ ⟪B, v - o⟫ ∧ ⟪y', v - o⟫ ≠ ⟪B, v - o⟫)
    (hN : NWS4 (quad ⟪o, v - o⟫ ⟪A, v - o⟫ ⟪y', v - o⟫ ⟪B, v - o⟫))
    (hnd : NoHDNAt (V.erase v) (v - o)) : IsRupert V := by
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hd
  set u := v - o
  have hu : u ≠ 0 := sub_ne_zero.mpr (Ne.symm hov)
  have D := fun X Y Z rX qX tX rY qY tY rZ qZ tZ hX hY hZ =>
    det3_frame o (A - o) (B - o) u X Y Z rX qX tX rY qY tY rZ qZ tZ hX hY hZ
  have co : o = o + (0 : ℝ) • (A - o) + (0 : ℝ) • (B - o) + (0 : ℝ) • u := by simp
  have cA : A = o + (1 : ℝ) • (A - o) + (0 : ℝ) • (B - o) + (0 : ℝ) • u := by
    simp only [zero_smul, add_zero, one_smul]; abel
  have cB : B = o + (0 : ℝ) • (A - o) + (1 : ℝ) • (B - o) + (0 : ℝ) • u := by
    simp only [zero_smul, add_zero, one_smul]; abel
  have c3' : y' = o + r3 • (A - o) + q3 • (B - o) + (0 : ℝ) • u := by
    rw [zero_smul, add_zero]; exact c3
  have hw : v = o - (-1 : ℝ) • u := by simp only [neg_smul, one_smul, sub_neg_eq_add, u]; abel
  rcases lt_or_gt_of_ne hE with hneg | hpos
  · refine isRupert_quad_rim_int V ∅ u hu (-1) (by norm_num) hw hvV hoV hy'V hBV hAV
      (by simp) (by simp) (by simp) (by simp) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      (NWS4_quad_swap hN) (by simp) hnd
    · rw [D o B y' 0 0 0 0 1 0 r3 q3 0 co cB c3']; nlinarith
    · rw [D o B A 0 0 0 0 1 0 1 0 0 co cB cA]; nlinarith
    · rw [D B y' A 0 1 0 r3 q3 0 1 0 0 cB c3' cA]; nlinarith
    · rw [D B y' o 0 1 0 r3 q3 0 0 0 0 cB c3' co]; nlinarith
    · rw [D y' A o r3 q3 0 1 0 0 0 0 0 c3' cA co]; nlinarith
    · rw [D y' A B r3 q3 0 1 0 0 0 1 0 c3' cA cB]; nlinarith
    · rw [D A o B 1 0 0 0 0 0 0 1 0 cA co cB]; nlinarith
    · rw [D A o y' 1 0 0 0 0 0 r3 q3 0 cA co c3']; nlinarith
    · intro z hz _ hzw hzo hzB hzy hzA
      obtain ⟨rX, qX, τ, hX, h1, h2, h3, h4⟩ := hrest z hz hzw hzo hzA hzy hzB
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [D o B z 0 0 0 0 1 0 rX qX τ co cB hX]; nlinarith
      · rw [D B y' z 0 1 0 r3 q3 0 rX qX τ cB c3' hX]; nlinarith
      · rw [D y' A z r3 q3 0 1 0 0 rX qX τ c3' cA hX]; nlinarith
      · rw [D A o z 1 0 0 0 0 0 rX qX τ cA co hX]; nlinarith
    · exact quad_injective d3 d2 d1 (Ne.symm d6) (Ne.symm d5) (Ne.symm d4)
  · refine isRupert_quad_rim_int V ∅ u hu (-1) (by norm_num) hw hvV hoV hy'V hAV hBV
      (by simp) (by simp) (by simp) (by simp) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      (quad_injective d1 d2 d3 d4 d5 d6) hN (by simp) hnd
    · rw [D o A y' 0 0 0 1 0 0 r3 q3 0 co cA c3']; nlinarith
    · rw [D o A B 0 0 0 1 0 0 0 1 0 co cA cB]; nlinarith
    · rw [D A y' B 1 0 0 r3 q3 0 0 1 0 cA c3' cB]; nlinarith
    · rw [D A y' o 1 0 0 r3 q3 0 0 0 0 cA c3' co]; nlinarith
    · rw [D y' B o r3 q3 0 0 1 0 0 0 0 c3' cB co]; nlinarith
    · rw [D y' B A r3 q3 0 0 1 0 1 0 0 c3' cB cA]; nlinarith
    · rw [D B o A 0 1 0 0 0 0 1 0 0 cB co cA]; nlinarith
    · rw [D B o y' 0 1 0 0 0 0 r3 q3 0 cB co c3']; nlinarith
    · intro z hz _ hzw hzo hzA hzy hzB
      obtain ⟨rX, qX, τ, hX, h1, h2, h3, h4⟩ := hrest z hz hzw hzo hzA hzy hzB
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [D o A z 0 0 0 1 0 0 rX qX τ co cA hX]; nlinarith
      · rw [D A y' z 1 0 0 r3 q3 0 rX qX τ cA c3' hX]; nlinarith
      · rw [D y' B z r3 q3 0 0 1 0 rX qX τ c3' cB hX]; nlinarith
      · rw [D B o z 0 1 0 0 0 0 rX qX τ cB co hX]; nlinarith

/-- The frame `2; 0, 5` of the view along `24`: the face `0235` (`3` opposite `2`). -/
theorem Type16.coords24 {x : Fin 7 → ℝ³} (T : Type16 x) :
    0 < T.t245.f (x 3) / T.t245.f (x 0) ∧ 0 < T.t024.f (x 3) / T.t024.f (x 5) ∧
    1 < T.t245.f (x 3) / T.t245.f (x 0) + T.t024.f (x 3) / T.t024.f (x 5) ∧
    x 3 = x 2 + (T.t245.f (x 3) / T.t245.f (x 0)) • (x 0 - x 2) +
      (T.t024.f (x 3) / T.t024.f (x 5)) • (x 5 - x 2) :=
  plane_quad_coords T.q0235.hN T.t245.hN T.t024.hN T.q1356.hN
    (T.q0235.zero 2 (by decide)) (T.q0235.zero 0 (by decide)) (T.q0235.zero 5 (by decide))
    (T.q0235.zero 3 (by decide)) (T.q0235.neg 1 (by decide)).ne
    (T.t245.zero 2 (by decide)) (T.t245.zero 5 (by decide)) (T.t245.neg 0 (by decide))
    (T.t245.neg 3 (by decide)) (T.t024.zero 2 (by decide)) (T.t024.zero 0 (by decide))
    (T.t024.neg 5 (by decide)) (T.t024.neg 3 (by decide))
    (T.q1356.zero 3 (by decide)) (T.q1356.zero 5 (by decide)) (T.q1356.neg 2 (by decide))
    (T.q1356.neg 0 (by decide))

/-- **The interior points at the view along `24`.**  If `2 → 4` is a quad edge of `O`,
a point `X` beneath `0235` and weakly beneath `036`, `1356` is strictly on the inner side
of the silhouette edges `03` and `35` (in the screen coordinates `r = f₂₄₅ / f₂₄₅ 0`,
`q = f₀₂₄ / f₀₂₄ 5`): the plane through `03` (resp. `35`) parallel to the view is a
positive combination of the planes of `0235` and `036` (resp. `1356`). -/
theorem Type16.inner24 {x : Fin 7 → ℝ³} (T : Type16 x)
    (hq1 : T.q1356.f (x 2) < T.q1356.f (x 4)) (hq2 : T.t036.f (x 2) < T.t036.f (x 4))
    (X : ℝ³) (τ : ℝ)
    (hX : X = x 2 + (T.t245.f X / T.t245.f (x 0)) • (x 0 - x 2) +
        (T.t024.f X / T.t024.f (x 5)) • (x 5 - x 2) + τ • (x 4 - x 2))
    (hAX : T.q0235.f X < 0) (hDX : T.t036.f X ≤ 0) (hBX : T.q1356.f X ≤ 0) :
    0 < (T.t245.f (x 3) / T.t245.f (x 0) - 1) * (T.t024.f X / T.t024.f (x 5)) -
        T.t024.f (x 3) / T.t024.f (x 5) * (T.t245.f X / T.t245.f (x 0) - 1) ∧
    0 < T.t245.f (x 3) / T.t245.f (x 0) * (1 - T.t024.f X / T.t024.f (x 5)) -
        T.t245.f X / T.t245.f (x 0) * (1 - T.t024.f (x 3) / T.t024.f (x 5)) := by
  obtain ⟨hr3, hq3, -, c3'⟩ := T.coords24
  set r3 := T.t245.f (x 3) / T.t245.f (x 0)
  set q3 := T.t024.f (x 3) / T.t024.f (x 5)
  set rX := T.t245.f X / T.t245.f (x 0)
  set qX := T.t024.f X / T.t024.f (x 5)
  have A0 := T.q0235.zero 0 (by decide); have A2 := T.q0235.zero 2 (by decide)
  have A5 := T.q0235.zero 5 (by decide); have A4 := T.q0235.neg 4 (by decide)
  have D0 := T.t036.zero 0 (by decide); have D3 := T.t036.zero 3 (by decide)
  have D2 := T.t036.neg 2 (by decide)
  have B3 := T.q1356.zero 3 (by decide); have B5 := T.q1356.zero 5 (by decide)
  have B2 := T.q1356.neg 2 (by decide)
  have c3 : x 3 = x 2 + r3 • (x 0 - x 2) + q3 • (x 5 - x 2) + (0 : ℝ) • (x 4 - x 2) := by
    rw [zero_smul, add_zero]; exact c3'
  have eA := affine_frame3 T.q0235.hN (x 2) (x 0) (x 5) (x 4) rX qX τ
  have eD := affine_frame3 T.t036.hN (x 2) (x 0) (x 5) (x 4) rX qX τ
  have eB := affine_frame3 T.q1356.hN (x 2) (x 0) (x 5) (x 4) rX qX τ
  have eD3 := affine_frame3 T.t036.hN (x 2) (x 0) (x 5) (x 4) r3 q3 0
  have eB3 := affine_frame3 T.q1356.hN (x 2) (x 0) (x 5) (x 4) r3 q3 0
  rw [← hX] at eA eD eB
  rw [← c3] at eD3 eB3
  rw [A2, A0, A5] at eA
  rw [D0] at eD eD3
  rw [B5] at eB eB3
  rw [D3] at eD3
  rw [B3] at eB3
  have hG : T.t036.f (x 2) * (1 - rX - qX) + qX * T.t036.f (x 5) < 0 := by
    have e : (T.t036.f (x 4) - T.t036.f (x 2)) * T.q0235.f X - T.q0235.f (x 4) * T.t036.f X =
        -T.q0235.f (x 4) * (T.t036.f (x 2) * (1 - rX - qX) + qX * T.t036.f (x 5)) := by
      rw [eA, eD]; ring
    have l : (T.t036.f (x 4) - T.t036.f (x 2)) * T.q0235.f X - T.q0235.f (x 4) * T.t036.f X
        < 0 := by
      nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr hq2) hAX,
        mul_nonneg (neg_nonneg.mpr A4.le) (neg_nonneg.mpr hDX)]
    rw [e] at l
    exact neg_of_mul_neg_right l (by linarith)
  have hH : T.q1356.f (x 2) * (1 - rX - qX) + rX * T.q1356.f (x 0) < 0 := by
    have e : (T.q1356.f (x 4) - T.q1356.f (x 2)) * T.q0235.f X - T.q0235.f (x 4) * T.q1356.f X =
        -T.q0235.f (x 4) * (T.q1356.f (x 2) * (1 - rX - qX) + rX * T.q1356.f (x 0)) := by
      rw [eA, eB]; ring
    have l : (T.q1356.f (x 4) - T.q1356.f (x 2)) * T.q0235.f X - T.q0235.f (x 4) * T.q1356.f X
        < 0 := by
      nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr hq1) hAX,
        mul_nonneg (neg_nonneg.mpr A4.le) (neg_nonneg.mpr hBX)]
    rw [e] at l
    exact neg_of_mul_neg_right l (by linarith)
  have G3 : T.t036.f (x 2) * (1 - r3 - q3) + q3 * T.t036.f (x 5) = 0 := by linarith
  have H3 : T.q1356.f (x 2) * (1 - r3 - q3) + r3 * T.q1356.f (x 0) = 0 := by linarith
  constructor
  · have e : T.t036.f (x 2) * ((r3 - 1) * qX - q3 * (rX - 1)) =
        q3 * (T.t036.f (x 2) * (1 - rX - qX) + qX * T.t036.f (x 5)) := by
      linear_combination (-qX) * G3
    have h' := mul_pos hq3 (neg_pos.mpr hG)
    by_contra hc; push Not at hc
    linarith [mul_nonneg_of_nonpos_of_nonpos D2.le hc, mul_neg_of_pos_of_neg hq3 hG]
  · have e : T.q1356.f (x 2) * (r3 * (1 - qX) - rX * (1 - q3)) =
        r3 * (T.q1356.f (x 2) * (1 - rX - qX) + rX * T.q1356.f (x 0)) := by
      linear_combination (-rX) * H3
    have h' := mul_pos hr3 (neg_pos.mpr hH)
    by_contra hc; push Not at hc
    linarith [mul_nonneg_of_nonpos_of_nonpos B2.le hc, mul_neg_of_pos_of_neg hr3 hH]

/-- **Lemma 11.8 (the bonus edge `2 → 4`).**  If `2 → 4` is a quad edge of `O` (`2`
strictly farther than `4` from the planes `136` and `036`), then at the view along `24`
the reduced polygon `K_2` is the face `0235`: its rim `2, 0, 3, 5` is a convex plane
quadrilateral (so `3` is always a corner), unimodal with no badness condition; `1` and
`6` are strictly inside (`Type16.inner24`) and there are no middles.  In general
position, without a horizontal double normal, `K` is Rupert. -/
theorem isRupert_type16_24 {x : Fin 7 → ℝ³} (T : Type16 x)
    (hq1 : T.q1356.f (x 2) < T.q1356.f (x 4)) (hq2 : T.t036.f (x 2) < T.t036.f (x 4))
    (hgen : GenPos (univ.image x)) (hnd : NoHDNAt ((univ.image x).erase (x 4)) (x 4 - x 2)) :
    IsRupert (univ.image x) := by
  classical
  have memV : ∀ i, x i ∈ univ.image x := fun i => mem_image_of_mem x (mem_univ i)
  have h24 : x 2 ≠ x 4 := T.inj.ne (by decide)
  have C0 := T.t024.zero 0 (by decide); have C2 := T.t024.zero 2 (by decide)
  have C4 := T.t024.zero 4 (by decide); have C5 := T.t024.neg 5 (by decide)
  have H2 := T.t245.zero 2 (by decide); have H4 := T.t245.zero 4 (by decide)
  have H5 := T.t245.zero 5 (by decide); have H0 := T.t245.neg 0 (by decide)
  obtain ⟨hr3, hq3, hrq3, c3⟩ := T.coords24
  have zne : ∀ i j : Fin 7, i ≠ j → j ≠ 2 → j ≠ 4 → ⟪x i, x 4 - x 2⟫ ≠ ⟪x j, x 4 - x 2⟫ :=
    fun i j hij hj2 hj4 => hgen.inner_ne_of_ne (memV i) (memV j) (memV 2) (memV 4)
      (T.inj.ne hij) h24 (Or.inl ⟨T.inj.ne hj2, T.inj.ne hj4⟩)
  refine isRupert_quad_rim_coords _ hr3 hq3 hrq3 c3
    (frame16_det_ne T.t024.hN T.t245.hN C2 C4 C0 C5.ne H2 H4 H5 H0.ne h24) h24
    (memV 4) (memV 2) (memV 0) (memV 3) (memV 5) ?_
    ⟨zne 2 0 (by decide) (by decide) (by decide), zne 2 3 (by decide) (by decide) (by decide),
      zne 2 5 (by decide) (by decide) (by decide), zne 0 3 (by decide) (by decide) (by decide),
      zne 0 5 (by decide) (by decide) (by decide), zne 3 5 (by decide) (by decide) (by decide)⟩
    (nws4_of_planar_quad hr3 hq3 hrq3 c3 (zne 2 0 (by decide) (by decide) (by decide))) hnd
  intro z hz hz4 hz2 hz0 hz3 hz5
  obtain ⟨i, -, rfl⟩ := mem_image.mp hz
  have key : ∀ j : Fin 7, (j = 1 ∨ j = 6) → ∃ rX qX τ : ℝ,
      x j = x 2 + rX • (x 0 - x 2) + qX • (x 5 - x 2) + τ • (x 4 - x 2) ∧ 0 < rX ∧ 0 < qX ∧
      0 < (T.t245.f (x 3) / T.t245.f (x 0) - 1) * qX -
        T.t024.f (x 3) / T.t024.f (x 5) * (rX - 1) ∧
      0 < T.t245.f (x 3) / T.t245.f (x 0) * (1 - qX) -
        rX * (1 - T.t024.f (x 3) / T.t024.f (x 5)) := by
    intro j hj
    obtain ⟨τ, hX⟩ := frame_coords T.t024.hN T.t245.hN C2 C4 C0 C5.ne H2 H4 H5 H0.ne h24 (x j)
    have hA : T.q0235.f (x j) < 0 := by rcases hj with rfl | rfl <;> exact T.q0235.neg _ (by decide)
    have hD : T.t036.f (x j) ≤ 0 := by
      rcases hj with rfl | rfl
      exacts [(T.t036.neg _ (by decide)).le, (T.t036.zero _ (by decide)).le]
    have hB : T.q1356.f (x j) ≤ 0 := by rcases hj with rfl | rfl <;> exact (T.q1356.zero _ (by decide)).le
    obtain ⟨i1, i2⟩ := T.inner24 hq1 hq2 (x j) τ hX hA hD hB
    refine ⟨_, _, τ, hX, ?_, ?_, i1, i2⟩
    · exact div_pos_of_neg_of_neg (by rcases hj with rfl | rfl <;> exact T.t245.neg _ (by decide)) H0
    · exact div_pos_of_neg_of_neg (by rcases hj with rfl | rfl <;> exact T.t024.neg _ (by decide)) C5
  fin_cases i
  · exact absurd rfl hz0
  · exact key 1 (Or.inl rfl)
  · exact absurd rfl hz2
  · exact absurd rfl hz3
  · exact absurd rfl hz4
  · exact absurd rfl hz5
  · exact key 6 (Or.inr rfl)

/-- **Lemma 11.R1 (a visible cap is far from the opposite quadrilateral).**  View along
`15`.  If the far end of `0235` along `35` is `0` (so `0` is farther than `2` from the
plane `1356`) and the cap `2` is not hidden in the triangle `1, 0, 4` at the view along
`15` (its image is not `λ P0 + μ P4` with `λ, μ > 0`, `λ + μ < 1`, from `q = P1 = P5`),
then `2` is strictly farther than `4` from the plane `1356`.  (The image of `2` is
always in the open angle `P0 q P4`: `λ = f₁₄₅ 2 / f₁₄₅ 0 > 0`, and `μ > 0` because the
diagonal `05` of `0235` separates `2` from `3`.) -/
theorem type16_R1 {x : Fin 7 → ℝ³} (T : Type16 x) (hfar : MidOf (x 3) (x 5) (x 0) (x 2))
    (hvis : ¬ ∃ l μ ν : ℝ, 0 < l ∧ 0 < μ ∧ l + μ < 1 ∧
      x 2 = x 1 + l • (x 0 - x 1) + μ • (x 4 - x 1) + ν • (x 5 - x 1)) :
    T.q1356.f (x 2) < T.q1356.f (x 4) := by
  have F1 := T.t145.zero 1 (by decide); have F4 := T.t145.zero 4 (by decide)
  have F5 := T.t145.zero 5 (by decide); have F0 := T.t145.neg 0 (by decide)
  have F2 := T.t145.neg 2 (by decide); have F3 := T.t145.neg 3 (by decide)
  have B1 := T.q1356.zero 1 (by decide); have B3 := T.q1356.zero 3 (by decide)
  have B5 := T.q1356.zero 5 (by decide); have B0 := T.q1356.neg 0 (by decide)
  have B2 := T.q1356.neg 2 (by decide); have B4 := T.q1356.neg 4 (by decide)
  have h15 : x 1 ≠ x 5 := T.inj.ne (by decide)
  set e := x 5 - x 1
  have hU : 0 < ⟪x 5, e⟫ - ⟪x 1, e⟫ := by
    rw [← inner_sub_left]; exact real_inner_self_pos.mpr (sub_ne_zero.mpr (Ne.symm h15))
  set l := T.t145.f (x 2) / T.t145.f (x 0)
  set μ := (T.q1356.f (x 2) - l * T.q1356.f (x 0)) / T.q1356.f (x 4)
  have hl : 0 < l := div_pos_of_neg_of_neg F2 F0
  -- `μ > 0`, from the quadrilateral `0235`
  obtain ⟨hα, hβ, hαβ, h2⟩ := T.coords0235
  set α := T.q1356.f (x 2) / T.q1356.f (x 0)
  set β := T.t036.f (x 2) / T.t036.f (x 5)
  have et := affine_frame T.t145.hN (x 3) (x 0) (x 5) α β
  have es := affine_frame T.q1356.hN (x 3) (x 0) (x 5) α β
  rw [← h2, F5] at et
  rw [← h2, B3, B5] at es
  have key : (T.q1356.f (x 2) - l * T.q1356.f (x 0)) * T.t145.f (x 0) =
      T.q1356.f (x 0) * (α + β - 1) * T.t145.f (x 3) := by
    have : l * T.t145.f (x 0) = T.t145.f (x 2) := by
      have := F0.ne; simp only [l]; field_simp
    linear_combination (-T.q1356.f (x 0)) * this + T.t145.f (x 0) * es - T.q1356.f (x 0) * et
  have hn : T.q1356.f (x 2) - l * T.q1356.f (x 0) < 0 := by
    have : 0 < (T.q1356.f (x 2) - l * T.q1356.f (x 0)) * T.t145.f (x 0) := by
      rw [key]; exact mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos B0 (by linarith)) F3
    by_contra hc; push Not at hc
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hc F0.le]
  have hμ : 0 < μ := div_pos_of_neg_of_neg hn B4
  have hs : T.q1356.f (x 2) = l * T.q1356.f (x 0) + μ * T.q1356.f (x 4) := by
    have := B4.ne; simp only [μ]; field_simp; ring
  -- the decomposition of `2` in the frame `1; 0, 4, 5`
  have hlμ : 1 ≤ l + μ := by
    by_contra hc; push Not at hc
    apply hvis
    refine ⟨l, μ, (⟪x 2, e⟫ - ⟪x 1, e⟫ - l * (⟪x 0, e⟫ - ⟪x 1, e⟫) -
      μ * (⟪x 4, e⟫ - ⟪x 1, e⟫)) / (⟪x 5, e⟫ - ⟪x 1, e⟫), hl, hμ, hc, ?_⟩
    refine eq_of_affine3 T.t145.hN T.q1356.hN (inner_affine e) (x 1) (x 0) (x 4) (x 5) ?_ ?_ ?_ ?_
    · rw [F1, F4, F5, B1, B5]
      have := mul_ne_zero F0.ne (mul_ne_zero B4.ne hU.ne')
      intro h; apply this; linarith
    · have := F0.ne; rw [affine_frame3 T.t145.hN, F1, F4, F5]; simp only [l]; field_simp; ring
    · rw [affine_frame3 T.q1356.hN, B1, B5, hs]; ring
    · rw [affine_frame3 (inner_affine e)]; field_simp; ring
  -- R1's inequality
  have hfar' := hfar.lt T.q1356.hN B3 B5 B0
  by_contra hc; push Not at hc
  nlinarith [mul_lt_mul_of_pos_left hfar' hl, mul_le_mul_of_nonneg_left hc hμ.le,
    mul_le_mul_of_nonpos_right hlμ B2.le]

/-- **Lemma 11.R2 (ii) (the S2 option in Gale signs).**  In the octahedral region, with
Gale data of `O` normalized for J's option `(a, b) = (2, 1)` (`κ_1 > 0`, `κ_2 ≠ 0`,
`[1 3] < 0`, `κ_3 ≠ 0`): if `2` is strictly farther than `4` from the plane `136`, it is
strictly farther than `4` from the plane `036`, so `2 → 4` is a quad edge of `O`
(Lemma 9.6 for the pair `{0, 1}`, the pole signs (G3), and Plücker). -/
theorem type16_R2 {x : Fin 7 → ℝ³} (T : Type16 x) (O : Oct16 x)
    (G : GaleData (x 1) (x 0) (x 2) (x 6) (x 3) (x 4))
    (hκ1 : 0 < galeD G.l G.m (x 1) (x 0)) (hκ2 : galeD G.l G.m (x 2) (x 6) ≠ 0)
    (hκ3 : galeD G.l G.m (x 3) (x 4) ≠ 0) (hU : galeD G.l G.m (x 1) (x 3) < 0)
    (h : T.q1356.f (x 2) < T.q1356.f (x 4)) : T.t036.f (x 2) < T.t036.f (x 4) := by
  set F := O.facets T
  have anti := galeD_anti G.l G.m
  have self := galeD_self G.l G.m
  obtain ⟨-, p2, p3⟩ := pole_signs F (G.hl.galeD G.hm (x 1)) (self _) hκ1.ne'
  have h12 : 0 < galeD G.l G.m (x 1) (x 2) := by
    by_contra hc; push Not at hc; nlinarith [mul_nonneg_of_nonpos_of_nonpos hc hU.le]
  have h14 : galeD G.l G.m (x 1) (x 4) < 0 := neg_of_mul_pos_right p2 hU.le
  obtain ⟨q1, -, -⟩ := pole_signs F.perm₁₂ (G.hl.galeD G.hm (x 2)).perm₁₂ (self _) hκ2
  have h02 : 0 < galeD G.l G.m (x 0) (x 2) := by
    have : galeD G.l G.m (x 2) (x 0) < 0 := by
      have h21 : galeD G.l G.m (x 2) (x 1) < 0 := by rw [anti]; linarith
      exact neg_of_mul_pos_right q1 h21.le
    rw [anti]; linarith
  obtain ⟨-, r2, r3⟩ := pole_signs F.swap₁ (G.hl.galeD G.hm (x 0)).swap₁ (self _)
    (by rw [anti]; linarith)
  have h03 : galeD G.l G.m (x 0) (x 3) < 0 := neg_of_mul_neg_right r3 h02.le
  have h04 : galeD G.l G.m (x 0) (x 4) < 0 := neg_of_mul_pos_right r2 h03.le
  obtain ⟨s1, s2, -⟩ := pole_signs F.perm₂₃.perm₁₂.swap₁
    (G.hl.galeD G.hm (x 4)).perm₂₃.perm₁₂.swap₁ (self _) (by rw [anti]; exact neg_ne_zero.mpr hκ3)
  have h42 : galeD G.l G.m (x 4) (x 2) < 0 := by
    have h41 : 0 < galeD G.l G.m (x 4) (x 1) := by rw [anti]; linarith
    obtain ⟨-, -, s3⟩ := pole_signs F.perm₂₃.perm₁₂.swap₁
      (G.hl.galeD G.hm (x 4)).perm₂₃.perm₁₂.swap₁ (self _) (by rw [anti]; exact neg_ne_zero.mpr hκ3)
    exact neg_of_mul_neg_right s3 h41.le
  have hnd6 : [x 2, x 6, x 4, x 3, x 1, x 0].Nodup := List.Nodup.map (l := [2, 6, 4, 3, 1, 0]) T.inj (by decide)
  have hnd6' : [x 2, x 6, x 4, x 3, x 0, x 1].Nodup := List.Nodup.map (l := [2, 6, 4, 3, 0, 1]) T.inj (by decide)
  -- Lemma 9.6 with `[0 ·]` at the face `136`
  have i1 := (facet_lt_iff_of_dep (G.hl.galeD G.hm (x 0)).perm₁₂.perm₂₃.swap₂
    (T.q1356.toO 6 3 1 (by decide) (by decide) (by decide) (by decide)) (by simp) (by simp) hnd6
    (self _) h02.ne').mp h
  have hs0 : galeD G.l G.m (x 0) (x 2) + galeD G.l G.m (x 0) (x 4) < 0 := by
    by_contra hc; push Not at hc; nlinarith
  -- Plücker gives `[1 2] + [1 4] < 0`
  have hpl := galeD_plucker G.l G.m (x 1) (x 0) (x 4) (x 2)
  have hs1 : galeD G.l G.m (x 1) (x 2) + galeD G.l G.m (x 1) (x 4) < 0 := by
    by_contra hc; push Not at hc
    have : 0 < galeD G.l G.m (x 1) (x 0) * galeD G.l G.m (x 4) (x 2) := by
      nlinarith [mul_pos h12 (show 0 < -galeD G.l G.m (x 0) (x 4) - galeD G.l G.m (x 0) (x 2) by
        linarith), mul_nonneg h02.le hc]
    nlinarith [mul_neg_of_pos_of_neg hκ1 h42]
  exact facet_lt_of_dep (G.hl.galeD G.hm (x 1)).perm₁₂.perm₂₃.swap₂.swap₃
    (T.t036.toO 6 3 0 (by decide) (by decide) (by decide) (by decide)) (by simp) (by simp) hnd6'
    (self _) (mul_neg_of_pos_of_neg h12 hs1)

/-- **Proposition 11.V (Claim V), with S1.**  In the octahedral region, with Gale data of
`O` normalized for J's option `(a, b) = (2, 1)` (`κ_1, κ_2 > 0`, `[1 3] < 0`,
`κ_3 ≠ 0`), if the cap `2` is not hidden in the triangle `1, 0, 4` at the view along
`15`, then `K` is Rupert (general position, no horizontal double normals).  If the far
end of `0235` along `35` is `0`, R1 and R2 make `2 → 4` a quad edge of `O` and Lemma 8
gives the test at `24`; if it is `2`, S1 applies at `35`: the third quadrilateral (far
end `1` of `1356`) or the T4 case (far end `6`, with `[2 3] [1 0] > 0`, R2 (i)), and
Lemma 11.U. -/
theorem isRupert_type16_V {x : Fin 7 → ℝ³} (T : Type16 x) (O : Oct16 x)
    (G : GaleData (x 1) (x 0) (x 2) (x 6) (x 3) (x 4))
    (hκ1 : 0 < galeD G.l G.m (x 1) (x 0)) (hκ2 : 0 < galeD G.l G.m (x 2) (x 6))
    (hκ3 : galeD G.l G.m (x 3) (x 4) ≠ 0) (hU : galeD G.l G.m (x 1) (x 3) < 0)
    (hvis : ¬ ∃ l μ ν : ℝ, 0 < l ∧ 0 < μ ∧ l + μ < 1 ∧
      x 2 = x 1 + l • (x 0 - x 1) + μ • (x 4 - x 1) + ν • (x 5 - x 1))
    (hgen : GenPos (univ.image x)) (hpar : NoPlaneParallel (univ.image x))
    (hnd : ∀ v ∈ univ.image x, ∀ w ∈ univ.image x, v ≠ w →
      NoHDNAt ((univ.image x).erase w) (w - v)) : IsRupert (univ.image x) := by
  have memV : ∀ i, x i ∈ univ.image x := fun i => mem_image_of_mem x (mem_univ i)
  have mid : ∀ {o v A m : ℝ³}, (∃ s t : ℝ, 0 < s ∧ s < 1 ∧ t ≠ 0 ∧ t + s - 1 ≠ 0 ∧
      m = o + s • (A - o) + t • (v - o)) → MidOf o v A m := by
    rintro o v A m ⟨s, t, h1, h2, -, -, h⟩; exact ⟨s, t, h1, h2, h⟩
  rcases T.far0235 hgen with h0 | h0
  · have hq1 := type16_R1 T (mid h0) hvis
    have hq2 := type16_R2 T O G hκ1 hκ2.ne' hκ3 hU hq1
    exact isRupert_type16_24 T hq1 hq2 hgen (hnd (x 2) (memV 2) (x 4) (memV 4) (T.inj.ne (by decide)))
  · refine isRupert_type16_35 T hgen hpar hnd ?_
    rcases T.far1356 hgen with h1 | h1
    · -- far ends `2`, `6`: the T4 case of S1 (R2 (i): `[2 3] [1 0] > 0`)
      have anti := galeD_anti G.l G.m
      set F := O.facets T
      obtain ⟨-, -, p3⟩ := pole_signs F (G.hl.galeD G.hm (x 1)) (galeD_self _ _ _) hκ1.ne'
      have h12 : 0 < galeD G.l G.m (x 1) (x 2) := by
        by_contra hc; push Not at hc; nlinarith [mul_nonneg_of_nonpos_of_nonpos hc hU.le]
      obtain ⟨-, -, q3⟩ := pole_signs F.perm₁₂ (G.hl.galeD G.hm (x 2)).perm₁₂ (galeD_self _ _ _)
        hκ2.ne'
      have h23 : 0 < galeD G.l G.m (x 2) (x 3) := by
        have h21 : galeD G.l G.m (x 2) (x 1) < 0 := by rw [anti]; linarith
        by_contra hc; push Not at hc; nlinarith [mul_nonneg_of_nonpos_of_nonpos h21.le hc]
      exact type16_not_bad35_T4σ' T O G (mul_pos h23 hκ1) hκ3 (mid h0) (mid h1)
    · exact type16_not_bad35_thirdQuad T O (mid h0) (mid h1)

/-- **Proposition 11.V by `σ`**: J's option `(a, b) = (1, 2)` (`κ_1, κ_2 > 0`,
`[2 3] < 0`, `κ_3 ≠ 0`) and the cap `1` not hidden in the triangle `2, 6, 4` at the view
along `25`. -/
theorem isRupert_type16_Vσ {x : Fin 7 → ℝ³} (T : Type16 x) (O : Oct16 x)
    (G : GaleData (x 1) (x 0) (x 2) (x 6) (x 3) (x 4))
    (hκ1 : 0 < galeD G.l G.m (x 1) (x 0)) (hκ2 : 0 < galeD G.l G.m (x 2) (x 6))
    (hκ3 : galeD G.l G.m (x 3) (x 4) ≠ 0) (hU : galeD G.l G.m (x 2) (x 3) < 0)
    (hvis : ¬ ∃ l μ ν : ℝ, 0 < l ∧ 0 < μ ∧ l + μ < 1 ∧
      x 1 = x 2 + l • (x 6 - x 2) + μ • (x 4 - x 2) + ν • (x 5 - x 2))
    (hgen : GenPos (univ.image x)) (hpar : NoPlaneParallel (univ.image x))
    (hnd : ∀ v ∈ univ.image x, ∀ w ∈ univ.image x, v ≠ w →
      NoHDNAt ((univ.image x).erase w) (w - v)) : IsRupert (univ.image x) := by
  rw [← image_sigma16] at hgen hpar hnd ⊢
  exact isRupert_type16_V T.sigma O.sigma G.perm₁₂ hκ2 hκ1 hκ3 hU hvis hgen hpar hnd

/-- **Proposition 11.V, Gale form** (any Gale data of `O`): `κ_1 κ_2 > 0`,
`[1 3] κ_1 < 0`, `κ_3 ≠ 0`, the cap `2` not hidden at the view along `15`. -/
theorem isRupert_type16_V' {x : Fin 7 → ℝ³} (T : Type16 x) (O : Oct16 x)
    (G : GaleData (x 1) (x 0) (x 2) (x 6) (x 3) (x 4))
    (h1 : 0 < galeD G.l G.m (x 1) (x 0) * galeD G.l G.m (x 2) (x 6))
    (h2 : galeD G.l G.m (x 1) (x 3) * galeD G.l G.m (x 1) (x 0) < 0)
    (hκ3 : galeD G.l G.m (x 3) (x 4) ≠ 0)
    (hvis : ¬ ∃ l μ ν : ℝ, 0 < l ∧ 0 < μ ∧ l + μ < 1 ∧
      x 2 = x 1 + l • (x 0 - x 1) + μ • (x 4 - x 1) + ν • (x 5 - x 1))
    (hgen : GenPos (univ.image x)) (hpar : NoPlaneParallel (univ.image x))
    (hnd : ∀ v ∈ univ.image x, ∀ w ∈ univ.image x, v ≠ w →
      NoHDNAt ((univ.image x).erase w) (w - v)) : IsRupert (univ.image x) := by
  obtain ⟨G', hpos, ε, hε, hG'⟩ := exists_gale_sign G (s := x 1) (t := x 0)
    (fun h0 => by rw [h0, zero_mul] at h1; exact lt_irrefl _ h1)
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  rw [hG'] at hpos
  refine isRupert_type16_V T O G' (by rw [hG']; exact hpos) ?_ ?_ ?_ hvis hgen hpar hnd
  · rw [hG']; nlinarith [mul_pos hpos h1]
  · rw [hG']; exact mul_ne_zero (by rcases hε with rfl | rfl <;> norm_num) hκ3
  · rw [hG']; nlinarith [mul_pos hpos (neg_pos.mpr h2)]

/-- **Proposition 11.V by `σ`, Gale form**: `κ_1 κ_2 > 0`, `[2 3] κ_2 < 0`, `κ_3 ≠ 0`,
the cap `1` not hidden at the view along `25`. -/
theorem isRupert_type16_Vσ' {x : Fin 7 → ℝ³} (T : Type16 x) (O : Oct16 x)
    (G : GaleData (x 1) (x 0) (x 2) (x 6) (x 3) (x 4))
    (h1 : 0 < galeD G.l G.m (x 1) (x 0) * galeD G.l G.m (x 2) (x 6))
    (h2 : galeD G.l G.m (x 2) (x 3) * galeD G.l G.m (x 2) (x 6) < 0)
    (hκ3 : galeD G.l G.m (x 3) (x 4) ≠ 0)
    (hvis : ¬ ∃ l μ ν : ℝ, 0 < l ∧ 0 < μ ∧ l + μ < 1 ∧
      x 1 = x 2 + l • (x 6 - x 2) + μ • (x 4 - x 2) + ν • (x 5 - x 2))
    (hgen : GenPos (univ.image x)) (hpar : NoPlaneParallel (univ.image x))
    (hnd : ∀ v ∈ univ.image x, ∀ w ∈ univ.image x, v ≠ w →
      NoHDNAt ((univ.image x).erase w) (w - v)) : IsRupert (univ.image x) := by
  rw [← image_sigma16] at hgen hpar hnd ⊢
  exact isRupert_type16_V' T.sigma O.sigma G.perm₁₂ (by rw [mul_comm]; exact h1) h2 hκ3 hvis
    hgen hpar hnd

/-! ### Lemma 11.5: the N2 branch of S2 -/

/-- **Lemma 11.5 (ii).**  If at the view along `15` the far end of `1356` is `6` (`3` a
middle), then at the view along `36` the far end of `1356` is `1` and `5` is a middle:
`5 = 3 + σ (1 − 3) + δ (3 − 6)`, `0 < σ < 1`, `δ > 0`. -/
theorem type16_lemma5_mid {x : Fin 7 → ℝ³} (T : Type16 x) (h : MidOf (x 1) (x 5) (x 6) (x 3)) :
    ∃ σ δ : ℝ, 0 < σ ∧ σ < 1 ∧ 0 < δ ∧ x 5 = x 3 + σ • (x 1 - x 3) + δ • (x 3 - x 6) := by
  obtain ⟨s, t, hs0, hs1, hx3⟩ := h
  have A1 := T.q0235.neg 1 (by decide); have A6 := T.q0235.neg 6 (by decide)
  have e := affine_frame T.q0235.hN (x 1) (x 6) (x 5) s t
  rw [← hx3, T.q0235.zero 3 (by decide), T.q0235.zero 5 (by decide)] at e
  -- `t − (1 − s) = s q₆ / q₁ > 0`
  have ht : 1 - s < t := by
    have : (t - (1 - s)) * T.q0235.f (x 1) = s * T.q0235.f (x 6) := by linear_combination e
    by_contra hc; push Not at hc
    nlinarith [mul_nonneg_of_nonpos_of_nonpos (show t - (1 - s) ≤ 0 by linarith) A1.le,
      mul_neg_of_pos_of_neg hs0 A6]
  have ht0 : 0 < t := by linarith
  refine ⟨1 - (1 - s) / t, s / t, ?_, ?_, div_pos hs0 ht0, ?_⟩
  · rw [sub_pos, div_lt_one ht0]; exact ht
  · have : 0 < (1 - s) / t := div_pos (by linarith) ht0
    linarith
  · have e2 : t • (x 5 - x 1) = x 3 - x 1 - s • (x 6 - x 1) := by rw [hx3]; abel
    have key : x 5 = x 1 + t⁻¹ • (x 3 - x 1 - s • (x 6 - x 1)) := by
      rw [← e2, smul_smul, inv_mul_cancel₀ ht0.ne', one_smul]; abel
    rw [key]; simp only [div_eq_mul_inv]; module

/-- **The N2 branch of Theorem M's S2 (Lemma 11.5 with §10's Lemma 7).**  In the
octahedral region, with Gale data normalized for J's option `(a, b) = (2, 1)`
(`κ_2, κ_1 > 0`, `[1 3] < 0`, `κ_3 ≠ 0`), if at the view along `15` the far end of
`1356` is `6` (`3` a middle), then `6 → 3` is a quad edge of `O` that is not bad (in
`K*` the far end of `1356*` along `5* 1` is `6`: `5` beyond `124` gives
`f₁₂₄ 6 < f₁₂₄ 3`, Lemma 11.5 (i)), `5` is a middle at its view (Lemma 11.5 (ii)), and
Lemma 9.3 with a middle gives a passage. -/
theorem isRupert_type16_S2N2 {x : Fin 7 → ℝ³} (T : Type16 x) (O : Oct16 x)
    (G : GaleData (x 1) (x 0) (x 2) (x 6) (x 3) (x 4))
    (hκ1 : 0 < galeD G.l G.m (x 1) (x 0)) (hκ2 : 0 < galeD G.l G.m (x 2) (x 6))
    (hκ3 : galeD G.l G.m (x 3) (x 4) ≠ 0) (hU : galeD G.l G.m (x 1) (x 3) < 0)
    (hfarK : MidOf (x 1) (x 5) (x 6) (x 3)) (hgen : GenPos (univ.image x))
    (hnd : ∀ v ∈ univ.image x, ∀ w ∈ univ.image x, v ≠ w →
      NoHDNAt ((univ.image x).erase w) (w - v)) : IsRupert (univ.image x) := by
  classical
  have memV : ∀ i, x i ∈ univ.image x := fun i => mem_image_of_mem x (mem_univ i)
  set F := (O.facets T).perm₁₂ with hF
  obtain ⟨σ, δ, hσ0, hσ1, hδ, hmid⟩ := type16_lemma5_mid T hfarK
  -- Lemma 11.5 (i): `f₁₂₄ 6 < f₁₂₄ 3`
  have hfar : F.abc'.f (x 6) < F.abc'.f (x 3) := by
    show O.t124.f (x 6) < O.t124.f (x 3)
    have e := affine_frame3 O.t124.hN (x 3) (x 1) (x 3) (x 6) σ 0 (-δ)
    rw [show x 3 + σ • (x 1 - x 3) + (0 : ℝ) • (x 3 - x 3) + (-δ) • (x 6 - x 3) = x 5 by
      rw [hmid]; module, O.t124.zero 1 (by decide)] at e
    have g5 := (O.five_beyond T).2
    have g3 := O.t124.neg 3 (by decide) (by decide)
    nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr hσ1) g3]
  obtain ⟨hq₂, hgood⟩ := type08_lemma7 F G.perm₁₂ hκ2 hκ1 hκ3 hU hfar
  have e : univ.image x = insert (x 5) ({x 6, x 2, x 3, x 4, x 1, x 0} : Finset ℝ³) := by
    rw [image_insert5]; ext z; simp only [mem_insert, mem_singleton]; tauto
  have := isRupert_quad_edge_middle (m := x 5) F.swap₁.perm₂₃ hfar hq₂ hgood
    ⟨σ, δ, hσ0, hσ1, hδ, Or.inl hmid⟩
    ⟨T.inj.ne (by decide), T.inj.ne (by decide), T.inj.ne (by decide), T.inj.ne (by decide),
      T.inj.ne (by decide), T.inj.ne (by decide)⟩
    (fun s t hs ht hst => by
      have hsV : s ∈ univ.image x := by
        rcases hs with rfl | rfl | rfl | rfl | rfl <;> exact memV _
      have htV : t ∈ univ.image x := by rcases ht with rfl | rfl | rfl <;> exact memV _
      refine hgen.inner_ne_of_ne hsV htV (memV 6) (memV 3) hst (T.inj.ne (by decide)) (Or.inl ?_)
      rcases ht with rfl | rfl | rfl <;> exact ⟨T.inj.ne (by decide), T.inj.ne (by decide)⟩)
    (by
      rw [← e]
      refine ⟨?_, hnd (x 6) (memV 6) (x 3) (memV 3) (T.inj.ne (by decide))⟩
      have := (hnd (x 3) (memV 3) (x 6) (memV 6) (T.inj.ne (by decide))).neg
      rwa [neg_sub] at this)
  rwa [← e] at this

/-- **The N2 branch of S2, Gale form** (any Gale data of `O`): `κ_1 κ_2 > 0`,
`[1 3] κ_1 < 0`, `κ_3 ≠ 0`, at the view along `15` the far end of `1356` is `6`. -/
theorem isRupert_type16_S2N2' {x : Fin 7 → ℝ³} (T : Type16 x) (O : Oct16 x)
    (G : GaleData (x 1) (x 0) (x 2) (x 6) (x 3) (x 4))
    (h1 : 0 < galeD G.l G.m (x 1) (x 0) * galeD G.l G.m (x 2) (x 6))
    (h2 : galeD G.l G.m (x 1) (x 3) * galeD G.l G.m (x 1) (x 0) < 0)
    (hκ3 : galeD G.l G.m (x 3) (x 4) ≠ 0)
    (hfarK : MidOf (x 1) (x 5) (x 6) (x 3)) (hgen : GenPos (univ.image x))
    (hnd : ∀ v ∈ univ.image x, ∀ w ∈ univ.image x, v ≠ w →
      NoHDNAt ((univ.image x).erase w) (w - v)) : IsRupert (univ.image x) := by
  obtain ⟨G', hpos, ε, hε, hG'⟩ := exists_gale_sign G (s := x 1) (t := x 0)
    (fun h0 => by rw [h0, zero_mul] at h1; exact lt_irrefl _ h1)
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  rw [hG'] at hpos
  refine isRupert_type16_S2N2 T O G' (by rw [hG']; exact hpos) ?_ ?_ ?_ hfarK hgen hnd
  · rw [hG']; nlinarith [mul_pos hpos h1]
  · rw [hG']; exact mul_ne_zero (by rcases hε with rfl | rfl <;> norm_num) hκ3
  · rw [hG']; nlinarith [mul_pos hpos (neg_pos.mpr h2)]

/-- **The N2 branch of S2 by `σ`, Gale form**: J's option `(1, 2)` (`κ_1 κ_2 > 0`,
`[2 3] κ_2 < 0`, `κ_3 ≠ 0`), at the view along `25` the far end of `0235` is `0`. -/
theorem isRupert_type16_S2N2σ' {x : Fin 7 → ℝ³} (T : Type16 x) (O : Oct16 x)
    (G : GaleData (x 1) (x 0) (x 2) (x 6) (x 3) (x 4))
    (h1 : 0 < galeD G.l G.m (x 1) (x 0) * galeD G.l G.m (x 2) (x 6))
    (h2 : galeD G.l G.m (x 2) (x 3) * galeD G.l G.m (x 2) (x 6) < 0)
    (hκ3 : galeD G.l G.m (x 3) (x 4) ≠ 0)
    (hfarK : MidOf (x 2) (x 5) (x 0) (x 3)) (hgen : GenPos (univ.image x))
    (hnd : ∀ v ∈ univ.image x, ∀ w ∈ univ.image x, v ≠ w →
      NoHDNAt ((univ.image x).erase w) (w - v)) : IsRupert (univ.image x) := by
  rw [← image_sigma16] at hgen hnd ⊢
  exact isRupert_type16_S2N2' T.sigma O.sigma G.perm₁₂ (by rw [mul_comm]; exact h1) h2 hκ3
    hfarK hgen hnd

/-! ### Theorem M′ (conditional) -/

/-- **The proved clauses of Theorem M′** for a type-16 point set (`[s t]` is
`galeD G.l G.m s t` for Gale data `G` of the octahedron `O = K − 5`, pairs `(1, 0)`,
`(2, 6)`, `(3, 4)`; "far end" refers to the view along `35`):
* Lemma 11.U: `35` is not bad;
* Corollary 11.Ua: an acute angle at `3` of `0235` or of `1356`;
* in the octahedral region (`Oct16`), Theorem M's S1 at the view along `35`: the third
  quadrilateral (far ends `2`, `1`; Lemma 11.3 (a)); J's T4 case (far ends `0`, `1` with
  `[1 3] [2 6] > 0`, or `2`, `6` with `[2 3] [1 0] > 0`, and `κ_3 ≠ 0`; Lemma 11.3 (b));
  the case N2 (far end `0` of `0235` with `[2 3] κ_1 > 0`, `κ_1 κ_3 > 0`, `κ_2 ≠ 0`: test
  `02`; far end `6` of `1356` with `[1 3] κ_2 > 0`, `κ_2 κ_3 > 0`, `κ_1 ≠ 0`: test `61`);
* in the octahedral region, Theorem M's S2 with the cap visible (Proposition 11.V): J's
  option `(2, 1)` (`κ_1 κ_2 > 0`, `[1 3] κ_1 < 0`, `κ_3 ≠ 0`) with the cap `2` not hidden
  in the triangle `1, 0, 4` at the view along `15`, or by `σ` the option `(1, 2)` with
  the cap `1` not hidden in the triangle `2, 6, 4` at the view along `25`;
* in the octahedral region, the N2 branch of S2 (Lemma 11.5): the option `(2, 1)` with
  the far end `6` of `1356` at the view along `15` (test `63`), or by `σ` the option
  `(1, 2)` with the far end `0` of `0235` at the view along `25` (test `03`).
Not included (not formalized): Theorem M's S2 in the T4 branch with the cap hidden
(Lemma 11.7) and S3 with a hidden cap (Lemmas 11.7, 11.9). -/
def Type16Clause (x : Fin 7 → ℝ³) : Prop :=
  ¬ Type16Bad35 x ∨
  (0 < ⟪x 0 - x 3, x 5 - x 3⟫ ∨ 0 < ⟪x 6 - x 3, x 5 - x 3⟫) ∨
  ∃ _ : Oct16 x,
    (MidOf (x 3) (x 5) (x 2) (x 0) ∧ MidOf (x 3) (x 5) (x 1) (x 6)) ∨
    ∃ G : GaleData (x 1) (x 0) (x 2) (x 6) (x 3) (x 4),
      (MidOf (x 3) (x 5) (x 0) (x 2) ∧ MidOf (x 3) (x 5) (x 1) (x 6) ∧
        0 < galeD G.l G.m (x 1) (x 3) * galeD G.l G.m (x 2) (x 6) ∧
        galeD G.l G.m (x 3) (x 4) ≠ 0) ∨
      (MidOf (x 3) (x 5) (x 2) (x 0) ∧ MidOf (x 3) (x 5) (x 6) (x 1) ∧
        0 < galeD G.l G.m (x 2) (x 3) * galeD G.l G.m (x 1) (x 0) ∧
        galeD G.l G.m (x 3) (x 4) ≠ 0) ∨
      (MidOf (x 3) (x 5) (x 0) (x 2) ∧
        0 < galeD G.l G.m (x 2) (x 3) * galeD G.l G.m (x 1) (x 0) ∧
        0 < galeD G.l G.m (x 1) (x 0) * galeD G.l G.m (x 3) (x 4) ∧
        galeD G.l G.m (x 2) (x 6) ≠ 0) ∨
      (MidOf (x 3) (x 5) (x 6) (x 1) ∧
        0 < galeD G.l G.m (x 1) (x 3) * galeD G.l G.m (x 2) (x 6) ∧
        0 < galeD G.l G.m (x 2) (x 6) * galeD G.l G.m (x 3) (x 4) ∧
        galeD G.l G.m (x 1) (x 0) ≠ 0) ∨
      (0 < galeD G.l G.m (x 1) (x 0) * galeD G.l G.m (x 2) (x 6) ∧
        galeD G.l G.m (x 1) (x 3) * galeD G.l G.m (x 1) (x 0) < 0 ∧
        galeD G.l G.m (x 3) (x 4) ≠ 0 ∧
        ¬ ∃ l μ ν : ℝ, 0 < l ∧ 0 < μ ∧ l + μ < 1 ∧
          x 2 = x 1 + l • (x 0 - x 1) + μ • (x 4 - x 1) + ν • (x 5 - x 1)) ∨
      (0 < galeD G.l G.m (x 1) (x 0) * galeD G.l G.m (x 2) (x 6) ∧
        galeD G.l G.m (x 2) (x 3) * galeD G.l G.m (x 2) (x 6) < 0 ∧
        galeD G.l G.m (x 3) (x 4) ≠ 0 ∧
        ¬ ∃ l μ ν : ℝ, 0 < l ∧ 0 < μ ∧ l + μ < 1 ∧
          x 1 = x 2 + l • (x 6 - x 2) + μ • (x 4 - x 2) + ν • (x 5 - x 2)) ∨
      (0 < galeD G.l G.m (x 1) (x 0) * galeD G.l G.m (x 2) (x 6) ∧
        galeD G.l G.m (x 1) (x 3) * galeD G.l G.m (x 1) (x 0) < 0 ∧
        galeD G.l G.m (x 3) (x 4) ≠ 0 ∧ MidOf (x 1) (x 5) (x 6) (x 3)) ∨
      (0 < galeD G.l G.m (x 1) (x 0) * galeD G.l G.m (x 2) (x 6) ∧
        galeD G.l G.m (x 2) (x 3) * galeD G.l G.m (x 2) (x 6) < 0 ∧
        galeD G.l G.m (x 3) (x 4) ≠ 0 ∧ MidOf (x 2) (x 5) (x 0) (x 3))

/-- **Theorem M′ of `FEWER-FACES-PROOFS.md` §11 (conditional).**  A type-16 point set
(`Type16`: the facets `0235`, `1356`, `024`, `036`, `046`, `145`, `146`, `245`) in general
position (`GenPos`, `NoPlaneParallel`), without horizontal double normals at the views
along its segments (`NoHDNAt`), for which one of the proved clauses of Theorem M and its
addendum holds (`Type16Clause`), is Rupert: the named edge crossing has a unimodal
reduced polygon (Theorem 8.9 with Theorem 7.3).  That some clause always holds is open
(the octahedral S2 and S3 branches with hidden caps are not formalized, and where `35`
is bad outside them no edge crossing is known to work), so there is no
`not_type16_of_isNopert`. -/
theorem isRupert_type16_M {x : Fin 7 → ℝ³} (T : Type16 x) (hgen : GenPos (univ.image x))
    (hpar : NoPlaneParallel (univ.image x))
    (hnd : ∀ v ∈ univ.image x, ∀ w ∈ univ.image x, v ≠ w →
      NoHDNAt ((univ.image x).erase w) (w - v))
    (hC : Type16Clause x) : IsRupert (univ.image x) := by
  rcases hC with h | h | ⟨O, h | ⟨G, h | h | h | h | h | h | h | h⟩⟩
  · exact isRupert_type16_35 T hgen hpar hnd h
  · exact isRupert_type16_35 T hgen hpar hnd (type16_not_bad35_of_acute T h)
  · exact isRupert_type16_35 T hgen hpar hnd (type16_not_bad35_thirdQuad T O h.1 h.2)
  · obtain ⟨h0, h1, h2, h3⟩ := h
    exact isRupert_type16_35 T hgen hpar hnd (type16_not_bad35_T4' T O G h2 h3 h0 h1)
  · obtain ⟨h0, h1, h2, h3⟩ := h
    exact isRupert_type16_35 T hgen hpar hnd (type16_not_bad35_T4σ' T O G h2 h3 h0 h1)
  · obtain ⟨h0, h1, h2, h3⟩ := h
    exact isRupert_type16_N2' T O G h1 h2 h3 h0 hgen hnd
  · obtain ⟨h0, h1, h2, h3⟩ := h
    exact isRupert_type16_N2σ' T O G h1 h2 h3 h0 hgen hnd
  · obtain ⟨h1, h2, h3, h4⟩ := h
    exact isRupert_type16_V' T O G h1 h2 h3 h4 hgen hpar hnd
  · obtain ⟨h1, h2, h3, h4⟩ := h
    exact isRupert_type16_Vσ' T O G h1 h2 h3 h4 hgen hpar hnd
  · obtain ⟨h1, h2, h3, h4⟩ := h
    exact isRupert_type16_S2N2' T O G h1 h2 h3 h4 hgen hnd
  · obtain ⟨h1, h2, h3, h4⟩ := h
    exact isRupert_type16_S2N2σ' T O G h1 h2 h3 h4 hgen hnd

end Minimality

end
