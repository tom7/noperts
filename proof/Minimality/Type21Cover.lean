module

public import Minimality.Type21Tier

@[expose] public section

/-!
# Type 21: the cap-face class, Gale computations (`FEWER-FACES-PROOFS.md` §16.0–16.3)

Labels as in `Type21Lemmas.lean`: `a, a', b, b', c, c', d = 0, 3, 4, 5, 1, 6, 2`;
`[s t] = galeD G.l G.m s t` for Gale data `G` of `O = K − 2`.

* **The normalized cap-face class** (§16.3): `CapNorm G`: `[3 0], [5 4], [6 1] > 0` and
  `ε = sign [3 5] = +1`; then the twelve cross brackets `[3 5], [3 4], [0 5], [0 4], [5 6],
  [5 1], [4 6], [4 1], [6 3], [6 0], [1 3], [1 0]` are positive (`CapNorm.signs`, from
  Lemma 13.4).
* **The cap** (§16.0): `IsCap21.gale_rel`: in the frame `2 = 0 + α (5 − 0) + β (6 − 0)` of
  `IsCap21.coords`, `(α + β − 1) [5 1] = α [1 0]` (the plane `346` and the dependency `[1 ·]`).
  With `τ = α / [5 1]` (the paper's `t̂`): `α = τ [5 1]`, `t = α + β − 1 = τ [1 0]`,
  `r' = β = 1 + τ ([1 0] − [5 1])`, `r = β + τ [1 6]`.
* **Lemma 16.2 (the dependencies of `K − 6`)** as needed: `type21_depO2_c` (`{1 ·}`, values
  `r [1 5], r' [1 4], r' [1 3], r [1 0], 0, [1 6]` at `5, 4, 3, 0, 1, 2`) and `type21_depO2_a`
  (`{0 ·}`, values `r [0 5], r [0 4] + τ [1 4] [6 0], r [0 3] + τ [1 3] [6 0], 0, r [0 1], [0 6]`),
  through `isDep_of_values`.
* **The facet values** in brackets (dependencies applied to the faces `014`, `134`, `135`,
  `015`): `type21_f014`, `type21_f134`, `type21_f135`, `type21_f015`.
* **The bracket identities** (Plücker relations and `Σ_t [s t] = 0`), `type21_ids`, checked
  by `ring` after eliminating `l 6`, `m 6`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### Dependencies from values -/

/-- A dependency of six distinct points with prescribed values. -/
theorem isDep_of_values {x₁ x₂ x₃ x₄ x₅ x₆ : ℝ³} (hnd : [x₁, x₂, x₃, x₄, x₅, x₆].Nodup)
    (v₁ v₂ v₃ v₄ v₅ v₆ : ℝ) (hs : v₁ + v₂ + v₃ + v₄ + v₅ + v₆ = 0)
    (hv : v₁ • x₁ + v₂ • x₂ + v₃ • x₃ + v₄ • x₄ + v₅ • x₅ + v₆ • x₆ = 0) :
    ∃ L : ℝ³ → ℝ, IsDep x₁ x₂ x₃ x₄ x₅ x₆ L ∧ L x₁ = v₁ ∧ L x₂ = v₂ ∧ L x₃ = v₃ ∧
      L x₄ = v₄ ∧ L x₅ = v₅ ∧ L x₆ = v₆ := by
  classical
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨h12, h13, h14, h15, h16⟩, ⟨h23, h24, h25, h26⟩, ⟨h34, h35, h36⟩, ⟨h45, h46⟩, h56, -⟩ :=
    hnd
  set L : ℝ³ → ℝ := fun t => if t = x₁ then v₁ else if t = x₂ then v₂ else if t = x₃ then v₃
    else if t = x₄ then v₄ else if t = x₅ then v₅ else v₆ with hL
  have e1 : L x₁ = v₁ := by simp [hL]
  have e2 : L x₂ = v₂ := by simp [hL, Ne.symm h12]
  have e3 : L x₃ = v₃ := by simp [hL, Ne.symm h13, Ne.symm h23]
  have e4 : L x₄ = v₄ := by simp [hL, Ne.symm h14, Ne.symm h24, Ne.symm h34]
  have e5 : L x₅ = v₅ := by simp [hL, Ne.symm h15, Ne.symm h25, Ne.symm h35, Ne.symm h45]
  have e6 : L x₆ = v₆ := by
    simp [hL, Ne.symm h16, Ne.symm h26, Ne.symm h36, Ne.symm h46, Ne.symm h56]
  refine ⟨L, ⟨?_, ?_⟩, e1, e2, e3, e4, e5, e6⟩
  · rw [e1, e2, e3, e4, e5, e6]; exact hs
  · rw [e1, e2, e3, e4, e5, e6]; exact hv

/-- Gale data with the two dependencies exchanged: every bracket changes sign. -/
def GaleData.flip {a a' b b' c c' : ℝ³} (G : GaleData a a' b b' c c') : GaleData a a' b b' c c' :=
  ⟨G.m, G.l, G.hm, G.hl, fun α β h1 h2 h3 h4 h5 h6 => by
    obtain ⟨hb, ha⟩ := G.indep β α (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith)
    exact ⟨ha, hb⟩⟩

theorem galeD_flip {a a' b b' c c' : ℝ³} (G : GaleData a a' b b' c c') (s t : ℝ³) :
    galeD G.flip.l G.flip.m s t = -galeD G.l G.m s t := by
  simp only [GaleData.flip, galeD]; ring

/-! ### The normalized cap-face class -/

/-- **The normalized cap-face class** (§16.3, labels `a, a', b, b', c, c' = 0, 3, 4, 5, 1, 6`):
`[3 0], [5 4], [6 1] > 0` (the pattern `(+, +, +)`) and `ε = sign [3 5] = +1`. -/
structure CapNorm {a a' b b' c c' : ℝ³} (G : GaleData a a' b b' c c') : Prop where
  h30 : 0 < galeD G.l G.m a' a
  h54 : 0 < galeD G.l G.m b' b
  h61 : 0 < galeD G.l G.m c' c
  h35 : 0 < galeD G.l G.m a' b'

/-- **The cross brackets of the normalized class** (Lemma 13.4): `[3 4], [0 5], [0 4]`
(`A × B`), `[5 6], [5 1], [4 6], [4 1]` (`B × C`), `[6 3], [6 0], [1 3], [1 0]` (`C × A`) are
positive, like `[3 5]`. -/
theorem type21_cross_signs {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    {G : GaleData a a' b b' c c'} (h35 : 0 < galeD G.l G.m a' b') :
    0 < galeD G.l G.m a' b ∧ 0 < galeD G.l G.m a b' ∧ 0 < galeD G.l G.m a b ∧
    0 < galeD G.l G.m b' c' ∧ 0 < galeD G.l G.m b' c ∧ 0 < galeD G.l G.m b c' ∧
    0 < galeD G.l G.m b c ∧
    0 < galeD G.l G.m c' a' ∧ 0 < galeD G.l G.m c' a ∧ 0 < galeD G.l G.m c a' ∧
    0 < galeD G.l G.m c a := by
  have anti := galeD_anti G.l G.m
  obtain ⟨⟨A1, A2, A3⟩, ⟨A1', A2', A3'⟩, AB, ⟨C1, C2, C3⟩⟩ := cluster_signs F G
  obtain ⟨⟨B1, -, B3⟩, -, -, -⟩ := cluster_signs F.perm₁₂ G.perm₁₂
  dsimp only [GaleData.perm₁₂] at B1 B3
  have h34 : 0 < galeD G.l G.m a' b := by nlinarith
  have h04 : 0 < galeD G.l G.m a b := by nlinarith
  have h05 : 0 < galeD G.l G.m a b' := by nlinarith
  have h31 : galeD G.l G.m a' c < 0 := by nlinarith
  have h36 : galeD G.l G.m a' c' < 0 := by nlinarith
  have h01 : galeD G.l G.m a c < 0 := by nlinarith
  have h06 : galeD G.l G.m a c' < 0 := by nlinarith
  have h40 : galeD G.l G.m b a < 0 := by rw [anti]; linarith
  have h41 : 0 < galeD G.l G.m b c := by nlinarith
  have h46 : 0 < galeD G.l G.m b c' := by nlinarith
  have h51 : 0 < galeD G.l G.m b' c := by nlinarith
  have h56 : 0 < galeD G.l G.m b' c' := by nlinarith
  refine ⟨h34, h05, h04, h56, h51, h46, h41, ?_, ?_, ?_, ?_⟩ <;> rw [anti] <;> linarith

theorem CapNorm.signs {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    {G : GaleData a a' b b' c c'} (hN : CapNorm G) :
    0 < galeD G.l G.m a' b ∧ 0 < galeD G.l G.m a b' ∧ 0 < galeD G.l G.m a b ∧
    0 < galeD G.l G.m b' c' ∧ 0 < galeD G.l G.m b' c ∧ 0 < galeD G.l G.m b c' ∧
    0 < galeD G.l G.m b c ∧
    0 < galeD G.l G.m c' a' ∧ 0 < galeD G.l G.m c' a ∧ 0 < galeD G.l G.m c a' ∧
    0 < galeD G.l G.m c a :=
  type21_cross_signs F hN.h35

/-- The cross-bracket normalization (`ε = sign [3 5] = +1`, `[3 0] > 0`, `[6 1] > 0`), shared by
the cap-face class and the pattern `(+, −, +)` of the other classes (§16 addendum). -/
structure CrossNorm {a a' b b' c c' : ℝ³} (G : GaleData a a' b b' c c') : Prop where
  h30 : 0 < galeD G.l G.m a' a
  h61 : 0 < galeD G.l G.m c' c
  h35 : 0 < galeD G.l G.m a' b'

theorem CapNorm.toCross {a a' b b' c c' : ℝ³} {G : GaleData a a' b b' c c'} (hN : CapNorm G) :
    CrossNorm G := ⟨hN.h30, hN.h61, hN.h35⟩

theorem CrossNorm.signs {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    {G : GaleData a a' b b' c c'} (hN : CrossNorm G) :
    0 < galeD G.l G.m a' b ∧ 0 < galeD G.l G.m a b' ∧ 0 < galeD G.l G.m a b ∧
    0 < galeD G.l G.m b' c' ∧ 0 < galeD G.l G.m b' c ∧ 0 < galeD G.l G.m b c' ∧
    0 < galeD G.l G.m b c ∧
    0 < galeD G.l G.m c' a' ∧ 0 < galeD G.l G.m c' a ∧ 0 < galeD G.l G.m c a' ∧
    0 < galeD G.l G.m c a :=
  type21_cross_signs F hN.h35

/-! ### The cap in brackets -/

/-- **The cap relation** (§16.0): with `2 = 0 + α (5 − 0) + β (6 − 0)` (`IsCap21.coords`),
`(α + β − 1) [5 1] = α [1 0]`: `2` lies on the plane `346`, and the dependency `[1 ·]`
applied to that plane gives `[1 0] f(0) + [1 5] f(5) = 0`. -/
theorem IsCap21.gale_rel {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'}
    (hd : IsCap21 F d) (G : GaleData a a' b b' c c') :
    (F.abc'.f d / F.abc'.f b' + F.ab'c.f d / F.ab'c.f c' - 1) * galeD G.l G.m b' c =
      F.abc'.f d / F.abc'.f b' * galeD G.l G.m c a := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  obtain ⟨-, -, -, hco⟩ := hd.coords
  set α := F.abc'.f d / F.abc'.f b'
  set β := F.ab'c.f d / F.ab'c.f c'
  have hf := affine_frame F.a'bc'.hN a b' c' α β
  rw [← hco, hd.a'bc', F.a'bc'.hR] at hf
  have r := (G.hl.galeD G.hm c).apply F.a'bc'.hN
  rw [F.a'bc'.hP, F.a'bc'.hQ, F.a'bc'.hR, galeD_self] at r
  have na := F.a'bc'.neg a (by simp) haa' hab hac'
  have hanti := galeD_anti G.l G.m c b'
  have key : F.a'bc'.f a * (α * galeD G.l G.m c a - (1 - α - β) * galeD G.l G.m c b') = 0 := by
    linear_combination α * r + galeD G.l G.m c b' * hf
  have := (mul_eq_zero.mp key).resolve_left na.ne
  rw [hanti]; linarith

/-! ### Bracket identities

Each identity is a consequence of the Plücker relations and `Σ_t [s t] = 0`; it is checked by
`ring` after writing the brackets in the dependencies `l`, `m` and eliminating `l 6`, `m 6`
(`type21_ring`). -/

theorem IsDep.l_last {a a' b b' c c' : ℝ³} {l : ℝ³ → ℝ} (hl : IsDep a a' b b' c c' l) :
    l c' = -(l a + l a' + l b + l b' + l c) := by linarith [hl.sum]

/-- Unfold the brackets, eliminate the dependencies at the sixth point, `ring`. -/
macro "type21_ring " hl:term:max hm:term:max : tactic =>
  `(tactic| (simp only [galeD, IsDep.l_last $hl, IsDep.l_last $hm]; ring))

theorem type21_id_P1 {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ}
    (hl : IsDep a a' b b' c c' l) (hm : IsDep a a' b b' c c' m) :
    galeD l m c' c * galeD l m a b' = galeD l m b' c' * galeD l m c a - galeD l m c' a *
      galeD l m b' c := by
  type21_ring hl hm

theorem type21_id_P2 {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ}
    (hl : IsDep a a' b b' c c' l) (hm : IsDep a a' b b' c c' m) :
    galeD l m a' a * galeD l m b c' = galeD l m a b * galeD l m c' a' - galeD l m c' a *
      galeD l m a' b := by
  type21_ring hl hm

theorem type21_id_P3 {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ}
    (_hl : IsDep a a' b b' c c' l) (_hm : IsDep a a' b b' c c' m) :
    galeD l m c a' * galeD l m b' b = galeD l m b c * galeD l m a' b' - galeD l m b' c *
      galeD l m a' b := by
  simp only [galeD]; ring

theorem type21_id_F1 {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ}
    (hl : IsDep a a' b b' c c' l) (hm : IsDep a a' b b' c c' m) :
    (galeD l m c a + galeD l m a' a + galeD l m a' b' - galeD l m b' c) * (galeD l m c a' -
      galeD l m a' b) = galeD l m c a' * (galeD l m b' c' - galeD l m c' a) + (galeD l m a' a +
      galeD l m a' b') * (galeD l m b c - galeD l m a' b) := by
  type21_ring hl hm

theorem type21_id_F3 {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ}
    (hl : IsDep a a' b b' c c' l) (hm : IsDep a a' b b' c c' m) :
    (galeD l m c a + galeD l m a' a + galeD l m a' b' - galeD l m b' c) * (galeD l m a b' -
      galeD l m c' a) = (galeD l m c a + galeD l m a' a) * (galeD l m b' c' - galeD l m c' a) +
      galeD l m a b' * (galeD l m b c - galeD l m a' b) := by
  type21_ring hl hm

theorem type21_id_F6 {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ}
    (hl : IsDep a a' b b' c c' l) (hm : IsDep a a' b b' c c' m) :
    (galeD l m c a + galeD l m a' a + galeD l m a' b' - galeD l m b' c) * (galeD l m b c' -
      galeD l m a' b) = (galeD l m b c - galeD l m a' b) * (galeD l m c' a' - galeD l m a' b) +
      galeD l m b c' * (galeD l m c a - galeD l m b' c) + galeD l m b c' * (galeD l m c' a' -
      galeD l m a' b) := by
  type21_ring hl hm

theorem type21_id_s4 {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ}
    (hl : IsDep a a' b b' c c' l) (hm : IsDep a a' b b' c c' m) :
    galeD l m b c' = galeD l m a b + galeD l m b' b - galeD l m b c + galeD l m a' b := by
  type21_ring hl hm

theorem type21_id_s3 {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ}
    (hl : IsDep a a' b b' c c' l) (hm : IsDep a a' b b' c c' m) :
    galeD l m c' a' - galeD l m a' b = galeD l m a' a + galeD l m a' b' - galeD l m c a' := by
  type21_ring hl hm

theorem type21_id_s0 {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ}
    (hl : IsDep a a' b b' c c' l) (hm : IsDep a a' b b' c c' m) :
    galeD l m a b + galeD l m a b' = galeD l m a' a + galeD l m c a + galeD l m c' a := by
  type21_ring hl hm

theorem type21_id_s1 {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ}
    (hl : IsDep a a' b b' c c' l) (hm : IsDep a a' b b' c c' m) :
    galeD l m c a - galeD l m b' c - galeD l m c' c = galeD l m b c - galeD l m c a' := by
  type21_ring hl hm

theorem type21_id_P4 {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ}
    (_hl : IsDep a a' b b' c c' l) (_hm : IsDep a a' b b' c c' m) :
    galeD l m c a' * galeD l m a b = galeD l m b c * galeD l m a' a + galeD l m c a *
      galeD l m a' b := by
  simp only [galeD]; ring

theorem type21_id_P5 {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ}
    (hl : IsDep a a' b b' c c' l) (hm : IsDep a a' b b' c c' m) :
    galeD l m c a' * galeD l m b' c' = galeD l m c' c * galeD l m a' b' + galeD l m b' c *
      galeD l m c' a' := by
  type21_ring hl hm

theorem type21_id_A1 {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ}
    (hl : IsDep a a' b b' c c' l) (hm : IsDep a a' b b' c c' m) :
    galeD l m b' c * galeD l m c' a - galeD l m c a * galeD l m b' c' + galeD l m c a *
      galeD l m a b' - galeD l m b' c * galeD l m a b' = -((galeD l m c a' - galeD l m b c) *
      galeD l m a b') := by
  type21_ring hl hm

theorem type21_id_D135 {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ}
    (hl : IsDep a a' b b' c c' l) (hm : IsDep a a' b b' c c' m) :
    galeD l m a b * galeD l m c a - galeD l m a b * galeD l m b' c - galeD l m c a *
      galeD l m b c' = -(galeD l m c a' * galeD l m a b - galeD l m b c * galeD l m a b +
      galeD l m b c * galeD l m c' a) := by
  type21_ring hl hm

theorem type21_id_kE {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ}
    (hl : IsDep a a' b b' c c' l) (hm : IsDep a a' b b' c c' m) :
    (galeD l m a' b' * galeD l m c a + galeD l m b' c * (galeD l m c' a' - galeD l m a' b')) *
      galeD l m a' a + (galeD l m c' a' - galeD l m a' b') * (galeD l m a' a * (galeD l m b c -
      galeD l m c a') - galeD l m c a' * galeD l m c' a) = galeD l m c a * galeD l m c' a' *
      (galeD l m c a' - galeD l m a' b) := by
  type21_ring hl hm

theorem type21_id_kA2 {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ}
    (hl : IsDep a a' b b' c c' l) (hm : IsDep a a' b b' c c' m) :
    (galeD l m a' b' * galeD l m c a + galeD l m b' c * (galeD l m c' a' - galeD l m a' b')) *
      (galeD l m b c - galeD l m c a) + (galeD l m b' c' - galeD l m a' b') * ((galeD l m c a -
      galeD l m b' c) * galeD l m b c - (galeD l m b c - galeD l m c a') * galeD l m c a) =
      galeD l m b c * galeD l m b' c * (galeD l m c' a' - galeD l m b' c') := by
  type21_ring hl hm

theorem type21_id_kAS {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ}
    (hl : IsDep a a' b b' c c' l) (hm : IsDep a a' b b' c c' m) :
    (galeD l m a' b' * galeD l m c a + galeD l m b' c * (galeD l m c' a' - galeD l m a' b')) *
      (galeD l m b c - galeD l m c a) + (galeD l m c' a' - galeD l m a' b') * ((galeD l m c a -
      galeD l m b' c) * galeD l m b c - (galeD l m b c - galeD l m c a') * galeD l m c a) =
      galeD l m c a * galeD l m c a' * (galeD l m c' a' - galeD l m b' c') := by
  type21_ring hl hm

theorem type21_id_kFS {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ}
    (hl : IsDep a a' b b' c c' l) (hm : IsDep a a' b b' c c' m) :
    (galeD l m a' b' * galeD l m c a + galeD l m b' c * (galeD l m c' a' - galeD l m a' b')) *
      (galeD l m b c' - galeD l m a' b) + (galeD l m c' a' - galeD l m a' b') * (-((galeD l m c a
      - galeD l m b' c) * galeD l m a' b)) = galeD l m c a * galeD l m c' a' * galeD l m b' b +
      galeD l m c a * galeD l m a' b * (galeD l m b' c' - galeD l m c' a') + galeD l m b c' *
      galeD l m b' c * (galeD l m c' a' - galeD l m a' b') := by
  type21_ring hl hm

theorem type21_id_kF2 {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ}
    (hl : IsDep a a' b b' c c' l) (hm : IsDep a a' b b' c c' m) :
    (galeD l m a' b' * galeD l m c a + galeD l m b' c * (galeD l m c' a' - galeD l m a' b')) *
      (galeD l m b c' - galeD l m a' b) + (galeD l m b' c' - galeD l m a' b') * (-((galeD l m c a
      - galeD l m b' c) * galeD l m a' b)) = galeD l m c' a' * (galeD l m b' b * (galeD l m c a -
      galeD l m b' c) + galeD l m b' c * (galeD l m b c' - galeD l m a' b)) := by
  type21_ring hl hm

theorem type21_id_B {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ}
    (hl : IsDep a a' b b' c c' l) (hm : IsDep a a' b b' c c' m) :
    galeD l m c' a - galeD l m b c' = galeD l m b' c' - galeD l m c' a' - galeD l m c' c := by
  type21_ring hl hm

theorem type21_id_A1end {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ}
    (hl : IsDep a a' b b' c c' l) (hm : IsDep a a' b b' c c' m) :
    (galeD l m a b' - galeD l m c' a) * (galeD l m c a' * galeD l m a b -
      galeD l m b c * galeD l m a b + galeD l m b c * galeD l m c' a) -
      galeD l m a b * (galeD l m c a' - galeD l m b c) * galeD l m a b' =
      galeD l m c' a * galeD l m c a * (galeD l m b c - galeD l m a' b) := by
  type21_ring hl hm

/-! ### The cap parameter and the facet values -/

/-- **The cap parameter** (§16.0): `2 = 0 + α (5 − 0) + β (6 − 0)` with `α, β > 0`,
`α + β > 1`, and `τ > 0` (the paper's `t̂`) with `α = τ [5 1]`, `α + β − 1 = τ [1 0]`. -/
theorem IsCap21.tau' {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'} (hd : IsCap21 F d)
    {G : GaleData a a' b b' c c'} (h35 : 0 < galeD G.l G.m a' b') :
    ∃ α β τ : ℝ, 0 < α ∧ 0 < β ∧ 1 < α + β ∧ 0 < τ ∧ d = a + α • (b' - a) + β • (c' - a) ∧
      α = τ * galeD G.l G.m b' c ∧ α + β - 1 = τ * galeD G.l G.m c a := by
  obtain ⟨hα, hβ, hαβ, hco⟩ := hd.coords
  have hrel := hd.gale_rel G
  obtain ⟨-, -, -, -, h51, -, -, -, -, -, h10⟩ := type21_cross_signs F h35
  generalize F.abc'.f d / F.abc'.f b' = α at *
  generalize F.ab'c.f d / F.ab'c.f c' = β at *
  refine ⟨α, β, α / galeD G.l G.m b' c, hα, hβ, hαβ, div_pos hα h51, hco, by field_simp, ?_⟩
  rw [div_mul_eq_mul_div, eq_div_iff h51.ne']
  linarith

theorem IsCap21.tau {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'} (hd : IsCap21 F d)
    {G : GaleData a a' b b' c c'} (hN : CrossNorm G) :
    ∃ α β τ : ℝ, 0 < α ∧ 0 < β ∧ 1 < α + β ∧ 0 < τ ∧ d = a + α • (b' - a) + β • (c' - a) ∧
      α = τ * galeD G.l G.m b' c ∧ α + β - 1 = τ * galeD G.l G.m c a :=
  hd.tau' hN.h35

/-- The face `014` (`F.abc`) in brackets: `[6 3] f(3) = [5 6] f(5)`, `[3 5] f(5) = [6 3] f(6)`,
and `f(2) = α f(5) + β f(6)`. -/
theorem type21_f014 {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') {α β : ℝ} (hco : d = a + α • (b' - a) + β • (c' - a)) :
    galeD G.l G.m c' a' * F.abc.f a' = galeD G.l G.m b' c' * F.abc.f b' ∧
    galeD G.l G.m a' b' * F.abc.f b' = galeD G.l G.m c' a' * F.abc.f c' ∧
    F.abc.f d = α * F.abc.f b' + β * F.abc.f c' := by
  have r1 := (G.hl.galeD G.hm c').apply F.abc.hN
  have r2 := (G.hl.galeD G.hm a').apply F.abc.hN
  rw [F.abc.hP, F.abc.hQ, F.abc.hR, galeD_self] at r1 r2
  have hf := affine_frame F.abc.hN a b' c' α β
  rw [← hco, F.abc.hP] at hf
  refine ⟨?_, ?_, by linarith⟩
  · rw [galeD_anti G.l G.m b' c'] at r1; linear_combination r1
  · rw [galeD_anti G.l G.m c' a'] at r2; linear_combination r2

/-- The face `134` (`F.a'bc`) in brackets: `[0 5] f(5) = [6 0] f(6)`,
`[0 5] f(0) = [5 6] f(6)`, and `f(2) = (1 − α − β) f(0) + α f(5) + β f(6)`. -/
theorem type21_f134 {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') {α β : ℝ} (hco : d = a + α • (b' - a) + β • (c' - a)) :
    galeD G.l G.m a b' * F.a'bc.f b' = galeD G.l G.m c' a * F.a'bc.f c' ∧
    galeD G.l G.m a b' * F.a'bc.f a = galeD G.l G.m b' c' * F.a'bc.f c' ∧
    F.a'bc.f d = (1 - α - β) * F.a'bc.f a + α * F.a'bc.f b' + β * F.a'bc.f c' := by
  have r1 := (G.hl.galeD G.hm a).apply F.a'bc.hN
  have r2 := (G.hl.galeD G.hm b').apply F.a'bc.hN
  rw [F.a'bc.hP, F.a'bc.hQ, F.a'bc.hR, galeD_self] at r1 r2
  have hf := affine_frame F.a'bc.hN a b' c' α β
  rw [← hco] at hf
  refine ⟨?_, ?_, by linarith⟩
  · rw [galeD_anti G.l G.m c' a] at r1; linear_combination r1
  · rw [galeD_anti G.l G.m a b'] at r2; linear_combination -r2

/-- The face `135` (`F.a'b'c`) in brackets: `[0 4] f(0) = [4 6] f(6)`,
`[6 0] f(0) = [4 6] f(4)`, and `f(2) = (1 − α − β) f(0) + β f(6)`. -/
theorem type21_f135 {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') {α β : ℝ} (hco : d = a + α • (b' - a) + β • (c' - a)) :
    galeD G.l G.m a b * F.a'b'c.f a = galeD G.l G.m b c' * F.a'b'c.f c' ∧
    galeD G.l G.m c' a * F.a'b'c.f a = galeD G.l G.m b c' * F.a'b'c.f b ∧
    F.a'b'c.f d = (1 - α - β) * F.a'b'c.f a + β * F.a'b'c.f c' := by
  have r1 := (G.hl.galeD G.hm b).apply F.a'b'c.hN
  have r2 := (G.hl.galeD G.hm c').apply F.a'b'c.hN
  rw [F.a'b'c.hP, F.a'b'c.hQ, F.a'b'c.hR, galeD_self] at r1 r2
  have hf := affine_frame F.a'b'c.hN a b' c' α β
  rw [← hco, F.a'b'c.hQ] at hf
  refine ⟨?_, ?_, by linarith⟩
  · rw [galeD_anti G.l G.m a b] at r1; linear_combination -r1
  · rw [galeD_anti G.l G.m b c'] at r2; linear_combination r2

/-- The face `015` (`F.ab'c`) in brackets: `[3 4] f(3) = [4 6] f(6)` and `f(2) = β f(6)`. -/
theorem type21_f015 {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') {α β : ℝ} (hco : d = a + α • (b' - a) + β • (c' - a)) :
    galeD G.l G.m a' b * F.ab'c.f a' = galeD G.l G.m b c' * F.ab'c.f c' ∧
    F.ab'c.f d = β * F.ab'c.f c' := by
  have r1 := (G.hl.galeD G.hm b).apply F.ab'c.hN
  rw [F.ab'c.hP, F.ab'c.hQ, F.ab'c.hR, galeD_self] at r1
  have hf := affine_frame F.ab'c.hN a b' c' α β
  rw [← hco, F.ab'c.hP, F.ab'c.hQ] at hf
  refine ⟨?_, by linarith⟩
  rw [galeD_anti G.l G.m a' b] at r1; linear_combination -r1

/-! ### Lemma 16.2: two dependencies of `K − 6` -/

theorem type21_nodup_O2 {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'} (hd : IsCap21 F d) :
    [d, c, b', b, a', a].Nodup := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd ⊢
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := hd.ne
  exact ⟨⟨hdc, hdb', hdb, hda', hda⟩, ⟨Ne.symm hb'c, Ne.symm hbc, Ne.symm ha'c, Ne.symm hac⟩,
    ⟨Ne.symm hbb', Ne.symm ha'b', Ne.symm hab'⟩, ⟨Ne.symm ha'b, Ne.symm hab⟩, Ne.symm haa',
    not_false⟩

/-- **The dependency `{1 ·}` of `K − 6`** (Lemma 16.2): with `r = β + τ [1 6]`, the values
`[1 6], 0, r [1 5], β [1 4], β [1 3], r [1 0]` at `2, 1, 5, 4, 3, 0`. -/
theorem type21_depO2_c {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'}
    (hd : IsCap21 F d) (G : GaleData a a' b b' c c') {α β τ : ℝ}
    (hco : d = a + α • (b' - a) + β • (c' - a)) (hα : α = τ * galeD G.l G.m b' c)
    (ht : α + β - 1 = τ * galeD G.l G.m c a) :
    ∃ L : ℝ³ → ℝ, IsDep d c b' b a' a L ∧ L d = galeD G.l G.m c c' ∧ L c = 0 ∧
      L b' = (β + τ * galeD G.l G.m c c') * galeD G.l G.m c b' ∧
      L b = β * galeD G.l G.m c b ∧ L a' = β * galeD G.l G.m c a' ∧
      L a = (β + τ * galeD G.l G.m c c') * galeD G.l G.m c a := by
  have hs := galeD_sum G.hl G.hm c
  have hv := (G.hl.galeD G.hm c).vsum
  rw [galeD_self] at hs hv
  have hX : α + τ * galeD G.l G.m c b' = 0 := by
    rw [hα, galeD_anti G.l G.m c b']; ring
  refine isDep_of_values (type21_nodup_O2 hd) _ _ _ _ _ _ ?_ ?_
  · linear_combination β * hs + galeD G.l G.m c c' * (hX - ht)
  · rw [hco]
    linear_combination (norm := module) β • hv + (galeD G.l G.m c c' * hX) • b' -
      (galeD G.l G.m c c' * ht) • a

/-- **The dependency `{0 ·}` of `K − 6`** (Lemma 16.2): with `r = β + τ [1 6]`, the values
`0, r [0 3] + τ [1 3] [6 0], r [0 5], r [0 4] + τ [1 4] [6 0], r [0 1], [0 6]` at
`0, 3, 5, 4, 1, 2`. -/
theorem type21_depO2_a {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'}
    (hd : IsCap21 F d) (G : GaleData a a' b b' c c') {α β τ : ℝ}
    (hco : d = a + α • (b' - a) + β • (c' - a)) (hα : α = τ * galeD G.l G.m b' c)
    (ht : α + β - 1 = τ * galeD G.l G.m c a) :
    ∃ L : ℝ³ → ℝ, IsDep a a' b' b c d L ∧ L a = 0 ∧
      L a' = (β + τ * galeD G.l G.m c c') * galeD G.l G.m a a' +
        τ * galeD G.l G.m c a' * galeD G.l G.m c' a ∧
      L b' = (β + τ * galeD G.l G.m c c') * galeD G.l G.m a b' ∧
      L b = (β + τ * galeD G.l G.m c c') * galeD G.l G.m a b +
        τ * galeD G.l G.m c b * galeD G.l G.m c' a ∧
      L c = (β + τ * galeD G.l G.m c c') * galeD G.l G.m a c ∧ L d = galeD G.l G.m a c' := by
  have hsa := galeD_sum G.hl G.hm a
  have hva := (G.hl.galeD G.hm a).vsum
  have hsc := galeD_sum G.hl G.hm c
  have hvc := (G.hl.galeD G.hm c).vsum
  rw [galeD_self] at hsa hva hsc hvc
  have hX : α + τ * galeD G.l G.m c b' = 0 := by
    rw [hα, galeD_anti G.l G.m c b']; ring
  have hnd := type21_nodup_O2 hd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, ⟨h6, h7, h8, h9⟩, ⟨h10, h11, h12⟩, ⟨h13, h14⟩, h15, -⟩ := hnd
  have hnd' : [a, a', b', b, c, d].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_or, List.nodup_nil, and_true]
    exact ⟨⟨Ne.symm h15, Ne.symm h12, Ne.symm h14, Ne.symm h9, Ne.symm h5⟩,
      ⟨Ne.symm h11, Ne.symm h13, Ne.symm h8, Ne.symm h4⟩, ⟨h10, Ne.symm h6, Ne.symm h2⟩,
      ⟨Ne.symm h7, Ne.symm h3⟩, Ne.symm h1, not_false⟩
  have anti := galeD_anti G.l G.m
  refine isDep_of_values hnd' _ _ _ _ _ _ ?_ ?_
  · rw [anti a c']
    linear_combination (β + τ * galeD G.l G.m c c') * hsa - τ * galeD G.l G.m a c' * hsc +
      galeD G.l G.m a c' * (hX - ht)
  · rw [hco, anti a c']
    linear_combination (norm := module) (β + τ * galeD G.l G.m c c') • hva -
      (τ * galeD G.l G.m a c') • hvc - (galeD G.l G.m a c' * ht) • a +
      (galeD G.l G.m a c' * hX) • b'

/-! ### Step 3 of Theorem 16.13: `Q` at `25` of `K − 6` -/

/-- `r = β + τ [1 6] = δ_134(2) / δ_134(6) > 0` and `r [0 5] = (1 − α − β) [5 6] + α [6 0] + β [0 5]`
(the face `134`), in the normalized class. -/
theorem type21_r_pos' {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'} (hd : IsCap21 F d)
    {G : GaleData a a' b b' c c'} (h35 : 0 < galeD G.l G.m a' b') {α β τ : ℝ}
    (hco : d = a + α • (b' - a) + β • (c' - a)) (hα : α = τ * galeD G.l G.m b' c)
    (ht : α + β - 1 = τ * galeD G.l G.m c a) :
    0 < β + τ * galeD G.l G.m c c' ∧
    F.a'bc.f d = (β + τ * galeD G.l G.m c c') * F.a'bc.f c' ∧
    galeD G.l G.m a b' * F.a'bc.f b' = galeD G.l G.m c' a * F.a'bc.f c' := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  obtain ⟨-, s05, -, -, -, -, -, -, -, -, -⟩ := type21_cross_signs F h35
  obtain ⟨e1, e2, e3⟩ := type21_f134 F G hco
  have P1 := type21_id_P1 G.hl G.hm
  have φn := F.a'bc.neg c' (by simp) (Ne.symm ha'c') (Ne.symm hbc') (Ne.symm hcc')
  have key : galeD G.l G.m a b' * F.a'bc.f d =
      galeD G.l G.m a b' * ((β + τ * galeD G.l G.m c c') * F.a'bc.f c') := by
    have h1 : 1 - α - β = -(τ * galeD G.l G.m c a) := by linarith
    rw [e3, h1, hα]
    rw [galeD_anti G.l G.m c c'] at P1
    linear_combination (-τ * galeD G.l G.m c a) * e2 + τ * galeD G.l G.m b' c * e1 +
      τ * F.a'bc.f c' * P1
  have hfd : F.a'bc.f d = (β + τ * galeD G.l G.m c c') * F.a'bc.f c' :=
    mul_left_cancel₀ s05.ne' key
  refine ⟨?_, hfd, e1⟩
  have := hd.a'bc
  rw [hfd] at this
  exact pos_of_mul_neg_left this φn.le

theorem type21_r_pos {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'} (hd : IsCap21 F d)
    {G : GaleData a a' b b' c c'} (hN : CrossNorm G) {α β τ : ℝ}
    (hco : d = a + α • (b' - a) + β • (c' - a)) (hα : α = τ * galeD G.l G.m b' c)
    (ht : α + β - 1 = τ * galeD G.l G.m c a) :
    0 < β + τ * galeD G.l G.m c c' ∧
    F.a'bc.f d = (β + τ * galeD G.l G.m c c') * F.a'bc.f c' ∧
    galeD G.l G.m a b' * F.a'bc.f b' = galeD G.l G.m c' a * F.a'bc.f c' :=
  type21_r_pos' hd hN.h35 hco hα ht

/-- **Lemma 16.11 (A1)** in the normalized class with `[6 0] < [0 5]` (F3) and
`[3 4] < [4 1]` (F4): the cap `2` is strictly farther than `5` beneath `134`.  The inequality
`r [0 5] > [6 0]` is affine in `τ`; it holds at `τ = 0` and, if `r` decreases, at the value of
`τ` where `2` would reach the plane `135` (which it does not: `2` is beneath `135`). -/
theorem type21_A1 {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'} (hd : IsCap21 F d)
    {G : GaleData a a' b b' c c'} (hN : CrossNorm G) {α β τ : ℝ} (hτ : 0 < τ)
    (hco : d = a + α • (b' - a) + β • (c' - a)) (hα : α = τ * galeD G.l G.m b' c)
    (ht : α + β - 1 = τ * galeD G.l G.m c a)
    (hF3 : galeD G.l G.m c' a < galeD G.l G.m a b')
    (hF4 : galeD G.l G.m a' b < galeD G.l G.m b c) :
    F.a'bc.f d < F.a'bc.f b' := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  obtain ⟨s34, s05, s04, s56, s51, s46, s41, s63, s60, s13, s10⟩ := hN.signs F
  obtain ⟨hr, hfd, e1⟩ := type21_r_pos hd hN hco hα ht
  obtain ⟨g1, -, g3⟩ := type21_f135 F G hco
  have φn := F.a'bc.neg c' (by simp) (Ne.symm ha'c') (Ne.symm hbc') (Ne.symm hcc')
  have ψn := F.a'b'c.neg c' (by simp) (Ne.symm ha'c') (Ne.symm hb'c') (Ne.symm hcc')
  have s1 := type21_id_s1 G.hl G.hm
  have D135 := type21_id_D135 G.hl G.hm
  have A1e := type21_id_A1end G.hl G.hm
  have e61 : galeD G.l G.m c c' = -galeD G.l G.m c' c := galeD_anti G.l G.m c' c
  -- `r = 1 + τ ([4 1] − [1 3])`
  have hrr : β + τ * galeD G.l G.m c c' =
      1 + τ * (galeD G.l G.m b c - galeD G.l G.m c a') := by
    rw [e61]; linear_combination ht - hα + τ * s1
  -- `2` beneath `135`: `[0 4] − τ E' > 0`
  have hC : 0 < galeD G.l G.m a b - τ * (galeD G.l G.m c a' * galeD G.l G.m a b -
      galeD G.l G.m b c * galeD G.l G.m a b + galeD G.l G.m b c * galeD G.l G.m c' a) := by
    have h135 := hd.a'b'c
    have k : galeD G.l G.m a b * F.a'b'c.f d =
        F.a'b'c.f c' * (galeD G.l G.m a b - τ * (galeD G.l G.m c a' * galeD G.l G.m a b -
          galeD G.l G.m b c * galeD G.l G.m a b + galeD G.l G.m b c * galeD G.l G.m c' a)) := by
      have h1 : 1 - α - β = -(τ * galeD G.l G.m c a) := by linarith
      rw [g3, h1]
      linear_combination (-τ * galeD G.l G.m c a) * g1 + F.a'b'c.f c' * τ * D135 +
        F.a'b'c.f c' * galeD G.l G.m a b * (ht - hα)
    have : galeD G.l G.m a b * F.a'b'c.f d < 0 := mul_neg_of_pos_of_neg s04 h135
    rw [k] at this
    exact pos_of_mul_neg_right this ψn.le
  -- `r [0 5] > [6 0]`
  have hA : galeD G.l G.m c' a < (β + τ * galeD G.l G.m c c') * galeD G.l G.m a b' := by
    rw [hrr]
    by_cases h : galeD G.l G.m c a' ≤ galeD G.l G.m b c
    · nlinarith [mul_nonneg hτ.le (sub_nonneg.mpr h)]
    · push Not at h
      have hE : 0 < galeD G.l G.m c a' * galeD G.l G.m a b - galeD G.l G.m b c * galeD G.l G.m a b +
          galeD G.l G.m b c * galeD G.l G.m c' a := by
        have : galeD G.l G.m c a' * galeD G.l G.m a b - galeD G.l G.m b c * galeD G.l G.m a b +
            galeD G.l G.m b c * galeD G.l G.m c' a = galeD G.l G.m a b *
              (galeD G.l G.m c a' - galeD G.l G.m b c) + galeD G.l G.m b c * galeD G.l G.m c' a := by
          ring
        rw [this]
        exact add_pos (mul_pos s04 (by linarith)) (mul_pos s41 s60)
      have key : (galeD G.l G.m c a' * galeD G.l G.m a b - galeD G.l G.m b c * galeD G.l G.m a b +
          galeD G.l G.m b c * galeD G.l G.m c' a) *
          ((1 + τ * (galeD G.l G.m b c - galeD G.l G.m c a')) * galeD G.l G.m a b' -
            galeD G.l G.m c' a) =
          galeD G.l G.m c' a * galeD G.l G.m c a * (galeD G.l G.m b c - galeD G.l G.m a' b) +
          (galeD G.l G.m c a' - galeD G.l G.m b c) * galeD G.l G.m a b' *
            (galeD G.l G.m a b - τ * (galeD G.l G.m c a' * galeD G.l G.m a b -
              galeD G.l G.m b c * galeD G.l G.m a b + galeD G.l G.m b c * galeD G.l G.m c' a)) := by
        linear_combination A1e
      have hpos : 0 < galeD G.l G.m c' a * galeD G.l G.m c a *
          (galeD G.l G.m b c - galeD G.l G.m a' b) +
          (galeD G.l G.m c a' - galeD G.l G.m b c) * galeD G.l G.m a b' *
            (galeD G.l G.m a b - τ * (galeD G.l G.m c a' * galeD G.l G.m a b -
              galeD G.l G.m b c * galeD G.l G.m a b + galeD G.l G.m b c * galeD G.l G.m c' a)) :=
        add_pos (mul_pos (mul_pos s60 s10) (by linarith))
          (mul_pos (mul_pos (by linarith) s05) hC)
      rw [← key] at hpos
      have := pos_of_mul_pos_right hpos hE.le
      linarith
  -- `f(2) = r f(6) < [6 0] f(6) / [0 5] = f(5)`
  rw [hfd]
  have : galeD G.l G.m a b' * ((β + τ * galeD G.l G.m c c') * F.a'bc.f c') <
      galeD G.l G.m a b' * F.a'bc.f b' := by
    rw [e1]; nlinarith
  exact lt_of_mul_lt_mul_left this s05.le

/-- **`Q` at `25` of `K − 6`**: if `1` is hidden along `2 → 5` in `K − 6` (`δ_014(2) > δ_014(5)`
and A1, `δ_134(2) > δ_134(5)`), then `2 → 5` is E-good (`{1 2} {1 5} = r [1 6] [1 5] > 0`, the
dependency `{1 ·}`), and `K` is Rupert (Lemma 3 of §9 for `K − 6`). -/
theorem isRupert_type21_Q25 {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap21 F d) (G : GaleData a a' b b' c c') (hN : CrossNorm G)
    (hA1 : F.a'bc.f d < F.a'bc.f b') (h3 : F.abc.f d < F.abc.f b')
    (hgen : GenPosTie (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hnd : NoHDNEdges (insert d ({a, a', b, b', c, c'} : Finset ℝ³))) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨s34, s05, s04, s56, s51, s46, s41, s63, s60, s13, s10⟩ := hN.signs F
  obtain ⟨α, β, τ, hα0, hβ, hαβ, hτ, hco, hα, ht⟩ := hd.tau hN
  obtain ⟨hr, -, -⟩ := type21_r_pos hd hN hco hα ht
  obtain ⟨L, hL, Ld, Lc, Lb', Lb, La', La⟩ := type21_depO2_c hd G hco hα ht
  have anti := galeD_anti G.l G.m
  have hgood : ¬ max ⟪b', b' - d⟫ ⟪b, b' - d⟫ ≤ min ⟪a', b' - d⟫ ⟪a, b' - d⟫ := by
    refine not_bad_of_dep hL (hd.ne.2.2.2.1) Lc ?_ ?_ ?_ ?_ ?_
    · rw [Ld, anti c' c]; linarith [hN.h61]
    · rw [Ld, Lb', anti b' c]; nlinarith [mul_pos hr s51, anti c' c, hN.h61]
    · rw [Lb, anti b c]; nlinarith
    · rw [La']; positivity
    · rw [La]; positivity
  rw [← type21_set_O2] at hgen hnd ⊢
  exact isRupert_type21_60 hd.O2 hd.sigma2 hA1 h3 hgood hgen hnd

/-- **Step 3 of Theorem 16.13** (`Q` at `25` of `K − 6`): in the normalized class with
(F3), (F4), if `δ_014(2) > δ_014(5)` then `1` is hidden along `2 → 5` of `K − 6` (the face `134`
by Lemma 16.11), so `Q` at `25` applies. -/
theorem isRupert_type21_step3 {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap21 F d) (G : GaleData a a' b b' c c') (hN : CrossNorm G)
    (hF3 : galeD G.l G.m c' a < galeD G.l G.m a b')
    (hF4 : galeD G.l G.m a' b < galeD G.l G.m b c)
    (h3 : F.abc.f d < F.abc.f b')
    (hgen : GenPosTie (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hnd : NoHDNEdges (insert d ({a, a', b, b', c, c'} : Finset ℝ³))) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨α, β, τ, hα0, hβ, hαβ, hτ, hco, hα, ht⟩ := hd.tau hN
  exact isRupert_type21_Q25 F hd G hN (type21_A1 hd hN hτ hco hα ht hF3 hF4) h3 hgen hnd

/-! ### Step 5 of Theorem 16.13: `Q` at `23` of `K − 6` -/

/-- **`Q` at `23` of `K − 6`** (the conclusion of Lemma 16.12), in the normalized class: if
H1 (`r' [3 4] < [4 6]`), H2 (`{3 5} = α [6 3] + β [3 5] < [5 6]`) and E (`τ [1 3] [6 0] < r [3 0]`)
hold, then `3 → 2` is a quad edge of `K − 6` (`0` hidden: the faces `015`, `014`), E-good
(`{0 3} {0 2} > 0`, the dependency `{0 ·}`; the sign of `{0 4}` by Lemma 13.4 for `K − 6`), and
`K` is Rupert (Lemma 3 of §9 for `K − 6` at `3 → 2`). -/
theorem isRupert_type21_step5 {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap21 F d) (G : GaleData a a' b b' c c') (hN : CrossNorm G) {α β τ : ℝ}
    (hco : d = a + α • (b' - a) + β • (c' - a)) (hα : α = τ * galeD G.l G.m b' c)
    (ht : α + β - 1 = τ * galeD G.l G.m c a)
    (hH1 : β * galeD G.l G.m a' b < galeD G.l G.m b c')
    (hH2 : α * galeD G.l G.m c' a' + β * galeD G.l G.m a' b' < galeD G.l G.m b' c')
    (hE : τ * galeD G.l G.m c a' * galeD G.l G.m c' a <
      (β + τ * galeD G.l G.m c c') * galeD G.l G.m a' a)
    (hgen : GenPosTie (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hnd : NoHDNEdges (insert d ({a, a', b, b', c, c'} : Finset ℝ³))) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd'
  obtain ⟨s34, s05, s04, s56, s51, s46, s41, s63, s60, s13, s10⟩ := hN.signs F
  obtain ⟨hr, -, -⟩ := type21_r_pos hd hN hco hα ht
  have anti := galeD_anti G.l G.m
  -- the face `015`: H1
  have hq₁ : F.ab'c.f a' < F.ab'c.f d := by
    obtain ⟨e1, e2⟩ := type21_f015 F G hco
    have n6 := F.ab'c.neg c' (by simp) (Ne.symm hac') (Ne.symm hb'c') (Ne.symm hcc')
    have : galeD G.l G.m a' b * F.ab'c.f a' < galeD G.l G.m a' b * F.ab'c.f d := by
      rw [e1, e2]; nlinarith
    exact lt_of_mul_lt_mul_left this s34.le
  -- the face `014`: H2
  have hq₂ : F.abc.f a' < F.abc.f d := by
    obtain ⟨e1, e2, e3⟩ := type21_f014 F G hco
    have n5 := F.abc.neg b' (by simp) (Ne.symm hab') (Ne.symm hbb') hb'c
    have : galeD G.l G.m c' a' * F.abc.f a' < galeD G.l G.m c' a' * F.abc.f d := by
      have k : galeD G.l G.m c' a' * F.abc.f d - galeD G.l G.m c' a' * F.abc.f a' =
          F.abc.f b' * (α * galeD G.l G.m c' a' + β * galeD G.l G.m a' b' - galeD G.l G.m b' c') := by
        rw [e3]; linear_combination -e1 - β * e2
      nlinarith
    exact lt_of_mul_lt_mul_left this s63.le
  -- not bad: the dependency `{0 ·}`
  obtain ⟨L, hL, La, La', Lb', Lb, Lc, Ld⟩ := type21_depO2_a hd G hco hα ht
  have hLb' : 0 < L b' := by rw [Lb']; positivity
  have hLb : 0 < L b := by
    obtain ⟨p1, -, -⟩ := pole_signs' hd.O2.perm₁₂.swap₁ hL La hLb'.ne'
    exact pos_of_mul_pos_right p1 hLb'.le
  have hLa' : L a' < 0 := by rw [La', anti a' a]; nlinarith
  have hgood : ¬ max ⟪d, d - a'⟫ ⟪c, d - a'⟫ ≤ min ⟪b', d - a'⟫ ⟪b, d - a'⟫ := by
    refine not_bad_of_dep hL.swap₁.perm₂₃.swap₂ (Ne.symm hd.ne.2.1) La hLa' ?_ ?_ hLb'.le hLb.le
    · rw [Ld, anti c' a]; linarith
    · rw [Lc, anti c a]; nlinarith
  rw [← type21_set_O2] at hgen hnd ⊢
  exact isRupert_type21_46 hd.O2 hd.sigma2 hq₁ hq₂ hgood hgen hnd

/-! ### Lemma 16.12: the sliver `Σ` is covered by `Q` at `23` -/

/-- **Lemma 16.12 (referee), in `τ`.**  In the normalized class with (F1) `[3 4] < [1 3]`,
(F5) `[5 1] < [1 0]`, (F6) `[3 4] < [4 6]`, let `τ > 0` satisfy `S ∪ H`:
`{3 5} = α [6 3] + β [3 5] ≤ [6 3]` (`δ_014(2) ≤ δ_014(5)`).  Then
* E holds: `τ [1 3] [6 0] < r [3 0]`;
* if `[6 3] < [5 6]`, H1 (`β [3 4] < [4 6]`) and H2 (`{3 5} < [5 6]`) hold;
* if `[5 6] < [6 3]`, then (B) `[6 0] < [4 6]`, and unless H1 and H2 both hold,
  (A) `r [1 0] < β [4 1]`: together, `0 → 4` is a quad edge of `K − 6` ((iii)).
The identities are `type21_id_kE`, `_kFS`, `_kF2`, `_kA2`, `_kAS` (`k = [3 5][1 0] +
[5 1]([6 3] − [3 5]) > 0`, `τ_S = ([6 3] − [3 5]) / k`, `τ_2 = ([5 6] − [3 5]) / k`). -/
theorem type21_lemma1612 {a a' b b' c c' : ℝ³} {F : OctFacets a a' b b' c c'}
    {G : GaleData a a' b b' c c'} (hN : CapNorm G) {α β τ : ℝ} (hτ : 0 < τ)
    (hα : α = τ * galeD G.l G.m b' c) (ht : α + β - 1 = τ * galeD G.l G.m c a)
    (hF1 : galeD G.l G.m a' b < galeD G.l G.m c a')
    (hF5 : galeD G.l G.m b' c < galeD G.l G.m c a)
    (hF6 : galeD G.l G.m a' b < galeD G.l G.m b c')
    (hS : α * galeD G.l G.m c' a' + β * galeD G.l G.m a' b' ≤ galeD G.l G.m c' a') :
    τ * galeD G.l G.m c a' * galeD G.l G.m c' a <
      (β + τ * galeD G.l G.m c c') * galeD G.l G.m a' a ∧
    (galeD G.l G.m c' a' < galeD G.l G.m b' c' →
      β * galeD G.l G.m a' b < galeD G.l G.m b c' ∧
      α * galeD G.l G.m c' a' + β * galeD G.l G.m a' b' < galeD G.l G.m b' c') ∧
    (galeD G.l G.m b' c' < galeD G.l G.m c' a' →
      galeD G.l G.m c' a < galeD G.l G.m b c' ∧
      (¬ (β * galeD G.l G.m a' b < galeD G.l G.m b c' ∧
        α * galeD G.l G.m c' a' + β * galeD G.l G.m a' b' < galeD G.l G.m b' c') →
        (β + τ * galeD G.l G.m c c') * galeD G.l G.m c a < β * galeD G.l G.m b c)) := by
  obtain ⟨s34, s05, s04, s56, s51, s46, s41, s63, s60, s13, s10⟩ := hN.signs F
  have h30 := hN.h30; have h54 := hN.h54; have h61 := hN.h61; have h35 := hN.h35
  have kE := type21_id_kE G.hl G.hm
  have kFS := type21_id_kFS G.hl G.hm
  have kF2 := type21_id_kF2 G.hl G.hm
  have kA2 := type21_id_kA2 G.hl G.hm
  have kAS := type21_id_kAS G.hl G.hm
  have iB := type21_id_B G.hl G.hm
  have s1 := type21_id_s1 G.hl G.hm
  have e61 : galeD G.l G.m c c' = -galeD G.l G.m c' c := galeD_anti G.l G.m c' c
  -- the brackets as variables
  set x30 := galeD G.l G.m a' a; set x54 := galeD G.l G.m b' b; set x61 := galeD G.l G.m c' c
  set x35 := galeD G.l G.m a' b'; set x34 := galeD G.l G.m a' b; set x05 := galeD G.l G.m a b'
  set x04 := galeD G.l G.m a b; set x56 := galeD G.l G.m b' c'; set x51 := galeD G.l G.m b' c
  set x46 := galeD G.l G.m b c'; set x41 := galeD G.l G.m b c; set x63 := galeD G.l G.m c' a'
  set x60 := galeD G.l G.m c' a; set x13 := galeD G.l G.m c a'; set x10 := galeD G.l G.m c a
  have hβ : β = 1 + τ * (x10 - x51) := by linarith
  have hr : β + τ * galeD G.l G.m c c' = 1 + τ * (x41 - x13) := by
    rw [e61]; linear_combination ht - hα + τ * s1
  rw [hr]
  set k := x35 * x10 + x51 * (x63 - x35) with hk_def
  have hk : 0 < k := by
    have : k = x35 * (x10 - x51) + x51 * x63 := by rw [hk_def]; ring
    rw [this]; nlinarith
  have h35k : α * x63 + β * x35 = x35 + τ * k := by rw [hα, hβ, hk_def]; ring
  rw [h35k] at hS ⊢
  have hmS : 0 < x63 - x35 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · -- E
    have key : (x63 - x35) * ((1 + τ * (x41 - x13)) * x30 - τ * x13 * x60) =
        (x63 - x35 - τ * k) * x30 + τ * (x10 * x63 * (x13 - x34)) := by
      rw [← kE, hk_def]; ring
    have : 0 < (x63 - x35) * ((1 + τ * (x41 - x13)) * x30 - τ * x13 * x60) := by
      rw [key]
      exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) h30.le)
        (mul_pos hτ (mul_pos (mul_pos s10 s63) (sub_pos.mpr hF1)))
    have := pos_of_mul_pos_right this hmS.le
    linarith only [this]
  · -- `[6 3] < [5 6]`: H1, H2
    intro h56
    refine ⟨?_, by linarith⟩
    have key : (x63 - x35) * (x46 - β * x34) =
        (x63 - x35 - τ * k) * (x46 - x34) + τ * (x10 * x63 * x54 + x10 * x34 * (x56 - x63) +
          x46 * x51 * (x63 - x35)) := by
      rw [← kFS, hβ, hk_def]; ring
    have h1 : 0 < x10 * x63 * x54 + x10 * x34 * (x56 - x63) + x46 * x51 * (x63 - x35) := by
      have := mul_pos (mul_pos s10 s63) h54
      have := mul_pos (mul_pos s10 s34) (sub_pos.mpr h56)
      have := mul_pos (mul_pos s46 s51) hmS
      linarith
    have : 0 < (x63 - x35) * (x46 - β * x34) := by
      rw [key]
      exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) (by linarith)) (mul_pos hτ h1)
    have := pos_of_mul_pos_right this hmS.le
    linarith only [this]
  · -- `[5 6] < [6 3]`: (B), and (A) unless H1, H2
    intro h56
    refine ⟨by linarith, fun hn => ?_⟩
    -- `τ k ≥ τ_2 k = [5 6] − [3 5]`
    have hτ2 : x56 - x35 ≤ τ * k := by
      by_contra hc
      push Not at hc
      apply hn
      refine ⟨?_, by linarith⟩
      have key : k * (x46 - β * x34) = (k * (x46 - x34) + (x56 - x35) * (-((x10 - x51) * x34))) +
          (x56 - x35 - τ * k) * ((x10 - x51) * x34) := by
        rw [hβ]; ring
      have h2 : 0 < k * (x46 - x34) + (x56 - x35) * (-((x10 - x51) * x34)) := by
        rw [kF2]
        have := mul_pos h54 (sub_pos.mpr hF5)
        have := mul_pos s51 (sub_pos.mpr hF6)
        positivity
      have h3 : 0 ≤ (x56 - x35 - τ * k) * ((x10 - x51) * x34) :=
        mul_nonneg (by linarith) (mul_nonneg (by linarith) s34.le)
      have : 0 < k * (x46 - β * x34) := by rw [key]; exact add_pos_of_pos_of_nonneg h2 h3
      have := pos_of_mul_pos_right this hk.le
      linarith only [this]
    have key : (x63 - x56) * k * (β * x41 - (1 + τ * (x41 - x13)) * x10) =
        (x63 - x35 - τ * k) * (k * (x41 - x10) + (x56 - x35) * ((x10 - x51) * x41 -
          (x41 - x13) * x10)) + (τ * k - (x56 - x35)) * (k * (x41 - x10) +
          (x63 - x35) * ((x10 - x51) * x41 - (x41 - x13) * x10)) := by
      rw [hβ]; ring
    rw [kA2, kAS] at key
    have hp1 : 0 < x41 * x51 * (x63 - x56) := mul_pos (mul_pos s41 s51) (by linarith)
    have hp2 : 0 < x10 * x13 * (x63 - x56) := mul_pos (mul_pos s10 s13) (by linarith)
    have : 0 < (x63 - x56) * k * (β * x41 - (1 + τ * (x41 - x13)) * x10) := by
      rw [key]
      rcases eq_or_lt_of_le hS with heq | hlt
      · have h0 : x63 - x35 - τ * k = 0 := by linarith only [heq]
        have : 0 < τ * k - (x56 - x35) := by linarith only [heq, h56]
        rw [h0, zero_mul, zero_add]
        exact mul_pos this hp2
      · exact add_pos_of_pos_of_nonneg (mul_pos (by linarith only [hlt]) hp1)
          (mul_nonneg (by linarith only [hτ2]) hp2.le)
    have := pos_of_mul_pos_right this (mul_pos (by linarith only [h56]) hk).le
    linarith only [this]

end Minimality

end
