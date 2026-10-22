module

public import Minimality.Type16Pairs

@[expose] public section

/-!
# Type 16: the cover (`FEWER-FACES-PROOFS.md` §19.6)

**Theorem 19.6** in the normal form, certificate form (`NF16.cert_nf`): off `R1 ∪ R2` the pair
at `06` (Proposition 14.3); in `R1` a step of Theorem 19.2, or on `Ω` Lemma 19.3 (`d > 1`), Lemma
19.4 (`d < 1`, `b < 1` or `H_A < 0`) or Lemma 19.5 (`Ω_open`); in `R2` the same after
`σ = (06)(12)`.  Each ends in a certificate `Cert16` (a rim certificate at a named view, §18.2;
no horizontal double normal assumed).  The special positions are explicit: `NF16.Gen`
(equalities in the sign conditions of the route and the far-end ties), `NF16.Views` (at most one
tie at `v_A`) and at most one tie at each edge view (`TieSeg`).  Depth ties are allowed
everywhere else: the Lemma E cover by Lemma E with ties; on `Ω` the quadrilateral rims are
robustly unimodal unless weakly separated, the pentagons by their open criteria
(`quint_B_robust`, `quint_Tc_robust`, `quint_A_robust`), and the pair and triple arguments
exclude the weak failures (`not_weakSep_of_meet`, `eq_of_weakSep_meet`, `weakSep_sign`; a weak
failure that is no sign at all puts three points at one depth, against `TieSeg`).

From a certificate to Rupertness (`Cert16.isRupert`, Theorems 18.1 and 18.3 at the shape
itself): convex position (`Type16.noSeg`), and no horizontal double normal at the named views
(`Type16.noHDN_views`, from the segment views and the lines of the six facet pairs).
`NF16.isRupert_type16` and `isRupert_type16_facets` keep the explicit special positions of the
entry point `not_type16_of_isNopert`; `Type16Limit.lean` removes them (Theorem 19.8).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Minimality

open scoped RealInnerProductSpace
open Finset

/-! ### From a certificate to Rupertness -/

theorem NoHDNAt.smul_view {V : Finset ℝ³} {u : ℝ³} (h : NoHDNAt V u) {c : ℝ} (hc : c ≠ 0) :
    NoHDNAt V (c • u) := by
  intro R hR r hr hRu
  refine h R hR (r / c) (div_ne_zero hr hc) ?_
  have e : c • R.toEuclideanLin u = r • ez := by rw [← map_smul]; exact hRu
  calc R.toEuclideanLin u = c⁻¹ • (c • R.toEuclideanLin u) := by
        rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = (r / c) • ez := by rw [e, smul_smul, div_eq_inv_mul]

/-- No horizontal double normal at the view `w − v` without `w` and without `v` is no horizontal
double normal at all: a strictly convex silhouette never contains both ends of the view. -/
theorem noHDNAt_of_erase {V : Finset ℝ³} {v w : ℝ³} (hvw : v ≠ w)
    (h1 : NoHDNAt (V.erase w) (w - v)) (h2 : NoHDNAt (V.erase v) (w - v)) :
    NoHDNAt V (w - v) := by
  intro R hR r hr hRu k y hyV hp
  by_cases hw : ∃ i, y i = w
  · obtain ⟨i, hi⟩ := hw
    refine h2 R hR r hr hRu k y (fun j => mem_erase.mpr ⟨fun hj => ?_, hyV j⟩) hp
    have hP : proj_xy (R.toEuclideanLin (y j)) = proj_xy (R.toEuclideanLin (y i)) := by
      have e : w = v + (w - v) := by abel
      rw [hj, hi, e, map_add, hRu, proj_xy_add', proj_xy_smul']
      have : proj_xy ez = 0 := by ext j; fin_cases j <;> simp [proj_xy, ez]
      rw [this, smul_zero, add_zero]
    have := hp.injective hP
    rw [this, hi] at hj
    exact hvw hj.symm
  · push Not at hw
    exact h1 R hR r hr hRu k y (fun j => mem_erase.mpr ⟨hw j, hyV j⟩) hp

/-- The line of two planes is orthogonal to the normal of the first plane: `planeLine` is also
`[C D A] B − [C D B] A`. -/
theorem planeLine_alt (p₀ p₁ p₂ q₀ q₁ q₂ : ℝ³) :
    planeLine p₀ p₁ p₂ q₀ q₁ q₂ = det3 (q₁ - q₀) (q₂ - q₀) (p₁ - p₀) • (p₂ - p₀) -
      det3 (q₁ - q₀) (q₂ - q₀) (p₂ - p₀) • (p₁ - p₀) := by
  ext i; fin_cases i <;>
    simp [planeLine, det3_expand] <;> ring

theorem inner_planeLine_right {p₀ p₁ p₂ q₀ q₁ q₂ n : ℝ³} (h1 : ⟪n, q₁ - q₀⟫ = 0)
    (h2 : ⟪n, q₂ - q₀⟫ = 0) : ⟪n, planeLine p₀ p₁ p₂ q₀ q₁ q₂⟫ = 0 := by
  simp only [planeLine, inner_sub_right, real_inner_smul_right, h1, h2, mul_zero, sub_zero]

theorem inner_planeLine_left {p₀ p₁ p₂ q₀ q₁ q₂ n : ℝ³} (h1 : ⟪n, p₁ - p₀⟫ = 0)
    (h2 : ⟪n, p₂ - p₀⟫ = 0) : ⟪n, planeLine p₀ p₁ p₂ q₀ q₁ q₂⟫ = 0 := by
  rw [planeLine_alt]
  simp only [inner_sub_right, real_inner_smul_right, h1, h2, mul_zero, sub_zero]

theorem Face16.inner_sub {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (F : Face16 x S) {a b : Fin 7}
    (ha : a ∈ S) (hb : b ∈ S) : ⟪F.N, x a - x b⟫ = 0 := by
  rw [← F.hN, F.zero a ha, F.zero b hb, sub_self]

/-- A point on a facet is not strictly inside a segment of two points not both on it. -/
theorem Face16.ne_seg {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (F : Face16 x S) {m i j : Fin 7}
    (hm : m ∈ S) (hij : i ∉ S ∨ j ∉ S) (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    x m ≠ x i + s • (x j - x i) := by
  intro e
  have h1 := F.hN (x i + s • (x j - x i)) (x i)
  have h2 := F.hN (x j) (x i)
  rw [add_sub_cancel_left, real_inner_smul_right, ← h2, ← e, F.zero m hm] at h1
  have hi : F.f (x i) ≤ 0 := by
    by_cases h : i ∈ S
    · exact (F.zero i h).le
    · exact (F.neg i h).le
  have hj : F.f (x j) ≤ 0 := by
    by_cases h : j ∈ S
    · exact (F.zero j h).le
    · exact (F.neg j h).le
  rcases hij with h | h
  · have := F.neg i h; nlinarith
  · have := F.neg j h; nlinarith

/-- **Type 16 is in convex position**: no point lies strictly inside a segment of two others
(each vertex is cut off by its facets). -/
theorem Type16.noSeg {x : Fin 7 → ℝ³} (T : Type16 x) :
    ∀ i j m : Fin 7, x m ≠ x i → x m ≠ x j → ∀ s : ℝ, 0 < s → s < 1 →
      x m ≠ x i + s • (x j - x i) := by
  intro i j m hmi hmj s hs0 hs1
  have hmi' : m ≠ i := fun h => hmi (by rw [h])
  have hmj' : m ≠ j := fun h => hmj (by rw [h])
  fin_cases m <;> fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hmi'
    | exact absurd rfl hmj'
    | exact T.q0235.ne_seg (by decide) (by decide) s hs0 hs1
    | exact T.q1356.ne_seg (by decide) (by decide) s hs0 hs1
    | exact T.t024.ne_seg (by decide) (by decide) s hs0 hs1
    | exact T.t036.ne_seg (by decide) (by decide) s hs0 hs1
    | exact T.t046.ne_seg (by decide) (by decide) s hs0 hs1
    | exact T.t145.ne_seg (by decide) (by decide) s hs0 hs1
    | exact T.t146.ne_seg (by decide) (by decide) s hs0 hs1
    | exact T.t245.ne_seg (by decide) (by decide) s hs0 hs1

/-- **A certificate gives Rupertness** (Theorem 18.1 with 18.3, at the shape itself): in convex
position, not in a plane, without horizontal double normals at the named views. -/
theorem Cert16.isRupert {x : Fin 7 → ℝ³} (hc : Cert16 x)
    (hseg : ∀ i j m : Fin 7, x m ≠ x i → x m ≠ x j → ∀ s : ℝ, 0 < s → s < 1 →
      x m ≠ x i + s • (x j - x i))
    (hsp : ∃ i j l m : Fin 7, det3 (x j - x i) (x l - x i) (x m - x i) ≠ 0)
    (hnd : ∀ v, view16 x v ≠ 0 → NoHDNAt (univ.image x) (view16 x v)) :
    IsRupert (univ.image x) := by
  obtain ⟨u, ⟨v, c, hc0, rfl⟩, k, hk, y, hy⟩ := hc.toN
  obtain ⟨lab, -, hat⟩ := hy.toAt
  have hk0 : NeZero k := ⟨by rcases hk with rfl | rfl | rfl <;> norm_num⟩
  have hu := hat.ne_zero
  have hv : view16 x v ≠ 0 := fun h => hu (by rw [h, smul_zero])
  exact isRupert_of_tendsto_rimCert x hseg hsp lab hu ((hnd v hv).smul_view hc0)
    (l := (⊤ : Filter Unit)) (fun _ => x) (fun _ => c • view16 x v)
    (fun _ => tendsto_const_nhds) tendsto_const_nhds
    (Filter.frequently_top.mpr ⟨(), hat, fun _ _ h => h⟩)

namespace NF16

variable {x : Fin 7 → ℝ³}

/-- The special position at the vertex view of the pentagon `A` of Lemma 19.5 (`v_A ≠ 0`): at
most one tie.  Depth ties at the other views are allowed (the quadrilateral rims are robustly
unimodal unless weakly separated, and the pair arguments exclude both weak separations), and the
horizontal double normals are checked where the certificate is used (`Cert16`). -/
structure Views (N : NF16 x) : Prop where
  vA : N.vA ≠ 0 → OneTieAt (univ.image x) N.vA

theorem nodup5_sub4 {z₀ z₁ z₂ z₃ z₄ : ℝ} (h : [z₀, z₁, z₂, z₃, z₄].Nodup) :
    [z₀, z₁, z₂, z₄].Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at h ⊢
  tauto

/-- **The residual `Ω`** (Lemmas 19.3, 19.4, 19.5; §19.6). -/
theorem cert_omega (N : NF16 x) (O : Omega N) (G : Gen N) (W : Views N)
    (hgt : TieSeg (univ.image x)) : Cert16 x := by
  have O' := O
  obtain ⟨hR1, hR2, hD, hqg, hg1, hqb, hc, nD2, nD3, nD4, nD6, nD7⟩ := O'
  have hf15 : 0 < N.d * N.q - (N.g - 1) * (N.p + N.r - 1) := by
    rcases lt_or_gt_of_ne G.f15 with h | h <;> [linarith; linarith [nD6]]
  rcases lt_or_gt_of_ne G.d1 with hd1 | hd1
  · -- `d < 1`
    have hd1' : 0 < 1 - N.d := by linarith
    have hf03 : 0 < -(N.q * (1 - N.d) + N.g * (N.r - 1)) := by
      rcases lt_or_gt_of_ne G.b1 with hb | hb
      · have h25 := nD3 (by linarith)
        refine pos_of_mul_pos_r N.ha ?_
        nlinarith [mul_pos (mul_pos (show 0 < 1 - N.b by linarith) hd1') N.hp]
      · have := nD4 (by linarith)
        rcases lt_or_gt_of_ne G.f03 with h | h <;> [linarith; linarith]
    have hvA0 : N.vA ≠ 0 := by
      simp only [vA]; exact nfV_ne_zero N.hD (Or.inl (ne_of_gt (mul_pos N.hg N.hp)))
    have hvA := W.vA hvA0
    have F1s : 0 < -((N.b - 1) * N.g * N.p * N.r + (N.q * (1 - N.d) + N.g * (N.r - 1)) *
        (N.a * (N.q - 1) - (N.b - 1) * N.p)) → Cert16 x := fun h =>
      cert_F1s N O hd1' hf03 h hgt
    rcases lt_or_gt_of_ne G.b1 with hb | hb
    · refine F1s ?_
      have hq1 : 0 < N.q - 1 := by linarith
      nlinarith [mul_pos (mul_pos (mul_pos (show 0 < 1 - N.b by linarith) N.hg) N.hp) N.hr,
        mul_pos hf03 (show 0 < N.a * (N.q - 1) - (N.b - 1) * N.p by
          nlinarith [mul_pos N.ha hq1, mul_pos (show 0 < 1 - N.b by linarith) N.hp])]
    rcases lt_or_gt_of_ne G.HA with hA | hA
    · exact F1s (by linarith)
    · have hpr : 0 < N.p + N.r - 1 := by
        rcases lt_or_gt_of_ne G.a1 with ha | ha
        · have := nD7 (by linarith) hd1'
          rcases lt_or_gt_of_ne G.pr with h | h <;> [linarith; linarith]
        · nlinarith [N.t0246, mul_pos (sub_pos.mpr ha) N.hq, N.hb]
      exact cert_T6 N O hd1' (by linarith) G.a1 hf03 hA hf15 hpr G.T5 hgt hvA
  · -- `d > 1`
    exact cert_F3 N O (by linarith) G.a1 hf15 hgt

/-- **Theorem 19.6 in `R1`.** -/
theorem cert_R1 (N : NF16 x) (hR1 : 0 < N.R1) (G : Gen N) (W : Views N)
    (hg : TieSeg (univ.image x)) : Cert16 x :=
  cert_R1_or_omega N hR1 G hg fun O => cert_omega N O G W hg

/-- **Theorem 19.6 (the cover), normal form, certificate form**: off the special positions,
every type-16 normal form has a certificate `Cert16` (a rim certificate at a named view): off
`R1 ∪ R2` the pair at `06`, in `R1` by `cert_R1`, in `R2` by `cert_R1` for `x ∘ σ`.  No
horizontal double normal is assumed. -/
theorem cert_nf (N : NF16 x) (G : Gen N) (Gσ : Gen N.sigma) (W : Views N)
    (Wσ : Views N.sigma) (h1 : N.R1 ≠ 0) (h2 : N.R2 ≠ 0) (hg : TieSeg (univ.image x)) :
    Cert16 x := by
  rcases lt_or_gt_of_ne h1 with hR1 | hR1
  · rcases lt_or_gt_of_ne h2 with hR2 | hR2
    · exact cert_E06 N hR1 hR2 hg
    · exact (cert_R1 N.sigma (by rw [sigma_R1]; exact hR2) Gσ Wσ
        (by rw [image_sigma16]; exact hg)).sigma
  · exact cert_R1 N hR1 G W hg


/-! ### The special positions from the points -/

/-- An affine function constant on a plane through `P, Q, R` (with `S` off it) has its linear part
zero on every direction of the plane. -/
theorem inner_zero_of_plane {f : ℝ³ → ℝ} {Nf : ℝ³} (hf : ∀ y z, f y - f z = ⟪Nf, y - z⟫)
    {P Q R S v : ℝ³} (hQ : f Q = f P) (hR : f R = f P) (hS : det3 (Q - P) (R - P) (S - P) ≠ 0)
    (hdet : det3 (Q - P) (R - P) v = 0) : ⟪Nf, v⟫ = 0 := by
  have hc := cramer (Q - P) (R - P) (S - P) v
  have e := congrArg (fun w => ⟪Nf, w⟫) hc
  simp only [inner_add_right, real_inner_smul_right] at e
  have a1 : ⟪Nf, Q - P⟫ = 0 := by rw [← hf, hQ, sub_self]
  have a2 : ⟪Nf, R - P⟫ = 0 := by rw [← hf, hR, sub_self]
  rw [a1, a2, hdet] at e
  simp only [mul_zero, zero_mul, add_zero] at e
  exact (mul_eq_zero.mp e).resolve_left hS

/-- **The special positions of a vertex view** along the line of two face planes (normals
`NP`, `NQ`): at every direction `u ≠ 0` of the line, at most one tie and no horizontal double
normal. -/
def ViewGen16 (V : Finset ℝ³) (NP NQ : ℝ³) : Prop :=
  ∀ u : ℝ³, u ≠ 0 → ⟪NP, u⟫ = 0 → ⟪NQ, u⟫ = 0 → OneTieAt V u ∧ NoHDNAt V u

theorem nodup_depths {x : Fin 7 → ℝ³} (hx : Function.Injective x) {u : ℝ³}
    (h : ∀ y ∈ univ.image x, ∀ z ∈ univ.image x, y ≠ z → ⟪y, u⟫ ≠ ⟪z, u⟫) (l : List (Fin 7))
    (hl : l.Nodup) : (l.map fun i => ⟪x i, u⟫).Nodup := by
  refine hl.map_on fun i _ j _ e => ?_
  by_contra hij
  exact h _ (mem_image i) _ (mem_image j) (hx.ne hij) e

/-- The vertex view `v_A` of Lemma 19.5 is special only where `ViewGen16` fails. -/
theorem Views.of (T : Type16 x) (N : NF16 x)
    (h6 : ViewGen16 (univ.image x) T.t036.N T.t146.N) : Views N := by
  refine ⟨fun hne => ?_⟩
  exact (h6 _ hne
      (inner_zero_of_plane T.t036.hN (P := x 0) (Q := x 3) (R := x 6) (v := N.vA) (S := x 5)
        (by rw [T.t036.zero 3 (by decide), T.t036.zero 0 (by decide)])
        (by rw [T.t036.zero 6 (by decide), T.t036.zero 0 (by decide)])
        (by nf_simp N; refine mul_ne_zero ?_ N.hD; simp only [det3c]; norm_num)
        (by simp only [NF16.vA, NF16.f03]; nf_simp N; simp only [det3c]; ring))
      (inner_zero_of_plane T.t146.hN (P := x 1) (Q := x 4) (R := x 6) (v := N.vA) (S := x 5)
        (by rw [T.t146.zero 4 (by decide), T.t146.zero 1 (by decide)])
        (by rw [T.t146.zero 6 (by decide), T.t146.zero 1 (by decide)])
        (by
              nf_simp N
              refine mul_ne_zero ?_ N.hD
              simp only [det3c]
              intro e
              nlinarith [mul_pos N.hp N.hgd])
        (by simp only [NF16.vA, NF16.f03]; nf_simp N; simp only [det3c]; ring))).1

theorem npp_idx {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (hpp : NoPlaneParallel (univ.image x)) {i j k l m : Fin 7} (h : [i, j, k, l, m].Nodup) :
    det3 (x j - x i) (x k - x i) (x m - x l) ≠ 0 :=
  hpp _ (mem_image i) _ (mem_image j) _ (mem_image k) _ (mem_image l) _ (mem_image m)
    (by simpa using h.map hx)

/-- **The nondegeneracy conditions from the points**: no parallel segments (`GenPosTie`: the
far-end ties `a, b, g, d = 1` are parallel segments), no plane through three points parallel to a
segment of two others (`NoPlaneParallel`: the facing conditions `q = g`, `r = d`, `c36`, `f15`,
`f03`, `p + r = 1`, `T5`), the coplanarities `0134`, `2346`, and the line `036 ∩ 146` not
parallel to the plane `245` (`H_A ≠ 0`). -/
theorem Gen.of (T : Type16 x) (N : NF16 x) (hg : GenPosTie (univ.image x))
    (hpp : NoPlaneParallel (univ.image x))
    (h0134 : det3 (x 0 - x 3) (x 1 - x 3) (x 4 - x 3) ≠ 0)
    (h2346 : det3 (x 2 - x 3) (x 4 - x 3) (x 6 - x 3) ≠ 0)
    (hHA : ∀ u : ℝ³, u ≠ 0 → ⟪T.t036.N, u⟫ = 0 → ⟪T.t146.N, u⟫ = 0 →
      det3 (x 4 - x 2) (x 5 - x 2) u ≠ 0) : Gen N := by
  have P := fun {i j k l m : Fin 7} (h : [i, j, k, l, m].Nodup) => npp_idx N.inj hpp h
  have hm := fun i => mem_image (x := x) i
  have par := fun {s t u v : Fin 7} (hst : s ≠ t) (huv : u ≠ v) (htu : t ≠ u ∧ t ≠ v) (r : ℝ) =>
    hg.ne_smul (hm s) (hm t) (hm u) (hm v) (N.inj.ne hst) (N.inj.ne huv)
      ⟨N.inj.ne htu.1, N.inj.ne htu.2⟩ r
  set D := det3 N.E₁ N.E₂ N.E₃
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_,
    fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_,
    fun e => ?_⟩
  · apply P (i := 3) (j := 0) (k := 6) (l := 1) (m := 4) (by decide)
    nf_simp N; simp only [det3c]; linear_combination (-D) * e
  · apply P (i := 3) (j := 0) (k := 5) (l := 1) (m := 4) (by decide)
    nf_simp N; simp only [det3c]; linear_combination D * e
  · apply h0134; nf_simp N; simp only [det3c]; linear_combination D * e
  · apply par (s := 0) (t := 2) (u := 3) (v := 5) (by decide) (by decide) ⟨by decide, by decide⟩ N.b
    rw [N.x0, N.x2, N.x3, N.x5, nfP_sub, nfP_sub, e]; simp only [nfV]; module
  · apply par (s := 5) (t := 2) (u := 3) (v := 0) (by decide) (by decide) ⟨by decide, by decide⟩ N.a
    rw [N.x0, N.x2, N.x3, N.x5, nfP_sub, nfP_sub, e]; simp only [nfV]; module
  · apply par (s := 5) (t := 1) (u := 3) (v := 6) (by decide) (by decide) ⟨by decide, by decide⟩ N.d
    rw [N.x1, N.x5, N.x3, N.x6, nfP_sub, nfP_sub, e]; simp only [nfV]; module
  · apply par (s := 6) (t := 1) (u := 3) (v := 5) (by decide) (by decide) ⟨by decide, by decide⟩ N.g
    rw [N.x1, N.x5, N.x3, N.x6, nfP_sub, nfP_sub, e]; simp only [nfV]; module
  · apply h2346; nf_simp N; simp only [det3c]; linear_combination D * e
  · apply P (i := 0) (j := 2) (k := 4) (l := 3) (m := 6) (by decide)
    nf_simp N; simp only [det3c]; linear_combination D * e
  · apply P (i := 0) (j := 4) (k := 6) (l := 1) (m := 5) (by decide)
    nf_simp N; simp only [det3c]; linear_combination D * e
  · apply P (i := 1) (j := 4) (k := 6) (l := 0) (m := 3) (by decide)
    nf_simp N; simp only [det3c]; linear_combination (-D) * e
  · apply P (i := 0) (j := 4) (k := 6) (l := 3) (m := 5) (by decide)
    nf_simp N; simp only [det3c]; linear_combination (-D) * e
  · have hv : N.vA ≠ 0 := by
      simp only [NF16.vA]; exact nfV_ne_zero N.hD (Or.inl (ne_of_gt (mul_pos N.hg N.hp)))
    apply hHA _ hv
      (inner_zero_of_plane T.t036.hN (P := x 0) (Q := x 3) (R := x 6) (v := N.vA) (S := x 5)
        (by rw [T.t036.zero 3 (by decide), T.t036.zero 0 (by decide)])
        (by rw [T.t036.zero 6 (by decide), T.t036.zero 0 (by decide)])
        (by nf_simp N; refine mul_ne_zero ?_ N.hD; simp only [det3c]; norm_num)
        (by simp only [NF16.vA, NF16.f03]; nf_simp N; simp only [det3c]; ring))
      (inner_zero_of_plane T.t146.hN (P := x 1) (Q := x 4) (R := x 6) (v := N.vA) (S := x 5)
        (by rw [T.t146.zero 4 (by decide), T.t146.zero 1 (by decide)])
        (by rw [T.t146.zero 6 (by decide), T.t146.zero 1 (by decide)])
        (by
              nf_simp N
              refine mul_ne_zero ?_ N.hD
              simp only [det3c]
              intro e
              nlinarith [mul_pos N.hp N.hgd])
        (by simp only [NF16.vA, NF16.f03]; nf_simp N; simp only [det3c]; ring))
    simp only [NF16.vA, NF16.f03]; nf_simp N; simp only [det3c]; linear_combination D * e
  · apply P (i := 0) (j := 2) (k := 4) (l := 1) (m := 5) (by decide)
    nf_simp N; simp only [det3c]; linear_combination (-D) * e

theorem R_ne (N : NF16 x) (hpp : NoPlaneParallel (univ.image x)) : N.R1 ≠ 0 ∧ N.R2 ≠ 0 := by
  constructor <;> intro e <;> simp only [R1, R2] at e
  · apply npp_idx N.inj hpp (i := 1) (j := 4) (k := 5) (l := 0) (m := 6) (by decide)
    nf_simp N; simp only [det3c]; linear_combination (-det3 N.E₁ N.E₂ N.E₃) * e
  · apply npp_idx N.inj hpp (i := 2) (j := 4) (k := 5) (l := 0) (m := 6) (by decide)
    nf_simp N; simp only [det3c]; linear_combination (-det3 N.E₁ N.E₂ N.E₃) * e


theorem det3_cyc (a b c : ℝ³) : det3 c a b = det3 a b c := by
  simp only [det3_expand]; ring

/-- No horizontal double normal at the views along the line of two planes (normals `NP`, `NQ`). -/
def _root_.Minimality.NoHDNLine16 (V : Finset ℝ³) (NP NQ : ℝ³) : Prop :=
  ∀ u : ℝ³, u ≠ 0 → ⟪NP, u⟫ = 0 → ⟪NQ, u⟫ = 0 → NoHDNAt V u

/-- **No horizontal double normal at the named views**, from the facets: at the views along
the segments, and along the lines of the six pairs of facets `046/145`, `036/146`, `0235/046`,
`046/245`, `036/024`, `1356/046`. -/
theorem _root_.Minimality.Type16.noHDN_views (T : Type16 x) (hnd : NoHDNEdges16 x)
    (V1 : NoHDNLine16 (univ.image x) T.t046.N T.t145.N)
    (V2 : NoHDNLine16 (univ.image x) T.t036.N T.t146.N)
    (V3 : NoHDNLine16 (univ.image x) T.q0235.N T.t046.N)
    (V1σ : NoHDNLine16 (univ.image x) T.t046.N T.t245.N)
    (V2σ : NoHDNLine16 (univ.image x) T.t036.N T.t024.N)
    (V3σ : NoHDNLine16 (univ.image x) T.q1356.N T.t046.N) :
    ∀ v, view16 x v ≠ 0 → NoHDNAt (univ.image x) (view16 x v) := by
  rintro (⟨i, j⟩ | t) hv
  · have hij : i ≠ j := fun h => hv (by simp [view16, h])
    exact noHDNAt_of_erase (T.inj.ne hij) (hnd.fwd T.toNF hij) (hnd.bwd T.toNF hij)
  fin_cases t
  · change planeLine (x 0) (x 4) (x 6) (x 1) (x 4) (x 5) ≠ 0 at hv
    change NoHDNAt _ (planeLine (x 0) (x 4) (x 6) (x 1) (x 4) (x 5))
    exact V1 _ hv (inner_planeLine_left (T.t046.inner_sub (by decide) (by decide))
      (T.t046.inner_sub (by decide) (by decide)))
      (inner_planeLine_right (T.t145.inner_sub (by decide) (by decide))
        (T.t145.inner_sub (by decide) (by decide)))
  · change planeLine (x 0) (x 3) (x 6) (x 1) (x 4) (x 6) ≠ 0 at hv
    change NoHDNAt _ (planeLine (x 0) (x 3) (x 6) (x 1) (x 4) (x 6))
    exact V2 _ hv (inner_planeLine_left (T.t036.inner_sub (by decide) (by decide))
      (T.t036.inner_sub (by decide) (by decide)))
      (inner_planeLine_right (T.t146.inner_sub (by decide) (by decide))
        (T.t146.inner_sub (by decide) (by decide)))
  · change planeLine (x 0) (x 3) (x 5) (x 0) (x 4) (x 6) ≠ 0 at hv
    change NoHDNAt _ (planeLine (x 0) (x 3) (x 5) (x 0) (x 4) (x 6))
    exact V3 _ hv (inner_planeLine_left (T.q0235.inner_sub (by decide) (by decide))
      (T.q0235.inner_sub (by decide) (by decide)))
      (inner_planeLine_right (T.t046.inner_sub (by decide) (by decide))
        (T.t046.inner_sub (by decide) (by decide)))
  · change planeLine (x 6) (x 4) (x 0) (x 2) (x 4) (x 5) ≠ 0 at hv
    change NoHDNAt _ (planeLine (x 6) (x 4) (x 0) (x 2) (x 4) (x 5))
    exact V1σ _ hv (inner_planeLine_left (T.t046.inner_sub (by decide) (by decide))
      (T.t046.inner_sub (by decide) (by decide)))
      (inner_planeLine_right (T.t245.inner_sub (by decide) (by decide))
        (T.t245.inner_sub (by decide) (by decide)))
  · change planeLine (x 6) (x 3) (x 0) (x 2) (x 4) (x 0) ≠ 0 at hv
    change NoHDNAt _ (planeLine (x 6) (x 3) (x 0) (x 2) (x 4) (x 0))
    exact V2σ _ hv (inner_planeLine_left (T.t036.inner_sub (by decide) (by decide))
      (T.t036.inner_sub (by decide) (by decide)))
      (inner_planeLine_right (T.t024.inner_sub (by decide) (by decide))
        (T.t024.inner_sub (by decide) (by decide)))
  · change planeLine (x 6) (x 3) (x 5) (x 6) (x 4) (x 0) ≠ 0 at hv
    change NoHDNAt _ (planeLine (x 6) (x 3) (x 5) (x 6) (x 4) (x 0))
    exact V3σ _ hv (inner_planeLine_left (T.q1356.inner_sub (by decide) (by decide))
      (T.q1356.inner_sub (by decide) (by decide)))
      (inner_planeLine_right (T.t046.inner_sub (by decide) (by decide))
        (T.t046.inner_sub (by decide) (by decide)))



/-- **Theorem 19.6 for type 16**, from the facets (`Type16`): off the special positions — general
position up to single ties (`GenPosTie`), no plane through three points parallel to a segment of two others
(`NoPlaneParallel`), no horizontal double normal at the edge views (`NoHDNEdges16`), the
coplanarities `0134`, `2346`, the lines `036 ∩ 146` and `036 ∩ 024` not parallel to the planes
`245`, `145` (`H_A ≠ 0` and its `σ`-image), and `ViewGen16` at the six vertex views
`046/145`, `036/146`, `0235/046` and their `σ`-images `046/245`, `036/024`, `1356/046` — a
type-16 point set is Rupert. -/
theorem isRupert_type16 (T : Type16 x) (hg : GenPosTie (univ.image x))
    (hpp : NoPlaneParallel (univ.image x)) (hnd : NoHDNEdges16 x)
    (h0134 : det3 (x 0 - x 3) (x 1 - x 3) (x 4 - x 3) ≠ 0)
    (h2346 : det3 (x 2 - x 3) (x 4 - x 3) (x 6 - x 3) ≠ 0)
    (hHA : ∀ u : ℝ³, u ≠ 0 → ⟪T.t036.N, u⟫ = 0 → ⟪T.t146.N, u⟫ = 0 →
      det3 (x 4 - x 2) (x 5 - x 2) u ≠ 0)
    (hHAσ : ∀ u : ℝ³, u ≠ 0 → ⟪T.t036.N, u⟫ = 0 → ⟪T.t024.N, u⟫ = 0 →
      det3 (x 4 - x 1) (x 5 - x 1) u ≠ 0)
    (V1 : ViewGen16 (univ.image x) T.t046.N T.t145.N)
    (V2 : ViewGen16 (univ.image x) T.t036.N T.t146.N)
    (V3 : ViewGen16 (univ.image x) T.q0235.N T.t046.N)
    (V1σ : ViewGen16 (univ.image x) T.t046.N T.t245.N)
    (V2σ : ViewGen16 (univ.image x) T.t036.N T.t024.N)
    (V3σ : ViewGen16 (univ.image x) T.q1356.N T.t046.N) : IsRupert (univ.image x) := by
  set N := T.toNF
  have eσ := image_sigma16 x
  have d1 : det3 (x 6 - x 3) (x 2 - x 3) (x 4 - x 3) ≠ 0 := by rwa [det3_cyc]
  have d2 : det3 (x 1 - x 3) (x 4 - x 3) (x 0 - x 3) ≠ 0 := by rwa [← det3_cyc]
  have hc := cert_nf N (Gen.of T N hg hpp h0134 h2346 hHA)
    (Gen.of T.sigma N.sigma (by rw [eσ]; exact hg) (by rw [eσ]; exact hpp) d1 d2 hHAσ)
    (Views.of T N V2) (Views.of T.sigma N.sigma (by rw [eσ]; exact V2σ))
    (R_ne N hpp).1 (R_ne N hpp).2 hg.toTieSeg
  refine hc.isRupert T.noSeg ⟨3, 0, 5, 6, ?_⟩ ?_
  · nf_simp N; simp only [det3c]; norm_num; exact N.hD
  exact T.noHDN_views hnd (fun u hu h1 h2 => (V1 u hu h1 h2).2) (fun u hu h1 h2 => (V2 u hu h1 h2).2)
    (fun u hu h1 h2 => (V3 u hu h1 h2).2) (fun u hu h1 h2 => (V1σ u hu h1 h2).2)
    (fun u hu h1 h2 => (V2σ u hu h1 h2).2) (fun u hu h1 h2 => (V3σ u hu h1 h2).2)


end NF16

/-- The linear part of an affine function, read off its facet function. -/
theorem Face16.ofAffine_inner {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (f : ℝ³ →ᵃ[ℝ] ℝ)
    (h : ∀ i, (i ∈ S → f (x i) = 0) ∧ (i ∉ S → f (x i) < 0)) (u : ℝ³) :
    ⟪(Face16.ofAffine f h).N, u⟫ = f.linear u := by
  have e := f.map_vadd 0 u
  rw [vadd_eq_add, vadd_eq_add, add_zero] at e
  have k := (Face16.ofAffine f h).hN u 0
  simp only [Face16.ofAffine, sub_zero] at k ⊢
  linarith

/-- **The special positions of a vertex view**, for affine face functions: at every direction
`u ≠ 0` of the line of the two planes, at most one pair of points at the same depth
(`OneTieAt`), and no horizontal double normal. -/
def ViewAff16 (V : Finset ℝ³) (fP fQ : ℝ³ →ᵃ[ℝ] ℝ) : Prop :=
  ∀ u : ℝ³, u ≠ 0 → fP.linear u = 0 → fQ.linear u = 0 → OneTieAt V u ∧ NoHDNAt V u

/-- The line of the planes of `fP`, `fQ` is not parallel to the plane `a b c`. -/
def LineAff16 (fP fQ : ℝ³ →ᵃ[ℝ] ℝ) (a b c : ℝ³) : Prop :=
  ∀ u : ℝ³, u ≠ 0 → fP.linear u = 0 → fQ.linear u = 0 → det3 (b - a) (c - a) u ≠ 0

/-- **Type 16 from its facets** (Theorem 19.6): seven points labelled so that `0235`, `1356`
(quadrilaterals), `024`, `036`, `046`, `145`, `146`, `245` are facets (functionals negative off
them) are Rupert, off the special positions of `NF16.isRupert_type16`. -/
theorem isRupert_type16_facets (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (fA fB fC fD fE fF fG fH : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 2, 3, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 2, 3, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({1, 3, 5, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({1, 3, 5, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({0, 2, 4} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({0, 2, 4} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 3, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 3, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) < 0))
    (hF : ∀ i, (i ∈ ({1, 4, 5} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({1, 4, 5} : Finset (Fin 7)) → fF (x i) < 0))
    (hG : ∀ i, (i ∈ ({1, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({1, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hH : ∀ i, (i ∈ ({2, 4, 5} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({2, 4, 5} : Finset (Fin 7)) → fH (x i) < 0))
    (hg : GenPosTie (univ.image x)) (hpp : NoPlaneParallel (univ.image x))
    (hnd : ∀ v ∈ univ.image x, ∀ w ∈ univ.image x, v ≠ w →
      NoHDNAt ((univ.image x).erase w) (w - v))
    (h0134 : det3 (x 0 - x 3) (x 1 - x 3) (x 4 - x 3) ≠ 0)
    (h2346 : det3 (x 2 - x 3) (x 4 - x 3) (x 6 - x 3) ≠ 0)
    (hL : LineAff16 fD fG (x 2) (x 4) (x 5) ∧ LineAff16 fD fC (x 1) (x 4) (x 5))
    (hV : ViewAff16 (univ.image x) fE fF ∧ ViewAff16 (univ.image x) fD fG ∧
      ViewAff16 (univ.image x) fA fE ∧ ViewAff16 (univ.image x) fE fH ∧
      ViewAff16 (univ.image x) fD fC ∧ ViewAff16 (univ.image x) fB fE) :
    IsRupert (univ.image x) := by
  let T : Type16 x := ⟨hx, Face16.ofAffine fA hA, Face16.ofAffine fB hB, Face16.ofAffine fC hC,
    Face16.ofAffine fD hD, Face16.ofAffine fE hE, Face16.ofAffine fF hF, Face16.ofAffine fG hG,
    Face16.ofAffine fH hH⟩
  have V : ∀ {fP fQ : ℝ³ →ᵃ[ℝ] ℝ} {SP SQ : Finset (Fin 7)}
      (hP : ∀ i, (i ∈ SP → fP (x i) = 0) ∧ (i ∉ SP → fP (x i) < 0))
      (hQ : ∀ i, (i ∈ SQ → fQ (x i) = 0) ∧ (i ∉ SQ → fQ (x i) < 0)),
      ViewAff16 (univ.image x) fP fQ →
        NF16.ViewGen16 (univ.image x) (Face16.ofAffine fP hP).N (Face16.ofAffine fQ hQ).N := by
    intro fP fQ SP SQ hP hQ h u hu h1 h2
    rw [Face16.ofAffine_inner] at h1 h2
    exact h u hu h1 h2
  have L : ∀ {fP fQ : ℝ³ →ᵃ[ℝ] ℝ} {SP SQ : Finset (Fin 7)}
      (hP : ∀ i, (i ∈ SP → fP (x i) = 0) ∧ (i ∉ SP → fP (x i) < 0))
      (hQ : ∀ i, (i ∈ SQ → fQ (x i) = 0) ∧ (i ∉ SQ → fQ (x i) < 0)) {a b c : ℝ³},
      LineAff16 fP fQ a b c → ∀ u : ℝ³, u ≠ 0 → ⟪(Face16.ofAffine fP hP).N, u⟫ = 0 →
        ⟪(Face16.ofAffine fQ hQ).N, u⟫ = 0 → det3 (b - a) (c - a) u ≠ 0 := by
    intro fP fQ SP SQ hP hQ a b c h u hu h1 h2
    rw [Face16.ofAffine_inner] at h1 h2
    exact h u hu h1 h2
  exact NF16.isRupert_type16 T hg hpp hnd h0134 h2346 (L hD hG hL.1) (L hD hC hL.2)
    (V hE hF hV.1) (V hD hG hV.2.1) (V hA hE hV.2.2.1) (V hE hH hV.2.2.2.1)
    (V hD hC hV.2.2.2.2.1) (V hB hE hV.2.2.2.2.2)

namespace NF16
end NF16

end Minimality

end
