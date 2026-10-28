module

public import Minimality.CaseC18Step4

@[expose] public section

/-!
# Type 18: Theorem LC, the level chord on `ClassH` (stage M7)

Paper: `FEWER-FACES-PROOFS.md` section 34.4.1.

Labels `(m1+, m1-, m2+, m2-, xb, xa, v) = (0, 6, 1, 2, 4, 3, 5)`.  On `ClassH` with the level chord
`dV 0 = dV 6` (hence `dV 4 = dV 0` too), the tilt `d = eF1 + τ e_y` (`τ < 0` small) of the view `uV`
makes the silhouette at `uV + ε d` the 4-cycle `(xb, m1+, v, m1-)` (`xa`, `m2±` strictly inside),
with `xb` strictly between `m1+` and `m1-` in depth, so the cycle is robustly unimodal.  No
`M`-middle is needed (`M = ∅`): every other vertex is strictly inside for small `ε > 0`.
-/

namespace Minimality.CaseC18

open Finset Filter Minimality.CaseC09 Minimality.CaseC20
open scoped RealInnerProductSpace Topology

namespace Shape18
variable (S : Shape18)

/-- The tilt `eF1 + τ e_y` (`eF1 = m1- - m1+`). -/
def eLC (τ : ℝ) : C3 := ⟨S.tm - S.tp, τ, -S.hm - S.hp⟩

/-- The corners of the 4-cycle `(xb, m1+, v, m1-)` and the three vertices strictly inside it. -/
def lcXb : C3 := ⟨0, 1, 0⟩
def lcMp : C3 := ⟨S.tp, 0, S.hp⟩
def lcV : C3 := ⟨0, 0, 0⟩
def lcMm : C3 := ⟨S.tm, 0, -S.hm⟩
def lcM2p : C3 := ⟨0, S.sp, S.kp⟩
def lcXa : C3 := ⟨1, 0, 0⟩
def lcM2m : C3 := ⟨0, S.sm, -S.km⟩

end Shape18

/-! ### Generic lemmas -/

/-- `xb` strictly between `m1+` and `m1-` makes the cycle `(xb, m1+, w, m1-)` robustly unimodal,
whatever the depth of `w` (neither diagonal lies strictly above the other). -/
theorem isRobustUnimodal_quad_between {z0 z1 z2 z3 : ℝ} (h1 : z1 < z0) (h3 : z0 < z3) :
    IsRobustUnimodal (quad z0 z1 z2 z3) :=
  robust_quad_of_nws (Or.inr (Or.inl h3)) (Or.inl h1)

/-- A vector orthogonal to a basis of `ℝ³` is zero. -/
theorem eq_zero_of_inner_basis (u e f : ℝ³) (hind : LinearIndependent ℝ ![u, e, f]) (l : ℝ³)
    (hu : ⟪l, u⟫ = 0) (he : ⟪l, e⟫ = 0) (hf : ⟪l, f⟫ = 0) : l = 0 := by
  let b := basisOfLinearIndependentOfCardEqFinrank hind (by simp)
  have hb : ∀ i, ⟪l, b i⟫ = 0 := by
    intro i
    have : b i = ![u, e, f] i := by simp [b]
    rw [this]
    fin_cases i <;> simpa
  have h0 : (innerSL ℝ l : ℝ³ →ₗ[ℝ] ℝ) = 0 := b.ext fun i => by simpa using hb i
  have := congrArg (fun g : ℝ³ →ₗ[ℝ] ℝ => g l) h0
  simpa using this

/-- Finitely many tilts are bad: if `u, e, f` are independent, then for a finite set `L` of nonzero
directions and any `δ > 0` some `τ ∈ (-δ, 0)` has `⟪l, u⟫ ≠ 0 ∨ ⟪l, e + τ f⟫ ≠ 0` for every `l ∈ L`
(each `l` kills at most one `τ`, since `l ⟂ u, e + τ f, e + τ' f` forces `l ⟂ u, e, f`). -/
theorem exists_good_tilt (L : Finset ℝ³) (u e f : ℝ³)
    (hind : LinearIndependent ℝ ![u, e, f])
    (hL : ∀ l ∈ L, l ≠ 0) (δ : ℝ) (hδ : 0 < δ) :
    ∃ τ : ℝ, -δ < τ ∧ τ < 0 ∧ ∀ l ∈ L, ⟪l, u⟫ ≠ 0 ∨ ⟪l, e + τ • f⟫ ≠ 0 := by
  classical
  have key : ∀ l ∈ L, ∀ τ τ' : ℝ, ⟪l, u⟫ = 0 → ⟪l, e + τ • f⟫ = 0 → ⟪l, e + τ' • f⟫ = 0 →
      τ = τ' := by
    intro l hl τ τ' h0 h1 h2
    by_contra hne
    have h1' : ⟪l, e⟫ + τ * ⟪l, f⟫ = 0 := by
      rwa [inner_add_right, real_inner_smul_right] at h1
    have h2' : ⟪l, e⟫ + τ' * ⟪l, f⟫ = 0 := by
      rwa [inner_add_right, real_inner_smul_right] at h2
    have hf : ⟪l, f⟫ = 0 := by
      have : (τ - τ') * ⟪l, f⟫ = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.2 hne)
    have he : ⟪l, e⟫ = 0 := by rw [hf] at h1'; linarith
    exact hL l hl (eq_zero_of_inner_basis u e f hind l h0 he hf)
  let T : Finset ℝ := L.image fun l =>
    if h : ∃ τ : ℝ, ⟪l, u⟫ = 0 ∧ ⟪l, e + τ • f⟫ = 0 then h.choose else 0
  obtain ⟨τ, hτ, hτT⟩ := (Set.Ioo_infinite (show -δ < 0 by linarith)).exists_notMem_finset T
  refine ⟨τ, hτ.1, hτ.2, fun l hl => ?_⟩
  by_contra hc
  push Not at hc
  have hex : ∃ τ : ℝ, ⟪l, u⟫ = 0 ∧ ⟪l, e + τ • f⟫ = 0 := ⟨τ, hc.1, hc.2⟩
  apply hτT
  refine Finset.mem_image.2 ⟨l, hl, ?_⟩
  rw [dif_pos hex]
  have := hex.choose_spec
  exact key l hl _ _ hc.1 this.2 hc.2

/-- The pair-direction form of `eventually_noHDNRim_slide` (its proof's `hpair` step): if every pair
direction of the cycle is non-orthogonal to `u₀` or to `e`, the rim has no horizontal double normal
at `u₀ + t e` for small `t > 0`. -/
theorem eventually_noHDNRim_slide_of_pairDirs {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (u₀ e : ℝ³)
    (h : ∀ i j : ZMod k, ∀ l ∈ pairDirs x i j, ⟪l, u₀⟫ ≠ 0 ∨ ⟪l, e⟫ ≠ 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), NoHDNRim x (u₀ + t • e) := by
  classical
  have hlin : ∀ l : ℝ³, ∀ t : ℝ, ⟪l, u₀ + t • e⟫ = ⟪l, u₀⟫ + t * ⟪l, e⟫ := by
    intro l t; rw [inner_add_right, real_inner_smul_right]
  have hev1 : ∀ l : ℝ³, ⟪l, u₀⟫ ≠ 0 ∨ ⟪l, e⟫ ≠ 0 →
      ∀ᶠ t in 𝓝[>] (0 : ℝ), ⟪l, u₀ + t • e⟫ ≠ 0 := by
    intro l h
    simp only [hlin]
    rcases h with h | h
    · by_cases he : ⟪l, e⟫ = 0
      · filter_upwards with t; rw [he, mul_zero, add_zero]; exact h
      · exact eventually_ne_affine he
    · exact eventually_ne_affine h
  have hpair : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i j : ZMod k, ∀ l ∈ pairDirs x i j,
      ⟪l, u₀ + t • e⟫ ≠ 0 := by
    refine eventually_all.mpr fun i => eventually_all.mpr fun j => ?_
    refine (eventually_all_finset _).mpr fun l hl => ?_
    exact hev1 l (h i j l hl)
  filter_upwards [hpair] with t ht R hR r hr hRu _ hh
  have hdepth : ∀ y, (R.toEuclideanLin y) 2 = r⁻¹ * ⟪y, u₀ + t • e⟫ := by
    intro y
    have : r * (R.toEuclideanLin y) 2 = ⟪y, u₀ + t • e⟫ := by
      rw [← inner_ez, ← real_inner_smul_right, ← hRu, inner_toEuclideanLin_SO3 hR]
    rw [← this]; field_simp
  obtain ⟨i, j, -, l, hl, hl0, Y, hY, Y', hY', r', hr', hYl, hext⟩ :=
    exists_pairDir_of_hdnE R hR x hh
  rw [hdepth] at hl0
  have hlu : ⟪l, u₀ + t • e⟫ = 0 := (mul_eq_zero.mp hl0).resolve_left (inv_ne_zero hr)
  exact ht i j l hl hlu

/-! ### The silhouette tests -/

theorem PS_ev_pos (u e a b : C3) (A : ℝ) (h : Dc a b u = A) (hA : 0 < A) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), PS 1 (C3.slide u e η) a b :=
  PS_ev' u e a b (Or.inl (by rw [h]; exact hA))

theorem PS_ev_deriv (u e a b : C3) (B : ℝ) (h0 : Dc a b u = 0) (hB : Dc a b e = B) (hB0 : 0 < B) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), PS 1 (C3.slide u e η) a b :=
  PS_ev' u e a b (Or.inr ⟨h0, by rw [hB]; exact hB0⟩)

namespace Shape18
variable (S : Shape18)

/-- **Step 2 (a), (c): the 4-cycle `(xb, m1+, v, m1-)` is ccw at `u_η`** (`τ < 0`), as `PCyc4`.
Strict at `η = 0` except the two tests with `v` collinear with the chord, whose `η`-derivative is
`-τ (hp tm + hm tp) > 0`. -/
theorem lc_cyc_ev (hV : 0 < S.Vp) (τ : ℝ) (hτ : τ < 0) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), Minimality.CaseC20.PCyc4 1 (C3.slide S.uV (S.eLC τ) η)
      lcXb S.lcMp lcV S.lcMm := by
  have hK := mul_pos S.tp_pos S.kp_pos
  have hΩ : 0 < S.Vp + S.kp * S.tp := by nlinarith [mul_pos S.kp_pos S.tp_pos]
  have hS : 0 < S.hp * S.tm + S.hm * S.tp :=
    add_pos (mul_pos S.hp_pos S.tm_pos) (mul_pos S.hm_pos S.tp_pos)
  have hB : 0 < -τ * (S.hp * S.tm + S.hm * S.tp) := mul_pos (by linarith) hS
  have t1 := PS_ev_pos S.uV (S.eLC τ) (S.lcMp.sub lcXb) (lcV.sub lcXb) (S.tp * S.kp)
    (by simp only [Dc, C3.sub, lcMp, lcXb, lcV, uV]; ring) hK
  have t2 := PS_ev_pos S.uV (S.eLC τ) (S.lcMp.sub lcXb) (S.lcMm.sub lcXb)
    (S.Vp + S.kp * S.tp)
    (by simp only [Dc, C3.sub, lcMp, lcXb, lcMm, uV, Vp]; ring) hΩ
  have t3 := PS_ev_deriv S.uV (S.eLC τ) (lcV.sub S.lcMp) (S.lcMm.sub S.lcMp)
    (-τ * (S.hp * S.tm + S.hm * S.tp))
    (by simp only [Dc, C3.sub, lcMp, lcV, lcMm, uV]; ring)
    (by simp only [Dc, C3.sub, lcMp, lcV, lcMm, eLC]; ring) hB
  have t4 := PS_ev_pos S.uV (S.eLC τ) (lcV.sub S.lcMp) (lcXb.sub S.lcMp) (S.tp * S.kp)
    (by simp only [Dc, C3.sub, lcMp, lcXb, lcV, uV]; ring) hK
  have t5 := PS_ev_pos S.uV (S.eLC τ) (S.lcMm.sub lcV) (lcXb.sub lcV) S.Vp
    (by simp only [Dc, C3.sub, lcMm, lcXb, lcV, uV, Vp]; ring) hV
  have t6 := PS_ev_deriv S.uV (S.eLC τ) (S.lcMm.sub lcV) (S.lcMp.sub lcV)
    (-τ * (S.hp * S.tm + S.hm * S.tp))
    (by simp only [Dc, C3.sub, lcMp, lcV, lcMm, uV]; ring)
    (by simp only [Dc, C3.sub, lcMp, lcV, lcMm, eLC]; ring) hB
  have t7 := PS_ev_pos S.uV (S.eLC τ) (lcXb.sub S.lcMm) (S.lcMp.sub S.lcMm)
    (S.Vp + S.kp * S.tp)
    (by simp only [Dc, C3.sub, lcMp, lcXb, lcMm, uV, Vp]; ring) hΩ
  have t8 := PS_ev_pos S.uV (S.eLC τ) (lcXb.sub S.lcMm) (lcV.sub S.lcMm) S.Vp
    (by simp only [Dc, C3.sub, lcMm, lcXb, lcV, uV, Vp]; ring) hV
  filter_upwards [t1, t2, t3, t4, t5, t6, t7, t8] with η a b c d e f g h
  exact ⟨a, b, c, d, e, f, g, h⟩

/-- `m2+` is strictly inside the 4-cycle (`-Ω + τ tp kp < 0`, i.e. the edge `(xb, m1+)` test has
derivative `Ω - τ tp kp > 0`). -/
theorem lc_rest_m2p_ev (hV : 0 < S.Vp) (τ : ℝ) (hτ : τ < 0) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), Minimality.CaseC20.PRest4 1 (C3.slide S.uV (S.eLC τ) η)
      lcXb S.lcMp lcV S.lcMm S.lcM2p := by
  have hK := mul_pos S.tp_pos S.kp_pos
  have hsp := S.sp_pos; have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hΩ : 0 < S.Vp + S.kp * S.tp := by nlinarith [mul_pos S.kp_pos S.tp_pos]
  have hB : 0 < S.Vp + S.kp * S.tp - τ * (S.tp * S.kp) := by nlinarith
  have t1 := PS_ev_deriv S.uV (S.eLC τ) (S.lcMp.sub lcXb) (S.lcM2p.sub lcXb)
    (S.Vp + S.kp * S.tp - τ * (S.tp * S.kp))
    (by simp only [Dc, C3.sub, lcMp, lcXb, lcM2p, uV]; ring)
    (by simp only [Dc, C3.sub, lcMp, lcXb, lcM2p, eLC, Vp]; ring) hB
  have t2 := PS_ev_pos S.uV (S.eLC τ) (lcV.sub S.lcMp) (S.lcM2p.sub S.lcMp)
    (S.sp * (S.tp * S.kp))
    (by simp only [Dc, C3.sub, lcMp, lcM2p, lcV, uV]; ring) (mul_pos hsp hK)
  have t3 := PS_ev_pos S.uV (S.eLC τ) (S.lcMm.sub lcV) (S.lcM2p.sub lcV) (S.sp * S.Vp)
    (by simp only [Dc, C3.sub, lcMm, lcM2p, lcV, uV, Vp]; ring) (mul_pos hsp hV)
  have t4 := PS_ev_pos S.uV (S.eLC τ) (lcXb.sub S.lcMm) (S.lcM2p.sub S.lcMm)
    ((1 - S.sp) * (S.Vp + S.kp * S.tp))
    (by simp only [Dc, C3.sub, lcMm, lcXb, lcM2p, uV, Vp]; ring) (mul_pos hsp1 hΩ)
  filter_upwards [t1, t2, t3, t4] with η a b c d
  exact ⟨a, b, c, d⟩

/-- `xa` is strictly inside the 4-cycle: the tests against the edges `(m1+, v)`, `(v, m1-)` vanish at
`η = 0` with derivatives `-τ hp`, `-τ hm`. -/
theorem lc_rest_xa_ev (hW : S.Wp < S.Vp) (τ : ℝ) (hτ : τ < 0) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), Minimality.CaseC20.PRest4 1 (C3.slide S.uV (S.eLC τ) η)
      lcXb S.lcMp lcV S.lcMm lcXa := by
  have hr : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := by
    have := S.roof_p'; linarith
  have hW' : 0 < S.Vp - S.Wp := sub_pos.2 hW
  have t1 := PS_ev_pos S.uV (S.eLC τ) (S.lcMp.sub lcXb) (lcXa.sub lcXb)
    (S.hp * (1 - S.sp) - S.kp * (1 - S.tp))
    (by simp only [Dc, C3.sub, lcMp, lcXb, lcXa, uV]; ring) hr
  have t2 := PS_ev_deriv S.uV (S.eLC τ) (lcV.sub S.lcMp) (lcXa.sub S.lcMp) (-τ * S.hp)
    (by simp only [Dc, C3.sub, lcMp, lcXa, lcV, uV]; ring)
    (by simp only [Dc, C3.sub, lcMp, lcXa, lcV, eLC]; ring)
    (mul_pos (by linarith) S.hp_pos)
  have t3 := PS_ev_deriv S.uV (S.eLC τ) (S.lcMm.sub lcV) (lcXa.sub lcV) (-τ * S.hm)
    (by simp only [Dc, C3.sub, lcMm, lcXa, lcV, uV]; ring)
    (by simp only [Dc, C3.sub, lcMm, lcXa, lcV, eLC]; ring)
    (mul_pos (by linarith) S.hm_pos)
  have t4 := PS_ev_pos S.uV (S.eLC τ) (lcXb.sub S.lcMm) (lcXa.sub S.lcMm) (S.Vp - S.Wp)
    (by simp only [Dc, C3.sub, lcMm, lcXb, lcXa, uV, Vp, Wp]; ring) hW'
  filter_upwards [t1, t2, t3, t4] with η a b c d
  exact ⟨a, b, c, d⟩

/-- `m2-` is strictly inside the 4-cycle (`D2p > 0`). -/
theorem lc_rest_m2m_ev (hD2 : 0 < S.D2p) (hV : 0 < S.Vp) (τ : ℝ) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), Minimality.CaseC20.PRest4 1 (C3.slide S.uV (S.eLC τ) η)
      lcXb S.lcMp lcV S.lcMm S.lcM2m := by
  have hK := mul_pos S.tp_pos S.kp_pos
  have hsm := S.sm_pos; have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have h0 : 0 < S.km * (S.tp * (1 - S.sp)) + (1 - S.sm) * (S.tp * S.kp) :=
    add_pos (mul_pos S.km_pos (mul_pos S.tp_pos hsp1)) (mul_pos hsm1 hK)
  have t1 := PS_ev_pos S.uV (S.eLC τ) (S.lcMp.sub lcXb) (S.lcM2m.sub lcXb)
    (S.km * (S.tp * (1 - S.sp)) + (1 - S.sm) * (S.tp * S.kp))
    (by simp only [Dc, C3.sub, lcMp, lcXb, lcM2m, uV]; ring) h0
  have t2 := PS_ev_pos S.uV (S.eLC τ) (lcV.sub S.lcMp) (S.lcM2m.sub S.lcMp)
    (S.sm * (S.tp * S.kp))
    (by simp only [Dc, C3.sub, lcMp, lcM2m, lcV, uV]; ring) (mul_pos hsm hK)
  have t3 := PS_ev_pos S.uV (S.eLC τ) (S.lcMm.sub lcV) (S.lcM2m.sub lcV) (S.sm * S.Vp)
    (by simp only [Dc, C3.sub, lcMm, lcM2m, lcV, uV, Vp]; ring) (mul_pos hsm hV)
  have t4 := PS_ev_pos S.uV (S.eLC τ) (lcXb.sub S.lcMm) (S.lcM2m.sub S.lcMm) S.D2p
    (by simp only [Dc, C3.sub, lcMm, lcXb, lcM2m, uV, Vp, D2p]; ring) hD2
  filter_upwards [t1, t2, t3, t4] with η a b c d
  exact ⟨a, b, c, d⟩

end Shape18

/-! ### The tilt at `V` -/

namespace Frame18
variable {x : Fin 7 → ℝ³} (F : Frame18 x)

/-- Independence of `uV`, `eF1`, `e_y` in `ℝ³` (their determinant in the frame is `-Ω`). -/
theorem lc_indep (hV : 0 < F.S.Vp) :
    LinearIndependent ℝ ![F.toFrame7.fvC F.S.uV, F.toFrame7.fvC F.S.eF1,
      F.toFrame7.fvC (⟨0, 1, 0⟩ : C3)] := by
  have hΩ : 0 < F.S.Vp + F.S.kp * F.S.tp := by nlinarith [mul_pos F.S.kp_pos F.S.tp_pos]
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hg' : g 0 • F.toFrame7.fvC F.S.uV + g 1 • F.toFrame7.fvC F.S.eF1 +
      g 2 • F.toFrame7.fvC (⟨0, 1, 0⟩ : C3) = 0 := by
    simpa [Fin.sum_univ_three] using hg
  have key := Fintype.linearIndependent_iff.1 F.toFrame7.indep
    ![g 0 * F.S.uV.x + g 1 * F.S.eF1.x, g 2, g 0 * F.S.uV.z + g 1 * F.S.eF1.z] (by
      have e : ∑ i, (![g 0 * F.S.uV.x + g 1 * F.S.eF1.x, g 2,
            g 0 * F.S.uV.z + g 1 * F.S.eF1.z] : Fin 3 → ℝ) i •
          (![F.toFrame7.u1, F.toFrame7.u2, F.toFrame7.e] : Fin 3 → ℝ³) i =
          g 0 • F.toFrame7.fvC F.S.uV + g 1 • F.toFrame7.fvC F.S.eF1 +
            g 2 • F.toFrame7.fvC (⟨0, 1, 0⟩ : C3) := by
        simp [Fin.sum_univ_three, Frame7.fvC, Shape18.uV, Shape18.eF1]
        module
      rw [e]; exact hg')
  have k0 : g 0 * (-F.S.sp * F.S.tp + F.S.tp) + g 1 * (F.S.tm - F.S.tp) = 0 := by
    simpa [Shape18.uV, Shape18.eF1] using key 0
  have k1 : g 2 = 0 := by simpa using key 1
  have k2 : g 0 * (-F.S.hp * F.S.sp + F.S.hp - F.S.kp) + g 1 * (-F.S.hm - F.S.hp) = 0 := by
    simpa [Shape18.uV, Shape18.eF1] using key 2
  have hE3 : -F.S.hm - F.S.hp ≠ 0 := by
    have := F.S.hm_pos; have := F.S.hp_pos; intro h; linarith
  have g0 : g 0 = 0 := by
    have : g 0 * (F.S.Vp + F.S.kp * F.S.tp) = 0 := by
      simp only [Shape18.Vp]
      linear_combination (F.S.tm - F.S.tp) * k2 - (-F.S.hm - F.S.hp) * k0
    exact (mul_eq_zero.mp this).resolve_right hΩ.ne'
  have g1 : g 1 = 0 := by
    rw [g0] at k2
    have : g 1 * (-F.S.hm - F.S.hp) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right hE3
  intro i
  fin_cases i
  · exact g0
  · exact g1
  · exact k1

/-- On `ClassH` with the level chord the three depths `m1+, xb, m1-` agree at `uV`. -/
theorem lc_dV_eq (hH : F.ClassH) (hlev : F.dV 0 = F.dV 6) : F.dV 4 = F.dV 0 := by
  rcases F.classH_depth_trichotomy hH with ⟨h6, h0⟩ | ⟨h0, h6⟩ | ⟨e0, e6⟩
  · linarith
  · linarith
  · exact e0.symm

/-- `0 < P0` and `0 < Q0`, the constant terms of the depth differences (`λ |e1|²`, `(1-λ) |e1|²`). -/
theorem lc_PQ_pos (hH : F.ClassH) :
    0 < (F.a12 - F.a11 * F.S.tp) * (F.S.tm - F.S.tp) + F.gg * F.S.hp * (F.S.hm + F.S.hp) ∧
    0 < F.a11 * F.S.tm * (F.S.tm - F.S.tp) + F.gg * F.S.hm * (F.S.hm + F.S.hp) -
      F.a12 * (F.S.tm - F.S.tp) := by
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos
  have hg := F.g_pos
  have hA11 : 0 ≤ F.a11 := real_inner_self_nonneg
  have hH' : F.a12 * (F.S.hp + F.S.hm) = F.a11 * (F.S.tp * F.S.hm + F.S.tm * F.S.hp) := hH
  have hsum : 0 < F.S.hp + F.S.hm := by linarith
  have hR : 0 < F.a11 * (F.S.tm - F.S.tp) ^ 2 + F.gg * (F.S.hp + F.S.hm) ^ 2 :=
    add_pos_of_nonneg_of_pos (mul_nonneg hA11 (sq_nonneg _)) (mul_pos hg (pow_pos hsum 2))
  have e1 : (F.S.hp + F.S.hm) * ((F.a12 - F.a11 * F.S.tp) * (F.S.tm - F.S.tp) +
      F.gg * F.S.hp * (F.S.hm + F.S.hp)) =
      F.S.hp * (F.a11 * (F.S.tm - F.S.tp) ^ 2 + F.gg * (F.S.hp + F.S.hm) ^ 2) := by
    linear_combination (F.S.tm - F.S.tp) * hH'
  have e2 : (F.S.hp + F.S.hm) * (F.a11 * F.S.tm * (F.S.tm - F.S.tp) +
      F.gg * F.S.hm * (F.S.hm + F.S.hp) - F.a12 * (F.S.tm - F.S.tp)) =
      F.S.hm * (F.a11 * (F.S.tm - F.S.tp) ^ 2 + F.gg * (F.S.hp + F.S.hm) ^ 2) := by
    linear_combination (-(F.S.tm - F.S.tp)) * hH'
  constructor
  · by_contra h
    push Not at h
    nlinarith [mul_pos hhp hR, mul_nonneg hsum.le (neg_nonneg.2 h)]
  · by_contra h
    push Not at h
    nlinarith [mul_pos hhm hR, mul_nonneg hsum.le (neg_nonneg.2 h)]

theorem lin_pos_of_abs {P0 P1 τ : ℝ} (hP0 : 0 < P0) (h : |τ| < P0 / (|P1| + 1)) :
    0 < P0 + τ * P1 := by
  have hp1 : 0 < |P1| + 1 := by positivity
  rw [lt_div_iff₀ hp1] at h
  have h1 : -|τ * P1| ≤ τ * P1 := neg_abs_le _
  have h2 : |τ * P1| ≤ |τ| * (|P1| + 1) := by
    rw [abs_mul]; nlinarith [abs_nonneg τ]
  linarith

/-- **Step 3, the depth identities**: along `u_η = uV + η (eF1 + τ e_y)`, `|τ| < τ₁`, `η > 0`,
`m1+ < xb < m1-` in `G`-depth (`ClassH` and `dV 0 = dV 6`; the differences are
`η (P0 + τ P1)` and `η (Q0 + τ Q1)` with `P0 = λ |e1|²`, `Q0 = (1-λ) |e1|²`). -/
theorem lc_depth_order (hH : F.ClassH) (hlev : F.dV 0 = F.dV 6) :
    ∃ τ₁ : ℝ, 0 < τ₁ ∧ ∀ τ : ℝ, |τ| < τ₁ → ∀ η : ℝ, 0 < η →
      F.toFrame7.GG (F.toFrame7.ptC 0) (C3.slide F.S.uV (F.S.eLC τ) η) <
        F.toFrame7.GG (F.toFrame7.ptC 4) (C3.slide F.S.uV (F.S.eLC τ) η) ∧
      F.toFrame7.GG (F.toFrame7.ptC 4) (C3.slide F.S.uV (F.S.eLC τ) η) <
        F.toFrame7.GG (F.toFrame7.ptC 6) (C3.slide F.S.uV (F.S.eLC τ) η) := by
  obtain ⟨hP, hQ⟩ := F.lc_PQ_pos hH
  set P0 := (F.a12 - F.a11 * F.S.tp) * (F.S.tm - F.S.tp) + F.gg * F.S.hp * (F.S.hm + F.S.hp)
  set Q0 := F.a11 * F.S.tm * (F.S.tm - F.S.tp) + F.gg * F.S.hm * (F.S.hm + F.S.hp) -
    F.a12 * (F.S.tm - F.S.tp)
  set P1 := F.a22 - F.a12 * F.S.tp
  set Q1 := F.a12 * F.S.tm - F.a22
  have d4 := F.lc_dV_eq hH hlev
  refine ⟨min (P0 / (|P1| + 1)) (Q0 / (|Q1| + 1)), lt_min (by positivity) (by positivity),
    fun τ hτ η hη => ?_⟩
  have hτP : |τ| < P0 / (|P1| + 1) := lt_of_lt_of_le hτ (min_le_left _ _)
  have hτQ : |τ| < Q0 / (|Q1| + 1) := lt_of_lt_of_le hτ (min_le_right _ _)
  have hp := lin_pos_of_abs hP hτP
  have hq := lin_pos_of_abs hQ hτQ
  rw [Frame7.GG_slide, Frame7.GG_slide, Frame7.GG_slide]
  have e04 : F.toFrame7.GG (F.toFrame7.ptC 4) F.S.uV = F.toFrame7.GG (F.toFrame7.ptC 0) F.S.uV :=
    d4
  have e06 : F.toFrame7.GG (F.toFrame7.ptC 6) F.S.uV = F.toFrame7.GG (F.toFrame7.ptC 0) F.S.uV :=
    hlev.symm
  have gP : F.toFrame7.GG (F.toFrame7.ptC 4) (F.S.eLC τ) -
      F.toFrame7.GG (F.toFrame7.ptC 0) (F.S.eLC τ) = P0 + τ * P1 := by
    simp only [GG_eq, ptC_4, ptC_0, Shape18.eLC, P0, P1]; ring
  have gQ : F.toFrame7.GG (F.toFrame7.ptC 6) (F.S.eLC τ) -
      F.toFrame7.GG (F.toFrame7.ptC 4) (F.S.eLC τ) = Q0 + τ * Q1 := by
    simp only [GG_eq, ptC_6, ptC_4, Shape18.eLC, Q0, Q1]; ring
  rw [e04, e06]
  constructor <;> nlinarith [mul_pos hη hp, mul_pos hη hq]

/-- **Theorem LC** (type 18, triangle rim at `V`, `ClassH` with the level chord): Rupert. -/
theorem vNt_level_rupert (hx : Function.Injective x) (hD2 : 0 < F.S.D2p) (hV : 0 < F.S.Vp)
    (hW : F.S.Wp < F.S.Vp) (hH : F.ClassH) (hlev : F.dV 0 = F.dV 6) :
    IsRupert (Finset.univ.image x) := by
  classical
  have htp := F.S.tp_pos
  have ux : 0 < -F.S.sp * F.S.tp + F.S.tp := by nlinarith [mul_pos htp (sub_pos.2 F.S.sp_lt)]
  obtain ⟨τ₁, hτ₁, hord⟩ := F.lc_depth_order hH hlev
  let L : Finset ℝ³ := Finset.univ.biUnion fun i : ZMod 4 => Finset.univ.biUnion fun j : ZMod 4 =>
    pairDirs (fun i => x (quad 4 0 5 6 i)) i j
  have hL : ∀ l ∈ L, l ≠ 0 := by
    intro l hl
    simp only [L, Finset.mem_biUnion, Finset.mem_univ, true_and] at hl
    obtain ⟨i, j, hl⟩ := hl
    exact (Finset.mem_filter.mp hl).2
  obtain ⟨τ, hτ1, hτ2, hgood⟩ := exists_good_tilt L (F.toFrame7.fvC F.S.uV)
    (F.toFrame7.fvC F.S.eF1) (F.toFrame7.fvC (⟨0, 1, 0⟩ : C3)) (F.lc_indep hV) hL τ₁ hτ₁
  have hvec : F.toFrame7.fvC (F.S.eLC τ) =
      F.toFrame7.fvC F.S.eF1 + τ • F.toFrame7.fvC (⟨0, 1, 0⟩ : C3) := by
    simp only [Frame7.fvC, Shape18.eLC, Shape18.eF1]; module
  have efv : ∀ η : ℝ, F.toFrame7.fvC (C3.slide F.S.uV (F.S.eLC τ) η) =
      F.toFrame7.fvC F.S.uV + η • F.toFrame7.fvC (F.S.eLC τ) := by
    intro η; simp only [Frame7.fvC, C3.slide]; module
  have hnd := eventually_noHDNRim_slide_of_pairDirs (fun i => x (quad 4 0 5 6 i))
    (F.toFrame7.fvC F.S.uV) (F.toFrame7.fvC (F.S.eLC τ)) (fun i j l hl => by
      have hmem : l ∈ L := by
        simp only [L, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨i, j, hl⟩
      rw [hvec]
      exact hgood l hmem)
  have hpos : ∀ᶠ η in 𝓝[>] (0 : ℝ), (0 : ℝ) < η := self_mem_nhdsWithin
  have hux := eventually_pos_affine (A := -F.S.sp * F.S.tp + F.S.tp) (B := F.S.tm - F.S.tp)
    (Or.inl ux)
  obtain ⟨η, hη0, hc, hr1, hr2, hr3, hnd', hu⟩ :=
    (hpos.and ((F.S.lc_cyc_ev hV τ hτ2).and ((F.S.lc_rest_m2p_ev hV τ hτ2).and
      ((F.S.lc_rest_xa_ev hW τ hτ2).and ((F.S.lc_rest_m2m_ev hD2 hV τ).and
        ((by simpa only [efv] using hnd : ∀ᶠ η in 𝓝[>] (0 : ℝ),
          NoHDNRim (fun i => x (quad 4 0 5 6 i)) (F.toFrame7.fvC (C3.slide F.S.uV (F.S.eLC τ) η))).and
          hux)))))).exists
  have ho := hord τ (abs_lt.2 ⟨hτ1, by linarith⟩) η hη0
  rw [F.ptC_0, F.ptC_4, F.ptC_6] at ho
  refine F.toFrame7.vertex4_rim hx 4 0 5 6 Shape18.lcXb (F.S.lcMp) Shape18.lcV (F.S.lcMm)
    F.ptC_4 F.ptC_0 F.ptC_5 F.ptC_6 ∅ (by simp) 1 (Or.inl rfl)
    (C3.slide F.S.uV (F.S.eLC τ) η)
    (Or.inl (by simp only [C3.slide, Shape18.uV, Shape18.eLC]; exact hu.ne')) hc ?_ ?_ hnd' (by simp)
  · intro j' hj' h4 h0 h5 h6
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · rw [F.ptC_1]; exact hr1
    · rw [F.ptC_2]; exact hr3
    · rw [F.ptC_3]; exact hr2
    · exact absurd rfl h4
    · exact absurd rfl h5
    · exact absurd rfl h6
  · exact isRobustUnimodal_quad_between ho.1 ho.2

/-- `Vside_classH` without the `hlev` hypothesis: for `D2p > 0` on the level chord
`dV 0 = dV 6` use Theorem LC (`vNt_level_rupert`). -/
theorem Vside_classH_any (hx : Function.Injective x) (hVp : F.S.dp < F.S.A1 * F.S.tp)
    (h1 : F.S.am < F.S.bp) (h2 : F.S.ap < F.S.bm) (hD2 : F.S.D2p ≠ 0) (hH : F.ClassH) :
    IsRupert (Finset.univ.image x) := by
  by_cases hl : 0 < F.S.D2p ∧ F.dV 0 = F.dV 6
  · obtain ⟨hpos, hlev⟩ := hl
    have htp := F.S.tp_pos
    have hV := F.dV_pos_of hVp
    have hA1 := sub_pos.2 (F.A1_of h1)
    have hA1z : 0 < F.S.hm * F.S.tp - F.S.hp * (1 - F.S.tm) := sub_pos.2 (F.zFrame.A1_of h2)
    have hW : F.S.Wp < F.S.Vp := by
      unfold Shape18.Wp Shape18.Vp
      have := F.S.roof_p'
      nlinarith [mul_pos hA1z (sub_pos.2 (F.S.sp_lt)), F.S.kp_pos, F.S.tm_lt, F.S.tm_pos]
    exact F.vNt_level_rupert hx hpos hV hW hH hlev
  · exact F.Vside_classH hx hVp h1 h2 hD2 hH (fun hp e => hl ⟨hp, e⟩)

end Frame18

end Minimality.CaseC18

end
