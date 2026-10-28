module

public import Minimality.SlideE
public import Minimality.RimHDN
public import Minimality.CaseC20TestsNR

@[expose] public section

/-!
# Persistence of the double normal gives eventual freedom along a slide
(`FEWER-FACES-PROOFS.md` §22.3, Lemma 7.4; stage M3 of the Theorem 27.41 plan)

* `eventually_noHDNRim_slide`: if no double normal of the cycle `x` in space is perpendicular to
  `u₀` and `e` (`NoPersistHDN`), then the rim has no horizontal double normal at the slid view
  `u₀ + t e` for all small `t > 0` (the eventual non-vanishing step of `isRupert_of_slideP`).
  No hypothesis on `u₀` is needed: a view with a horizontal double normal is nonzero anyway.
* `Frame7.eventually_noHDNRim_slide`: the same for the `C3.slide` parametrization in frame
  coordinates.
* `Frame7.rupert_vertex_or_rim`, `Frame7.vertex4_rim`, `Frame20.tANR_rim`, `Frame20.tANR'`: the
  vertex bridge and `T_A`'s non-realizable slide with the rim-only hypothesis (`tANR_rim`:
  `NoHDNRim` of the rim `0 6 4 3` frequently along the slide; `tANR'`: `NoPersistHDN` of that rim).
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- **Persistence implies eventual freedom** (Lemma 7.4 along a slide): if the cycle `x` has no
double normal in space perpendicular to `u₀` and `e`, then for all small `t > 0` the rim has no
horizontal double normal at the view `u₀ + t e`. -/
theorem eventually_noHDNRim_slide {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (u₀ e : ℝ³)
    (hbad : NoPersistHDN x u₀ e) :
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
      (⟪l, u₀⟫ ≠ 0 ∨ ⟪l, e⟫ ≠ 0) → ⟪l, u₀ + t • e⟫ ≠ 0 := by
    refine eventually_all.mpr fun i => eventually_all.mpr fun j => ?_
    refine (eventually_all_finset _).mpr fun l _ => ?_
    by_cases hl : ⟪l, u₀⟫ ≠ 0 ∨ ⟪l, e⟫ ≠ 0
    · filter_upwards [hev1 l hl] with t ht _ using ht
    · filter_upwards with t h using absurd h hl
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
  by_cases hl' : ⟪l, u₀⟫ ≠ 0 ∨ ⟪l, e⟫ ≠ 0
  · exact ht i j l hl hl' hlu
  · push Not at hl'
    have hYY : Y' ≠ Y := by
      intro hc
      rw [hc, sub_self] at hYl
      exact (mem_filter.mp hl).2 ((smul_eq_zero.mp hYl.symm).resolve_left hr')
    refine hbad i j Y hY Y' hY' hYY ?_ ?_ hext
    · rw [hYl, real_inner_smul_left, hl'.1, mul_zero]
    · rw [hYl, real_inner_smul_left, hl'.2, mul_zero]

end Minimality

namespace Minimality.CaseC18.Frame7
open Minimality.CaseC09 Minimality.CaseC20 Filter
open scoped RealInnerProductSpace Topology
variable {x : Fin 7 → ℝ³} (F : Frame7 x)

/-- **Persistence implies eventual freedom, in frame coordinates**: the `C3.slide`
parametrization `u + η e` of the views. -/
theorem eventually_noHDNRim_slide {k : ℕ} [NeZero k] (c : ZMod k → Fin 7) (u e : C3)
    (hbad : NoPersistHDN (fun i => x (c i)) (F.fvC u) (F.fvC e)) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), NoHDNRim (fun i => x (c i)) (F.fvC (C3.slide u e η)) := by
  filter_upwards [Minimality.eventually_noHDNRim_slide (fun i => x (c i)) (F.fvC u) (F.fvC e)
    hbad] with η h
  have : F.fvC (C3.slide u e η) = F.fvC u + η • F.fvC e := by
    simp only [fvC, C3.slide]; module
  rw [this]; exact h

/-- **Theorem 18.1 (tie form) at a vertex view in frame coordinates, rim-only**: as
`rupert_vertex_or`, with the horizontal double normals excluded for the rim cycle only. -/
theorem rupert_vertex_or_rim (hx : Function.Injective x) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (c : ZMod k → Fin 7) (M : Finset (Fin 7)) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (u : C3)
    (hu : u.x ≠ 0 ∨ u.y ≠ 0 ∨ u.z ≠ 0) (hMc : ∀ m ∈ M, ∀ i, m ≠ c i)
    (hcyc : ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 →
      PS σ u ((F.ptC (c (i + 1))).sub (F.ptC (c i))) ((F.ptC (c j)).sub (F.ptC (c i))))
    (hrest : ∀ j' : Fin 7, j' ∉ M → (∀ jj, j' ≠ c jj) → ∀ i : ZMod k,
      PS σ u ((F.ptC (c (i + 1))).sub (F.ptC (c i))) ((F.ptC j').sub (F.ptC (c i))))
    (hz : IsRobustUnimodal (fun i => F.GG (F.ptC (c i)) u) ∨
      (k = 3 ∧ ∀ i j, F.GG (F.ptC (c i)) u = F.GG (F.ptC (c j)) u))
    (hnd : NoHDNRim (fun i => x (c i)) (F.fvC u))
    (hM : ∀ m ∈ M, ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      (F.ptC m).x = (F.ptC (c i)).x + s * ((F.ptC (c (i + 1))).x - (F.ptC (c i)).x) + δ * u.x ∧
      (F.ptC m).y = (F.ptC (c i)).y + s * ((F.ptC (c (i + 1))).y - (F.ptC (c i)).y) + δ * u.y ∧
      (F.ptC m).z = (F.ptC (c i)).z + s * ((F.ptC (c (i + 1))).z - (F.ptC (c i)).z) + δ * u.z) :
    IsRupert (Finset.univ.image x) := by
  classical
  set u0 : ℝ³ := F.fvC u with hu0def
  have hκ := F.kap_ne
  set t := σ * F.kap with ht
  set ε : ℝ := if 0 < t then 1 else -1 with hε
  have hεs : ε = 1 ∨ ε = -1 := sgn_cases t
  have hεε : ε * ε = 1 := sgn_sq t
  have hu0 : u0 ≠ 0 := by
    intro h0
    have := F.coord_zero (a := u.x) (b := u.y) (c := u.z) (by exact h0)
    rcases hu with h | h | h
    · exact h this.1
    · exact h this.2.1
    · exact h this.2.2
  have hu' : ε • u0 ≠ 0 := by
    intro h0
    rcases hεs with h | h <;> rw [h] at h0 <;> simp at h0 <;> exact hu0 h0
  have hconv : ∀ a b : C3, 0 < σ * Dc a b u → 0 < det3 (F.fvC a) (F.fvC b) (ε • u0) := by
    intro a b h
    have hk2 : 0 < F.kap ^ 2 := by positivity
    rw [det3_smul_right, hu0def, F.det3_fvC]
    refine sgn_pos t _ ?_
    have := mul_pos hk2 h
    calc 0 < F.kap ^ 2 * (σ * Dc a b u) := this
      _ = t * (F.kap * Dc a b u) := by rw [ht]; ring
  refine isRupert_of_vertexView_robust_or (Finset.univ.image x) (M.image x) (ε • u0) hu' (k := k) hk
    (fun i => x (c i)) (fun i => Finset.mem_image_of_mem x (Finset.mem_univ _)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro i hi
    obtain ⟨m, hm, hmi⟩ := Finset.mem_image.mp hi
    exact hMc m hm i (hx hmi)
  · intro i j hi hj
    show 0 < det3 (x (c (i + 1)) - x (c i)) (x (c j) - x (c i)) (ε • u0)
    rw [F.x_sub, F.x_sub]
    exact hconv _ _ (hcyc i j hi hj)
  · intro y hy hyM hyx i
    obtain ⟨j', -, rfl⟩ := Finset.mem_image.mp hy
    show 0 < det3 (x (c (i + 1)) - x (c i)) (x j' - x (c i)) (ε • u0)
    rw [F.x_sub, F.x_sub]
    exact hconv _ _ (hrest j' (fun h => hyM (Finset.mem_image_of_mem x h))
      (fun jj h => hyx jj (by simp [h])) i)
  · have hfun : (fun i : ZMod k => ε * (F.GG (F.ptC (c i)) u + ⟪F.base, u0⟫)) =
        fun i => ⟪x (c i), ε • u0⟫ := by
      funext i
      rw [real_inner_smul_right, hu0def, F.inner_x_fvC]; ring
    rcases hz with hz | ⟨hk3, hlev⟩
    · left
      have h1 := (robust_add_const hz (⟪F.base, u0⟫)).sigma hεs
      rw [← hfun]; exact h1
    · right
      refine ⟨hk3, fun i j => ?_⟩
      show ⟪x (c i), ε • u0⟫ = ⟪x (c j), ε • u0⟫
      have hi : ε * (F.GG (F.ptC (c i)) u + ⟪F.base, u0⟫) = ⟪x (c i), ε • u0⟫ := congrFun hfun i
      have hj : ε * (F.GG (F.ptC (c j)) u + ⟪F.base, u0⟫) = ⟪x (c j), ε • u0⟫ := congrFun hfun j
      rw [← hi, ← hj, hlev i j]
  · have hnd' : NoHDNRim (fun i => x (c i)) (ε • u0) := by
      rcases hεs with h | h
      · rw [h, one_smul]; exact hnd
      · rw [h, neg_one_smul]; exact hnd.neg
    exact hnd'
  · intro m hm
    obtain ⟨m0, hm0, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨i, s, δ, hs0, hs1, hδ, ex, ey, ez⟩ := hM m0 hm0
    refine ⟨i, s, ε * δ, hs0, hs1, ?_, ?_⟩
    · rcases hεs with h | h <;> rw [h] <;> simp [hδ]
    · have key : F.fvC ((F.ptC m0).sub (F.ptC (c i))) =
          s • F.fvC ((F.ptC (c (i + 1))).sub (F.ptC (c i))) + δ • u0 := by
        rw [← F.fvC_lin ((F.ptC (c (i + 1))).sub (F.ptC (c i))) u s δ]
        congr 1
        simp only [C3.sub]
        congr 1 <;> linarith
      rw [← F.x_sub, ← F.x_sub] at key
      show x m0 = x (c i) + s • (x (c (i + 1)) - x (c i)) + (ε * δ) • (ε • u0)
      rw [smul_smul, show ε * δ * ε = δ * (ε * ε) by ring, hεε, mul_one]
      have : x m0 = x (c i) + (x m0 - x (c i)) := by abel
      rw [this, key]; abel


/-- **The vertex bridge for four-corner rims** (Theorem 18.1 in its tie form at a view in frame
coordinates, `Frame7.rupert_vertex`), from the explicit strict tests. -/
theorem vertex4_rim (hx : Function.Injective x) (c0 c1 c2 c3 : Fin 7) (P0 P1 P2 P3 : C3)
    (e0 : F.ptC c0 = P0) (e1 : F.ptC c1 = P1) (e2 : F.ptC c2 = P2) (e3 : F.ptC c3 = P3)
    (M : Finset (Fin 7)) (hMc : ∀ m ∈ M, m ≠ c0 ∧ m ≠ c1 ∧ m ≠ c2 ∧ m ≠ c3)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (u : C3) (hu : u.x ≠ 0 ∨ u.y ≠ 0 ∨ u.z ≠ 0)
    (hc : PCyc4 σ u P0 P1 P2 P3)
    (hr : ∀ j' : Fin 7, j' ∉ M → j' ≠ c0 → j' ≠ c1 → j' ≠ c2 → j' ≠ c3 →
      PRest4 σ u P0 P1 P2 P3 (F.ptC j'))
    (hz : IsRobustUnimodal (quad (F.GG P0 u) (F.GG P1 u) (F.GG P2 u) (F.GG P3 u)))
    (hnd : NoHDNRim (fun i => x (quad c0 c1 c2 c3 i)) (F.fvC u))
    (hM : ∀ m ∈ M, ∃ i : ZMod 4, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      (F.ptC m).x = (quad P0 P1 P2 P3 i).x + s * ((quad P0 P1 P2 P3 (i + 1)).x -
        (quad P0 P1 P2 P3 i).x) + δ * u.x ∧
      (F.ptC m).y = (quad P0 P1 P2 P3 i).y + s * ((quad P0 P1 P2 P3 (i + 1)).y -
        (quad P0 P1 P2 P3 i).y) + δ * u.y ∧
      (F.ptC m).z = (quad P0 P1 P2 P3 i).z + s * ((quad P0 P1 P2 P3 (i + 1)).z -
        (quad P0 P1 P2 P3 i).z) + δ * u.z) :
    IsRupert (Finset.univ.image x) := by
  have hc' : ∀ i, F.ptC (quad c0 c1 c2 c3 i) = quad P0 P1 P2 P3 i := by
    intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp [quad_0, quad_1, quad_2, quad_3, e0, e1, e2, e3]
  refine F.rupert_vertex_or_rim hx (k := 4) (by norm_num) (quad c0 c1 c2 c3) M σ hσ u hu ?_ ?_ ?_ ?_ hnd ?_
  · intro m hm i
    obtain ⟨a0, a1, a2, a3⟩ := hMc m hm
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp [quad_0, quad_1, quad_2, quad_3, a0, a1, a2, a3]
  · intro i j h1 h2
    simp only [hc']
    exact hc.all i j h1 h2
  · intro j' hj' hjc i
    simp only [hc']
    refine (hr j' hj' ?_ ?_ ?_ ?_).all i
    · exact fun h => hjc 0 (by simp [quad_0, h])
    · exact fun h => hjc 1 (by simp [quad_1, h])
    · exact fun h => hjc 2 (by simp [quad_2, h])
    · exact fun h => hjc 3 (by simp [quad_3, h])
  · have : (fun i : ZMod 4 => F.GG (F.ptC (quad c0 c1 c2 c3 i)) u) =
        quad (F.GG P0 u) (F.GG P1 u) (F.GG P2 u) (F.GG P3 u) := by
      funext i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp [quad_0, quad_1, quad_2, quad_3, e0, e1, e2, e3]
    rw [this]; exact Or.inl hz
  · intro m hm
    obtain ⟨i, s, δ, hs0, hs1, hδ, ex, ey, ez⟩ := hM m hm
    refine ⟨i, s, δ, hs0, hs1, hδ, ?_, ?_, ?_⟩
    · rw [hc' i, hc' (i + 1)]; exact ex
    · rw [hc' i, hc' (i + 1)]; exact ey
    · rw [hc' i, hc' (i + 1)]; exact ez

end Minimality.CaseC18.Frame7

namespace Minimality.CaseC20

open Finset Filter Minimality.CaseC09 Minimality.CaseC18
open scoped RealInnerProductSpace Topology

/-- `T_A` for `b+ < a-` along the slide of the circle of the face `0135`, with the rim-only
hypothesis: no horizontal double normal of the rim `0 6 4 3` at arbitrarily small slid views. -/
theorem Frame20.tANR_rim {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x) (hA1 : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm)
    (hA : F.dep F.S.u_tANR 0 < F.dep F.S.u_tANR 6 ∨ F.dep F.S.u_tANR 0 < F.dep F.S.u_tANR 3 ∨ F.dep F.S.u_tANR 4 < F.dep F.S.u_tANR 6 ∨ F.dep F.S.u_tANR 4 < F.dep F.S.u_tANR 3) (hB : F.dep F.S.u_tANR 6 < F.dep F.S.u_tANR 0 ∨ F.dep F.S.u_tANR 3 < F.dep F.S.u_tANR 0 ∨ F.dep F.S.u_tANR 6 < F.dep F.S.u_tANR 4 ∨ F.dep F.S.u_tANR 3 < F.dep F.S.u_tANR 4)
    (hnd : ∃ᶠ η in 𝓝[>] (0 : ℝ), NoHDNRim (fun i : ZMod 4 => x (quad 0 6 4 3 i)) (F.toFrame7.fvC (C3.slide F.S.u_tANR ⟨0, 0, -1⟩ η))) :
    IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  have hcev := (tANR_pcyc F.S hA1).ev ⟨0, 0, -1⟩
  have hrev2 := (tANR_prest2 F.S hA1).ev ⟨0, 0, -1⟩
  have hmev5 := tANR_mid5 F.S hA1
  have hmev1 := tANR_mid1 F.S hA1
  have hzev : ∀ᶠ η in 𝓝[>] (0 : ℝ), IsRobustUnimodal (quad (F.dep (C3.slide F.S.u_tANR ⟨0, 0, -1⟩ η) 0) (F.dep (C3.slide F.S.u_tANR ⟨0, 0, -1⟩ η) 6) (F.dep (C3.slide F.S.u_tANR ⟨0, 0, -1⟩ η) 4) (F.dep (C3.slide F.S.u_tANR ⟨0, 0, -1⟩ η) 3)) := by
    have h0 := Q4_ev_strict (z := quad (F.dep F.S.u_tANR 0) (F.dep F.S.u_tANR 6) (F.dep F.S.u_tANR 4) (F.dep F.S.u_tANR 3)) (w := quad (F.dep ⟨0, 0, -1⟩ 0) (F.dep ⟨0, 0, -1⟩ 6) (F.dep ⟨0, 0, -1⟩ 4) (F.dep ⟨0, 0, -1⟩ 3))
      (by simpa only [quad_0, quad_1, quad_2, quad_3] using hA)
      (by simpa only [quad_0, quad_1, quad_2, quad_3] using hB)
    filter_upwards [h0] with η hη
    obtain ⟨hA', hB'⟩ := hη
    simp only [quad_0, quad_1, quad_2, quad_3] at hA' hB'
    simp only [Frame20.dep_slide]
    exact robust_quad_of_nws hA' hB'
  obtain ⟨η, hnd', hc, hr2, hm5, hm1, hz⟩ := (hnd.and_eventually ((hcev).and ((hrev2).and ((hmev5).and ((hmev1).and (hzev)))))).exists
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  refine F.toFrame7.vertex4_rim hx 0 6 4 3 _ _ _ _ (F.ptC_0) (F.ptC_6) (F.ptC_4) (F.ptC_3) ({5, 1} : Finset (Fin 7)) ?_ 1 (Or.inl rfl) (C3.slide F.S.u_tANR ⟨0, 0, -1⟩ η) ?_ hc ?_ ?_ hnd' ?_
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl <;> decide
  · exact (Or.inl (by simp only [C3.slide, Shape20.u_tANR]; intro h0; linarith [htp1, h0]))
  · intro j' hjM h0 h1 h2 h3
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · exact absurd (by simp) hjM
    · rw [F.ptC_2]; exact hr2
    · exact absurd rfl h3
    · exact absurd rfl h2
    · exact absurd (by simp) hjM
    · exact absurd rfl h1
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using hz
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · obtain ⟨s, δ, hs0, hs1, hδ, ex, ey, ez⟩ := hm5
      refine ⟨3, s, δ, hs0, hs1, hδ, ?_, ?_, ?_⟩ <;>
        simp only [b3, quad_0, quad_3, F.ptC_5] at ex ey ez ⊢ <;>
        linarith
    · obtain ⟨s, δ, hs0, hs1, hδ, ex, ey, ez⟩ := hm1
      refine ⟨3, s, δ, hs0, hs1, hδ, ?_, ?_, ?_⟩ <;>
        simp only [b3, quad_0, quad_3, F.ptC_1] at ex ey ez ⊢ <;>
        linarith


/-- `T_A` for `b+ < a-` along the slide of the circle of the face `0135`, with a rim-only
persistence hypothesis: no double normal of the rim `0 6 4 3` in space is perpendicular to the
view `u_tANR` and the slide direction `(0, 0, -1)`. -/
theorem Frame20.tANR' {x : Fin 7 → ℝ³} (F : Frame20 x) (hx : Function.Injective x) (hA1 : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm)
    (hA : F.dep F.S.u_tANR 0 < F.dep F.S.u_tANR 6 ∨ F.dep F.S.u_tANR 0 < F.dep F.S.u_tANR 3 ∨ F.dep F.S.u_tANR 4 < F.dep F.S.u_tANR 6 ∨ F.dep F.S.u_tANR 4 < F.dep F.S.u_tANR 3) (hB : F.dep F.S.u_tANR 6 < F.dep F.S.u_tANR 0 ∨ F.dep F.S.u_tANR 3 < F.dep F.S.u_tANR 0 ∨ F.dep F.S.u_tANR 6 < F.dep F.S.u_tANR 4 ∨ F.dep F.S.u_tANR 3 < F.dep F.S.u_tANR 4)
    (hnp : NoPersistHDN (fun i : ZMod 4 => x (quad 0 6 4 3 i)) (F.toFrame7.fvC F.S.u_tANR)
      (F.toFrame7.fvC ⟨0, 0, -1⟩)) :
    IsRupert (Finset.univ.image x) :=
  F.tANR_rim hx hA1 hA hB
    (F.toFrame7.eventually_noHDNRim_slide (quad 0 6 4 3) _ _ hnp).frequently

end Minimality.CaseC20

end
