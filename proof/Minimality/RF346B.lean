module

public import Minimality.RF346B_A

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true

open scoped RealInnerProductSpace Topology
open Filter Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.RimFromSigns
open Minimality.T24.Q45 Minimality.T24.R012

namespace Minimality.T24.R012

variable {x : Fin 7 → ℝ³}

private lemma rf_view_inner (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (b c : ℝ³) (ε : ℝ) :
    ⟪F.N t, b + ε • c⟫ = ⟪F.N t, b⟫ + ε * ⟪F.N t, c⟫ := by
  rw [inner_add_right, real_inner_smul_right]

/-- Rim data for the 5-rim `(1,6,3,5,2)` from the facet signs `N1,N2,N3,N8 > 0`, `N5,N6,N7 < 0`
at a view in the plane of 012. -/
theorem rf346b_rim_data (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hN0 : ⟪F.N 0, u⟫ = 0) (h1 : 0 < ⟪F.N 1, u⟫) (h2 : 0 < ⟪F.N 2, u⟫) (h3 : 0 < ⟪F.N 3, u⟫)
    (h5 : ⟪F.N 5, u⟫ < 0) (h6 : ⟪F.N 6, u⟫ < 0) (h7 : ⟪F.N 7, u⟫ < 0) (h8 : 0 < ⟪F.N 8, u⟫) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧ StrictConvex5 (fun i => x (rimN i)) u ρ ∧
      (∀ i : ZMod 5, 0 < ρ * det3 (x (rimN (i + 1)) - x (rimN i)) (x 4 - x (rimN i)) u) := by
  have hne_01 : cross u (x 6 - x 1) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 1 1 6 (by decide) (by decide) h1.ne' 0 (by decide) (by decide)
  have hne_12 : cross u (x 3 - x 6) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 8 6 3 (by decide) (by decide) h8.ne' 1 (by decide) (by decide)
  have hne_23 : cross u (x 5 - x 3) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 3 3 5 (by decide) (by decide) h3.ne' 7 (by decide) (by decide)
  have hne_34 : cross u (x 2 - x 5) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 2 5 2 (by decide) (by decide) h2.ne' 3 (by decide) (by decide)
  have hne_40 : cross u (x 1 - x 2) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 5 2 1 (by decide) (by decide) h5.ne 2 (by decide) (by decide)
  exact fiveRim_of_signs F (u := u) rimN 4 5 1 7 8 6 3 6 2 0
    (by decide) (by decide) hN0
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨h5, h1⟩
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨h7, h8⟩
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨h6, h3⟩
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨h6, h2⟩
    hne_01 hne_12 hne_23 hne_34 hne_40
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

/-- Orientation: `ρ Ω < 0` for the view `A (x0-x1) + B (x2-x1)`, `A > 0`. -/
theorem rf346b_rho_omega {u : ℝ³} {A B ρ : ℝ} (hA : 0 < A)
    (hu : u = A • (x 0 - x 1) + B • (x 2 - x 1))
    (hc : StrictConvex5 (fun i => x (rimN i)) u ρ) :
    ρ * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) < 0 := by
  have h := hc 4 1 (by decide) (by decide)
  have e : det3 (x (rimN (4 + 1)) - x (rimN 4)) (x (rimN 1) - x (rimN 4)) u =
      -A * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
    change det3 (x 1 - x 2) (x 6 - x 2) u = _
    rw [hu]
    simp only [det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  rw [e] at h
  have h1 : 0 < ρ * (-A * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)) := h
  by_contra hn; push Not at hn
  nlinarith [mul_nonneg hA.le hn]

/-- **Core of the 5-rim `(1,6,3,5,2)` leaf** (chord `2 → 1` of facet 012, middle `0`, vertex `4` inside):
a base view `b` in the plane of 012 and a tilt `c` in that plane, facet signs `N1,N2,N3,N8 > 0`,
`N5,N6,N7 < 0` at `b + ε c` (ties at `b` broken by `c`), the K5 lexicographic rule-outs (or a
depth-separated corner) at the base view, tie genericity and the Lemma H foot data. -/
theorem rf346b_core (F : S0xFac 9 s0x_S24 x) (b c : ℝ³)
    (hb0 : ⟪F.N 0, b⟫ = 0) (hc0 : ⟪F.N 0, c⟫ = 0)
    (h1 : 0 < ⟪F.N 1, b⟫ ∨ (⟪F.N 1, b⟫ = 0 ∧ 0 < ⟪F.N 1, c⟫))
    (h2 : 0 < ⟪F.N 2, b⟫ ∨ (⟪F.N 2, b⟫ = 0 ∧ 0 < ⟪F.N 2, c⟫))
    (h3 : 0 < ⟪F.N 3, b⟫ ∨ (⟪F.N 3, b⟫ = 0 ∧ 0 < ⟪F.N 3, c⟫))
    (h8 : 0 < ⟪F.N 8, b⟫ ∨ (⟪F.N 8, b⟫ = 0 ∧ 0 < ⟪F.N 8, c⟫))
    (h5 : ⟪F.N 5, b⟫ < 0 ∨ (⟪F.N 5, b⟫ = 0 ∧ ⟪F.N 5, c⟫ < 0))
    (h6 : ⟪F.N 6, b⟫ < 0 ∨ (⟪F.N 6, b⟫ = 0 ∧ ⟪F.N 6, c⟫ < 0))
    (h7 : ⟪F.N 7, b⟫ < 0 ∨ (⟪F.N 7, b⟫ = 0 ∧ ⟪F.N 7, c⟫ < 0))
    (hU : (¬ LexAltIncr (fun i => x (rimN i)) b c 0 ∧ ¬ LexAltDecr (fun i => x (rimN i)) b c 1 ∧
        ¬ LexAltIncr (fun i => x (rimN i)) b c 2 ∧ ¬ LexAltDecr (fun i => x (rimN i)) b c 3 ∧
        ((0 < det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 3 - x 1) (x 5 - x 6) (x 1 - x 6) ∧
            ¬ LexAltDecr (fun i => x (rimN i)) b c 4) ∨
          (det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 3 - x 1) (x 5 - x 6) (x 1 - x 6) < 0 ∧
            ¬ LexAltIncr (fun i => x (rimN i)) b c 4))) ∨
      ∃ m : ZMod 5,
        DSd (fun i => x (rimN i)) (-det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)) b c m ∨
        DSd (fun i => x (rimN i)) (det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)) (-b) (-c) m)
    (hgen : ∀ i j : ZMod 5, i ≠ j →
      ⟪x (rimN i) - x (rimN j), b⟫ ≠ 0 ∨ ⟪x (rimN i) - x (rimN j), c⟫ ≠ 0)
    (w : ZMod 5) (hw : w = 1 ∨ w = 2 ∨ w = 3)
    (hfar : ∀ m : ZMod 5, m ≠ w → rimN m ∉ s0x_S24 0 → F.f 0 (x (rimN w)) < F.f 0 (x (rimN m)))
    (hoff : ⟪F.N 0, cross (x 1 - x 2) (x (rimN w) - x 2)⟫ ≠ 0 ∨
      ⟪x (rimN w) - x 2, x 1 - x 2⟫ < 0 ∨ ⟪x (rimN w) - x 1, x 2 - x 1⟫ < 0) :
    FaceChordView F 0 := by
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) with hΩ
  set p : ZMod 5 → ℝ³ := fun i => x (rimN i) with hp
  have ev0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have evs : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 1, b + ε • c⟫ ∧ 0 < ⟪F.N 2, b + ε • c⟫ ∧
      0 < ⟪F.N 3, b + ε • c⟫ ∧ ⟪F.N 5, b + ε • c⟫ < 0 ∧ ⟪F.N 6, b + ε • c⟫ < 0 ∧
      ⟪F.N 7, b + ε • c⟫ < 0 ∧ 0 < ⟪F.N 8, b + ε • c⟫ := by
    filter_upwards [evp' _ _ _ h1, evp' _ _ _ h2, evp' _ _ _ h3, evn' _ _ _ h5, evn' _ _ _ h6,
      evn' _ _ _ h7, evp' _ _ _ h8] with ε e1 e2 e3 e5 e6 e7 e8
    exact ⟨e1, e2, e3, e5, e6, e7, e8⟩
  have hN0 : ∀ ε : ℝ, ⟪F.N 0, b + ε • c⟫ = 0 := by
    intro ε; rw [rf_view_inner, hb0, hc0]; ring
  have hcvx : ∀ᶠ ε in 𝓝[>] (0 : ℝ), StrictConvex5 p (b + ε • c) (-Ω) := by
    filter_upwards [evs] with ε ⟨e1, e2, e3, e5, e6, e7, e8⟩
    obtain ⟨A, B, hA, -, -, hu⟩ := rf346b_coords F (hN0 ε) e5 e1 e2
    obtain ⟨ρ, -, hcv, -⟩ := rf346b_rim_data F (hN0 ε) e1 e2 e3 e5 e6 e7 e8
    exact strictConvex5_of_rho (rf346b_rho_omega hA hu hcv) hcv
  obtain ⟨k0, k1, k2, k3⟩ := rf346b_sub_kappa_sign F
  have hinj := ev_injective b c p hgen
  have hZ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Function.Injective (fun i => ⟪p i, b + ε • c⟫) ∧
      UniOrSep p (b + ε • c) := by
    rcases hU with ⟨hD0, hI1, hD2, hI3, h4⟩ | ⟨m, hm | hm⟩
    · have hrules : ∀ m : ZMod 5, ((-Ω) * quadKappa (subquad p m) < 0 ∧ ¬ LexAltDecr p b c m) ∨
          (0 < (-Ω) * quadKappa (subquad p m) ∧ ¬ LexAltIncr p b c m) := by
        intro m
        rcases zmod5_cases m with rfl | rfl | rfl | rfl | rfl
        · exact Or.inr ⟨k0, hD0⟩
        · exact Or.inl ⟨k1, hI1⟩
        · exact Or.inr ⟨k2, hD2⟩
        · exact Or.inl ⟨k3, hI3⟩
        · rcases h4 with ⟨hk, hn⟩ | ⟨hk, hn⟩
          · refine Or.inl ⟨?_, hn⟩
            change (-Ω) * det3 (x 3 - x 1) (x 5 - x 6) (x 1 - x 6) < 0; linarith
          · refine Or.inr ⟨?_, hn⟩
            change 0 < (-Ω) * det3 (x 3 - x 1) (x 5 - x 6) (x 1 - x 6); linarith
      filter_upwards [ev_unimodal_five b c (-Ω) hcvx hinj hrules] with ε ⟨hi, hcu⟩
      exact ⟨hi, Or.inl (strictUnimodal_of_cyclic (by decide) hcu)⟩
    · filter_upwards [ev_ds p (-Ω) b c m hcvx hm, hinj] with ε ⟨a, c', h⟩ hi
      exact ⟨hi, Or.inr ⟨a, c', h⟩⟩
    · have hcn : ∀ᶠ ε in 𝓝[>] (0 : ℝ), StrictConvex5 p (-b + ε • -c) (-(-Ω)) := by
        filter_upwards [hcvx] with ε h
        have := strictConvex5_neg h
        rwa [show -(b + ε • c) = -b + ε • -c by rw [smul_neg, neg_add]] at this
      rw [neg_neg] at hcn
      filter_upwards [ev_ds p Ω (-b) (-c) m hcn hm, hinj] with ε ⟨a, c', h⟩ hi
      refine ⟨hi, Or.inr ⟨a, c', ?_⟩⟩
      have := h.neg
      rwa [show -(-b + ε • -c) = b + ε • c by rw [smul_neg, neg_add, neg_neg, neg_neg]] at this
  obtain ⟨ε, ⟨e1, e2, e3, e5, e6, e7, e8⟩, hε, hinj', hz⟩ := (evs.and (ev0.and hZ)).exists
  obtain ⟨A, B, hA, hB, hAB, hu⟩ := rf346b_coords F (hN0 ε) e5 e1 e2
  obtain ⟨ρ, hρ, hcv, hin4⟩ := rf346b_rim_data F (hN0 ε) e1 e2 e3 e5 e6 e7 e8
  have hε' : (0 : ℝ) < ε := hε
  have hw' : rimN w ∉ s0x_S24 0 := by rcases hw with rfl | rfl | rfl <;> decide
  refine ⟨b + ε • c, 5, inferInstance, rimN, 4, w, ρ, hN0 ε, by decide, by decide, by decide, hρ,
    hcv, ?_, ?_, hinj', hz, hw', hfar, hoff⟩
  · intro q hq0 hqr i
    have hq4 : q = 4 := by
      fin_cases q <;> first | rfl | (exfalso; revert hq0; decide) | (exfalso; exact hqr 1 rfl) |
        (exfalso; exact hqr 2 rfl) | (exfalso; exact hqr 3 rfl)
    subst hq4
    exact hin4 i
  · intro q hq0 hqr
    have hq0' : q = 0 := by
      fin_cases q <;> first | rfl | (exfalso; revert hq0; decide) | (exfalso; exact hqr 0 rfl) |
        (exfalso; exact hqr 4 rfl)
    subst hq0'
    have hAne : A ≠ 0 := hA.ne'
    refine ⟨(A + B) / A, 1 / A, by positivity, ?_, by positivity, ?_⟩
    · rw [div_lt_one hA]; linarith
    · change x 0 = x 2 + ((A + B) / A) • (x 1 - x 2) + (1 / A) • (b + ε • c)
      rw [hu]
      ext j
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      field_simp
      ring


/-- The root of facet 346 on the circle of 012 (division free, a positive multiple of
`(x0-x1) + t (x2-x1)` with `t = -N8(x0-x1)/N8(x2-x1)`) when `f8 x1 < f8 x2`. -/
noncomputable def rootB (F : S0xFac 9 s0x_S24 x) : ℝ³ :=
  (F.f 8 (x 2) - F.f 8 (x 1)) • (x 0 - x 1) - (F.f 8 (x 0) - F.f 8 (x 1)) • (x 2 - x 1)

theorem rootB_eq (F : S0xFac 9 s0x_S24 x) :
    rootB F = (F.f 8 (x 2) - F.f 8 (x 1)) • (x 0 - x 1) +
      (-(F.f 8 (x 0) - F.f 8 (x 1))) • (x 2 - x 1) := by
  simp only [rootB, neg_smul, sub_eq_add_neg]

theorem inner_N8_rootB (F : S0xFac 9 s0x_S24 x) : ⟪F.N 8, rootB F⟫ = 0 := by
  rw [rootB_eq, rf346b_inner_plane]; ring

/-- **The 5-rim leaf `q012_f346_5`** (`s:f235+` on 016 via `Sym24`, `t:f346+` on 012 here): the facet-346
root `b = rootB F` on the circle of 012 lies in the window `t ∈ (-1, 0)` (`f8 x1 < f8 x0 < f8 x2`), and
the view `b + ε (x2 - x1)` has the 5-rim `(1,6,3,5,2)` with chord `2 → 1` and middle `0`. Case
conditions: the facet signs `N3 > 0`, `N6, N7 < 0` at the root (`N1, N2 > 0`, `N5, N8` are automatic from the
window), the K5 lexicographic rule-outs (or a depth-separated corner), genericity and the Lemma H data. -/
theorem q012_f346_5 (F : S0xFac 9 s0x_S24 x)
    (hlo : F.f 8 (x 1) < F.f 8 (x 0)) (hhi : F.f 8 (x 0) < F.f 8 (x 2))
    (h3 : 0 < ⟪F.N 3, rootB F⟫ ∨ (⟪F.N 3, rootB F⟫ = 0 ∧ 0 < ⟪F.N 3, x 2 - x 1⟫))
    (h6 : ⟪F.N 6, rootB F⟫ < 0 ∨ (⟪F.N 6, rootB F⟫ = 0 ∧ ⟪F.N 6, x 2 - x 1⟫ < 0))
    (h7 : ⟪F.N 7, rootB F⟫ < 0 ∨ (⟪F.N 7, rootB F⟫ = 0 ∧ ⟪F.N 7, x 2 - x 1⟫ < 0))
    (hU : (¬ LexAltIncr (fun i => x (rimN i)) (rootB F) (x 2 - x 1) 0 ∧
        ¬ LexAltDecr (fun i => x (rimN i)) (rootB F) (x 2 - x 1) 1 ∧
        ¬ LexAltIncr (fun i => x (rimN i)) (rootB F) (x 2 - x 1) 2 ∧
        ¬ LexAltDecr (fun i => x (rimN i)) (rootB F) (x 2 - x 1) 3 ∧
        ((0 < det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 3 - x 1) (x 5 - x 6) (x 1 - x 6) ∧
            ¬ LexAltDecr (fun i => x (rimN i)) (rootB F) (x 2 - x 1) 4) ∨
          (det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 3 - x 1) (x 5 - x 6) (x 1 - x 6) < 0 ∧
            ¬ LexAltIncr (fun i => x (rimN i)) (rootB F) (x 2 - x 1) 4))) ∨
      ∃ m : ZMod 5,
        DSd (fun i => x (rimN i)) (-det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)) (rootB F) (x 2 - x 1) m ∨
        DSd (fun i => x (rimN i)) (det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1))
          (-rootB F) (-(x 2 - x 1)) m)
    (hgen : ∀ i j : ZMod 5, i ≠ j →
      ⟪x (rimN i) - x (rimN j), rootB F⟫ ≠ 0 ∨ ⟪x (rimN i) - x (rimN j), x 2 - x 1⟫ ≠ 0)
    (w : ZMod 5) (hw : w = 1 ∨ w = 2 ∨ w = 3)
    (hfar : ∀ m : ZMod 5, m ≠ w → rimN m ∉ s0x_S24 0 → F.f 0 (x (rimN w)) < F.f 0 (x (rimN m)))
    (hoff : ⟪F.N 0, cross (x 1 - x 2) (x (rimN w) - x 2)⟫ ≠ 0 ∨
      ⟪x (rimN w) - x 2, x 1 - x 2⟫ < 0 ∨ ⟪x (rimN w) - x 1, x 2 - x 1⟫ < 0) :
    FaceChordView F 0 := by
  have hA : 0 < F.f 8 (x 2) - F.f 8 (x 1) := by linarith
  have hB : -(F.f 8 (x 0) - F.f 8 (x 1)) < 0 := by linarith
  have inn : ∀ t : Fin 9, ⟪F.N t, rootB F⟫ = (F.f 8 (x 2) - F.f 8 (x 1)) * (F.f t (x 0) - F.f t (x 1)) +
      (-(F.f 8 (x 0) - F.f 8 (x 1))) * (F.f t (x 2) - F.f t (x 1)) := by
    intro t; rw [rootB_eq, rf346b_inner_plane]
  have hc : ∀ t : Fin 9, ⟪F.N t, x 2 - x 1⟫ = F.f t (x 2) - F.f t (x 1) := fun t => F.inner_sub t 2 1
  have z0 := F.zero 0 0 (by decide); have z1 := F.zero 0 1 (by decide); have z2 := F.zero 0 2 (by decide)
  refine rf346b_core F (rootB F) (x 2 - x 1) ?_ ?_ ?_ ?_ h3 ?_ ?_ h6 h7 hU hgen w hw hfar hoff
  · rw [inn, z0, z1, z2]; ring
  · rw [hc, z1, z2]; ring
  · left
    rw [inn, F.zero 1 0 (by decide), F.zero 1 1 (by decide)]
    nlinarith [F.neg 1 2 (by decide)]
  · left
    rw [inn]
    have f2 := F.neg 2 1 (by decide)
    rw [F.zero 2 0 (by decide), F.zero 2 2 (by decide)]
    nlinarith
  · right; refine ⟨inner_N8_rootB F, ?_⟩; rw [hc]; linarith
  · left
    rw [inn, F.zero 5 1 (by decide), F.zero 5 2 (by decide)]
    nlinarith [F.neg 5 0 (by decide)]

end Minimality.T24.R012
