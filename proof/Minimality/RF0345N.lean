module

public import Minimality.R012W
public import Minimality.R012F

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace Topology
open Filter Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.RimFromSigns
open Minimality.T24.Q45 Minimality.T24.R012

namespace Minimality.T24.R012
variable {x : Fin 7 → ℝ³}

/-- Root of the 0345 facet (`N3`) on the 012 chord line `u0 t = (x0 - x1) + t (x2 - x1)`. -/
noncomputable def t3n (F : S0xFac 9 s0x_S24 x) : ℝ :=
  - ⟪F.N 3, x 0 - x 1⟫ / ⟪F.N 3, x 2 - x 1⟫

theorem rf0345n_inner_N3 (F : S0xFac 9 s0x_S24 x) (t : ℝ) :
    ⟪F.N 3, u0 x t⟫ = ⟪F.N 3, x 0 - x 1⟫ + t * ⟪F.N 3, x 2 - x 1⟫ := by
  simp only [u0, inner_add_right, real_inner_smul_right]

/-- For `t3 < -1`: `N3` vanishes at `u0 t3` and increases strictly along the chord line. -/
theorem rf0345n_t3 (F : S0xFac 9 s0x_S24 x) (h : t3n F < -1) :
    ⟪F.N 3, u0 x (t3n F)⟫ = 0 ∧ 0 < ⟪F.N 3, x 2 - x 1⟫ := by
  have ha : 0 < ⟪F.N 3, x 0 - x 1⟫ := by
    have h0 := inner_N3_u0 F 0
    rw [rf0345n_inner_N3] at h0
    have := lambda3_pos F
    unfold lambda3 at this
    linarith
  have hs : 0 < ⟪F.N 3, x 2 - x 1⟫ := by
    rcases lt_trichotomy ⟪F.N 3, x 2 - x 1⟫ 0 with hn | hn | hn
    · exfalso
      have : 0 < t3n F := by
        unfold t3n; exact div_pos_of_neg_of_neg (by linarith) hn
      linarith
    · exfalso
      have : t3n F = 0 := by unfold t3n; rw [hn]; simp
      linarith
    · exact hn
  refine ⟨?_, hs⟩
  rw [rf0345n_inner_N3]; unfold t3n
  have := hs.ne'
  field_simp; ring

/-- `Ω * κ < 0` for the quad `(0,1,6,4)`: `κ` is the signed volume of the tetrahedron `0 1 6 4`, `Ω` that of
`0 1 6 2`, and `2`, `4` lie on the same side of facet 016. -/
theorem omega_kappa0164 (F : S0xFac 9 s0x_S24 x) :
    det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 6 - x 0) (x 4 - x 1) (x 0 - x 1) < 0 := by
  have hΩ := omega_ne_zero F
  have hN1 : F.N 1 ≠ 0 := N_ne_zero F 1 2 (by decide) 0 (by decide)
  obtain ⟨k, hk⟩ := cross_smul_N F 1 (x 0 - x 1) (x 6 - x 1)
    (by rw [F.inner_sub, F.zero 1 0 (by decide), F.zero 1 1 (by decide)]; ring)
    (by rw [F.inner_sub, F.zero 1 6 (by decide), F.zero 1 1 (by decide)]; ring) hN1
  have f2 : F.f 1 (x 2) < 0 := F.neg 1 2 (by decide)
  have f4 : F.f 1 (x 4) < 0 := F.neg 1 4 (by decide)
  have i2 : ⟪F.N 1, x 2 - x 1⟫ = F.f 1 (x 2) := by
    rw [F.inner_sub, F.zero 1 1 (by decide)]; ring
  have i4 : ⟪F.N 1, x 4 - x 1⟫ = F.f 1 (x 4) := by
    rw [F.inner_sub, F.zero 1 1 (by decide)]; ring
  have eΩ : det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) = - (k * F.f 1 (x 2)) := by
    have : det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) = - det3 (x 0 - x 1) (x 6 - x 1) (x 2 - x 1) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [this]
    unfold det3; rw [hk, real_inner_smul_left, i2]
  have eκ : det3 (x 6 - x 0) (x 4 - x 1) (x 0 - x 1) = k * F.f 1 (x 4) := by
    have : det3 (x 6 - x 0) (x 4 - x 1) (x 0 - x 1) = det3 (x 0 - x 1) (x 6 - x 1) (x 4 - x 1) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [this]
    unfold det3; rw [hk, real_inner_smul_left, i4]
  have hk0 : k ≠ 0 := by
    intro h0; apply hΩ; rw [eΩ, h0]; ring
  rw [eΩ, eκ]
  have hk2 : 0 < k ^ 2 := sq_pos_of_ne_zero hk0
  nlinarith [mul_pos hk2 (mul_pos_of_neg_of_neg f2 f4)]

theorem det3_x01_x06_u0 (t : ℝ) : det3 (x 1 - x 0) (x 6 - x 0) (u0 x t) =
    t * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
  simp only [u0, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring

/-- Rim data for the quad `(0,1,6,4)` at `u0 t`, `t < 0`, from the facet signs (chord `0 → 1` on facet 012,
ridges `1 6` (facets 5 | 1), `6 4` (8 | 4), `4 0` (3 | 4)); interior vertices `3`, `5`. -/
theorem quadRim0164 (F : S0xFac 9 s0x_S24 x) (t : ℝ) (ht : t < 0)
    (hN1 : 0 < ⟪F.N 1, u0 x t⟫) (hN5 : ⟪F.N 5, u0 x t⟫ < 0) (hN4 : 0 < ⟪F.N 4, u0 x t⟫)
    (hN8 : ⟪F.N 8, u0 x t⟫ < 0) (hN3 : ⟪F.N 3, u0 x t⟫ < 0) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧ 0 < ρ * (-det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)) ∧
      (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
        0 < ρ * det3 (quad (x 0) (x 1) (x 6) (x 4) (i + 1) - quad (x 0) (x 1) (x 6) (x 4) i)
          (quad (x 0) (x 1) (x 6) (x 4) j - quad (x 0) (x 1) (x 6) (x 4) i) (u0 x t)) ∧
      (∀ y : Fin 7, y ∉ s0x_S24 0 → y ≠ 6 → y ≠ 4 → ∀ i : ZMod 4,
        0 < ρ * det3 (quad (x 0) (x 1) (x 6) (x 4) (i + 1) - quad (x 0) (x 1) (x 6) (x 4) i)
          (x y - quad (x 0) (x 1) (x 6) (x 4) i) (u0 x t)) := by
  set u := u0 x t with hu
  have hN0 : ⟪F.N 0, u⟫ = 0 := inner_N0_u0 F t
  have hdiff : ∀ P Q : Fin 7, P ≠ Q → x Q - x P ≠ 0 := fun P Q h => by
    obtain ⟨f, hf1, hf2⟩ := hsep P Q h
    exact pt_ne_of_facet F f P Q hf1 hf2
  have hne01 : cross u (x 1 - x 0) ≠ 0 :=
    cross_ne_zero_of_facet_two F 1 0 1 (by decide) (by decide) (hdiff 0 1 (by decide)) hN1.ne'
  have hne16 : cross u (x 6 - x 1) ≠ 0 :=
    cross_ne_zero_of_facet_two F 1 1 6 (by decide) (by decide) (hdiff 1 6 (by decide)) hN1.ne'
  have hne64 : cross u (x 4 - x 6) ≠ 0 :=
    cross_ne_zero_of_facet_two F 4 6 4 (by decide) (by decide) (hdiff 6 4 (by decide)) hN4.ne'
  have hne40 : cross u (x 0 - x 4) ≠ 0 :=
    cross_ne_zero_of_facet_two F 4 4 0 (by decide) (by decide) (hdiff 4 0 (by decide)) hN4.ne'
  obtain ⟨σ₀, hσ₀_ne, hσ₀⟩ := det3_sign_edgeOn F 0 0 1 (by decide) (by decide) u hN0 hne01
  obtain ⟨σ₁, -, hσ₁⟩ := det3_sign_ridge F 5 1 1 6 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u
    ⟨hN5, hN1⟩ hne16
  obtain ⟨σ₂, -, hσ₂⟩ := det3_sign_ridge F 8 4 6 4 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u
    ⟨hN8, hN4⟩ hne64
  obtain ⟨σ₃, -, hσ₃⟩ := det3_sign_ridge F 3 4 4 0 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u
    ⟨hN3, hN4⟩ hne40
  have h0_6 : 0 < σ₀ * det3 (x 1 - x 0) (x 6 - x 0) u := hσ₀ 6 (by decide)
  have h1_0 : 0 < σ₁ * det3 (x 6 - x 1) (x 0 - x 1) u := hσ₁ 0 (Or.inl (by decide))
  have c016 : det3 (x 1 - x 0) (x 6 - x 0) u = det3 (x 6 - x 1) (x 0 - x 1) u :=
    Minimality.det3_cycle_triangle (x 0) (x 1) (x 6) u
  have s01 : 0 < σ₀ * σ₁ := sign_prod h0_6 (by rw [c016]; exact h1_0)
  have h1_4 : 0 < σ₁ * det3 (x 6 - x 1) (x 4 - x 1) u := hσ₁ 4 (Or.inl (by decide))
  have h2_1 : 0 < σ₂ * det3 (x 4 - x 6) (x 1 - x 6) u := hσ₂ 1 (Or.inl (by decide))
  have c164 : det3 (x 6 - x 1) (x 4 - x 1) u = det3 (x 4 - x 6) (x 1 - x 6) u :=
    Minimality.det3_cycle_triangle (x 1) (x 6) (x 4) u
  have s12 : 0 < σ₁ * σ₂ := sign_prod h1_4 (by rw [c164]; exact h2_1)
  have h2_0 : 0 < σ₂ * det3 (x 4 - x 6) (x 0 - x 6) u := hσ₂ 0 (Or.inl (by decide))
  have h3_6 : 0 < σ₃ * det3 (x 0 - x 4) (x 6 - x 4) u := hσ₃ 6 (Or.inl (by decide))
  have c640 : det3 (x 4 - x 6) (x 0 - x 6) u = det3 (x 0 - x 4) (x 6 - x 4) u :=
    Minimality.det3_cycle_triangle (x 6) (x 4) (x 0) u
  have s23 : 0 < σ₂ * σ₃ := sign_prod h2_0 (by rw [c640]; exact h3_6)
  have s02 : 0 < σ₀ * σ₂ := sign_transfer s01 s12
  have s03 : 0 < σ₀ * σ₃ := sign_transfer s02 s23
  have key : ∀ y : Fin 7, y ∉ s0x_S24 0 → y ≠ 6 → y ≠ 4 → ∀ i : ZMod 4,
      0 < σ₀ * det3 (quad (x 0) (x 1) (x 6) (x 4) (i + 1) - quad (x 0) (x 1) (x 6) (x 4) i)
          (x y - quad (x 0) (x 1) (x 6) (x 4) i) u := by
    intro y hy0 hy6 hy4 i
    have hy : y ∉ s0x_S24 5 ∧ y ∉ s0x_S24 4 := by
      revert y; decide
    fin_cases i
    · exact hσ₀ y hy0
    · exact sign_transfer s01 (hσ₁ y (Or.inl hy.1))
    · exact sign_transfer s02 (hσ₂ y (Or.inr hy.2))
    · exact sign_transfer s03 (hσ₃ y (Or.inr hy.2))
  have hcyc : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      0 < σ₀ * det3 (quad (x 0) (x 1) (x 6) (x 4) (i + 1) - quad (x 0) (x 1) (x 6) (x 4) i)
        (quad (x 0) (x 1) (x 6) (x 4) j - quad (x 0) (x 1) (x 6) (x 4) i) u := by
    intro i j hj1 hj2
    fin_cases i <;> fin_cases j
    · exact False.elim (hj1 rfl)
    · exact False.elim (hj2 rfl)
    · exact h0_6
    · exact hσ₀ 4 (by decide)
    · exact sign_transfer s01 h1_0
    · exact False.elim (hj1 rfl)
    · exact False.elim (hj2 rfl)
    · exact sign_transfer s01 h1_4
    · exact sign_transfer s02 h2_0
    · exact sign_transfer s02 h2_1
    · exact False.elim (hj1 rfl)
    · exact False.elim (hj2 rfl)
    · exact False.elim (hj2 rfl)
    · exact sign_transfer s03 (hσ₃ 1 (Or.inl (by decide)))
    · exact sign_transfer s03 h3_6
    · exact False.elim (hj1 rfl)
  refine ⟨σ₀, hσ₀_ne, ?_, hcyc, key⟩
  have h := h0_6
  rw [hu, det3_x01_x06_u0] at h
  by_contra hn
  push Not at hn
  have e : σ₀ * (t * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)) =
      (-t) * (σ₀ * (-det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1))) := by ring
  rw [e] at h
  exact absurd h (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos (by linarith) hn))

/-- Foot/off-chord condition for the far vertex `w` over the chord `0 → 1`. -/
def Off01 (F : S0xFac 9 s0x_S24 x) (w : Fin 7) : Prop :=
  ⟪F.N 0, cross (x 1 - x 0) (x w - x 0)⟫ ≠ 0 ∨ ⟪x w - x 0, x 1 - x 0⟫ < 0 ∨ ⟪x w - x 1, x 0 - x 1⟫ < 0

theorem chord_middle_012_neg {t : ℝ} (ht : t < -1) :
    x 2 = x 0 + (1 + t⁻¹) • (x 1 - x 0) + t⁻¹ • u0 x t := by
  have h0 : t ≠ 0 := by intro h; rw [h] at ht; norm_num at ht
  ext j
  simp only [u0, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  field_simp
  ring

/-- **Leaf `q012_f0345_neg_lo`**: rim `(0,1,6,4)` at `u0 (t3 - ε)`, `t3 < -1` the root of the 0345 facet on the
012 line; chord `0 → 1` on facet 012 with middle `2`; interior `3`, `5`. Lemma K (mirror sense `0 < ρ κ`):
the diagonals `{0,6}`, `{1,4}` satisfy `min(z0,z6) < max(z1,z4)` at `u0 t3`. -/
theorem q012_f0345_neg_lo (F : S0xFac 9 s0x_S24 x)
    (ht : t3n F < -1)
    (hN4 : 0 < ⟪F.N 4, u0 x (t3n F)⟫)
    (hN8 : ⟪F.N 8, u0 x (t3n F)⟫ < 0)
    (hbase : min ⟪x 0, u0 x (t3n F)⟫ ⟪x 6, u0 x (t3n F)⟫ <
      max ⟪x 1, u0 x (t3n F)⟫ ⟪x 4, u0 x (t3n F)⟫)
    (hfar : F.f 0 (x 6) ≠ F.f 0 (x 4))
    (hoff6 : F.f 0 (x 6) < F.f 0 (x 4) → Off01 F 6)
    (hoff4 : F.f 0 (x 4) < F.f 0 (x 6) → Off01 F 4)
    (hgen : Gen4 (quad (x 0) (x 1) (x 6) (x 4)) (u0 x (t3n F)) (x 2 - x 1)) :
    FaceChordView F 0 := by
  obtain ⟨hz, hb⟩ := rf0345n_t3 F ht
  set t0 := t3n F with ht0
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) with hΩdef
  set p : ZMod 4 → ℝ³ := quad (x 0) (x 1) (x 6) (x 4) with hp
  have ht_neg : t0 < 0 := by linarith
  have hN1 : 0 < ⟪F.N 1, u0 x t0⟫ := by
    rw [inner_N1_u0]; exact mul_pos_of_neg_of_neg (by linarith [lambda1_pos F]) ht_neg
  have hN5 := inner_N5_u0_neg F t0
  have ht_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), t0 + (-1) * ε < -1 := by
    filter_upwards [Minimality.eventually_pos_affine (A := -1 - t0) (B := 1) (Or.inl (by linarith))]
      with ε hε
    linarith
  have hs : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 < ⟪F.N 1, u0 x (t0 + (-1) * ε)⟫ ∧ ⟪F.N 5, u0 x (t0 + (-1) * ε)⟫ < 0 ∧
      0 < ⟪F.N 4, u0 x (t0 + (-1) * ε)⟫ ∧ ⟪F.N 8, u0 x (t0 + (-1) * ε)⟫ < 0 ∧
      ⟪F.N 3, u0 x (t0 + (-1) * ε)⟫ < 0 := by
    filter_upwards [ev_pos_u0 (F.N 1) t0 (-1) (Or.inl hN1), ev_neg_u0 (F.N 5) t0 (-1) (Or.inl hN5),
      ev_pos_u0 (F.N 4) t0 (-1) (Or.inl hN4), ev_neg_u0 (F.N 8) t0 (-1) (Or.inl hN8),
      ev_neg_u0 (F.N 3) t0 (-1) (Or.inr ⟨hz, by linarith⟩)] with ε h1 h5 h4 h8 h3
    exact ⟨h1, h5, h4, h8, h3⟩
  have hcyc_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ i, 0 < (-Ω) * triD p (u0 x t0 + ε • ((-1 : ℝ) • (x 2 - x 1))) i := by
    filter_upwards [hs, ht_ev] with ε ⟨h1, h5, h4, h8, h3⟩ htε
    rw [view_eq]
    obtain ⟨ρ, hρ, hρΩ, hcyc, -⟩ := quadRim0164 F (t0 + (-1) * ε) (by linarith) h1 h5 h4 h8 h3
    intro i
    have hne1 : (i + 2 : ZMod 4) ≠ i := by
      intro h
      have : (2 : ZMod 4) = 0 := by
        calc (2 : ZMod 4) = (i + 2) - i := by ring
        _ = i - i := by rw [h]
        _ = 0 := sub_self i
      revert this; decide
    have hne2 : (i + 2 : ZMod 4) ≠ i + 1 := by
      intro h
      have : (1 : ZMod 4) = 0 := by
        calc (1 : ZMod 4) = (i + 2) - (i + 1) := by ring
        _ = (i + 1) - (i + 1) := by rw [h]
        _ = 0 := sub_self _
      revert this; decide
    have h := hcyc i (i + 2) hne1 hne2
    have hT : 0 < (ρ * (-Ω)) * (ρ * triD p (u0 x (t0 + (-1) * ε)) i) := mul_pos hρΩ h
    have e : (ρ * (-Ω)) * (ρ * triD p (u0 x (t0 + (-1) * ε)) i) =
        ρ ^ 2 * ((-Ω) * triD p (u0 x (t0 + (-1) * ε)) i) := by ring
    rw [e] at hT
    exact pos_of_mul_pos_right hT (sq_nonneg ρ)
  have hgen' : ∀ i j, i ≠ j → ⟪p i - p j, u0 x t0⟫ ≠ 0 ∨ ⟪p i - p j, (-1 : ℝ) • (x 2 - x 1)⟫ ≠ 0 := by
    intro i j hij
    rcases hgen i j hij with h | h
    · exact Or.inl h
    · right; rw [real_inner_smul_right]; exact mul_ne_zero (by norm_num) h
  have hk : 0 < (-Ω) * det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1) := by
    have := omega_kappa0164 F
    show 0 < (-Ω) * det3 (x 6 - x 0) (x 4 - x 1) (x 0 - x 1)
    linarith
  have hU : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Function.Injective (fun i => ⟪p i, u0 x t0 + ε • ((-1 : ℝ) • (x 2 - x 1))⟫) ∧
      IsCyclicUnimodal (fun i => ⟪p i, u0 x t0 + ε • ((-1 : ℝ) • (x 2 - x 1))⟫) :=
    cornerU_mirror p (u0 x t0) ((-1 : ℝ) • (x 2 - x 1)) (-Ω) hcyc_ev hk hbase hgen'
  obtain ⟨ε, ⟨h1, h5, h4, h8, h3⟩, htε, hinj, huni⟩ := (hs.and (ht_ev.and hU)).exists
  rw [view_eq] at hinj huni
  obtain ⟨ρ, hρ, -, hcyc, hI⟩ := quadRim0164 F (t0 + (-1) * ε) (by linarith) h1 h5 h4 h8 h3
  set r : ZMod 4 → Fin 7 := quad (0 : Fin 7) 1 6 4 with hr
  have hrx : ∀ i, x (r i) = quad (x 0) (x 1) (x 6) (x 4) i := by intro i; fin_cases i <;> rfl
  have h_uni := Minimality.strictUnimodal_of_cyclic (by decide) huni
  have h0S : (0 : Fin 7) ∈ s0x_S24 0 := by decide
  have h1S : (1 : Fin 7) ∈ s0x_S24 0 := by decide
  obtain ⟨w, hwS, hfar', hoff'⟩ : ∃ w : ZMod 4, r w ∉ s0x_S24 0 ∧
      (∀ m, m ≠ w → r m ∉ s0x_S24 0 → F.f 0 (x (r w)) < F.f 0 (x (r m))) ∧
      (⟪F.N 0, cross (x (r (0 + 1)) - x (r 0)) (x (r w) - x (r 0))⟫ ≠ 0 ∨
        ⟪x (r w) - x (r 0), x (r (0 + 1)) - x (r 0)⟫ < 0 ∨
        ⟪x (r w) - x (r (0 + 1)), x (r 0) - x (r (0 + 1))⟫ < 0) := by
    rcases lt_or_gt_of_ne hfar with hlt | hlt
    · refine ⟨2, by decide, ?_, hoff6 hlt⟩
      intro m hm hmS
      fin_cases m
      · exact absurd h0S hmS
      · exact absurd h1S hmS
      · exact absurd rfl hm
      · exact hlt
    · refine ⟨3, by decide, ?_, hoff4 hlt⟩
      intro m hm hmS
      fin_cases m
      · exact absurd h0S hmS
      · exact absurd h1S hmS
      · exact hlt
      · exact absurd rfl hm
  refine ⟨u0 x (t0 + (-1) * ε), 4, inferInstance, r, 0, w, ρ, inner_N0_u0 F _, by decide, h0S, h1S, hρ,
    ?_, ?_, ?_, ?_, ?_, hwS, hfar', hoff'⟩
  · intro i j hj1 hj2
    simp_rw [hrx]
    exact hcyc i j hj1 hj2
  · intro q hq0 hqr i
    simp_rw [hrx]
    exact hI q hq0 (hqr 2) (hqr 3) i
  · intro q hq hqr
    have hq2 : q = 2 := by
      revert hq; have h0 := hqr 0; have h1 := hqr 1
      fin_cases q <;> first | (intro _; rfl) | (intro hq; exfalso; revert hq; decide) |
        (exfalso; exact h0 rfl) | (exfalso; exact h1 rfl)
    subst hq2
    have hτ0 : t0 + (-1) * ε < 0 := by linarith
    have hinv : (t0 + (-1) * ε)⁻¹ < 0 := inv_lt_zero.mpr hτ0
    have hne : t0 + (-1) * ε ≠ 0 := hτ0.ne
    have hs0 : 0 < 1 + (t0 + (-1) * ε)⁻¹ := by
      have e : 1 + (t0 + (-1) * ε)⁻¹ = ((t0 + (-1) * ε) + 1) / (t0 + (-1) * ε) := by
        rw [eq_div_iff hne, add_mul, inv_mul_cancel₀ hne]; ring
      rw [e]; exact div_pos_of_neg_of_neg (by linarith) hτ0
    refine ⟨1 + (t0 + (-1) * ε)⁻¹, (t0 + (-1) * ε)⁻¹, hs0, by linarith, hinv.ne, ?_⟩
    · exact chord_middle_012_neg htε
  · simp_rw [hrx]; exact hinj
  · simp_rw [hrx]; exact Or.inl h_uni

end Minimality.T24.R012
