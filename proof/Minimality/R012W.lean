module

public import Minimality.R012
public import Minimality.Q45Leaf
public import Minimality.CornerU
public import Minimality.DiagCross
public import Minimality.FaceChordFac
public import Minimality.Type24SAT.K24.Par2546


@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace Topology
open Filter Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.RimFromSigns
open Minimality.T24.Q45 Minimality.T24.R012

set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000
namespace Minimality.T24.R012
variable {x : Fin 7 → ℝ³}

def Off012 (F : S0xFac 9 s0x_S24 x) (w : Fin 7) : Prop :=
  ⟪F.N 0, cross (x 0 - x 2) (x w - x 2)⟫ ≠ 0 ∨ ⟪x w - x 2, x 0 - x 2⟫ < 0 ∨ ⟪x w - x 0, x 2 - x 0⟫ < 0

def Gen4 (p : ZMod 4 → ℝ³) (b d : ℝ³) : Prop :=
  ∀ i j : ZMod 4, i ≠ j → ⟪p i - p j, b⟫ ≠ 0 ∨ ⟪p i - p j, d⟫ ≠ 0

theorem hsep : ∀ P Q : Fin 7, P ≠ Q → ∃ f : Fin 9, P ∈ s0x_S24 f ∧ Q ∉ s0x_S24 f := by decide

/-- Combinatorial side conditions of a quad rim `(0, A, B, 2)` on the 012 chord circle. -/
def Good012 (A B I J : Fin 7) (ta ta' tb tb' tc tc' : Fin 9) : Prop :=
  0 ∈ s0x_S24 ta ∧ 0 ∈ s0x_S24 ta' ∧ A ∈ s0x_S24 ta ∧ A ∈ s0x_S24 ta' ∧
  A ∈ s0x_S24 tb ∧ A ∈ s0x_S24 tb' ∧ B ∈ s0x_S24 tb ∧ B ∈ s0x_S24 tb' ∧
  B ∈ s0x_S24 tc ∧ B ∈ s0x_S24 tc' ∧ 2 ∈ s0x_S24 tc ∧ 2 ∈ s0x_S24 tc' ∧
  (∀ y, y ≠ 0 → y ≠ A → y ∉ s0x_S24 ta ∨ y ∉ s0x_S24 ta') ∧
  (∀ y, y ≠ A → y ≠ B → y ∉ s0x_S24 tb ∨ y ∉ s0x_S24 tb') ∧
  (∀ y, y ≠ B → y ≠ 2 → y ∉ s0x_S24 tc ∨ y ∉ s0x_S24 tc') ∧
  A ∉ s0x_S24 0 ∧ B ∉ s0x_S24 0 ∧ I ∉ s0x_S24 0 ∧ J ∉ s0x_S24 0 ∧
  A ≠ B ∧ I ≠ A ∧ I ≠ B ∧ J ≠ A ∧ J ≠ B ∧
  (∀ q, q ∉ s0x_S24 0 → q ≠ A → q ≠ B → q = I ∨ q = J) ∧
  (∀ q, q ∈ s0x_S24 0 → q ≠ 0 → q ≠ 2 → q = 1) ∧
  ta ≠ 0 ∧ tb ≠ 0 ∧ tc ≠ 0 ∧ ta' ≠ 0 ∧ tb' ≠ 0 ∧ tc' ≠ 0

instance (A B I J : Fin 7) (ta ta' tb tb' tc tc' : Fin 9) :
    Decidable (Good012 A B I J ta ta' tb tb' tc tc') := by unfold Good012; infer_instance

theorem det3_x02_u0 (t : ℝ) : det3 (x 0 - x 2) (x 6 - x 2) (u0 x t) =
    -(1 + t) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
  simp only [u0, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring

theorem quadRim012 (F : S0xFac 9 s0x_S24 x) (t : ℝ) (ht : 0 < 1 + t)
    (A B I J : Fin 7) (ta ta' tb tb' tc tc' : Fin 9)
    (hG : Good012 A B I J ta ta' tb tb' tc tc') (h6 : A = 6 ∨ B = 6 ∨ I = 6 ∨ J = 6)
    (ha : ⟪F.N ta, u0 x t⟫ < 0 ∧ 0 < ⟪F.N ta', u0 x t⟫)
    (hb : ⟪F.N tb, u0 x t⟫ < 0 ∧ 0 < ⟪F.N tb', u0 x t⟫)
    (hc : ⟪F.N tc, u0 x t⟫ < 0 ∧ 0 < ⟪F.N tc', u0 x t⟫) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧ 0 < ρ * (-det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)) ∧
      (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
        0 < ρ * det3 (quad (x 0) (x A) (x B) (x 2) (i + 1) - quad (x 0) (x A) (x B) (x 2) i)
          (quad (x 0) (x A) (x B) (x 2) j - quad (x 0) (x A) (x B) (x 2) i) (u0 x t)) ∧
      (∀ i : ZMod 4,
        0 < ρ * det3 (quad (x 0) (x A) (x B) (x 2) (i + 1) - quad (x 0) (x A) (x B) (x 2) i)
          (x I - quad (x 0) (x A) (x B) (x 2) i) (u0 x t)) ∧
      (∀ i : ZMod 4,
        0 < ρ * det3 (quad (x 0) (x A) (x B) (x 2) (i + 1) - quad (x 0) (x A) (x B) (x 2) i)
          (x J - quad (x 0) (x A) (x B) (x 2) i) (u0 x t)) := by
  obtain ⟨h0a, h0a', hAa, hAa', hAb, hAb', hBb, hBb', hBc, hBc', h2c, h2c', hoa, hob, hoc,
    hA0, hB0, hI0, hJ0, hAB, hIA, hIB, hJA, hJB, -, -, -, -, -, -, -, -⟩ := hG
  set u := u0 x t with hu
  have hN0 : ⟪F.N 0, u⟫ = 0 := inner_N0_u0 F t
  have hN2 : ⟪F.N 2, u⟫ ≠ 0 := by
    rw [hu, inner_N2_u0]; exact (mul_pos (lambda2_pos F) ht).ne'
  have hdiff : ∀ P Q : Fin 7, P ≠ Q → x Q - x P ≠ 0 := fun P Q h => by
    obtain ⟨f, hf1, hf2⟩ := hsep P Q h
    exact pt_ne_of_facet F f P Q hf1 hf2
  have h00 : (0 : Fin 7) ∈ s0x_S24 0 := by decide
  have h20 : (2 : Fin 7) ∈ s0x_S24 0 := by decide
  have hA2 : A ≠ 0 := fun h => hA0 (h ▸ h00)
  have hB2 : B ≠ 0 := fun h => hB0 (h ▸ h00)
  have hA2' : A ≠ 2 := fun h => hA0 (h ▸ h20)
  have hB2' : B ≠ 2 := fun h => hB0 (h ▸ h20)
  have hne01 : cross u (x A - x 0) ≠ 0 :=
    cross_ne_zero_of_facet_two F ta 0 A h0a hAa (hdiff 0 A (Ne.symm hA2)) ha.1.ne
  have hne12 : cross u (x B - x A) ≠ 0 :=
    cross_ne_zero_of_facet_two F tb A B hAb hBb (hdiff A B hAB) hb.1.ne
  have hne23 : cross u (x 2 - x B) ≠ 0 :=
    cross_ne_zero_of_facet_two F tc B 2 hBc h2c (hdiff B 2 hB2') hc.1.ne
  have hne30 : cross u (x 0 - x 2) ≠ 0 :=
    cross_ne_zero_of_facet_two F 2 2 0 (by decide) (by decide) (hdiff 2 0 (by decide)) hN2
  obtain ⟨σ₀, hσ₀_ne, hσ₀⟩ := det3_sign_ridge F ta ta' 0 A ⟨h0a, h0a'⟩ ⟨hAa, hAa'⟩ u ha hne01
  obtain ⟨σ₁, hσ₁_ne, hσ₁⟩ := det3_sign_ridge F tb tb' A B ⟨hAb, hAb'⟩ ⟨hBb, hBb'⟩ u hb hne12
  obtain ⟨σ₂, hσ₂_ne, hσ₂⟩ := det3_sign_ridge F tc tc' B 2 ⟨hBc, hBc'⟩ ⟨h2c, h2c'⟩ u hc hne23
  obtain ⟨σ₃, hσ₃_ne, hσ₃⟩ := det3_sign_edgeOn F 0 2 0 h20 h00 u hN0 hne30
  have c01 : det3 (x A - x 0) (x B - x 0) u = det3 (x B - x A) (x 0 - x A) u :=
    Minimality.det3_cycle_triangle (x 0) (x A) (x B) u
  have c12 : det3 (x B - x A) (x 2 - x A) u = det3 (x 2 - x B) (x A - x B) u :=
    Minimality.det3_cycle_triangle (x A) (x B) (x 2) u
  have c23 : det3 (x 2 - x B) (x 0 - x B) u = det3 (x 0 - x 2) (x B - x 2) u :=
    Minimality.det3_cycle_triangle (x B) (x 2) (x 0) u
  have h0B : 0 < σ₀ * det3 (x A - x 0) (x B - x 0) u := hσ₀ B (hoa B hB2 hAB.symm)
  have h1_0 : 0 < σ₁ * det3 (x B - x A) (x 0 - x A) u := hσ₁ 0 (hob 0 (Ne.symm hA2) (Ne.symm hB2))
  have h1_0' : 0 < σ₁ * det3 (x A - x 0) (x B - x 0) u := by rw [c01]; exact h1_0
  have s01 : 0 < σ₀ * σ₁ := sign_prod h0B h1_0'
  have h1_2 : 0 < σ₁ * det3 (x B - x A) (x 2 - x A) u := hσ₁ 2 (hob 2 (Ne.symm hA2') (Ne.symm hB2'))
  have h2_A : 0 < σ₂ * det3 (x 2 - x B) (x A - x B) u := hσ₂ A (hoc A hAB hA2')
  have h2_A' : 0 < σ₂ * det3 (x B - x A) (x 2 - x A) u := by rw [c12]; exact h2_A
  have s12 : 0 < σ₁ * σ₂ := sign_prod h1_2 h2_A'
  have s02 : 0 < σ₀ * σ₂ := sign_transfer s01 s12
  have h2_0 : 0 < σ₂ * det3 (x 2 - x B) (x 0 - x B) u := hσ₂ 0 (hoc 0 (Ne.symm hB2) (by decide))
  have h3_B : 0 < σ₃ * det3 (x 0 - x 2) (x B - x 2) u := hσ₃ B hB0
  have h3_B' : 0 < σ₃ * det3 (x 2 - x B) (x 0 - x B) u := by rw [c23]; exact h3_B
  have s23 : 0 < σ₂ * σ₃ := sign_prod h2_0 h3_B'
  have s03 : 0 < σ₀ * σ₃ := sign_transfer s02 s23
  have key : ∀ y : Fin 7, y ∉ s0x_S24 0 → y ≠ A → y ≠ B →
      ∀ i : ZMod 4, 0 < σ₀ * det3 (quad (x 0) (x A) (x B) (x 2) (i + 1) - quad (x 0) (x A) (x B) (x 2) i)
          (x y - quad (x 0) (x A) (x B) (x 2) i) u := by
    intro y hy0 hyA hyB i
    have hy0' : y ≠ 0 := fun h => hy0 (h ▸ h00)
    have hy2' : y ≠ 2 := fun h => hy0 (h ▸ h20)
    fin_cases i
    · exact hσ₀ y (hoa y hy0' hyA)
    · exact sign_transfer s01 (hσ₁ y (hob y hyA hyB))
    · exact sign_transfer s02 (hσ₂ y (hoc y hyB hy2'))
    · exact sign_transfer s03 (hσ₃ y hy0)
  have hcyc : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      0 < σ₀ * det3 (quad (x 0) (x A) (x B) (x 2) (i + 1) - quad (x 0) (x A) (x B) (x 2) i)
        (quad (x 0) (x A) (x B) (x 2) j - quad (x 0) (x A) (x B) (x 2) i) u := by
    intro i j hj1 hj2
    fin_cases i <;> fin_cases j
    · exact False.elim (hj1 rfl)
    · exact False.elim (hj2 rfl)
    · exact h0B
    · exact hσ₀ 2 (hoa 2 (by decide) hA2'.symm)
    · exact sign_transfer s01 h1_0
    · exact False.elim (hj1 rfl)
    · exact False.elim (hj2 rfl)
    · exact sign_transfer s01 h1_2
    · exact sign_transfer s02 h2_0
    · exact sign_transfer s02 h2_A
    · exact False.elim (hj1 rfl)
    · exact False.elim (hj2 rfl)
    · exact False.elim (hj2 rfl)
    · exact sign_transfer s03 (hσ₃ A hA0)
    · exact sign_transfer s03 h3_B
    · exact False.elim (hj1 rfl)
  have orient : 0 < σ₀ * det3 (x 0 - x 2) (x 6 - x 2) u →
      0 < σ₀ * (-det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)) := by
    intro h
    rw [hu, det3_x02_u0] at h
    by_contra hn
    push Not at hn
    have e : σ₀ * (-(1 + t) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)) =
        (1 + t) * (σ₀ * (-det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1))) := by ring
    rw [e] at h
    exact absurd h (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos ht.le hn))
  refine ⟨σ₀, hσ₀_ne, ?_, hcyc, key I hI0 hIA hIB, key J hJ0 hJA hJB⟩
  rcases h6 with h | h | h | h
  · have := hcyc 3 1 (by decide) (by decide)
    rw [h] at this
    exact orient this
  · have := hcyc 3 2 (by decide) (by decide)
    rw [h] at this
    exact orient this
  · have := key I hI0 hIA hIB 3
    rw [h] at this
    exact orient this
  · have := key J hJ0 hJA hJB 3
    rw [h] at this
    exact orient this

theorem omega_mul_D0254_neg (F : S0xFac 9 s0x_S24 x) :
    det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 2 - x 0) (x 5 - x 0) (x 4 - x 0) < 0 := by
  have hΩ := omega_ne_zero F
  have hΩ2 : 0 < det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) ^ 2 := sq_pos_of_ne_zero hΩ
  have f06 : F.f 0 (x 6) < 0 := F.neg 0 6 (by decide)
  have f05 : F.f 0 (x 5) < 0 := F.neg 0 5 (by decide)
  have f21 : F.f 2 (x 1) < 0 := F.neg 2 1 (by decide)
  have f24 : F.f 2 (x 4) < 0 := F.neg 2 4 (by decide)
  have z01 : ⟪F.N 0, x 1 - x 0⟫ = 0 := by
    rw [F.inner_sub, F.zero 0 1 (by decide), F.zero 0 0 (by decide)]; ring
  have z02 : ⟪F.N 0, x 2 - x 0⟫ = 0 := by
    rw [F.inner_sub, F.zero 0 2 (by decide), F.zero 0 0 (by decide)]; ring
  have n06 : ⟪F.N 0, x 6 - x 0⟫ = F.f 0 (x 6) := by
    rw [F.inner_sub, F.zero 0 0 (by decide)]; ring
  have n05 : ⟪F.N 0, x 5 - x 0⟫ = F.f 0 (x 5) := by
    rw [F.inner_sub, F.zero 0 0 (by decide)]; ring
  have hc := vol3_smul_cramer (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) (x 5 - x 0)
  have hi := congr_arg (fun v => ⟪F.N 0, v⟫) hc
  simp only [real_inner_smul_right, inner_add_right, z01, z02, n06, n05, mul_zero, zero_add,
    add_zero] at hi
  have e6 : vol3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) = -det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
    simp only [det3_expand, vol3, PiLp.sub_apply]; ring
  have e5 : vol3 (x 1 - x 0) (x 2 - x 0) (x 5 - x 0) = det3 (x 2 - x 0) (x 5 - x 0) (x 1 - x 0) := by
    simp only [det3_expand, vol3, PiLp.sub_apply]; ring
  rw [e6, e5] at hi
  -- hi : -Ω * f0 x5 = D1 * f0 x6
  have hD1 : det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 2 - x 0) (x 5 - x 0) (x 1 - x 0) < 0 := by
    by_contra hn
    push Not at hn
    have h1 : 0 < det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) ^ 2 * (-F.f 0 (x 5)) := mul_pos hΩ2 (by linarith)
    have h2 : det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) ^ 2 * (-F.f 0 (x 5)) =
        (det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 2 - x 0) (x 5 - x 0) (x 1 - x 0)) * F.f 0 (x 6) := by
      have := congrArg (fun r => det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * r) hi
      linear_combination this
    rw [h2] at h1
    nlinarith [mul_nonneg hn (neg_nonneg.mpr f06.le)]
  have y20 : ⟪F.N 2, x 2 - x 0⟫ = 0 := by
    rw [F.inner_sub, F.zero 2 2 (by decide), F.zero 2 0 (by decide)]; ring
  have y25 : ⟪F.N 2, x 5 - x 0⟫ = 0 := by
    rw [F.inner_sub, F.zero 2 5 (by decide), F.zero 2 0 (by decide)]; ring
  have y21 : ⟪F.N 2, x 1 - x 0⟫ = F.f 2 (x 1) := by
    rw [F.inner_sub, F.zero 2 0 (by decide)]; ring
  have y24 : ⟪F.N 2, x 4 - x 0⟫ = F.f 2 (x 4) := by
    rw [F.inner_sub, F.zero 2 0 (by decide)]; ring
  have hc2 := vol3_smul_cramer (x 2 - x 0) (x 5 - x 0) (x 1 - x 0) (x 4 - x 0)
  have hi2 := congr_arg (fun v => ⟪F.N 2, v⟫) hc2
  simp only [real_inner_smul_right, inner_add_right, y20, y25, y21, y24, mul_zero, zero_add,
    add_zero] at hi2
  have e1 : vol3 (x 2 - x 0) (x 5 - x 0) (x 1 - x 0) = det3 (x 2 - x 0) (x 5 - x 0) (x 1 - x 0) := by
    simp only [det3_expand, vol3, PiLp.sub_apply]; ring
  have e4 : vol3 (x 2 - x 0) (x 5 - x 0) (x 4 - x 0) = det3 (x 2 - x 0) (x 5 - x 0) (x 4 - x 0) := by
    simp only [det3_expand, vol3, PiLp.sub_apply]; ring
  rw [e1, e4] at hi2
  -- hi2 : D1 * f2 x4 = Δ * f2 x1
  by_contra hn
  push Not at hn
  have h3 := congrArg (fun r => det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * r) hi2
  nlinarith [mul_nonneg hn (neg_nonneg.mpr f21.le), mul_pos_of_neg_of_neg hD1 f24]

theorem kap1 (F : S0xFac 9 s0x_S24 x) :
    0 < det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 6 - x 0) (x 2 - x 4) (x 0 - x 4) := by
  have h := omega_mul_det3_0246_pos_unconditional F
  have e : det3 (x 6 - x 0) (x 2 - x 4) (x 0 - x 4) = det3 (x 0 - x 6) (x 2 - x 6) (x 4 - x 6) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  rw [e]; exact h

theorem kap4 (F : S0xFac 9 s0x_S24 x) :
    det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 3 - x 0) (x 2 - x 6) (x 0 - x 6) < 0 := by
  have h := omega_mul_det3_0236_pos_unconditional F
  have e : det3 (x 3 - x 0) (x 2 - x 6) (x 0 - x 6) = -det3 (x 0 - x 6) (x 2 - x 6) (x 3 - x 6) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  rw [e]; linarith

theorem kap2 (F : S0xFac 9 s0x_S24 x) :
    det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 3 - x 0) (x 2 - x 4) (x 0 - x 4) < 0 := by
  obtain ⟨al, be, hal, hbe, -, h3⟩ := Minimality.T24.Par.par2546_quad F
  have e : det3 (x 3 - x 0) (x 2 - x 4) (x 0 - x 4) = al * det3 (x 2 - x 0) (x 5 - x 0) (x 4 - x 0) := by
    rw [h3]; simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; ring
  rw [e]
  have := omega_mul_D0254_neg F
  nlinarith [mul_neg_of_pos_of_neg hal this]

theorem kap3 (F : S0xFac 9 s0x_S24 x) :
    0 < det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 3 - x 0) (x 2 - x 5) (x 0 - x 5) := by
  obtain ⟨al, be, hal, hbe, -, h3⟩ := Minimality.T24.Par.par2546_quad F
  have e : det3 (x 3 - x 0) (x 2 - x 5) (x 0 - x 5) = -(be * det3 (x 2 - x 0) (x 5 - x 0) (x 4 - x 0)) := by
    rw [h3]; simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; ring
  rw [e]
  have := omega_mul_D0254_neg F
  nlinarith [mul_neg_of_pos_of_neg hbe this]

theorem final012 (F : S0xFac 9 s0x_S24 x) (t : ℝ) (ht : 0 < t)
    (A B I J : Fin 7) (ta ta' tb tb' tc tc' : Fin 9)
    (hG : Good012 A B I J ta ta' tb tb' tc tc') (h6 : A = 6 ∨ B = 6 ∨ I = 6 ∨ J = 6)
    (ha : ⟪F.N ta, u0 x t⟫ < 0 ∧ 0 < ⟪F.N ta', u0 x t⟫)
    (hb : ⟪F.N tb, u0 x t⟫ < 0 ∧ 0 < ⟪F.N tb', u0 x t⟫)
    (hc : ⟪F.N tc, u0 x t⟫ < 0 ∧ 0 < ⟪F.N tc', u0 x t⟫)
    (hinj : Function.Injective (fun i : ZMod 4 => ⟪quad (x 0) (x A) (x B) (x 2) i, u0 x t⟫))
    (huni : IsCyclicUnimodal (fun i : ZMod 4 => ⟪quad (x 0) (x A) (x B) (x 2) i, u0 x t⟫))
    (hw : (F.f 0 (x A) < F.f 0 (x B) ∧ Off012 F A) ∨ (F.f 0 (x B) < F.f 0 (x A) ∧ Off012 F B)) :
    FaceChordView F 0 := by
  obtain ⟨ρ, hρ, -, hcyc, hI, hJ⟩ :=
    quadRim012 F t (by linarith) A B I J ta ta' tb tb' tc tc' hG h6 ha hb hc
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hA0, hB0, hI0, hJ0, hAB, hIA, hIB, hJA, hJB,
    hIJ, hmid1, -⟩ := hG
  set r : ZMod 4 → Fin 7 := quad (0 : Fin 7) A B 2 with hr
  have hrx : ∀ i, x (r i) = quad (x 0) (x A) (x B) (x 2) i := by intro i; fin_cases i <;> rfl
  have h_uni := Minimality.strictUnimodal_of_cyclic (by decide) huni
  have h0S : (0 : Fin 7) ∈ s0x_S24 0 := by decide
  have h2S : (2 : Fin 7) ∈ s0x_S24 0 := by decide
  obtain ⟨w, hwS, hfar', hoff'⟩ : ∃ w : ZMod 4, r w ∉ s0x_S24 0 ∧
      (∀ m, m ≠ w → r m ∉ s0x_S24 0 → F.f 0 (x (r w)) < F.f 0 (x (r m))) ∧
      (⟪F.N 0, cross (x (r (3 + 1)) - x (r 3)) (x (r w) - x (r 3))⟫ ≠ 0 ∨
        ⟪x (r w) - x (r 3), x (r (3 + 1)) - x (r 3)⟫ < 0 ∨
        ⟪x (r w) - x (r (3 + 1)), x (r 3) - x (r (3 + 1))⟫ < 0) := by
    rcases hw with ⟨hlt, hoff⟩ | ⟨hlt, hoff⟩
    · refine ⟨1, hA0, ?_, hoff⟩
      intro m hm hmS
      fin_cases m
      · exact absurd h0S hmS
      · exact absurd rfl hm
      · exact hlt
      · exact absurd h2S hmS
    · refine ⟨2, hB0, ?_, hoff⟩
      intro m hm hmS
      fin_cases m
      · exact absurd h0S hmS
      · exact hlt
      · exact absurd rfl hm
      · exact absurd h2S hmS
  refine ⟨u0 x t, 4, inferInstance, r, 3, w, ρ, inner_N0_u0 F t, by decide, h2S, h0S, hρ,
    ?_, ?_, ?_, ?_, ?_, hwS, hfar', hoff'⟩
  · intro i j hj1 hj2
    simp_rw [hrx]
    exact hcyc i j hj1 hj2
  · intro q hq0 hqr i
    simp_rw [hrx]
    rcases hIJ q hq0 (hqr 1) (hqr 2) with rfl | rfl
    · exact hI i
    · exact hJ i
  · intro q hq hqr
    have hq1 := hmid1 q hq (hqr 0) (hqr 3)
    subst hq1
    obtain ⟨s, δ, hs0, hs1, hδ, heq⟩ := chord_middle_012 (x := x) ht
    exact ⟨s, δ, hs0, hs1, hδ, heq⟩
  · simp_rw [hrx]; exact hinj
  · simp_rw [hrx]; exact Or.inl h_uni

theorem ev_pos_u0 (N : ℝ³) (t0 σ : ℝ)
    (h : 0 < ⟪N, u0 x t0⟫ ∨ (⟪N, u0 x t0⟫ = 0 ∧ 0 < σ * ⟪N, x 2 - x 1⟫)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪N, u0 x (t0 + σ * ε)⟫ := by
  filter_upwards [Minimality.eventually_pos_affine (A := ⟪N, u0 x t0⟫) (B := σ * ⟪N, x 2 - x 1⟫) h]
    with ε hε
  rw [inner_u0_add]
  have : σ * ε * ⟪N, x 2 - x 1⟫ = ε * (σ * ⟪N, x 2 - x 1⟫) := by ring
  rw [this]; exact hε

theorem ev_neg_u0 (N : ℝ³) (t0 σ : ℝ)
    (h : ⟪N, u0 x t0⟫ < 0 ∨ (⟪N, u0 x t0⟫ = 0 ∧ σ * ⟪N, x 2 - x 1⟫ < 0)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪N, u0 x (t0 + σ * ε)⟫ < 0 := by
  have h' : 0 < -⟪N, u0 x t0⟫ ∨ (-⟪N, u0 x t0⟫ = 0 ∧ 0 < -(σ * ⟪N, x 2 - x 1⟫)) := by
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, by linarith⟩
  filter_upwards [Minimality.eventually_pos_affine (A := -⟪N, u0 x t0⟫) (B := -(σ * ⟪N, x 2 - x 1⟫)) h']
    with ε hε
  rw [inner_u0_add]
  have : σ * ε * ⟪N, x 2 - x 1⟫ = ε * (σ * ⟪N, x 2 - x 1⟫) := by ring
  rw [this]; nlinarith

theorem view_eq (t0 σ ε : ℝ) :
    u0 x t0 + ε • (σ • (x 2 - x 1)) = u0 x (t0 + σ * ε) := by
  rw [u0_add, smul_smul, mul_comm]

theorem leaf_core012 (F : S0xFac 9 s0x_S24 x) (t0 σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (ht0 : 0 < t0)
    (A B I J : Fin 7) (ta ta' tb tb' tc tc' : Fin 9)
    (hG : Good012 A B I J ta ta' tb tb' tc tc') (h6 : A = 6 ∨ B = 6 ∨ I = 6 ∨ J = 6)
    (hs : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (⟪F.N ta, u0 x (t0 + σ * ε)⟫ < 0 ∧ 0 < ⟪F.N ta', u0 x (t0 + σ * ε)⟫) ∧
      (⟪F.N tb, u0 x (t0 + σ * ε)⟫ < 0 ∧ 0 < ⟪F.N tb', u0 x (t0 + σ * ε)⟫) ∧
      (⟪F.N tc, u0 x (t0 + σ * ε)⟫ < 0 ∧ 0 < ⟪F.N tc', u0 x (t0 + σ * ε)⟫))
    (hbk : (0 < det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x B - x 0) (x 2 - x A) (x 0 - x A) ∧
        min ⟪x A, u0 x t0⟫ ⟪x 2, u0 x t0⟫ < max ⟪x 0, u0 x t0⟫ ⟪x B, u0 x t0⟫) ∨
      (det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x B - x 0) (x 2 - x A) (x 0 - x A) < 0 ∧
        min ⟪x 0, u0 x t0⟫ ⟪x B, u0 x t0⟫ < max ⟪x A, u0 x t0⟫ ⟪x 2, u0 x t0⟫))
    (hgen : Gen4 (quad (x 0) (x A) (x B) (x 2)) (u0 x t0) (x 2 - x 1))
    (hw : (F.f 0 (x A) < F.f 0 (x B) ∧ Off012 F A) ∨ (F.f 0 (x B) < F.f 0 (x A) ∧ Off012 F B)) :
    FaceChordView F 0 := by
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) with hΩdef
  have hΩ : Ω ≠ 0 := omega_ne_zero F
  set p : ZMod 4 → ℝ³ := quad (x 0) (x A) (x B) (x 2) with hp
  have hσ0 : σ ≠ 0 := by
    rcases hσ with h | h
    · rw [h]; exact one_ne_zero
    · rw [h]; norm_num
  have ht_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < t0 + σ * ε := by
    have := Minimality.eventually_pos_affine (A := t0) (B := σ) (Or.inl ht0)
    filter_upwards [this] with ε hε
    linarith [hε, show ε * σ = σ * ε from mul_comm _ _]
  have hcyc_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ i, 0 < (-Ω) * triD p (u0 x t0 + ε • (σ • (x 2 - x 1))) i := by
    filter_upwards [hs, ht_ev] with ε ⟨ha, hb, hc⟩ ht
    rw [view_eq]
    obtain ⟨ρ, hρ, hρΩ, hcyc, -, -⟩ :=
      quadRim012 F (t0 + σ * ε) (by linarith) A B I J ta ta' tb tb' tc tc' hG h6 ha hb hc
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
    have hT : 0 < (ρ * (-Ω)) * (ρ * triD p (u0 x (t0 + σ * ε)) i) := mul_pos hρΩ h
    have e : (ρ * (-Ω)) * (ρ * triD p (u0 x (t0 + σ * ε)) i) =
        ρ ^ 2 * ((-Ω) * triD p (u0 x (t0 + σ * ε)) i) := by ring
    rw [e] at hT
    exact pos_of_mul_pos_right hT (sq_nonneg ρ)
  have hgen' : ∀ i j, i ≠ j → ⟪p i - p j, u0 x t0⟫ ≠ 0 ∨ ⟪p i - p j, σ • (x 2 - x 1)⟫ ≠ 0 := by
    intro i j hij
    rcases hgen i j hij with h | h
    · exact Or.inl h
    · right; rw [real_inner_smul_right]; exact mul_ne_zero hσ0 h
  have hU : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Function.Injective (fun i => ⟪p i, u0 x t0 + ε • (σ • (x 2 - x 1))⟫) ∧
      IsCyclicUnimodal (fun i => ⟪p i, u0 x t0 + ε • (σ • (x 2 - x 1))⟫) := by
    rcases hbk with ⟨hk, hb'⟩ | ⟨hk, hb'⟩
    · exact cornerU p (u0 x t0) (σ • (x 2 - x 1)) (-Ω) hcyc_ev (by
        show (-Ω) * det3 (x B - x 0) (x 2 - x A) (x 0 - x A) < 0
        linarith) hb' hgen'
    · exact cornerU_mirror p (u0 x t0) (σ • (x 2 - x 1)) (-Ω) hcyc_ev (by
        show 0 < (-Ω) * det3 (x B - x 0) (x 2 - x A) (x 0 - x A)
        linarith) hb' hgen'
  obtain ⟨ε, ⟨ha, hb, hc⟩, ht, hinj, huni⟩ := (hs.and (ht_ev.and hU)).exists
  rw [view_eq] at hinj huni
  exact final012 F (t0 + σ * ε) ht A B I J ta ta' tb tb' tc tc' hG h6 ha hb hc hinj huni hw

theorem hw_of_ne (F : S0xFac 9 s0x_S24 x) (A B : Fin 7)
    (hfar : F.f 0 (x A) ≠ F.f 0 (x B))
    (hoffA : F.f 0 (x A) < F.f 0 (x B) → Off012 F A)
    (hoffB : F.f 0 (x B) < F.f 0 (x A) → Off012 F B) :
    (F.f 0 (x A) < F.f 0 (x B) ∧ Off012 F A) ∨ (F.f 0 (x B) < F.f 0 (x A) ∧ Off012 F B) := by
  rcases lt_or_gt_of_ne hfar with h | h
  · exact Or.inl ⟨h, hoffA h⟩
  · exact Or.inr ⟨h, hoffB h⟩

theorem ev_N7_pos (F : S0xFac 9 s0x_S24 x) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 7, u0 x (omega3_012 F + 1 * ε)⟫ := by
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have : (0 : ℝ) < ε := hε
  rw [inner_N7_u0]
  have := lambda7_pos F
  have e : omega3_012 F + 1 * ε - omega3_012 F = ε := by ring
  rw [e]; positivity

theorem ev_N7_neg (F : S0xFac 9 s0x_S24 x) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 7, u0 x (omega3_012 F + (-1) * ε)⟫ < 0 := by
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have : (0 : ℝ) < ε := hε
  rw [inner_N7_u0]
  have := lambda7_pos F
  have e : omega3_012 F + (-1) * ε - omega3_012 F = -ε := by ring
  rw [e]; nlinarith

theorem q012_w3_pos (F : S0xFac 9 s0x_S24 x)
    (hω3 : 0 < omega3_012 F)
    (hN4 : ⟪F.N 4, u0 x (omega3_012 F)⟫ < 0)
    (hN3 : 0 < ⟪F.N 3, u0 x (omega3_012 F)⟫)
    (hN8 : 0 < ⟪F.N 8, u0 x (omega3_012 F)⟫)
    (hbase : min ⟪x 4, u0 x (omega3_012 F)⟫ ⟪x 2, u0 x (omega3_012 F)⟫ <
      max ⟪x 0, u0 x (omega3_012 F)⟫ ⟪x 6, u0 x (omega3_012 F)⟫)
    (hfar : F.f 0 (x 4) ≠ F.f 0 (x 6))
    (hoff4 : F.f 0 (x 4) < F.f 0 (x 6) → Off012 F 4)
    (hoff6 : F.f 0 (x 6) < F.f 0 (x 4) → Off012 F 6)
    (hgen : Gen4 (quad (x 0) (x 4) (x 6) (x 2)) (u0 x (omega3_012 F)) (x 2 - x 1)) :
    FaceChordView F 0 := by
  refine leaf_core012 F (omega3_012 F) 1 (Or.inl rfl) hω3 4 6 3 5 4 3 4 8 5 7 (by decide)
    (Or.inr (Or.inl rfl)) ?_ (Or.inl ⟨kap1 F, hbase⟩) hgen (hw_of_ne F 4 6 hfar hoff4 hoff6)
  filter_upwards [ev_neg_u0 (F.N 4) _ 1 (Or.inl hN4), ev_pos_u0 (F.N 3) _ 1 (Or.inl hN3),
    ev_pos_u0 (F.N 8) _ 1 (Or.inl hN8),
    ev_neg_u0 (F.N 5) _ 1 (Or.inl (inner_N5_u0_neg F _)), ev_N7_pos F] with ε h4 h3 h8 h5 h7
  exact ⟨⟨h4, h3⟩, ⟨h4, h8⟩, ⟨h5, h7⟩⟩

theorem q012_w3_neg_A (F : S0xFac 9 s0x_S24 x)
    (hω3 : 0 < omega3_012 F)
    (hN4 : ⟪F.N 4, u0 x (omega3_012 F)⟫ < 0)
    (hN3 : 0 < ⟪F.N 3, u0 x (omega3_012 F)⟫)
    (hN6 : 0 < ⟪F.N 6, u0 x (omega3_012 F)⟫)
    (hN8 : ⟪F.N 8, u0 x (omega3_012 F)⟫ < 0)
    (hbase : min ⟪x 0, u0 x (omega3_012 F)⟫ ⟪x 3, u0 x (omega3_012 F)⟫ <
      max ⟪x 4, u0 x (omega3_012 F)⟫ ⟪x 2, u0 x (omega3_012 F)⟫)
    (hfar : F.f 0 (x 4) ≠ F.f 0 (x 3))
    (hoff4 : F.f 0 (x 4) < F.f 0 (x 3) → Off012 F 4)
    (hoff3 : F.f 0 (x 3) < F.f 0 (x 4) → Off012 F 3)
    (hgen : Gen4 (quad (x 0) (x 4) (x 3) (x 2)) (u0 x (omega3_012 F)) (x 2 - x 1)) :
    FaceChordView F 0 := by
  refine leaf_core012 F (omega3_012 F) (-1) (Or.inr rfl) hω3 4 3 5 6 4 3 8 3 7 6 (by decide)
    (Or.inr (Or.inr (Or.inr rfl))) ?_ (Or.inr ⟨kap2 F, hbase⟩) hgen (hw_of_ne F 4 3 hfar hoff4 hoff3)
  filter_upwards [ev_neg_u0 (F.N 4) _ (-1) (Or.inl hN4), ev_pos_u0 (F.N 3) _ (-1) (Or.inl hN3),
    ev_neg_u0 (F.N 8) _ (-1) (Or.inl hN8), ev_pos_u0 (F.N 6) _ (-1) (Or.inl hN6),
    ev_N7_neg F] with ε h4 h3 h8 h6 h7
  exact ⟨⟨h4, h3⟩, ⟨h8, h3⟩, ⟨h7, h6⟩⟩

theorem q012_w3_neg_B (F : S0xFac 9 s0x_S24 x)
    (hω3 : 0 < omega3_012 F)
    (hN3 : ⟪F.N 3, u0 x (omega3_012 F)⟫ < 0)
    (hN6 : 0 < ⟪F.N 6, u0 x (omega3_012 F)⟫)
    (hbase : min ⟪x 5, u0 x (omega3_012 F)⟫ ⟪x 2, u0 x (omega3_012 F)⟫ <
      max ⟪x 0, u0 x (omega3_012 F)⟫ ⟪x 3, u0 x (omega3_012 F)⟫)
    (hfar : F.f 0 (x 5) ≠ F.f 0 (x 3))
    (hoff5 : F.f 0 (x 5) < F.f 0 (x 3) → Off012 F 5)
    (hoff3 : F.f 0 (x 3) < F.f 0 (x 5) → Off012 F 3)
    (hgen : Gen4 (quad (x 0) (x 5) (x 3) (x 2)) (u0 x (omega3_012 F)) (x 2 - x 1)) :
    FaceChordView F 0 := by
  have hN2 : 0 < ⟪F.N 2, u0 x (omega3_012 F)⟫ := by
    rw [inner_N2_u0]; exact mul_pos (lambda2_pos F) (by linarith)
  refine leaf_core012 F (omega3_012 F) (-1) (Or.inr rfl) hω3 5 3 4 6 3 2 3 6 7 6 (by decide)
    (Or.inr (Or.inr (Or.inr rfl))) ?_ (Or.inl ⟨kap3 F, hbase⟩) hgen (hw_of_ne F 5 3 hfar hoff5 hoff3)
  filter_upwards [ev_neg_u0 (F.N 3) _ (-1) (Or.inl hN3), ev_pos_u0 (F.N 2) _ (-1) (Or.inl hN2),
    ev_pos_u0 (F.N 6) _ (-1) (Or.inl hN6), ev_N7_neg F] with ε h3 h2 h6 h7
  exact ⟨⟨h3, h2⟩, ⟨h3, h6⟩, ⟨h7, h6⟩⟩

theorem inner_N4_e0 (F : S0xFac 9 s0x_S24 x) : ⟪F.N 4, x 0 - x 1⟫ = lambda4 F := by
  have := (F.hN 4 (x 0) (x 1)).symm
  rw [F.zero 4 0 (by decide), zero_sub] at this
  exact this

theorem omega4_inv (F : S0xFac 9 s0x_S24 x) (hω4 : 0 < omega4_012 F) :
    0 < inv_omega4_012 F ∧ omega4_012 F * inv_omega4_012 F = 1 := by
  have hl := lambda4_pos F
  have h0 := inner_N4_e0 F
  unfold omega4_012 at hω4 ⊢
  unfold inv_omega4_012
  rw [h0] at hω4 ⊢ 
  set e := ⟪F.N 4, x 2 - x 1⟫
  have he : e < 0 := by
    by_contra hn; push Not at hn
    have : -e / lambda4 F ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hl.le
    linarith
  have hed : e ≠ 0 := he.ne
  refine ⟨?_, ?_⟩
  · exact div_pos_of_neg_of_neg (by linarith) he
  · field_simp

theorem q012_w4_neg (F : S0xFac 9 s0x_S24 x)
    (hω4 : 0 < omega4_012 F)
    (hN7 : ⟪F.N 7, u0 x (inv_omega4_012 F)⟫ < 0)
    (hN6 : 0 < ⟪F.N 6, u0 x (inv_omega4_012 F)⟫)
    (hN8 : 0 < ⟪F.N 8, u0 x (inv_omega4_012 F)⟫)
    (hbase : min ⟪x 0, u0 x (inv_omega4_012 F)⟫ ⟪x 3, u0 x (inv_omega4_012 F)⟫ <
      max ⟪x 6, u0 x (inv_omega4_012 F)⟫ ⟪x 2, u0 x (inv_omega4_012 F)⟫)
    (hfar : F.f 0 (x 6) ≠ F.f 0 (x 3))
    (hoff6 : F.f 0 (x 6) < F.f 0 (x 3) → Off012 F 6)
    (hoff3 : F.f 0 (x 3) < F.f 0 (x 6) → Off012 F 3)
    (hgen : Gen4 (quad (x 0) (x 6) (x 3) (x 2)) (u0 x (inv_omega4_012 F)) (x 2 - x 1)) :
    FaceChordView F 0 := by
  obtain ⟨hpos, hprod⟩ := omega4_inv F hω4
  refine leaf_core012 F (inv_omega4_012 F) (-1) (Or.inr rfl) hpos 6 3 4 5 1 4 7 8 7 6 (by decide)
    (Or.inl rfl) ?_ (Or.inr ⟨kap4 F, hbase⟩) hgen (hw_of_ne F 6 3 hfar hoff6 hoff3)
  have ht_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < inv_omega4_012 F + (-1) * ε := by
    have := Minimality.eventually_pos_affine (A := inv_omega4_012 F) (B := -1) (Or.inl hpos)
    filter_upwards [this] with ε hε
    linarith
  have e1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 1, u0 x (inv_omega4_012 F + (-1) * ε)⟫ < 0 := by
    filter_upwards [ht_ev] with ε hε
    rw [inner_N1_u0]
    have := lambda1_pos F
    nlinarith
  have e4 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 4, u0 x (inv_omega4_012 F + (-1) * ε)⟫ := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : (0 : ℝ) < ε := hε
    rw [inner_N4_u0]
    have e : 1 - omega4_012 F * (inv_omega4_012 F + (-1) * ε) = omega4_012 F * ε := by
      linear_combination (-1) * hprod
    rw [e]
    exact mul_pos (lambda4_pos F) (mul_pos hω4 hε')
  filter_upwards [e1, e4, ev_neg_u0 (F.N 7) _ (-1) (Or.inl hN7), ev_pos_u0 (F.N 8) _ (-1) (Or.inl hN8),
    ev_pos_u0 (F.N 6) _ (-1) (Or.inl hN6)] with ε h1 h4 h7 h8 h6
  exact ⟨⟨h1, h4⟩, ⟨h7, h8⟩, ⟨h7, h6⟩⟩

end Minimality.T24.R012

