module

public import Minimality.Generic.WaistW
public import Minimality.Type08S.L2.K71B
public import Minimality.Type08S.L2.K83B

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option maxHeartbeats 1000000
open scoped RealInnerProductSpace
open Minimality Minimality.Type08Sp Minimality.Type08Sp.C2

theorem k88_ptv (x y z : ℝ) : (Minimality.pt x y z : ℝ³) = !₂[x,y,z] := by
  ext i; fin_cases i <;> simp [Minimality.pt]

/-- Orthonormal frame with `T` in the 'positive' direction of `r`. -/
theorem k88_frame {p q r S N : ℝ³} (hdet : det3 p q r ≠ 0) (hS : ⟪S,S⟫ = 1) (hN : ⟪N,N⟫ = 1)
    (hSN : ⟪S,N⟫ = 0) {l : ℝ} (hl : 1 + l ≠ 0) (hSe : ∃ k : ℝ, k ≠ 0 ∧ q - p = k • S)
    (hNR : ∃ k : ℝ, k ≠ 0 ∧ q + l • p = k • N) :
    ∃ T : ℝ³, IsFrame S T N ∧ 0 < ⟪r, T⟫ ∧ ⟪p, T⟫ = 0 ∧ ⟪q, T⟫ = 0 := by
  obtain ⟨k1, hk1, e1⟩ := hSe
  obtain ⟨k2, hk2, e2⟩ := hNR
  have hF := fr_of_orth hS hN hSN
  set T0 := cross S N with hT0
  have hTS : ⟪T0, S⟫ = 0 := hF.n12
  have hTN : ⟪T0, N⟫ = 0 := hF.n13
  have hT0T : ⟪T0, T0⟫ = 1 := hF.n11
  have hp : ⟪p, T0⟫ = 0 := by
    have h1 : ⟪q - p, T0⟫ = 0 := by rw [e1, real_inner_smul_left, real_inner_comm, hTS]; ring
    have h2 : ⟪q + l • p, T0⟫ = 0 := by rw [e2, real_inner_smul_left, real_inner_comm, hTN]; ring
    rw [inner_sub_left] at h1; rw [inner_add_left, real_inner_smul_left] at h2
    have : (1 + l) * ⟪p, T0⟫ = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hl
  have hq : ⟪q, T0⟫ = 0 := by
    have h1 : ⟪q - p, T0⟫ = 0 := by rw [e1, real_inner_smul_left, real_inner_comm, hTS]; ring
    rw [inner_sub_left] at h1; linarith
  have hr : ⟪r, T0⟫ ≠ 0 := by
    intro h0
    have := congrArg (fun x => ⟪x, T0⟫) (cramer p q r T0)
    simp only [real_inner_smul_left, inner_add_left] at this
    rw [hp, hq, h0, hT0T] at this
    apply hdet; nlinarith [this]
  have hTT : IsFrame S T0 N := ⟨hS, hT0T, hN, by rw [real_inner_comm]; exact hTS, hSN, hTN⟩
  rcases lt_or_gt_of_ne hr with h | h
  · have hF' := fr_of_orth hN hS (by rw [real_inner_comm]; exact hSN)
    refine ⟨cross N S, ⟨hS, hF'.n11, hN, ?_, hSN, ?_⟩, ?_, ?_, ?_⟩
    · rw [real_inner_comm]; exact hF'.n13
    · exact hF'.n12
    · have : cross N S = -T0 := by rw [hT0]; exact cross_anti' S N
      rw [this, inner_neg_right]; linarith
    · have : cross N S = -T0 := by rw [hT0]; exact cross_anti' S N
      rw [this, inner_neg_right, hp]; simp
    · have : cross N S = -T0 := by rw [hT0]; exact cross_anti' S N
      rw [this, inner_neg_right, hq]; simp
  · exact ⟨T0, hTT, h, hp, hq⟩

theorem k88_geom {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6)
    (hAv : ⟪a - d, a' - b'⟫ < 0)
    (hzab : ⟪a - b', k61_R a a' b b' d⟫ = 0) (hzba : ⟪a' - b, k61_R a a' b b' d⟫ = 0) :
    ∃ sx sy dz cz ez : ℝ, 0 < sx ∧ 0 < sy ∧
      (IsRupert (WaistW.VV (sx*⟪b-a,b-a⟫) (sx*⟪a'-a,b-a⟫) (sy*γ6) (sx*⟪b'-a,b-a⟫) (sy*β1)
        (sx*⟪d-a,b-a⟫) dz (sx*⟪c'-a,b-a⟫) cz (sx*⟪c-a,b-a⟫) sy ez) → IsRupert (V8 a a' b b' c c' d)) := by
  obtain ⟨hdet, hc', hb', ha', -⟩ := hC
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  set R := k61_R a a' b b' d with hR
  have hRdef : R = q + k61_lam a a' b b' d • p := rfl
  set l := k61_lam a a' b b' d with hl
  have h3 : ⟪a' - b', R⟫ = 0 := k61_tie hAv.ne
  have hRe : ⟪b - a, R⟫ = 0 := by
    have : b - a = -(a' - b) + (a' - b') + (-(a - b')) := by abel
    rw [this, inner_add_left, inner_add_left, inner_neg_left, inner_neg_left, hzab, hzba, h3]; ring
  have hea : b - a = q - p := by rw [hp, hq]; abel
  have he0 : b - a ≠ 0 := by
    intro h; rw [hea] at h
    apply hdet
    exact det3_eq_zero_of_lin (u := p) (v := q) (w := r) (α := -1) (β := 1) (γ := 0)
      (by linear_combination (norm := module) h) (by simp)
  have hR0 : R ≠ 0 := by
    intro h; rw [hRdef] at h
    apply hdet
    exact det3_eq_zero_of_lin (u := p) (v := q) (w := r) (α := l) (β := 1) (γ := 0)
      (by linear_combination (norm := module) h) (by simp)
  have hl1 : 1 + l ≠ 0 := by
    intro h
    have : R = b - a := by rw [hRdef, hea]; have : l = -1 := by linarith
                           rw [this]; module
    rw [this] at hRe
    exact he0 (inner_self_eq_zero.1 hRe)
  have hen : 0 < ‖b - a‖ := norm_pos_iff.2 he0
  have hRn : 0 < ‖R‖ := norm_pos_iff.2 hR0
  set S := (‖b - a‖⁻¹) • (b - a) with hS
  set N := (‖R‖⁻¹) • R with hN
  have hSS : ⟪S, S⟫ = 1 := by
    rw [hS, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]; field_simp
  have hNN : ⟪N, N⟫ = 1 := by
    rw [hN, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]; field_simp
  have hSN : ⟪S, N⟫ = 0 := by
    rw [hS, hN, real_inner_smul_left, real_inner_smul_right, hRe]; simp
  obtain ⟨T, hF, hrT, hpT, hqT⟩ := k88_frame (p := p) (q := q) (r := r) (S := S) (N := N) hdet hSS hNN hSN hl1
    ⟨‖b - a‖, hen.ne', by rw [← hea, hS, smul_smul, mul_inv_cancel₀ hen.ne', one_smul]⟩
    ⟨‖R‖, hRn.ne', by rw [← hRdef, hN, smul_smul, mul_inv_cancel₀ hRn.ne', one_smul]⟩
  refine ⟨‖b - a‖⁻¹, ⟪r, T⟫, ⟪d - a, N⟫, ⟪c' - a, N⟫, ⟪c - a, N⟫, by positivity, hrT, fun hV => ?_⟩
  have hTv : ∀ x, ⟪x - a, T⟫ = ⟪x - d, T⟫ := by
    intro x
    have : x - a = (x - d) - p := by rw [hp]; abel
    rw [this, inner_sub_left, hpT]; ring
  have hSv : ∀ x, ⟪x - a, S⟫ = ‖b - a‖⁻¹ * ⟪x - a, b - a⟫ := by
    intro x; rw [hS, real_inner_smul_right]
  have hNv : ∀ x, ⟪x - a, R⟫ = 0 → ⟪x - a, N⟫ = 0 := by
    intro x h; rw [hN, real_inner_smul_right, h]; ring
  have hb'a : ⟪b' - a, R⟫ = 0 := by
    have : b' - a = -(a - b') := by abel
    rw [this, inner_neg_left, hzab]; ring
  have ha'a : ⟪a' - a, R⟫ = 0 := by
    have : a' - a = (a' - b') + (b' - a) := by abel
    rw [this, inner_add_left, h3, hb'a]; ring
  have hba : ⟪b - a, R⟫ = 0 := hRe
  have ya' : ⟪a' - a, T⟫ = ⟪r, T⟫ * γ6 := by
    rw [hTv]; have : a' - d = β6 • q + γ6 • r := by rw [ha']; abel
    rw [this, inner_add_left, real_inner_smul_left, real_inner_smul_left, hqT]; ring
  have yb' : ⟪b' - a, T⟫ = ⟪r, T⟫ * β1 := by
    rw [hTv]; have : b' - d = α1 • p + β1 • r := by rw [hb']; abel
    rw [this, inner_add_left, real_inner_smul_left, real_inner_smul_left, hpT]; ring
  have yc' : ⟪c' - a, T⟫ = 0 := by
    rw [hTv]; have : c' - d = α1 • p + β1 • q := by rw [hc']; abel
    rw [this, inner_add_left, real_inner_smul_left, real_inner_smul_left, hpT, hqT]; ring
  have yc : ⟪c - a, T⟫ = ⟪r, T⟫ := by rw [hTv]
  have yb : ⟪b - a, T⟫ = 0 := by
    rw [hTv]; have : b - d = q := rfl
    rw [this, hqT]
  have yd : ⟪d - a, T⟫ = 0 := by
    rw [hTv]; simp
  refine isRupert_of_frame_image _ (v := a) hF ?_
  have key : ∀ x, (orthoFrameMat S T N).toEuclideanLin (x - a) = (!₂[⟪x - a, S⟫, ⟪x - a, T⟫, ⟪x - a, N⟫] : ℝ³) :=
    fun x => by rw [orthoFrameMat_apply, k88_ptv]
  simp only [V8, Finset.image_insert, Finset.image_singleton, key]
  have eA : (!₂[⟪a - a, S⟫, ⟪a - a, T⟫, ⟪a - a, N⟫] : ℝ³) = !₂[0,0,0] := by simp
  have eB : (!₂[⟪b - a, S⟫, ⟪b - a, T⟫, ⟪b - a, N⟫] : ℝ³) = !₂[‖b - a‖⁻¹ * ⟪b - a, b - a⟫, 0, 0] := by
    rw [hSv, yb, hNv _ hba]
  have eA' : (!₂[⟪a' - a, S⟫, ⟪a' - a, T⟫, ⟪a' - a, N⟫] : ℝ³) = !₂[‖b - a‖⁻¹ * ⟪a' - a, b - a⟫, ⟪r, T⟫ * γ6, 0] := by
    rw [hSv, ya', hNv _ ha'a]
  have eB' : (!₂[⟪b' - a, S⟫, ⟪b' - a, T⟫, ⟪b' - a, N⟫] : ℝ³) = !₂[‖b - a‖⁻¹ * ⟪b' - a, b - a⟫, ⟪r, T⟫ * β1, 0] := by
    rw [hSv, yb', hNv _ hb'a]
  have eD : (!₂[⟪d - a, S⟫, ⟪d - a, T⟫, ⟪d - a, N⟫] : ℝ³) = !₂[‖b - a‖⁻¹ * ⟪d - a, b - a⟫, 0, ⟪d - a, N⟫] := by
    rw [hSv, yd]
  have eC' : (!₂[⟪c' - a, S⟫, ⟪c' - a, T⟫, ⟪c' - a, N⟫] : ℝ³) = !₂[‖b - a‖⁻¹ * ⟪c' - a, b - a⟫, 0, ⟪c' - a, N⟫] := by
    rw [hSv, yc']
  have eC : (!₂[⟪c - a, S⟫, ⟪c - a, T⟫, ⟪c - a, N⟫] : ℝ³) = !₂[‖b - a‖⁻¹ * ⟪c - a, b - a⟫, ⟪r, T⟫, ⟪c - a, N⟫] := by
    rw [hSv, yc]
  rw [eA, eB, eA', eB', eD, eC', eC]
  convert hV using 1
  unfold WaistW.VV
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto
