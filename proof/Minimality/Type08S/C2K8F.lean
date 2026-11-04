module

public import Minimality.Type08S.C2K8E

@[expose] public section

/-! # K8F: wrapper for `TpA1ii` with `C = ⟪c - d, b - d⟫ > 0`: every `s` except `s = 0` with `⟪t - c', b - d⟫ = 0`
(`t = a'` if `X E ≥ 0`, i.e. `β6 ≥ 1` — this includes `β6 = 1` —, `t = b` if `X E < 0`). -/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

set_option maxHeartbeats 6400000 in
theorem tpA1ii_pos_hasLexCell {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (h : TpA1ii a a' b b' c c' d) (hCp : 0 < ⟪c - d, b - d⟫)
    (h1 : 0 ≤ det3 (a' - b) (c - d) (a - d) * det3 (b - d) (c - d) (a - d) → ⟪a' - c', c - d⟫ = 0 →
      ⟪a' - c', b - d⟫ ≠ 0)
    (h2 : det3 (a' - b) (c - d) (a - d) * det3 (b - d) (c - d) (a - d) < 0 → ⟪b - c', c - d⟫ = 0 →
      ⟪b - c', b - d⟫ ≠ 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hT', -, hAl, hCnn, -, -⟩ := h
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hα4, hγ4, hαγ, hβ1, hβ6p, hγ6, hγ61, hcv⟩ :=
    norm08_coordsTp' N hT'
  set D := det3 (a - d) (c - d) (b - d) with hD
  have hD0 : D ≠ 0 := by
    intro h0; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = -D := by simp only [hD, det3_expand]; ring
    rw [e, h0, neg_zero]
  have hα41 : α4 = 1 := by
    have e1 := det_alpha (b := b) hb'
    have : (α4 - 1) * D = 0 := by rw [hD]; rw [hAl] at e1; linarith
    have := (mul_eq_zero.mp this).resolve_right hD0
    linarith
  subst hα41
  set E := det3 (b - d) (c - d) (a - d) with hE
  have hE' : E = -D := by simp only [hE, hD, det3_expand]; ring
  have eB6 : det3 (a' - b) (c - d) (a - d) = (β6 - 1) * E := by
    rw [ha']; simp only [hE, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hE0 : E ≠ 0 := by rw [hE']; exact neg_ne_zero.2 hD0
  have hEE : 0 < E * E := mul_self_pos.2 hE0
  have hXE : det3 (a' - b) (c - d) (a - d) * E = (β6 - 1) * (E * E) := by rw [eB6]; ring
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  have hΔ : det3 p q r ≠ 0 := hdet
  have eO : fpoint p q r d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eA : fpoint p q r d (1, 0, 0) = a := by simp only [fpoint, fcomb, hp]; module
  have eB : fpoint p q r d (0, 1, 0) = b := by simp only [fpoint, fcomb, hq]; module
  have eC : fpoint p q r d (0, 0, 1) = c := by simp only [fpoint, fcomb, hr]; module
  have eC' : fpoint p q r d (1, β1, 0) = c' := by rw [hc']; simp only [fpoint, fcomb, hp, hq]; module
  have eB' : fpoint p q r d (1, 0, γ4) = b' := by rw [hb']; simp only [fpoint, fcomb, hp, hr]; module
  have eA' : fpoint p q r d (0, β6, γ6) = a' := by rw [ha']; simp only [fpoint, fcomb, hq, hr]; module
  have hr0 : r ≠ 0 := by intro h0; rw [h0] at hΔ; simp [det3_expand] at hΔ
  have hm : ∀ t : ℝ × ℝ × ℝ, (t = (0, 0, 1) ∨ t = (0, 0, 0) ∨ t = (1, 0, 0) ∨ t = (1, β1, 0) ∨
      t = (0, β6, γ6) ∨ t = (0, 1, 0) ∨ t = (1, 0, γ4)) → fpoint p q r d t ∈ V8 a a' b b' c c' d := by
    intro t ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [eO, eA, eB, eC, eC', eB', eA'] <;> simp [V8]
  have hVall : ∀ y ∈ V8 a a' b b' c c' d, y = fpoint p q r d (0, 0, 1) ∨ y = fpoint p q r d (0, 0, 0) ∨
      y = fpoint p q r d (1, 0, 0) ∨ y = fpoint p q r d (1, β1, 0) ∨ y = fpoint p q r d (0, β6, γ6) ∨
      y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (1, 0, γ4) := by
    intro y hy
    simp only [eO, eA, eB, eC, eC', eB', eA']
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  have hCC : ⟪q, r⟫ = ⟪c - d, b - d⟫ := real_inner_comm _ _
  have hC : 0 < ⟪q, r⟫ := by rw [hCC]; exact hCp
  have es1 : ⟪a' - c', r⟫ = (β6 - β1) * ⟪q, r⟫ + γ6 * ⟪r, r⟫ - ⟪p, r⟫ := by
    have : a' - c' = (β6 - β1) • q + γ6 • r - p := by rw [ha', hc']; simp only [hp, hq, hr]; module
    rw [this, inner_sub_left, inner_add_left, inner_smul_left, inner_smul_left]
    simp only [conj_trivial]
  have es2 : ⟪b - c', r⟫ = (1 - β1) * ⟪q, r⟫ - ⟪p, r⟫ := by
    have : b - c' = (1 - β1) • q - p := by rw [hc']; simp only [hp, hq]; module
    rw [this, inner_sub_left, inner_smul_left]
    simp only [conj_trivial]
  have hdA' : fpoint p q r d (0, β6, γ6) - fpoint p q r d (1, β1, 0) = a' - c' := by rw [eA', eC']
  have hdB : fpoint p q r d (0, 1, 0) - fpoint p q r d (1, β1, 0) = b - c' := by rw [eB, eC']
  refine ⟨r, hr0, ?_⟩
  have hs : 1 < β6 + γ6 := hcv
  rcases le_or_gt 0 (det3 (a' - b) (c - d) (a - d) * E) with hge | hlt
  · -- `β6 ≥ 1`, `t = a'`
    have hβ6g : 1 ≤ β6 := by
      by_contra hcon
      push Not at hcon
      rw [hXE] at hge
      nlinarith
    have h1' := h1 hge
    rw [es1] at h1'
    rcases lt_trichotomy ((β6 - β1) * ⟪q, r⟫ + γ6 * ⟪r, r⟫ - ⟪p, r⟫) 0 with hn | hz | hpp
    · obtain ⟨η, hη, hco, -⟩ := k8_tilt4 (β1 := β1) 0 0 hβ1
      exact k8q4p_hasLexCellAt _ p q r d hΔ hβ1 hγ4 hβ6g hγ6 hs (u1 := -η) (u2 := -1) (t1 := -η) (t2 := 0)
        (by simpa using hη.ne') hco hC hn.le (fun e => absurd e hn.ne)
        (fun i => by
          rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;> apply hm <;>
            simp [k8q4pCyc, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5]) hVall
    · have hy0 : ⟪a' - c', q⟫ ≠ 0 := h1' hz
      rcases lt_or_gt_of_ne hy0 with hyn | hyp
      · obtain ⟨η, hη, hco, hw⟩ := k8_tilt1 (β1 := β1) ⟪a' - c', p⟫ ⟪a' - c', q⟫ hβ1
        refine k8q1p_hasLexCellAt _ p q r d hΔ hβ1 hγ4 hβ6g hγ6 hs (u1 := η) (u2 := -1) (t1 := η) (t2 := 0)
          (by simpa using hη.ne') hco hC hz.ge (fun _ lam hl0 hl1 => by rw [hdA']; exact hw hyn lam hl0 hl1)
          (fun i => by
            rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> apply hm <;>
              simp [k8q1pCyc, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4]) hVall
      · obtain ⟨η, hη, hco, hw⟩ := k8_tilt4 (β1 := β1) ⟪a' - c', p⟫ ⟪a' - c', q⟫ hβ1
        refine k8q4p_hasLexCellAt _ p q r d hΔ hβ1 hγ4 hβ6g hγ6 hs (u1 := -η) (u2 := -1) (t1 := -η) (t2 := 0)
          (by simpa using hη.ne') hco hC hz.le (fun _ lam hl0 hl1 => by rw [hdA']; exact hw hyp lam hl0 hl1)
          (fun i => by
            rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;> apply hm <;>
              simp [k8q4pCyc, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5]) hVall
    · obtain ⟨η, hη, hco, -⟩ := k8_tilt1 (β1 := β1) 0 0 hβ1
      exact k8q1p_hasLexCellAt _ p q r d hΔ hβ1 hγ4 hβ6g hγ6 hs (u1 := η) (u2 := -1) (t1 := η) (t2 := 0)
        (by simpa using hη.ne') hco hC hpp.le (fun e => absurd e hpp.ne')
        (fun i => by
          rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> apply hm <;>
            simp [k8q1pCyc, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4]) hVall
  · -- `β6 < 1`, `t = b`
    have hβ6l : β6 < 1 := by
      by_contra hcon
      push Not at hcon
      rw [hXE] at hlt
      nlinarith
    have h2' := h2 hlt
    rw [es2] at h2'
    rcases lt_trichotomy ((1 - β1) * ⟪q, r⟫ - ⟪p, r⟫) 0 with hn | hz | hpp
    · obtain ⟨η, hη, hco, -⟩ := k8_tilt4 (β1 := β1) 0 0 hβ1
      exact k8q4m_hasLexCellAt _ p q r d hΔ hβ1 hγ4 hβ6p hβ6l hγ6 hs (u1 := -η) (u2 := -1) (t1 := -η) (t2 := 0)
        (by simpa using hη.ne') (fun lam hl0 hl1 => ⟨(hco lam hl0 hl1).1, (hco lam hl0 hl1).2.1⟩) hC hn.le
        (fun e => absurd e hn.ne)
        (fun i => by
          rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> apply hm <;>
            simp [k3q4mCyc, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4]) hVall
    · have hy0 : ⟪b - c', q⟫ ≠ 0 := h2' hz
      rcases lt_or_gt_of_ne hy0 with hyn | hyp
      · obtain ⟨η, hη, hco, hw⟩ := k8_tilt1 (β1 := β1) ⟪b - c', p⟫ ⟪b - c', q⟫ hβ1
        refine k8q1m_hasLexCellAt _ p q r d hΔ hβ1 hγ4 hβ6p hβ6l hγ6 hs (u1 := η) (u2 := -1) (t1 := η) (t2 := 0)
          (by simpa using hη.ne') (fun lam hl0 hl1 => ⟨(hco lam hl0 hl1).1, (hco lam hl0 hl1).2.1⟩) hC hz.ge
          (fun _ lam hl0 hl1 => by rw [hdB]; exact hw hyn lam hl0 hl1)
          (fun i => by
            rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;> apply hm <;>
              simp [k3q1mCyc, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5]) hVall
      · obtain ⟨η, hη, hco, hw⟩ := k8_tilt4 (β1 := β1) ⟪b - c', p⟫ ⟪b - c', q⟫ hβ1
        refine k8q4m_hasLexCellAt _ p q r d hΔ hβ1 hγ4 hβ6p hβ6l hγ6 hs (u1 := -η) (u2 := -1) (t1 := -η) (t2 := 0)
          (by simpa using hη.ne') (fun lam hl0 hl1 => ⟨(hco lam hl0 hl1).1, (hco lam hl0 hl1).2.1⟩) hC hz.le
          (fun _ lam hl0 hl1 => by rw [hdB]; exact hw hyp lam hl0 hl1)
          (fun i => by
            rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> apply hm <;>
              simp [k3q4mCyc, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4]) hVall
    · obtain ⟨η, hη, hco, -⟩ := k8_tilt1 (β1 := β1) 0 0 hβ1
      exact k8q1m_hasLexCellAt _ p q r d hΔ hβ1 hγ4 hβ6p hβ6l hγ6 hs (u1 := η) (u2 := -1) (t1 := η) (t2 := 0)
        (by simpa using hη.ne') (fun lam hl0 hl1 => ⟨(hco lam hl0 hl1).1, (hco lam hl0 hl1).2.1⟩) hC hpp.le
        (fun e => absurd e hpp.ne')
        (fun i => by
          rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;> apply hm <;>
            simp [k3q1mCyc, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5]) hVall

end C2
end Type08Sp
end Minimality
