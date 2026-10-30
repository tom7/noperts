module

public import Minimality.Type08S.P2TBt2
public import Minimality.Type08S.P2TB2e

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkP / B / Bt3: `close_caseB_T` (statement as `PT1.lean`).
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- N2's weak far triple at `T` (`caseB_Xba`'s second alternative).  (Copied from PT1.) -/
def N2WST (a' b b' c c' d : ℝ³) : Prop :=
  ⟪b, b - d⟫ = ⟪c', b - d⟫ ∧ ⟪b', b - d⟫ = ⟪c', b - d⟫ ∧ ⟪c, b - d⟫ ≤ ⟪c', b - d⟫ ∧ ⟪c', b - d⟫ ≤ ⟪a', b - d⟫

/-- **The case-B leftover at `T`** (copied from PT1). -/
def S4TB (a a' b b' c c' d : ℝ³) : Prop :=
  IsT a' b c d ∧ ¬ RobKb a a' b b' c c' d ∧
    ((N2WST a' b b' c c' d ∧ AngBig a b b' c d ∧ ¬ NoPersistHDN (quad d c' b' c) (b - d) (eAB b c' d)) ∨
     (N2WST a' b b' c c' d ∧ ¬ AngBig a b b' c d ∧ ¬ NoHDNAt ({d, c', b', c} : Finset ℝ³) (b - d)) ∨
     (RobXba a' b b' c' d ∧ ¬ AngBig a b b' c d ∧ ⟪c', b - d⟫ = ⟪b', b - d⟫ ∧
       ¬ NoHDNAt ({b, c', b', a'} : Finset ℝ³) (b - d) ∧ ¬ NoHDNAt ({d, c', b', c} : Finset ℝ³) (b - d)))

variable {e1 e2 e3 : ℝ³}

/-- The labels of the `K_2` tests are the quadrilateral `(d, c', b', c)`. -/
theorem lab_K2f (a a' b b' c c' d : ℝ³) (j : ZMod 4) :
    pts08 a a' b b' c c' d ((test08 1 false false).lab j) = quad d c' b' c j := by
  rcases zmod4_cases j with rfl | rfl | rfl | rfl <;> rfl

theorem lab_K2t (a a' b b' c c' d : ℝ³) (j : ZMod 4) :
    pts08 a a' b b' c c' d ((test08 1 true false).lab j) = quad d c' b' c j := by
  rcases zmod4_cases j with rfl | rfl | rfl | rfl <;> rfl

theorem quad_mem (d c' b' c : ℝ³) (j : ZMod 4) : quad d c' b' c j ∈ ({d, c', b', c} : Finset ℝ³) := by
  rcases zmod4_cases j with rfl | rfl | rfl | rfl <;> simp [quad]

/-- A rim HDN of `K_2` gives `¬ NoHDNAt {d, c', b', c} (b - d)`. -/
theorem hdn_K2 {a a' b b' c c' d : ℝ³} {s : Bool} (h : RobHDN a a' b b' c c' d (1, s, false)) :
    ¬ NoHDNAt ({d, c', b', c} : Finset ℝ³) (b - d) := by
  intro hno
  obtain ⟨k', hk', σ, -, -, hnh⟩ := h
  apply hnh
  cases s
  · have hu : (test08 1 false false).view (pts08 a a' b b' c c' d) = -(b - d) := rfl
    have hmem : ∀ i, pts08 a a' b b' c c' d ((test08 1 false false).lab (σ i)) ∈
        ({d, c', b', c} : Finset ℝ³) := fun i => by
          have h1 := lab_K2f a a' b b' c c' d (σ i)
          have h2 := quad_mem d c' b' c (σ i)
          rw [← h1] at h2; exact h2
    show NoHDNRim _ ((test08 1 false false).view (pts08 a a' b b' c c' d))
    rw [hu]
    exact hno.neg.rim _ hmem
  · have hu : (test08 1 true false).view (pts08 a a' b b' c c' d) = b - d := rfl
    have hmem : ∀ i, pts08 a a' b b' c c' d ((test08 1 true false).lab (σ i)) ∈
        ({d, c', b', c} : Finset ℝ³) := fun i => by
          have h1 := lab_K2t a a' b b' c c' d (σ i)
          have h2 := quad_mem d c' b' c (σ i)
          rw [← h1] at h2; exact h2
    show NoHDNRim _ ((test08 1 true false).view (pts08 a a' b b' c c' d))
    rw [hu]
    exact hno.rim _ hmem

/-- Frame-level key: `NoPersistHDN (quad)` gives the rim version for `κv • e3`. -/
theorem noPersist_key {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hT : IsT a' b c d)
    (hF : Fr e1 e2 e3) {κ : ℝ} (hκ : κ ≠ 0) (hxe : d - b = κ • e3) (hf2 : ⟪c' - b, e2⟫ = 0)
    (hL : 0 < ⟪c' - b, e1⟫) (hr' : 0 < ⟪b' - b, e2⟫)
    (hq : NoPersistHDN (quad d c' b' c) (b - d) (eAB b c' d)) {k' : ℕ} [NeZero k'] (σ : ZMod k' → ZMod 4)
    (κv : ℝ) (hκv : κv = κ ∨ κv = -κ)
    (hcyc : ∀ i j : ZMod k', j ≠ i → j ≠ i + 1 → 0 < det3 (quad d c' b' c (σ (i + 1)) - quad d c' b' c (σ i))
      (quad d c' b' c (σ j) - quad d c' b' c (σ i)) (κv • e3))
    (hleft : ∀ (i : ZMod k') (a_ : ZMod 4), 0 ≤ det3 (quad d c' b' c (σ (i + 1)) - quad d c' b' c (σ i))
      (quad d c' b' c a_ - quad d c' b' c (σ i)) (κv • e3)) (hk3 : 3 ≤ k') :
    NoPersistHDN (fun i => quad d c' b' c (σ i)) (κv • e3) (⟪c' - b, e1⟫ • e1) := by
  have hκ0 : -κ ≠ 0 := neg_ne_zero.mpr hκ
  have hbd : b - d = (-κ) • e3 := by rw [neg_smul, ← hxe]; abel
  have hq1 : NoPersistHDN (quad d c' b' c) ((-κ) • e3) (⟪c' - b, e1⟫ • e1) := by
    have := hq
    rw [hbd] at this
    have he : eAB b c' d = ⟪c' - b, e1⟫ • e1 := by
      unfold eAB
      rw [hbd]
      exact eF_of_view hF _ _ (-κ) hκ0 rfl hf2
    rw [he] at this
    exact this
  have hκv0 : κv ≠ 0 := by rcases hκv with h | h <;> rw [h] <;> simp [hκ]
  have hq2 := noPersist_u_smul hq1 (lam := κv / (-κ)) (div_ne_zero hκv0 hκ0)
  have : (κv / (-κ)) • ((-κ) • e3) = κv • e3 := by rw [smul_smul]; congr 1; field_simp
  rw [this] at hq2
  exact noPersist_core N hT hF hκ hκv hxe hf2 hL hr' hk3 σ _ _ rfl rfl hcyc hleft hq2

/-- `NoPersistHDN` for the quadrilateral gives it for the rim of `K_2` at `T`. -/
theorem noPersist_sigma {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hT : IsT a' b c d) {s : Bool}
    {k' : ℕ} [NeZero k'] {σ : ZMod k' → ZMod (test08 1 s false).k}
    (hrim : RimCertAt (pts08 a a' b b' c c' d) ((test08 1 s false).view (pts08 a a' b b' c c' d))
      ((test08 1 s false).lab ∘ σ))
    (hrob : IsRobustUnimodal (fun i => ⟪pts08 a a' b b' c c' d ((test08 1 s false).lab (σ i)),
      (test08 1 s false).view (pts08 a a' b b' c c' d)⟫))
    (hq : NoPersistHDN (quad d c' b' c) (b - d) (eAB b c' d)) :
    NoPersistHDN (fun i => pts08 a a' b b' c c' d ((test08 1 s false).lab (σ i)))
      ((test08 1 s false).view (pts08 a a' b b' c c' d)) (eF a a' b b' c c' d (1, s, false)) := by
  obtain ⟨e1, e2, e3, κ, hF, hκ, hxe, hf2, hL, hr'⟩ := frame_K2 N
  have hκ0 : -κ ≠ 0 := neg_ne_zero.mpr hκ
  cases s
  · have hu : (test08 1 false false).view (pts08 a a' b b' c c' d) = κ • e3 := by
      show -(b - d) = κ • e3
      rw [neg_sub]; exact hxe
    obtain ⟨hk3, hcyc, hleft, hz⟩ := rim_transfer (m := 4) (test08 1 false false).lab σ _
      (quad d c' b' c) (lab_K2f a a' b b' c c' d) hrim hrob
    rw [hu] at hcyc hleft
    have := noPersist_key N hT hF hκ hxe hf2 hL hr' hq σ κ (Or.inl rfl) hcyc hleft hk3
    rw [hu]
    have he : eF a a' b b' c c' d (1, false, false) = ⟪c' - b, e1⟫ • e1 :=
      (show eF a a' b b' c c' d (1, false, false) = _ from rfl).trans (eF_of_view hF _ _ κ hκ hu hf2)
    rw [he]
    have hfun : (fun i => pts08 a a' b b' c c' d ((test08 1 false false).lab (σ i))) =
        fun i => quad d c' b' c (σ i) := funext fun i => lab_K2f a a' b b' c c' d (σ i)
    rw [hfun]; exact this
  · have hbd : b - d = (-κ) • e3 := by rw [neg_smul, ← hxe]; abel
    have hu : (test08 1 true false).view (pts08 a a' b b' c c' d) = (-κ) • e3 := by
      show b - d = (-κ) • e3
      exact hbd
    obtain ⟨hk3, hcyc, hleft, hz⟩ := rim_transfer (m := 4) (test08 1 true false).lab σ _
      (quad d c' b' c) (lab_K2t a a' b b' c c' d) hrim hrob
    rw [hu] at hcyc hleft
    have := noPersist_key N hT hF hκ hxe hf2 hL hr' hq σ (-κ) (Or.inr rfl) hcyc hleft hk3
    rw [hu]
    have he : eF a a' b b' c c' d (1, true, false) = ⟪c' - b, e1⟫ • e1 :=
      (show eF a a' b b' c c' d (1, true, false) = _ from rfl).trans (eF_of_view hF _ _ (-κ) hκ0 hu hf2)
    rw [he]
    have hfun : (fun i => pts08 a a' b b' c c' d ((test08 1 true false).lab (σ i))) =
        fun i => quad d c' b' c (σ i) := funext fun i => lab_K2t a a' b b' c c' d (σ i)
    rw [hfun]; exact this

theorem close_caseB_T {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hT : IsT a' b c d)
    (hB : ¬ RobKb a a' b b' c c' d) {s : Bool} (h : RobHDN a a' b b' c c' d (1, s, false)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨ S4TB a a' b b' c c' d := by
  classical
  have hHDN := hdn_K2 h
  rcases caseB_Xba N hT hB with hX | hN2
  · by_cases hang : AngBig a b b' c d
    · exact Or.inl (cellXba_rupert N hT hang hX)
    by_cases heq : ⟪c', b - d⟫ = ⟪b', b - d⟫
    · by_cases hno : NoHDNAt ({b, c', b', a'} : Finset ℝ³) (b - d)
      · exact Or.inl (poly_rupert_off N hT (x0 := b) (x0' := d) (y0 := a') (y0' := c)
          (Or.inl ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩) hX hno)
      · exact Or.inr ⟨hT, hB, Or.inr (Or.inr ⟨hX, hang, heq, hno, hHDN⟩)⟩
    · exact Or.inl (cellXba2_rupert N hT hB hang hX heq)
  · have hN : N2WST a' b b' c c' d := hN2
    by_cases hang : AngBig a b b' c d
    · by_cases hnp : NoPersistHDN (quad d c' b' c) (b - d) (eAB b c' d)
      · obtain ⟨k', hk', σ, hrim, hrob, -⟩ := h
        exact Or.inl (K2_slide_angBig N hT hang hrim hrob (noPersist_sigma N hT hrim hrob hnp))
      · exact Or.inr ⟨hT, hB, Or.inl ⟨hN, hang, hnp⟩⟩
    · exact Or.inr ⟨hT, hB, Or.inr (Or.inl ⟨hN, hang, hHDN⟩)⟩

end Type08Sp
end Minimality

