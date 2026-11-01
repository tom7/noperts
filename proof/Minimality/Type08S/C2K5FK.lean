module

public import Minimality.Type08S.C2K5FJ

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem k5f_lexLt_iff (a b : ℝ × ℝ) : LexLt a b ↔ toLex a < toLex b := by
  unfold LexLt; rw [Prod.Lex.lt_iff]; rfl

theorem k5f_lexLt_z {a b : ℝ × ℝ} (h : LexLt a b) : a.1 ≤ b.1 := by
  unfold LexLt at h; rcases h with h | ⟨h, -⟩ <;> linarith

/-- Lex unimodality from "at most one lex peak" (the existence of a peak is automatic). -/
theorem k5f_lexUni_of_pairs {k : ℕ} [NeZero k] (hn1 : ∀ i : ZMod k, i + 1 ≠ i) (hn2 : ∀ i : ZMod k, i - 1 ≠ i)
    (z w : ZMod k → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (hpair : ∀ i j : ZMod k, (LexLt (z (i - 1), w (i - 1)) (z i, w i) ∧ LexLt (z (i + 1), w (i + 1)) (z i, w i)) →
      (LexLt (z (j - 1), w (j - 1)) (z j, w j) ∧ LexLt (z (j + 1), w (j + 1)) (z j, w j)) → i = j) :
    LexUni z w := by
  classical
  refine ⟨hinj, ?_⟩
  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image (Finset.univ : Finset (ZMod k))
    (fun i => toLex (z i, w i)) Finset.univ_nonempty
  have hlt : ∀ j, j ≠ i0 → LexLt (z j, w j) (z i0, w i0) := by
    intro j hj
    rw [k5f_lexLt_iff]
    refine lt_of_le_of_ne (hi0 j (Finset.mem_univ _)) ?_
    intro h
    have h' := toLex.injective h
    exact hj (hinj j i0 (congrArg Prod.fst h') (congrArg Prod.snd h'))
  rw [Finset.card_eq_one]
  refine ⟨i0, ?_⟩
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hj
    exact hpair j i0 hj ⟨hlt _ (hn2 i0), hlt _ (hn1 i0)⟩
  · rintro rfl
    exact ⟨hlt _ (hn2 j), hlt _ (hn1 j)⟩

theorem k5f_E1_lex (P Q R d : ℝ³) {m k t α4 γ4 : ℝ} (hm : 0 < m) (hk : 0 < k) (hk1 : k < 1) (ht : 0 < t)
    (ht1 : t < 1) (hα4 : 1 < α4) (hγ4 : 1 < γ4) (hrel : (γ4 - 1) * (m + k) = α4 * (1 - k))
    (hs : 0 < ⟪R, R⟫)
    (hζ : -t * m * ⟪P, R⟫ + ⟪Q, R⟫ - t * k * ⟪R, R⟫ < -m * ⟪P, R⟫ - k * ⟪R, R⟫)
    (w : ZMod 5 → ℝ)
    (hinj : ∀ i j, ⟪fpoint P Q R d (k5fE1Cyc m k t α4 γ4 i), R⟫ = ⟪fpoint P Q R d (k5fE1Cyc m k t α4 γ4 j), R⟫ →
      w i = w j → i = j) :
    LexUni (fun i => ⟪fpoint P Q R d (k5fE1Cyc m k t α4 γ4 i), R⟫) w := by
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have e0 : (0 : ZMod 5) - 1 = 4 := by decide
  have e1 : (1 : ZMod 5) - 1 = 0 := by decide
  have e2 : (2 : ZMod 5) - 1 = 1 := by decide
  have e3 : (3 : ZMod 5) - 1 = 2 := by decide
  have e4 : (4 : ZMod 5) - 1 = 3 := by decide
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  refine k5f_lexUni_of_pairs (by decide) (by decide) _ _ hinj ?_
  intro i j hi hj
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [e0, e1, e2, e3, e4, f0, f1, f2, f3, f4] at hi hj <;>
    first
    | rfl
    | exact absurd hj.1 (lexLt_asymm hi.2)
    | exact absurd hj.2 (lexLt_asymm hi.1)
    | (exfalso
       have a1 := k5f_lexLt_z hi.1
       have a2 := k5f_lexLt_z hi.2
       have a3 := k5f_lexLt_z hj.1
       have a4 := k5f_lexLt_z hj.2
       simp only [k5fE1Cyc, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4, hz] at a1 a2 a3 a4 hinj
       first
       | linarith
       | exact k5f_E1_real30 (x := ⟪P, R⟫) (s := ⟪R, R⟫) hm hk hs (by linarith) (by linarith)
       | exact k5f_E1_real41 (x := ⟪P, R⟫) (y := ⟪Q, R⟫) (s := ⟪R, R⟫) hm hk ht1 hα4 hγ4 hs (by linarith) (by linarith) (by linarith) (by linarith)
       | exact k5f_E1_real (x := ⟪P, R⟫) (y := ⟪Q, R⟫) (s := ⟪R, R⟫) hm hk hk1 ht ht1 hα4 hγ4 hrel hs (by linarith) (by linarith) (by linarith))

theorem k5f_E2_lex (P Q R d : ℝ³) {m k t α4 γ4 : ℝ} (hm : 0 < m) (hk : 0 < k) (hk1 : k < 1) (ht : 0 < t)
    (ht1 : t < 1) (hα4 : 1 < α4) (hγ4 : 1 < γ4) (hrel : (γ4 - 1) * (m + k) = α4 * (1 - k))
    (hs : 0 < ⟪R, R⟫)
    (hζ : -m * ⟪P, R⟫ - k * ⟪R, R⟫ < -t * m * ⟪P, R⟫ + ⟪Q, R⟫ - t * k * ⟪R, R⟫)
    (w : ZMod 4 → ℝ)
    (hinj : ∀ i j, ⟪fpoint P Q R d (k5fE2Cyc m k t α4 γ4 i), R⟫ = ⟪fpoint P Q R d (k5fE2Cyc m k t α4 γ4 j), R⟫ →
      w i = w j → i = j) :
    LexUni (fun i => ⟪fpoint P Q R d (k5fE2Cyc m k t α4 γ4 i), R⟫) w := by
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have e0 : (0 : ZMod 4) - 1 = 3 := by decide
  have e1 : (1 : ZMod 4) - 1 = 0 := by decide
  have e2 : (2 : ZMod 4) - 1 = 1 := by decide
  have e3 : (3 : ZMod 4) - 1 = 2 := by decide
  obtain ⟨f0, f1, f2, f3⟩ := z4_add
  refine k5f_lexUni_of_pairs (by decide) (by decide) _ _ hinj ?_
  intro i j hi hj
  rcases z4_cases i with rfl | rfl | rfl | rfl <;>
    rcases z4_cases j with rfl | rfl | rfl | rfl <;>
    simp only [e0, e1, e2, e3, f0, f1, f2, f3] at hi hj <;>
    first
    | rfl
    | exact absurd hj.1 (lexLt_asymm hi.2)
    | exact absurd hj.2 (lexLt_asymm hi.1)
    | (exfalso
       have a1 := k5f_lexLt_z hi.1
       have a2 := k5f_lexLt_z hi.2
       have a3 := k5f_lexLt_z hj.1
       have a4 := k5f_lexLt_z hj.2
       simp only [k5fE2Cyc_0, k5fE2Cyc_1, k5fE2Cyc_2, k5fE2Cyc_3, hz] at a1 a2 a3 a4 hinj
       first
       | linarith
       | exact k5f_E2_real (x := ⟪P, R⟫) (y := ⟪Q, R⟫) (s := ⟪R, R⟫) hm hk hk1 ht ht1 hα4 hγ4 hrel hs hζ
           (by linarith) (by linarith))

end C2
end Type08Sp
end Minimality
