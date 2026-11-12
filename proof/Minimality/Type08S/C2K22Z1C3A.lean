module

public import Minimality.Type08S.C2K22ZA
public import Minimality.Type08S.C2K19G
public import Minimality.Type08S.C2K18A
public import Minimality.Type08S.C2K17GA4

@[expose] public section


set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- Quadrilateral `b, a', b', c'` in the frame `(b-d, c-d, a-c')`; `ℓ = 1/(α1-1)`. -/
def k22z1c3Y (ℓ α4 γ4 β6 : ℝ) : ZMod 4 → ℝ × ℝ × ℝ :=
  ![(1, 0, 0), (β6, 1, 0), (-α4 * ℓ, γ4, -α4 * ℓ), (-ℓ, 0, -ℓ - 1)]

theorem k22z1c3Y_0 : k22z1c3Y ℓ α4 γ4 β6 0 = (1, 0, 0) := rfl
theorem k22z1c3Y_1 : k22z1c3Y ℓ α4 γ4 β6 1 = (β6, 1, 0) := rfl
theorem k22z1c3Y_2 : k22z1c3Y ℓ α4 γ4 β6 2 = (-α4 * ℓ, γ4, -α4 * ℓ) := rfl
theorem k22z1c3Y_3 : k22z1c3Y ℓ α4 γ4 β6 3 = (-ℓ, 0, -ℓ - 1) := rfl

theorem k22z1c3Y_inj {ℓ α4 γ4 β6 : ℝ} (hℓ : 0 < ℓ) (hα4 : 1 < α4) (hγ4 : 1 < γ4) (hβ6 : 1 < β6) :
    ∀ i j, k22z1c3Y ℓ α4 γ4 β6 i = k22z1c3Y ℓ α4 γ4 β6 j → i = j := by
  intro i j h
  have := mul_pos hℓ (by linarith : (0:ℝ) < α4)
  rcases k19_z4_cases i with rfl | rfl | rfl | rfl <;>
    rcases k19_z4_cases j with rfl | rfl | rfl | rfl <;>
    simp only [k22z1c3Y_0, k22z1c3Y_1, k22z1c3Y_2, k22z1c3Y_3, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith)

set_option maxHeartbeats 12800000 in
theorem k22z1c3_tsc {D ℓ α4 γ4 β6 v1 v2 : ℝ} (hD : 0 < D) (hℓ : 0 < ℓ) (hα4 : 1 < α4) (hγ4 : 1 < γ4)
    (hβ6 : β6 * γ4 = γ4 + α4 - 1) (hv2 : v2 < 0) (hv : γ4 * v1 + (α4 - 1) * ℓ * v2 < 0) :
    (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      TSc D (k22z1c3Y ℓ α4 γ4 β6 (i + 1) - k22z1c3Y ℓ α4 γ4 β6 i)
        (k22z1c3Y ℓ α4 γ4 β6 j - k22z1c3Y ℓ α4 γ4 β6 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 1, 0), (-ℓ, 0, -ℓ)], ∀ i : ZMod 4,
      TSc D (k22z1c3Y ℓ α4 γ4 β6 (i + 1) - k22z1c3Y ℓ α4 γ4 β6 i)
        (t - k22z1c3Y ℓ α4 γ4 β6 i) (v1, v2, 0)) := by
  obtain ⟨e0, e1, e2, e3, f0, f1, f2, f3⟩ := k19_z4
  have hβ61 : 1 < β6 := by nlinarith
  have k1 := hD
  have kl := mul_pos hD hℓ
  have kl1 := mul_pos (mul_pos hD hℓ) (sub_pos.2 hα4)
  have kl2 := mul_pos (mul_pos hD hℓ) (by linarith : (0:ℝ) < α4)
  have kg := mul_pos hD (sub_pos.2 hγ4)
  have kb := mul_pos hD (sub_pos.2 hβ61)
  have kb' := mul_pos hD (by linarith : (0:ℝ) < β6)
  have kgb := mul_pos (mul_pos hD (sub_pos.2 hγ4)) (by linarith : (0:ℝ) < β6)
  have kg' := mul_pos hD (by linarith : (0:ℝ) < γ4)
  have kv := mul_pos hD (neg_pos.2 hv2)
  have kvv := mul_pos hD (neg_pos.2 hv)
  have kgl := mul_pos (mul_pos hD hℓ) (by linarith : (0:ℝ) < γ4)
  have kgl1 := mul_pos (mul_pos hD hℓ) (sub_pos.2 hγ4)
  have kab := mul_pos (mul_pos hD (by linarith : (0:ℝ) < α4)) (by linarith : (0:ℝ) < β6)
  refine ⟨?_, ?_⟩
  · intro i j h1 h2'
    rcases k19_z4_cases i with rfl | rfl | rfl | rfl <;>
      rcases k19_z4_cases j with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, e0, e1, e2, e3, f0, f1, f2, f3, k22z1c3Y_0, k22z1c3Y_1, k22z1c3Y_2, k22z1c3Y_3,
            Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; nlinarith)
         | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;>
    rcases k19_z4_cases i with rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, e0, e1, e2, e3, f0, f1, f2, f3, k22z1c3Y_0, k22z1c3Y_1, k22z1c3Y_2, k22z1c3Y_3,
            Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

/-- Lex unimodality of the 4-cycle `(b, a', b', c')` from the depth facts. -/
theorem k22z1c3_uni (z w : ZMod 4 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h30 : z 3 < z 0) (h : z 1 ≤ z 0 → z 2 < z 1) : LexUni z w := by
  obtain ⟨e0, e1, e2, e3, f0, f1, f2, f3⟩ := k19_z4
  have ne : ∀ i j : ZMod 4, i ≠ j → (z i, w i) ≠ (z j, w j) := fun i j hij e =>
    hij (hinj _ _ (congrArg Prod.fst e) (congrArg Prod.snd e))
  have L : ∀ i j : ZMod 4, z i < z j → LexLt (z i, w i) (z j, w j) := fun i j h => Or.inl h
  have hl30 := L 3 0 h30
  have pk1 : LexLt (z 0, w 0) (z 1, w 1) → LexLt (z 2, w 2) (z 1, w 1) → LexUni z w := fun l01 l21 => by
    refine k19_lexUni_nb z w hinj 1 (by rw [f1]; exact l01) (by rw [e1]; exact l21) ?_
    intro i hi
    rcases k19_z4_cases i with rfl | rfl | rfl | rfl
    · right; rw [e0]; exact l01
    · exact absurd rfl hi
    · left; rw [f2]; exact l21
    · right; rw [e3]; exact hl30
  have pk0 : LexLt (z 1, w 1) (z 0, w 0) → LexLt (z 2, w 2) (z 1, w 1) → LexUni z w := fun l10 l21 => by
    refine k19_lexUni_nb z w hinj 0 (by rw [f0]; exact hl30) (by rw [e0]; exact l10) ?_
    intro i hi
    rcases k19_z4_cases i with rfl | rfl | rfl | rfl
    · exact absurd rfl hi
    · left; rw [f1]; exact l10
    · left; rw [f2]; exact l21
    · right; rw [e3]; exact hl30
  have pk2 : LexLt (z 0, w 0) (z 1, w 1) → LexLt (z 1, w 1) (z 2, w 2) → LexUni z w := fun l01 l12 => by
    have h12 : z 1 ≤ z 2 := by rcases l12 with h | ⟨h, _⟩ <;> linarith
    have h01 : z 0 ≤ z 1 := by rcases l01 with h | ⟨h, _⟩ <;> linarith
    have l32 := L 3 2 (by linarith)
    refine k19_lexUni_nb z w hinj 2 (by rw [f2]; exact l12) (by rw [e2]; exact l32) ?_
    intro i hi
    rcases k19_z4_cases i with rfl | rfl | rfl | rfl
    · right; rw [e0]; exact l01
    · right; rw [e1]; exact l12
    · exact absurd rfl hi
    · right; rw [e3]; exact hl30
  rcases lt_or_ge (z 0) (z 1) with h01 | h01
  · have l01 := L 0 1 h01
    rcases lexLt_total (ne 1 2 (by decide)) with l12 | l21
    · exact pk2 l01 l12
    · exact pk1 l01 l21
  · have l21 := L 2 1 (h h01)
    rcases lexLt_total (ne 0 1 (by decide)) with l01 | l10
    · exact pk1 l01 l21
    · exact pk0 l10 l21

end C2
end Type08Sp
end Minimality
