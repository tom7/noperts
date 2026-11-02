module

public import Minimality.MaxwellRadonA
public import Minimality.MaxwellRadonB

@[expose] public section


namespace Minimality.MRB

open Real Finset

/-- cumulative polygon vertices -/
noncomputable def mrb_X (L θ : ℕ → ℝ) (k : ℕ) : ℝ := mrb_sx L θ (Finset.range (k + 1))
noncomputable def mrb_Y (L θ : ℕ → ℝ) (k : ℕ) : ℝ := mrb_sy L θ (Finset.range (k + 1))

/-- orientation of three points -/
def mrb_O (X Y : ℕ → ℝ) (i j k : ℕ) : ℝ :=
  (X j - X i) * (Y k - Y i) - (Y j - Y i) * (X k - X i)

theorem mrb_sx_diff (L θ : ℕ → ℝ) {i j : ℕ} (h : i ≤ j) :
    mrb_X L θ j - mrb_X L θ i = mrb_sx L θ (Finset.Ico (i + 1) (j + 1)) := by
  unfold mrb_X mrb_sx
  rw [← Finset.sum_range_add_sum_Ico _ (show i + 1 ≤ j + 1 by omega)]; ring

theorem mrb_sy_diff (L θ : ℕ → ℝ) {i j : ℕ} (h : i ≤ j) :
    mrb_Y L θ j - mrb_Y L θ i = mrb_sy L θ (Finset.Ico (i + 1) (j + 1)) := by
  unfold mrb_Y mrb_sy
  rw [← Finset.sum_range_add_sum_Ico _ (show i + 1 ≤ j + 1 by omega)]; ring

theorem mrb_O_eq (L θ : ℕ → ℝ) {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    mrb_O (mrb_X L θ) (mrb_Y L θ) i j k =
      mrb_sx L θ (Finset.Ico (i + 1) (j + 1)) * mrb_sy L θ (Finset.Ico (j + 1) (k + 1)) -
      mrb_sy L θ (Finset.Ico (i + 1) (j + 1)) * mrb_sx L θ (Finset.Ico (j + 1) (k + 1)) := by
  have h1 := mrb_sx_diff L θ hij
  have h2 := mrb_sx_diff L θ hjk
  have h3 := mrb_sx_diff L θ (hij.trans hjk)
  have g1 := mrb_sy_diff L θ hij
  have g2 := mrb_sy_diff L θ hjk
  have g3 := mrb_sy_diff L θ (hij.trans hjk)
  unfold mrb_O
  have e1 : mrb_X L θ k - mrb_X L θ i = mrb_X L θ j - mrb_X L θ i + (mrb_X L θ k - mrb_X L θ j) := by ring
  have e2 : mrb_Y L θ k - mrb_Y L θ i = mrb_Y L θ j - mrb_Y L θ i + (mrb_Y L θ k - mrb_Y L θ j) := by ring
  rw [e1, e2, h2, g2, h1, g1]; ring

theorem mrb_sx_union (w φ : ℕ → ℝ) {s t : Finset ℕ} (h : Disjoint s t) :
    mrb_sx w φ (s ∪ t) = mrb_sx w φ s + mrb_sx w φ t := by
  unfold mrb_sx; rw [Finset.sum_union h]

theorem mrb_sy_union (w φ : ℕ → ℝ) {s t : Finset ℕ} (h : Disjoint s t) :
    mrb_sy w φ (s ∪ t) = mrb_sy w φ s + mrb_sy w φ t := by
  unfold mrb_sy; rw [Finset.sum_union h]

theorem mrb_sx_range_split (w φ : ℕ → ℝ) {m n : ℕ} (h : m ≤ n) :
    mrb_sx w φ (Finset.range n) = mrb_sx w φ (Finset.range m) + mrb_sx w φ (Finset.Ico m n) := by
  unfold mrb_sx; rw [Finset.sum_range_add_sum_Ico _ h]

theorem mrb_sy_range_split (w φ : ℕ → ℝ) {m n : ℕ} (h : m ≤ n) :
    mrb_sy w φ (Finset.range n) = mrb_sy w φ (Finset.range m) + mrb_sy w φ (Finset.Ico m n) := by
  unfold mrb_sy; rw [Finset.sum_range_add_sum_Ico _ h]

theorem mrb_orient (r : ℕ) (θ L : ℕ → ℝ)
    (hθ : ∀ i j, i < j → j < r → θ i < θ j)
    (hwin : ∀ i j, i < r → j < r → θ i - θ j < 2 * π)
    (hL : ∀ k, k < r → 0 < L k)
    (hF1 : mrb_sy L θ (Finset.range r) = 0) (hF2 : mrb_sx L θ (Finset.range r) = 0) :
    ∀ i j k, i < j → j < k → k < r → 0 < mrb_O (mrb_X L θ) (mrb_Y L θ) i j k := by
  intro i j k hij hjk hk
  rw [mrb_O_eq L θ hij.le hjk.le]
  have hjr : j < r := by omega
  have hir : i < r := by omega
  have hdis : Disjoint (Finset.range (i + 1)) (Finset.Ico (k + 1) r) := by
    rw [Finset.disjoint_left]; intro m hm hm'; simp at hm hm'; omega
  have c1 := mrb_sx_diff L θ hij.le
  have c2 := mrb_sx_diff L θ hjk.le
  have c3 := mrb_sy_diff L θ hij.le
  have c4 := mrb_sy_diff L θ hjk.le
  have s1 := mrb_sx_range_split L θ (show k + 1 ≤ r by omega)
  have s2 := mrb_sy_range_split L θ (show k + 1 ≤ r by omega)
  have u1 := mrb_sx_union L θ hdis
  have u2 := mrb_sy_union L θ hdis
  unfold mrb_X at c1 c2
  unfold mrb_Y at c3 c4
  refine mrb_three L θ (Finset.Ico (i + 1) (j + 1)) (Finset.Ico (j + 1) (k + 1))
    (Finset.range (i + 1) ∪ Finset.Ico (k + 1) r) ⟨j, by simp; omega⟩ ⟨k, by simp; omega⟩
    ⟨i, by simp⟩ ?_ ?_ ?_ ?_ ?_ ?_
  · intro m hm; simp at hm; exact hL m (by omega)
  · intro m hm; simp at hm; exact hL m (by omega)
  · intro m hm; simp at hm; exact hL m (by omega)
  · rw [u1]; linarith
  · rw [u2]; linarith
  · intro a ha b hb c hc
    simp only [Finset.mem_Ico] at ha hb
    have har : a < r := by omega
    have hbr : b < r := by omega
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico] at hc
    rcases hc with hc | hc
    · have hca : c < a := by omega
      have := mrb_tri (hθ c a hca har) (hθ a b (by omega) hbr) (hwin b c hbr (by omega))
      linarith
    · have := mrb_tri (hθ a b (by omega) hbr) (hθ b c (by omega) hc.2) (hwin c a hc.2 har)
      linarith

end Minimality.MRB
