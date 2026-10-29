module

public import Minimality.Generic.PV.PVChain

@[expose] public section


/-! Sequences with no consecutive local maximum are V-shaped; splitting into the two runs. -/
namespace Minimality
open Finset

theorem vshaped_nat {n : ℕ} (g : ℕ → ℝ) (hn : 0 < n)
    (hinj : ∀ i j, i < n → j < n → g i = g j → i = j)
    (hc : ∀ k, k + 2 < n → g (k + 1) < max (g k) (g (k + 2))) :
    ∃ m, m < n ∧ (∀ i j, i < j → j ≤ m → g j < g i) ∧ (∀ i j, m ≤ i → i < j → j < n → g i < g j) := by
  obtain ⟨m, hm, hmin⟩ := (Finset.range n).exists_min_image g ⟨0, by simpa using hn⟩
  have hm' : m < n := by simpa using hm
  have hlt : ∀ i, i < n → i ≠ m → g m < g i := fun i hi him =>
    lt_of_le_of_ne (hmin i (by simpa using hi)) (fun e => him (hinj _ _ hm' hi e).symm)
  -- left part: steps go down
  have hdown : ∀ k, k + 1 ≤ m → g (k + 1) < g k := by
    intro k hk
    by_contra hcon
    have hup : g k < g (k + 1) := by
      rcases lt_trichotomy (g k) (g (k + 1)) with h | h | h
      · exact h
      · exact absurd (hinj _ _ (by omega) (by omega) h) (by omega)
      · exact absurd h hcon
    -- propagate upward to m
    have : ∀ t, k + t + 1 ≤ m → g (k + t) < g (k + t + 1) := by
      intro t
      induction t with
      | zero => intro _; simpa using hup
      | succ t ih =>
        intro ht
        have h1 := ih (by omega)
        have h2 := hc (k + t) (by omega)
        have h3 : g (k + t + 1) < g (k + t + 2) := by
          rcases lt_max_iff.mp h2 with h | h
          · linarith
          · exact h
        have e1 : k + (t + 1) = k + t + 1 := by omega
        rw [e1]; exact h3
    have h4 := this (m - k - 1) (by omega)
    have e2 : k + (m - k - 1) + 1 = m := by omega
    rw [e2] at h4
    have := hmin (k + (m - k - 1)) (by simp; omega)
    linarith
  have hupr : ∀ k, m ≤ k → k + 1 < n → g k < g (k + 1) := by
    intro k hk hk1
    by_contra hcon
    have hd : g (k + 1) < g k := by
      rcases lt_trichotomy (g k) (g (k + 1)) with h | h | h
      · exact absurd h hcon
      · exact absurd (hinj _ _ (by omega) (by omega) h) (by omega)
      · exact h
    -- propagate downward to m
    have : ∀ t, t ≤ k - m → g (k - t + 1) < g (k - t) := by
      intro t
      induction t with
      | zero => intro _; simpa using hd
      | succ t ih =>
        intro ht
        have h1 := ih (by omega)
        have h2 := hc (k - t - 1) (by omega)
        have e1 : k - t - 1 + 1 = k - t := by omega
        have e2 : k - t - 1 + 2 = k - t + 1 := by omega
        rw [e1, e2] at h2
        have h3 : g (k - t) < g (k - t - 1) := by
          rcases lt_max_iff.mp h2 with h | h
          · exact h
          · linarith
        have e3 : k - (t + 1) = k - t - 1 := by omega
        rw [e3]
        have e4 : k - t - 1 + 1 = k - t := by omega
        rw [e4]; exact h3
    have h4 := this (k - m) le_rfl
    have e5 : k - (k - m) = m := by omega
    rw [e5] at h4
    have h5 := hmin (m + 1) (by simp; omega)
    have h6 := hlt (m + 1) (by omega) (by omega)
    linarith
  refine ⟨m, hm', ?_, ?_⟩
  · intro i j hij hjm
    induction j, hij using Nat.le_induction with
    | base => exact hdown i hjm
    | succ j hij ih =>
      exact lt_trans (hdown j hjm) (ih (by omega))
  · intro i j hmi hij hjn
    induction j, hij using Nat.le_induction with
    | base => exact hupr i hmi hjn
    | succ j hij ih =>
      exact lt_trans (ih (by omega)) (hupr j (by omega) hjn)

/-- Split a V-shaped sequence into a strictly decreasing and a strictly increasing run. -/
theorem vshaped_lists {n : ℕ} (f : Fin n → ℝ) (hv : VShapedSeq f) :
    ∃ A B : List ℝ, List.ofFn f = A ++ B ∧ A.Pairwise (· > ·) ∧ B.Pairwise (· < ·) ∧
      A.length + B.length = n := by
  obtain ⟨m, hdec, hinc⟩ := hv
  have hm : (m : ℕ) < n := m.isLt
  refine ⟨List.ofFn (fun i : Fin ((m : ℕ) + 1) => f ⟨i, by omega⟩),
    List.ofFn (fun i : Fin (n - ((m : ℕ) + 1)) => f ⟨(m : ℕ) + 1 + i, by omega⟩), ?_, ?_, ?_, ?_⟩
  · apply List.ext_getElem
    · simp; omega
    · intro i h1 h2
      simp only [List.getElem_ofFn, List.getElem_append]
      split_ifs with h
      · simp
      · simp only [List.length_ofFn] at h
        simp only [List.getElem_ofFn, List.length_ofFn]
        congr 1; ext; simp; omega
  · rw [List.pairwise_ofFn]
    intro i j hij
    refine hdec ⟨i, by omega⟩ ⟨j, by omega⟩ (Fin.mk_lt_mk.mpr hij) ?_
    show (j : ℕ) ≤ (m : ℕ)
    have := j.isLt; omega
  · rw [List.pairwise_ofFn]
    intro i j hij
    refine hinc ⟨(m : ℕ) + 1 + i, by omega⟩ ⟨(m : ℕ) + 1 + j, by omega⟩ ?_ ?_
    · show (m : ℕ) ≤ (m : ℕ) + 1 + i
      omega
    · show (m : ℕ) + 1 + i < (m : ℕ) + 1 + j
      have : (i : ℕ) < j := hij
      omega
  · simp

theorem vshaped_of_consec {n : ℕ} (f : Fin n → ℝ) (hn : 0 < n) (hinj : Function.Injective f)
    (hc : ∀ k (h : k + 2 < n), f ⟨k + 1, by omega⟩ < max (f ⟨k, by omega⟩) (f ⟨k + 2, h⟩)) :
    VShapedSeq f := by
  obtain ⟨m, hmn, h1, h2⟩ := vshaped_nat (n := n) (fun j => if h : j < n then f ⟨j, h⟩ else 0) hn
    (by
      intro i j hi hj he
      simp only [hi, hj, dite_true] at he
      exact congrArg Fin.val (hinj he))
    (by
      intro k hk
      simpa [show k < n by omega, show k + 1 < n by omega, hk] using hc k hk)
  refine ⟨⟨m, hmn⟩, fun i j hij hjm => ?_, fun i j hmi hij => ?_⟩
  · have := h1 i j hij hjm
    simpa [i.isLt, j.isLt] using this
  · have := h2 i j hmi hij j.isLt
    simpa [i.isLt, j.isLt] using this

end Minimality
