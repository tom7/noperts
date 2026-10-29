module

public import Minimality.Generic.PV.PVRim
public import Minimality.Generic.PV.PVCycle

@[expose] public section


namespace Minimality
open scoped RealInnerProductSpace
open Finset

theorem ofFn_head? {m : ℕ} (hm : 0 < m) (g : Fin m → ℝ) : (List.ofFn g).head? = some (g ⟨0, hm⟩) := by
  rw [List.head?_eq_getElem?]
  simp [List.getElem?_ofFn, hm]

theorem ofFn_getLast? {m : ℕ} (hm : 0 < m) (g : Fin m → ℝ) :
    (List.ofFn g).getLast? = some (g ⟨m - 1, by omega⟩) := by
  rw [List.getLast?_eq_getElem?]
  simp [hm]

/-- **Lemma SK for a face chain** (both signs): the unimodality of `chain-depths ++ R` is that of
the skeleton `(first, extreme, last) ++ R`. -/
theorem chain_cu {s : ℝ} (hs : s = 1 ∨ s = -1) {n d : ℝ³} {F : Finset ℝ³} {A B : ℝ³} {m : ℕ}
    {c : Fin m → ℝ³} (hc : IsFaceChain s n d F A B c) (R : List ℝ) (e : ℝ)
    (he : ∃ i, ⟪d, c i⟫ = e) (hext : ∀ i, s * e ≤ s * ⟪d, c i⟫)
    (hnd : (List.ofFn (fun i => ⟪d, c i⟫) ++ R).Nodup) :
    CU (List.ofFn (fun i => ⟪d, c i⟫) ++ R) ↔ CU (skel1 ⟪d, A⟫ e ⟪d, B⟫ ++ R) := by
  have hm : 0 < m := by have := hc.two; omega
  have ha : (List.ofFn fun i => ⟪d, c i⟫).head? = some ⟪d, A⟫ := by
    rw [ofFn_head? hm, hc.first hm]
  have hb : (List.ofFn fun i => ⟪d, c i⟫).getLast? = some ⟪d, B⟫ := by
    rw [ofFn_getLast? hm, hc.last (by omega)]
  have hmem : e ∈ List.ofFn (fun i => ⟪d, c i⟫) := by
    obtain ⟨i, hi⟩ := he; rw [List.mem_ofFn]; exact ⟨i, hi⟩
  obtain ⟨i0, hi0⟩ := he
  rcases hs with rfl | rfl
  · have hv := hc.vshape
    simp only [one_mul] at hv
    obtain ⟨A', B', hAB, hA, hB, hl⟩ := vshaped_lists _ hv
    rw [hAB] at ha hb hmem hnd ⊢
    refine CU_chain_V m A' B' R _ e _ hl hA hB hnd hc.two ha hb hmem ?_
    intro x hx
    rw [← hAB, List.mem_ofFn] at hx
    obtain ⟨j, rfl⟩ := hx
    simpa using hext j
  · have hv := hc.vshape
    obtain ⟨A', B', hAB, hA, hB, hl⟩ := vshaped_lists _ hv
    have hmap : (List.ofFn fun i => ⟪d, c i⟫) = (A'.map Neg.neg) ++ (B'.map Neg.neg) := by
      rw [← List.map_append, ← hAB, List.map_ofFn]
      apply List.ofFn_inj.mpr
      funext i; simp
    rw [hmap] at ha hb hmem hnd ⊢
    refine CU_chain_L m (A'.map Neg.neg) (B'.map Neg.neg) R _ e _ (by simpa using hl) ?_ ?_ hnd hc.two ha hb hmem ?_
    · rw [List.pairwise_map]; exact hA.imp fun {a b} h => by simpa using h
    · rw [List.pairwise_map]; exact hB.imp fun {a b} h => by simpa using h
    · intro x hx
      rw [← hmap, List.mem_ofFn] at hx
      obtain ⟨j, rfl⟩ := hx
      have := hext j
      linarith

end Minimality
