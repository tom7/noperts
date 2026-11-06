module

public import Mathlib
public import MinimalityExtra
public import Minimality.Generic.PV.FaceCircle

/-!
# Lemma SK and Corollary FC (skeletons of a face circle)

Reduction to `Minimality.CU_chain_V`, `CU_chain_L`, `isRupert_faceCircle_skelV`, `_skelL`.
-/

@[expose] public section

open scoped RealInnerProductSpace


namespace MinimalityExtra

theorem listCU_iff (L : List ℝ) : ListCyclicUnimodal L ↔ Minimality.CU L := Iff.rfl

theorem chainSkeleton_eq (a e c : ℝ) : chainSkeleton a e c = Minimality.skel1 a e c := by
  simp [chainSkeleton, Minimality.skel1]

theorem skeletonLemma : SkeletonLemma := by
  intro A B R a e c hnd h2 ha hc he hshape
  rw [listCU_iff, listCU_iff, chainSkeleton_eq]
  rcases hshape with ⟨hA, hB, hext⟩ | ⟨hA, hB, hext⟩
  · exact Minimality.CU_chain_V _ A B R a e c rfl hA hB hnd (by simpa using h2) ha hc he hext
  · exact Minimality.CU_chain_L _ A B R a e c rfl hA hB hnd (by simpa using h2) ha hc he hext

theorem det3_eq' (a b c : ℝ³) : MinimalityExtra.det3 a b c = Minimality.det3 a b c := by
  rw [Minimality.det3_expand]; rfl

theorem faceCircleSkeleton : FaceCircleSkeleton := by
  intro V n u₀ v h σ hσ hn hu₀ hu hV N m hm hmN x hxV hplane hdir hchain hR hinj
    A B R a e c hdepth hAB ha hc he hshape hsk
  simp only [det3_eq'] at hdir hchain hR
  have hR' : ∀ i : ZMod (N + 1), m ≤ i.val + 1 → ∀ y ∈ V, y ≠ x i → y ≠ x (i + 1) →
      Minimality.TiltSignS σ (x (i + 1) - x i) (y - x i) u₀ v := fun i hi y hy h1 h2 => hR i hi y hy h1 h2
  have hsk' : Minimality.CU (Minimality.skel1 a e c ++ R) := by
    rw [← chainSkeleton_eq]; exact hsk
  rcases hshape with ⟨hA, hB, hext⟩ | ⟨hA, hB, hext⟩
  · exact Minimality.isRupert_faceCircle_skelV V n u₀ v h σ hσ hn hu₀ hu hV hm hmN x hxV hplane hdir
      hchain hR' hinj A B R a e c hdepth hAB hA hB ha hc he hext hsk'
  · exact Minimality.isRupert_faceCircle_skelL V n u₀ v h σ hσ hn hu₀ hu hV hm hmN x hxV hplane hdir
      hchain hR' hinj A B R a e c hdepth hAB hA hB ha hc he hext hsk'

end MinimalityExtra
