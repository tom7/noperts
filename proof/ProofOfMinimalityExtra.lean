module

public import MinimalityExtra.ShadowMap
public import MinimalityExtra.Sandwich
public import MinimalityExtra.Chirotope
public import MinimalityExtra.Sanity
public import MinimalityExtra.VertexOverBoundary
public import MinimalityExtra.LimitRows
public import MinimalityExtra.SeptLimit
public import MinimalityExtra.MetricIdentities
public import MinimalityExtra.TorqueForms
public import MinimalityExtra.MetricFreedom
public import MinimalityExtra.Opposite
public import MinimalityExtra.PassageSymmetry
public import MinimalityExtra.ArrangementVertex
public import MinimalityExtra.FaceNormal
public import MinimalityExtra.TetraViews
public import MinimalityExtra.PictureSymmetric
public import MinimalityExtra.NoUnimodal
public import MinimalityExtra.GramExtension
public import MinimalityExtra.Box
public import MinimalityExtra.NoUnimodalOpenNear
public import MinimalityExtra.NoUnimodalOpen
public import MinimalityExtra.MetricSpin
public import MinimalityExtra.MetricUniform
public import MinimalityExtra.SilhouetteCodes
public import MinimalityExtra.Merge
public import MinimalityExtra.TwoPeakRim
public import MinimalityExtra.CoplanarIff
public import MinimalityExtra.NoUnimodalCheck
public import MinimalityExtra.FlatMetrics
public import MinimalityExtra.TestPairs
public import MinimalityExtra.NoUnimodalOpenCheck
public import MinimalityExtra.FacePairRigid
public import MinimalityExtra.NoUnimodalData
public import MinimalityExtra.NoUnimodalOpenData
public import MinimalityExtra.DepthSeparated
public import MinimalityExtra.EdgePlane
public import MinimalityExtra.StrictSeptRupert
public import MinimalityExtra.BoxShadow
public import MinimalityExtra.FaceCircleSkeleton
public import MinimalityExtra.AcuteEdge
public import MinimalityExtra.PatchEdge
public import MinimalityExtra.TwoDisjointFaces
public import Minimality.Tilt
public import Minimality.Thm73
public import Minimality.Crossing
public import Minimality.OctaTools
/-!
# The definitions of `MinimalityExtra.lean` agree with the project's

* `MinimalityExtra.det3`, `cross`, `TiltCert`, `IsCyclicUnimodal` agree with the
  `Minimality` ones, so `HasFirstOrderPassage V` implies `IsRupert V`.
* `unimodalViewIsRupert`: `HasUnimodalView x → IsRupert`, by `Minimality.isRupert_of_tilted_unimodal`
  with no tilt; `coplanarSilhouetteIsRupert` (Theorem 5), `triangleShadowIsRupert`, `FreeAt.isRupert`.
-/

@[expose] public section


namespace MinimalityExtra

theorem cross_eq (a b : EuclideanSpace ℝ (Fin 3)) : MinimalityExtra.cross a b = Minimality.cross a b := rfl

theorem det3_eq (a b c : EuclideanSpace ℝ (Fin 3)) : MinimalityExtra.det3 a b c = Minimality.det3 a b c := by
  rw [Minimality.det3_expand]; rfl

theorem tiltCert_iff (V : Finset (EuclideanSpace ℝ (Fin 3))) (w ω τ x : EuclideanSpace ℝ (Fin 3)) :
    MinimalityExtra.TiltCert V w ω τ x ↔ Minimality.TiltCert V w ω τ x := by
  simp only [MinimalityExtra.TiltCert, Minimality.TiltCert, det3_eq, cross_eq]

theorem isCyclicUnimodal_iff {k : ℕ} [NeZero k] (z : ZMod k → ℝ) :
    MinimalityExtra.IsCyclicUnimodal z ↔ Minimality.IsCyclicUnimodal z := Iff.rfl

theorem HasFirstOrderPassage.isRupert {V : Finset (EuclideanSpace ℝ (Fin 3))} (h : HasFirstOrderPassage V) :
    IsRupert V := by
  obtain ⟨w, ω, τ, hw, hc⟩ := h
  exact Minimality.isRupert_of_tiltCert V w hw ω τ fun y hy => (tiltCert_iff V w ω τ y).1 (hc y hy)

section Core
open scoped RealInnerProductSpace
open Finset

open scoped RealInnerProductSpace

theorem coplanarSilhouetteIsRupert : CoplanarSilhouetteIsRupert := by
  intro V W u hWV hW _ hu h
  exact Minimality.isRupert_of_admissibleViews_nonempty V W hWV hW ⟨u, hu, h⟩

theorem triangleShadowIsRupert : TriangleShadowIsRupert := by
  classical
  intro V a b c u ha hb hc hai hu h
  have hcol : ¬ Collinear ℝ ({a, b, c} : Set ℝ³) := by
    rw [affineIndependent_iff_not_collinear_set] at hai
    exact hai
  have hsub : ({a, b, c} : Finset ℝ³) ⊆ V := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hco : (({a, b, c} : Finset ℝ³) : Set ℝ³) = {a, b, c} := by simp
  refine Minimality.isRupert_of_admissibleViews_nonempty V {a, b, c} hsub (by rwa [hco]) ⟨u, by rwa [hco], ?_⟩
  intro v hv hvW
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hvW
  rw [hco]; exact h v hv hvW.1 hvW.2.1 hvW.2.2

theorem FreeAt.isRupert {V : Finset ℝ³} {w : ℝ³} (hw : w ≠ 0) (h : FreeAt V w) : IsRupert V := by
  obtain ⟨ω, τ, hc⟩ := h
  exact HasFirstOrderPassage.isRupert ⟨w, ω, τ, hw, hc⟩

open scoped RealInnerProductSpace
open Finset

theorem unimodalViewIsRupert : UnimodalViewIsRupert := by
  classical
  intro x ⟨u, k, hk, lab, h3, hinj, hrim, hz⟩
  have hu : u ≠ 0 := by
    rintro rfl
    have h2 : (2 : ZMod k) ≠ 0 := by
      intro h
      have h' : ((2:ℕ) : ZMod k) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at h'
      have := Nat.le_of_dvd (by norm_num) h'; omega
    have h1 : (2 : ZMod k) ≠ 1 := by
      intro h
      have h' : ((1:ℕ) : ZMod k) = 0 := by
        have : (2 : ZMod k) - 1 = 0 := by rw [h]; simp
        have e : ((1:ℕ) : ZMod k) = (2 : ZMod k) - 1 := by norm_num
        rw [e]; exact this
      rw [ZMod.natCast_eq_zero_iff] at h'
      have := Nat.le_of_dvd (by norm_num) h'; omega
    have := hrim (lab 2) 0 (fun h => h2 (hinj h)) (fun h => by simp at h; exact h1 (hinj h))
    simp [det3_eq, Minimality.det3, Minimality.cross] at this
  let z0 : ZMod k → ℝ := fun i => ⟪x (lab i), u⟫
  have hz' : Minimality.IsCyclicUnimodal z0 := hz
  refine Minimality.isRupert_of_tilted_unimodal (Finset.univ.image x) u 0 hu h3 (fun i => x (lab i))
    (fun i => mem_image_of_mem _ (mem_univ _)) ?_ ?_
    (fun z => ∀ i, (z0 i < z0 (i+1) → z i < z (i+1)) ∧ (z0 (i+1) < z0 i → z (i+1) < z i))
    ?_ ?_ ?_ ?_
  · intro i j hji hji1
    left
    have := hrim (lab j) i (fun h => hji (hinj h)) (fun h => hji1 (hinj h))
    rwa [det3_eq] at this
  · intro y hy hyx i
    left
    obtain ⟨m, -, rfl⟩ := mem_image.mp hy
    have := hrim m i (fun h => hyx i (by rw [h])) (fun h => hyx (i+1) (by rw [h]))
    rwa [det3_eq] at this
  · rw [Set.ofPred_forall]
    refine isOpen_iInter_of_finite fun i => ?_
    refine IsOpen.inter ?_ ?_
    · by_cases c : z0 i < z0 (i+1)
      · simp only [c, true_imp_iff]; exact isOpen_lt (continuous_apply i) (continuous_apply (i+1))
      · simp only [c, false_imp_iff]; exact isOpen_univ
    · by_cases c : z0 (i+1) < z0 i
      · simp only [c, true_imp_iff]; exact isOpen_lt (continuous_apply (i+1)) (continuous_apply i)
      · simp only [c, false_imp_iff]; exact isOpen_univ
  · intro z c hc hQ i
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := (hQ i).1 h; simp only; nlinarith
    · have := (hQ i).2 h; simp only; nlinarith
  · intro i; exact ⟨fun h => h, fun h => h⟩
  · intro z zi hQ
    have key : ∀ i, (z i < z (i+1) ↔ z0 i < z0 (i+1)) ∧ (z (i+1) < z i ↔ z0 (i+1) < z0 i) := by
      intro i
      have hne : z0 i ≠ z0 (i+1) → True := fun _ => trivial
      constructor
      · refine ⟨fun h => ?_, (hQ i).1⟩
        rcases lt_trichotomy (z0 i) (z0 (i+1)) with c | c | c
        · exact c
        · have := hz'.1 c; rw [← this] at h; exact absurd h (lt_irrefl _) 
        · linarith [(hQ i).2 c]
      · refine ⟨fun h => ?_, (hQ i).2⟩
        rcases lt_trichotomy (z0 i) (z0 (i+1)) with c | c | c
        · linarith [(hQ i).1 c]
        · have := hz'.1 c; rw [← this] at h; exact absurd h (lt_irrefl _)
        · exact c
    refine ⟨zi, ?_⟩
    have hf := hz'.2
    rw [← hf]
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and]
    have a : z (i-1) < z i ↔ z0 (i-1) < z0 i := by simpa using (key (i-1)).1
    have b : z (i+1) < z i ↔ z0 (i+1) < z0 i := (key i).2
    exact and_congr a b

#print axioms unimodalViewIsRupert
#print axioms coplanarSilhouetteIsRupert
#print axioms triangleShadowIsRupert
#print axioms FreeAt.isRupert

end Core

#print axioms silhouetteCodeCounts

end MinimalityExtra

#print axioms MinimalityExtra.HasFirstOrderPassage.isRupert
