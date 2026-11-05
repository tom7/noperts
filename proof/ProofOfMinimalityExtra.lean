module

public import MinimalityExtra.NoUnimodal
public import MinimalityExtra.Sanity
public import MinimalityExtra.MetricUniform
public import MinimalityExtra.TetraViews
public import Minimality.Tilt
public import Minimality.Thm73
public import Minimality.OctaTools

/-!
# The definitions of `MinimalityExtra.lean` agree with the project's

* `MinimalityExtra.det3`, `cross`, `TiltCert`, `IsCyclicUnimodal` agree with the
  `Minimality` ones, so `HasFirstOrderPassage V` implies `IsRupert V`.
* `HasUnimodalView x → IsRupert` (the unimodal criterion for this definition) is not proved
  here: the criterion `isRupert_of_genericUnimodalView` needs a generic view (strictly convex
  silhouette, all other points inside, a rotation matrix), which a perturbation argument
  would have to supply from a `StrictRim` view.
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

end MinimalityExtra

#print axioms MinimalityExtra.HasFirstOrderPassage.isRupert
