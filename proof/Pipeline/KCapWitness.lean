module

public import Pipeline.BalancedWitness
public import Pipeline.CapTheorem
public import Pipeline.KCapPoly

@[expose] public section

/-!
# A balanced witness at one pose of a cap chart

`balanced_pose_not_rupert`: a pose whose view is a positive multiple of u
and whose relative rotation is the Cayley rotation of w, with contacts k
(directions c_k, d_k = u × c_k, weights λ_k ≥ 0 balancing the d_k, one of them
positive on a nonzero d_k), outer vertices j_k maximal along d_k among the
vertices, and inner vertices i_k with

  Σ_k λ_k (N(w) v_{i_k} · d_k − D(w) v_{j_k} · d_k) ≥ 0

(the witness polynomial's value; N/D is the Cayley rotation), is not Rupert
for the hull of the vertices (`not_rupert_of_balanced_support`).
-/

namespace Noperts.Pipeline

namespace KCap

open scoped Matrix RealInnerProductSpace

theorem rdot_comm' (a b : Fin 3 → ℝ) : rdot a b = rdot b a := by simp only [rdot]; ring

theorem rdot_rcross_self' (u c : Fin 3 → ℝ) : rdot u (rcross u c) = 0 := by
  simp only [rdot, rcross, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

theorem toEuc_inner (a b : Fin 3 → ℝ) : ⟪Cap.toEuc a, Cap.toEuc b⟫ = rdot a b := by
  rw [Cap.inner_toEuc]; rfl

theorem rcayleyNum_eq' (w v : Fin 3 → ℝ) :
    rcayleyNum w v = (1 + rdot w w) • (cayleyMatrix (w 0) (w 1) (w 2)).mulVec v := by
  have h := Cap.cayley_mulVec w v
  exact h.symm

/-- `balanced_pose_not_rupert` with inner points anywhere in the hull S (e.g. on a segment
between two vertices). -/
theorem balanced_pose_not_rupert_hull {ι : Type} [Fintype ι] (V : List (Fin 3 → ℝ)) (S : Set ℝ³)
    (hS : S = convexHull ℝ {v | ∃ vj ∈ V, v = Cap.toEuc vj})
    (p : MatrixPose) (u : Fin 3 → ℝ) (ξ : ℝ) (hview : p.view = ξ • u)
    (w : Fin 3 → ℝ) (hR : p.relativeRotation = cayleyMatrix (w 0) (w 1) (w 2))
    (c : ι → Fin 3 → ℝ) (lam : ι → ℝ) (i j : ι → Fin 3 → ℝ)
    (hlam : ∀ k, 0 ≤ lam k) (hbal : ∑ k, lam k • rcross u (c k) = 0)
    (hpos : ∃ k, 0 < lam k ∧ rcross u (c k) ≠ 0)
    (hi : ∀ k, Cap.toEuc (i k) ∈ S)
    (hmax : ∀ k, ∀ v ∈ V, rdot v (rcross u (c k)) ≤ rdot (j k) (rcross u (c k)))
    (hP : 0 ≤ ∑ k, lam k * (rdot (rcayleyNum w (i k)) (rcross u (c k)) -
      (1 + rdot w w) * rdot (j k) (rcross u (c k)))) :
    ¬ RupertPose p S := by
  set Rm := cayleyMatrix (w 0) (w 1) (w 2)
  set d : ι → Fin 3 → ℝ := fun k => rcross u (c k)
  have hD : 0 < 1 + rdot w w := by
    have : 0 ≤ rdot w w := by simp only [rdot]; nlinarith [sq_nonneg (w 0), sq_nonneg (w 1), sq_nonneg (w 2)]
    linarith
  have hmulE : ∀ v : Fin 3 → ℝ, Rm.toEuclideanLin (Cap.toEuc v) = Cap.toEuc (Rm.mulVec v) := by
    intro v; simp [Matrix.toLpLin_apply, Cap.toEuc]
  apply not_rupert_of_balanced_support p S (fun k => Cap.toEuc (d k)) lam (fun k => rdot (j k) (d k))
    (fun k => Cap.toEuc (i k))
  · -- (O d)_z = view · d = ξ (u · d) = 0.
    intro k
    have h2 : (p.outerRot.val.toEuclideanLin (Cap.toEuc (d k))) 2 = rdot p.view (d k) := by
      simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Cap.toEuc, rdot,
        MatrixPose.view]
    rw [h2, hview]
    have : rdot (ξ • u) (d k) = ξ * rdot u (d k) := by simp only [rdot, Pi.smul_apply, smul_eq_mul]; ring
    rw [this, rdot_rcross_self', mul_zero]
  · exact hlam
  · have : ∑ k, lam k • Cap.toEuc (d k) = Cap.toEuc (∑ k, lam k • d k) := by
      simp [Cap.toEuc]
    rw [this]
    simp only [d]
    rw [hbal]
    rfl
  · obtain ⟨k, hk, hd⟩ := hpos
    refine ⟨k, hk, ?_⟩
    intro h0
    apply hd
    have := congrArg WithLp.ofLp h0
    simpa [Cap.toEuc] using this
  · intro k v hv
    rw [hS] at hv
    revert v
    apply Cap.inner_le_of_mem_convexHull
    rintro v ⟨vj, hvj, rfl⟩
    rw [toEuc_inner, rdot_comm']
    exact hmax k vj hvj
  · exact hi
  · -- Σ λ M ≤ Σ λ ⟪d, R v_i⟫: hP divided by D.
    rw [hR]
    simp only [hmulE, toEuc_inner]
    have hterm : ∀ k, lam k * (rdot (rcayleyNum w (i k)) (d k) - (1 + rdot w w) * rdot (j k) (d k)) =
        (1 + rdot w w) * (lam k * rdot (d k) (Rm.mulVec (i k)) - lam k * rdot (j k) (d k)) := by
      intro k
      rw [rcayleyNum_eq']
      have : rdot ((1 + rdot w w) • Rm.mulVec (i k)) (d k) = (1 + rdot w w) * rdot (d k) (Rm.mulVec (i k)) := by
        simp only [rdot, Pi.smul_apply, smul_eq_mul]; ring
      rw [this]; ring
    have hsum : ∑ k, lam k * (rdot (rcayleyNum w (i k)) (d k) - (1 + rdot w w) * rdot (j k) (d k)) =
        (1 + rdot w w) * ∑ k, (lam k * rdot (d k) (Rm.mulVec (i k)) - lam k * rdot (j k) (d k)) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => hterm k)
    have hP' : 0 ≤ ∑ k, (lam k * rdot (d k) (Rm.mulVec (i k)) - lam k * rdot (j k) (d k)) := by
      have := hP
      simp only [d] at hsum
      rw [hsum] at this
      exact nonneg_of_mul_nonneg_right (by linarith) hD |> fun h => by
        have := (mul_nonneg_iff_of_pos_left hD).mp this; exact this
    rw [Finset.sum_sub_distrib] at hP'
    linarith

theorem balanced_pose_not_rupert {ι : Type} [Fintype ι] (V : List (Fin 3 → ℝ)) (S : Set ℝ³)
    (hS : S = convexHull ℝ {v | ∃ vj ∈ V, v = Cap.toEuc vj})
    (p : MatrixPose) (u : Fin 3 → ℝ) (ξ : ℝ) (hview : p.view = ξ • u)
    (w : Fin 3 → ℝ) (hR : p.relativeRotation = cayleyMatrix (w 0) (w 1) (w 2))
    (c : ι → Fin 3 → ℝ) (lam : ι → ℝ) (i j : ι → Fin 3 → ℝ)
    (hlam : ∀ k, 0 ≤ lam k) (hbal : ∑ k, lam k • rcross u (c k) = 0)
    (hpos : ∃ k, 0 < lam k ∧ rcross u (c k) ≠ 0)
    (hi : ∀ k, i k ∈ V)
    (hmax : ∀ k, ∀ v ∈ V, rdot v (rcross u (c k)) ≤ rdot (j k) (rcross u (c k)))
    (hP : 0 ≤ ∑ k, lam k * (rdot (rcayleyNum w (i k)) (rcross u (c k)) -
      (1 + rdot w w) * rdot (j k) (rcross u (c k)))) :
    ¬ RupertPose p S :=
  balanced_pose_not_rupert_hull V S hS p u ξ hview w hR c lam i j hlam hbal hpos
    (fun k => by rw [hS]; exact subset_convexHull ℝ _ ⟨i k, hi k, rfl⟩) hmax hP

end KCap

end Noperts.Pipeline

end
