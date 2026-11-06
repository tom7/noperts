module

public import Mathlib
public import MinimalityExtra
public import Minimality.Tilt
public import Minimality.OctaTools

/-!
# The Septopert is a limit of Rupert shapes

Proof of `MinimalityExtra.SeptopertIsLimitOfRupert`.  Family `SLX t`: the Septopert (integer
vertices) with the `x`-coordinate of vertex 6 raised by `10^6 t`.  For `0 < t < 1` the view
`w = (-10 - t, -t, 10 - t)` (a tilt of order `t` off the face circle of the face `3 4 5`, next to the
mirror view `(-1, 0, 1)`) has strict rim `6, 1, 5, 4, 2` (vertices `0` and `3` hidden), and the
motion `ω = (1 + t, -32, 1)`, `τ = (-1200000 t, -470000 t, 0)` moves every rim corner strictly
inward.  Found with exact LP (`out/bottleneck/side17/`): the order-0 part `ω₀ = (1,-32,1)`, `τ₀ = 0`
makes four rows positive and six rows zero, the order-`t` part makes those six positive.
-/

@[expose] public section


namespace MinimalityExtra
open scoped RealInnerProductSpace
open Finset

noncomputable def SLX (t : ℝ) : Fin 7 → ℝ³ :=
  ![!₂[-940638, 327651, 327651], !₂[327651, -940638, 327651], !₂[327651, 327651, -940638],
    !₂[703968, 47788, 47788], !₂[47788, 703968, 47788], !₂[47788, 47788, 703968],
    !₂[-514207 + 1000000 * t, -514207, -514207]]

noncomputable def SLW (t : ℝ) : ℝ³ := !₂[-10 - t, -t, 10 - t]

theorem all7 (i : Fin 7) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by
  revert i; decide

theorem slx_free (t : ℝ) (h0 : 0 < t) (h1 : t < 1) : FreeAt (univ.image (SLX t)) (SLW t) := by
  refine ⟨!₂[1 + t, -32, 1], !₂[-1200000 * t, -470000 * t, 0], ?_⟩
  intro y hy
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hy
  obtain ⟨i, rfl⟩ := hy
  have m : ∀ i, SLX t i ∈ univ.image (SLX t) := fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have ht2 := mul_pos h0 h0
  have ht3 := mul_pos ht2 h0
  have h1' : 0 < 1 - t := by linarith
  rcases all7 i with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- vertex 0, hidden in triangle 6 4 2
    right
    refine ⟨SLX t 6, m _, SLX t 4, m _, SLX t 2, m _, ?_, ?_, ?_, ?_⟩ <;>
      simp [SLX, SLW, det3] <;> nlinarith
  · left
    refine ⟨SLX t 6, m _, SLX t 5, m _, ?_, ?_, ?_⟩ <;>
      simp [SLX, SLW, det3, cross] <;> nlinarith
  · left
    refine ⟨SLX t 4, m _, SLX t 6, m _, ?_, ?_, ?_⟩ <;>
      simp [SLX, SLW, det3, cross] <;> nlinarith
  · right
    refine ⟨SLX t 1, m _, SLX t 5, m _, SLX t 4, m _, ?_, ?_, ?_, ?_⟩ <;>
      simp [SLX, SLW, det3] <;> nlinarith
  · left
    refine ⟨SLX t 5, m _, SLX t 2, m _, ?_, ?_, ?_⟩ <;>
      simp [SLX, SLW, det3, cross] <;> nlinarith
  · left
    refine ⟨SLX t 1, m _, SLX t 4, m _, ?_, ?_, ?_⟩ <;>
      simp [SLX, SLW, det3, cross] <;> nlinarith
  · left
    refine ⟨SLX t 2, m _, SLX t 1, m _, ?_, ?_, ?_⟩ <;>
      simp [SLX, SLW, det3, cross] <;> nlinarith


theorem sl_det3_eq (a b c : ℝ³) : MinimalityExtra.det3 a b c = Minimality.det3 a b c := by
  rw [Minimality.det3_expand]; rfl

theorem sl_tiltCert (V : Finset ℝ³) (w ω τ x : ℝ³) (h : MinimalityExtra.TiltCert V w ω τ x) :
    Minimality.TiltCert V w ω τ x := by
  simpa only [MinimalityExtra.TiltCert, Minimality.TiltCert, sl_det3_eq,
    show MinimalityExtra.cross = Minimality.cross from rfl] using h

theorem slx_isRupert (t : ℝ) (h0 : 0 < t) (h1 : t < 1) : IsRupert (univ.image (SLX t)) := by
  obtain ⟨ω, τ, hc⟩ := slx_free t h0 h1
  have hw : SLW t ≠ 0 := by
    intro h
    have := congrArg (fun v : ℝ³ => v 1) h
    simp [SLW] at this
    linarith
  exact Minimality.isRupert_of_tiltCert _ (SLW t) hw ω τ fun y hy => sl_tiltCert _ _ _ _ _ (hc y hy)

theorem septopertIsLimitOfRupert : SeptopertIsLimitOfRupert := by
  intro ε hε
  set t : ℝ := min (1 / 2) (ε / 2000000) with ht
  have ht0 : 0 < t := lt_min (by norm_num) (by positivity)
  have ht1 : t < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have ht2 : 1000000 * t < ε := by
    have := min_le_right (1 / 2 : ℝ) (ε / 2000000)
    linarith
  refine ⟨SLX t, ?_, ?_, slx_isRupert t ht0 ht1⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [SLX] <;> first | exact hε | (rw [abs_of_pos (by positivity)]; exact ht2)
  · intro h
    have := congrArg (fun x : Fin 7 → ℝ³ => x 6 0) h
    simp [SLX] at this
    linarith

end MinimalityExtra
