module

public import Minimality.LinkRim24

@[expose] public section

/-!
# Type 24 link edges 26 and 02: rim determinants (nopert229 report LINKRIM24); the type-free head and `EdgeRimDet.transfer` are in `LinkRim24`.
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace

namespace Minimality
namespace Link24R

open Finset

theorem inner_neg {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} {p q : Fin 7} (F : Face16 x S) (hp : p ∈ S)
    (hq : q ∉ S) : ⟪F.N, x q - x p⟫ < 0 := by
  rw [Type24.f_eq_inner F q p, F.zero p hp]; have := F.neg q hq; linarith

theorem inner_pos {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} {p q : Fin 7} (F : Face16 x S) (hp : p ∉ S)
    (hq : q ∈ S) : 0 < ⟪F.N, x q - x p⟫ := by
  rw [Type24.f_eq_inner F q p, F.zero q hq]; have := F.neg p hp; linarith

theorem inner_zero {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} {p q : Fin 7} (F : Face16 x S) (hp : p ∈ S)
    (hq : q ∈ S) : ⟪F.N, x q - x p⟫ = 0 := by
  rw [Type24.f_eq_inner F q p, F.zero q hq, F.zero p hp]; simp

theorem ref26610 {x : Fin 7 → ℝ³} (hM : 0 < det24 x) :
    0 < det3 (x 1 - x 6) (x 0 - x 6) (x 6 - x 2) := by
  have e1 : x 1 - x 6 = (0:ℝ) • (x 0 - x 1) + (0:ℝ) • (x 2 - x 1) + (-1:ℝ) • (x 6 - x 1) := by
    module
  have e2 : x 0 - x 6 = (1:ℝ) • (x 0 - x 1) + (0:ℝ) • (x 2 - x 1) + (-1:ℝ) • (x 6 - x 1) := by
    module
  have e3 : x 6 - x 2 = (0:ℝ) • (x 0 - x 1) + (-1:ℝ) • (x 2 - x 1) + (1:ℝ) • (x 6 - x 1) := by
    module
  rw [e1, e2, e3, det3_comb]
  have : det24 x = vol3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := rfl
  rw [← this]
  nlinarith

theorem ref02216 {x : Fin 7 → ℝ³} (hM : 0 < det24 x) :
    0 < det3 (x 1 - x 2) (x 6 - x 2) (x 2 - x 0) := by
  have e1 : x 1 - x 2 = (0:ℝ) • (x 0 - x 1) + (-1:ℝ) • (x 2 - x 1) + (0:ℝ) • (x 6 - x 1) := by
    module
  have e2 : x 6 - x 2 = (0:ℝ) • (x 0 - x 1) + (-1:ℝ) • (x 2 - x 1) + (1:ℝ) • (x 6 - x 1) := by
    module
  have e3 : x 2 - x 0 = (-1:ℝ) • (x 0 - x 1) + (1:ℝ) • (x 2 - x 1) + (0:ℝ) • (x 6 - x 1) := by
    module
  rw [e1, e2, e3, det3_comb]
  have : det24 x = vol3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := rfl
  rw [← this]
  nlinarith

def rim26 (q X : Fin 7) : ZMod 5 → Fin 7 := ![X, 1, 0, q, 3]
def rim02 (X : Fin 7) : ZMod 5 → Fin 7 := ![X, 1, 6, 3, 5]
def rim02s (X : Fin 7) : ZMod 6 → Fin 7 := ![X, 1, 6, 4, 3, 5]



/-! ### Link edge `26` -/

theorem det26A {x : Fin 7 → ℝ³} (T : Type24 x) (F0345 : Face16 x {0, 3, 4, 5}) (F346 : Face16 x {3, 4, 6}) (hM : 0 < det24 x)
    (hs : ⟪F0345.N, x 6 - x 2⟫ < 0) : EdgeRimDet x (x 6 - x 2) 2 1 5 (rim26 4 6) := by
  have inj := T.inj
  have hne : ∀ a b : Fin 7, a ≠ b → x a ≠ x b := fun a b h e => h (inj e)
  have s012 := inner_neg (p := 2) (q := 6) T.t012 (by decide) (by decide)
  have s012lt := s012
  have s016 := inner_pos (p := 2) (q := 6) T.t016 (by decide) (by decide)
  have s0345 := hs
  have s0345lt := s0345
  have s046 := inner_pos (p := 2) (q := 6) T.t046 (by decide) (by decide)
  have s126 := inner_zero (p := 2) (q := 6) T.t126 (by decide) (by decide)
  have s236 := inner_zero (p := 2) (q := 6) T.t236 (by decide) (by decide)
  have s346 := inner_pos (p := 2) (q := 6) F346 (by decide) (by decide)
  have t610 := ref26610 hM
  have t103 : 0 < det3 (x 0 - x 1) (x 3 - x 1) (x 6 - x 2) :=
    edgeStep T.t016 T.t012 _ (a := 1) (b := 0) (w := 6) (v := 3) (by decide) (by decide) (by decide) (by decide)
      (hne 1 0 (by decide)) s016 s012.le (by rw [← tcyc x _ 6 1 0]; exact t610) (Or.inl (by decide)) (Or.inl (by decide))
  have t104 : 0 < det3 (x 0 - x 1) (x 4 - x 1) (x 6 - x 2) :=
    edgeStep T.t016 T.t012 _ (a := 1) (b := 0) (w := 6) (v := 4) (by decide) (by decide) (by decide) (by decide)
      (hne 1 0 (by decide)) s016 s012.le (by rw [← tcyc x _ 6 1 0]; exact t610) (Or.inl (by decide)) (Or.inl (by decide))
  have t105 : 0 < det3 (x 0 - x 1) (x 5 - x 1) (x 6 - x 2) :=
    edgeStep T.t016 T.t012 _ (a := 1) (b := 0) (w := 6) (v := 5) (by decide) (by decide) (by decide) (by decide)
      (hne 1 0 (by decide)) s016 s012.le (by rw [← tcyc x _ 6 1 0]; exact t610) (Or.inl (by decide)) (Or.inl (by decide))
  have t613 : 0 < det3 (x 1 - x 6) (x 3 - x 6) (x 6 - x 2) :=
    edgeStep T.t016 T.t126 _ (a := 6) (b := 1) (w := 0) (v := 3) (by decide) (by decide) (by decide) (by decide)
      (hne 6 1 (by decide)) s016 s126.le t610 (Or.inl (by decide)) (Or.inl (by decide))
  have t614 : 0 < det3 (x 1 - x 6) (x 4 - x 6) (x 6 - x 2) :=
    edgeStep T.t016 T.t126 _ (a := 6) (b := 1) (w := 0) (v := 4) (by decide) (by decide) (by decide) (by decide)
      (hne 6 1 (by decide)) s016 s126.le t610 (Or.inl (by decide)) (Or.inl (by decide))
  have t615 : 0 < det3 (x 1 - x 6) (x 5 - x 6) (x 6 - x 2) :=
    edgeStep T.t016 T.t126 _ (a := 6) (b := 1) (w := 0) (v := 5) (by decide) (by decide) (by decide) (by decide)
      (hne 6 1 (by decide)) s016 s126.le t610 (Or.inl (by decide)) (Or.inl (by decide))
  have t043 : 0 < det3 (x 4 - x 0) (x 3 - x 0) (x 6 - x 2) :=
    edgeStep T.t046 F0345 _ (a := 0) (b := 4) (w := 1) (v := 3) (by decide) (by decide) (by decide) (by decide)
      (hne 0 4 (by decide)) s046 s0345.le (by rw [← tcyc x _ 1 0 4]; exact t104) (Or.inl (by decide)) (Or.inr ⟨by decide, s0345lt⟩)
  have t045 : 0 < det3 (x 4 - x 0) (x 5 - x 0) (x 6 - x 2) :=
    edgeStep T.t046 F0345 _ (a := 0) (b := 4) (w := 1) (v := 5) (by decide) (by decide) (by decide) (by decide)
      (hne 0 4 (by decide)) s046 s0345.le (by rw [← tcyc x _ 1 0 4]; exact t104) (Or.inl (by decide)) (Or.inr ⟨by decide, s0345lt⟩)
  have t046 : 0 < det3 (x 4 - x 0) (x 6 - x 0) (x 6 - x 2) :=
    edgeStep T.t046 F0345 _ (a := 0) (b := 4) (w := 1) (v := 6) (by decide) (by decide) (by decide) (by decide)
      (hne 0 4 (by decide)) s046 s0345.le (by rw [← tcyc x _ 1 0 4]; exact t104) (Or.inl (by decide)) (Or.inl (by decide))
  have t431 : 0 < det3 (x 3 - x 4) (x 1 - x 4) (x 6 - x 2) :=
    edgeStep F346 F0345 _ (a := 4) (b := 3) (w := 0) (v := 1) (by decide) (by decide) (by decide) (by decide)
      (hne 4 3 (by decide)) s346 s0345.le (by rw [← tcyc x _ 0 4 3]; exact t043) (Or.inr ⟨by decide, s0345lt⟩) (Or.inl (by decide))
  have t435 : 0 < det3 (x 3 - x 4) (x 5 - x 4) (x 6 - x 2) :=
    edgeStep F346 F0345 _ (a := 4) (b := 3) (w := 0) (v := 5) (by decide) (by decide) (by decide) (by decide)
      (hne 4 3 (by decide)) s346 s0345.le (by rw [← tcyc x _ 0 4 3]; exact t043) (Or.inr ⟨by decide, s0345lt⟩) (Or.inr ⟨by decide, s0345lt⟩)
  have t436 : 0 < det3 (x 3 - x 4) (x 6 - x 4) (x 6 - x 2) :=
    edgeStep F346 F0345 _ (a := 4) (b := 3) (w := 0) (v := 6) (by decide) (by decide) (by decide) (by decide)
      (hne 4 3 (by decide)) s346 s0345.le (by rw [← tcyc x _ 0 4 3]; exact t043) (Or.inr ⟨by decide, s0345lt⟩) (Or.inl (by decide))
  have t360 : 0 < det3 (x 6 - x 3) (x 0 - x 3) (x 6 - x 2) :=
    edgeStep F346 T.t236 _ (a := 3) (b := 6) (w := 1) (v := 0) (by decide) (by decide) (by decide) (by decide)
      (hne 3 6 (by decide)) s346 s236.le (by rw [← tcyc x _ 1 3 6, ← tcyc x _ 6 1 3]; exact t613) (Or.inl (by decide)) (Or.inl (by decide))
  have t365 : 0 < det3 (x 6 - x 3) (x 5 - x 3) (x 6 - x 2) :=
    edgeStep F346 T.t236 _ (a := 3) (b := 6) (w := 1) (v := 5) (by decide) (by decide) (by decide) (by decide)
      (hne 3 6 (by decide)) s346 s236.le (by rw [← tcyc x _ 1 3 6, ← tcyc x _ 6 1 3]; exact t613) (Or.inl (by decide)) (Or.inl (by decide))
  have t106 : 0 < det3 (x 0 - x 1) (x 6 - x 1) (x 6 - x 2) := (by rw [← tcyc x _ 6 1 0]; exact t610)
  have t041 : 0 < det3 (x 4 - x 0) (x 1 - x 0) (x 6 - x 2) := (by rw [← tcyc x _ 1 0 4]; exact t104)
  have t430 : 0 < det3 (x 3 - x 4) (x 0 - x 4) (x 6 - x 2) := (by rw [← tcyc x _ 0 4 3]; exact t043)
  have t361 : 0 < det3 (x 6 - x 3) (x 1 - x 3) (x 6 - x 2) := (by rw [← tcyc x _ 1 3 6, ← tcyc x _ 6 1 3]; exact t613)
  have t364 : 0 < det3 (x 6 - x 3) (x 4 - x 3) (x 6 - x 2) := (by rw [← tcyc x _ 4 3 6]; exact t436)
  refine ⟨by norm_num, one_ne_zero, ?_, ?_, ?_⟩
  · show x 2 = x 6 - (1 : ℝ) • (x 6 - x 2)
    rw [one_smul]; abel
  · obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
    have r0 : rim26 4 6 0 = 6 := rfl
    have r1 : rim26 4 6 1 = 1 := rfl
    have r2 : rim26 4 6 2 = 0 := rfl
    have r3 : rim26 4 6 3 = 4 := rfl
    have r4 : rim26 4 6 4 = 3 := rfl
    intro i j hj1 hj2
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [a0, a1, a2, a3, a4, r0, r1, r2, r3, r4] at hj1 hj2 ⊢ <;>
    first | exact absurd rfl hj1 | exact absurd rfl hj2 | assumption
  · obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
    have r0 : rim26 4 6 0 = 6 := rfl
    have r1 : rim26 4 6 1 = 1 := rfl
    have r2 : rim26 4 6 2 = 0 := rfl
    have r3 : rim26 4 6 3 = 4 := rfl
    have r4 : rim26 4 6 4 = 3 := rfl
    intro v hv hvr i
    have h0 := hvr 0; have h1 := hvr 1; have h2 := hvr 2; have h3 := hvr 3; have h4 := hvr 4
    rw [r0] at h0; rw [r1] at h1; rw [r2] at h2; rw [r3] at h3; rw [r4] at h4
    have hv5 : v = 5 := by
      clear hvr; fin_cases v <;> simp_all
    subst hv5
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    simp only [a0, a1, a2, a3, a4, r0, r1, r2, r3, r4] <;> assumption


theorem det26B {x : Fin 7 → ℝ³} (T : Type24 x) (F0345 : Face16 x {0, 3, 4, 5}) (F235 : Face16 x {2, 3, 5}) (F346 : Face16 x {3, 4, 6}) (hM : 0 < det24 x)
    (hs : 0 < ⟪F0345.N, x 6 - x 2⟫) : EdgeRimDet x (x 6 - x 2) 2 1 5 (rim26 5 6) := by
  have inj := T.inj
  have hne : ∀ a b : Fin 7, a ≠ b → x a ≠ x b := fun a b h e => h (inj e)
  have s012 := inner_neg (p := 2) (q := 6) T.t012 (by decide) (by decide)
  have s012lt := s012
  have s016 := inner_pos (p := 2) (q := 6) T.t016 (by decide) (by decide)
  have s025 := inner_neg (p := 2) (q := 6) T.t025 (by decide) (by decide)
  have s025lt := s025
  have s0345 := hs
  have s126 := inner_zero (p := 2) (q := 6) T.t126 (by decide) (by decide)
  have s235 := inner_neg (p := 2) (q := 6) F235 (by decide) (by decide)
  have s235lt := s235
  have s236 := inner_zero (p := 2) (q := 6) T.t236 (by decide) (by decide)
  have s346 := inner_pos (p := 2) (q := 6) F346 (by decide) (by decide)
  have t610 := ref26610 hM
  have t103 : 0 < det3 (x 0 - x 1) (x 3 - x 1) (x 6 - x 2) :=
    edgeStep T.t016 T.t012 _ (a := 1) (b := 0) (w := 6) (v := 3) (by decide) (by decide) (by decide) (by decide)
      (hne 1 0 (by decide)) s016 s012.le (by rw [← tcyc x _ 6 1 0]; exact t610) (Or.inl (by decide)) (Or.inl (by decide))
  have t104 : 0 < det3 (x 0 - x 1) (x 4 - x 1) (x 6 - x 2) :=
    edgeStep T.t016 T.t012 _ (a := 1) (b := 0) (w := 6) (v := 4) (by decide) (by decide) (by decide) (by decide)
      (hne 1 0 (by decide)) s016 s012.le (by rw [← tcyc x _ 6 1 0]; exact t610) (Or.inl (by decide)) (Or.inl (by decide))
  have t105 : 0 < det3 (x 0 - x 1) (x 5 - x 1) (x 6 - x 2) :=
    edgeStep T.t016 T.t012 _ (a := 1) (b := 0) (w := 6) (v := 5) (by decide) (by decide) (by decide) (by decide)
      (hne 1 0 (by decide)) s016 s012.le (by rw [← tcyc x _ 6 1 0]; exact t610) (Or.inl (by decide)) (Or.inl (by decide))
  have t613 : 0 < det3 (x 1 - x 6) (x 3 - x 6) (x 6 - x 2) :=
    edgeStep T.t016 T.t126 _ (a := 6) (b := 1) (w := 0) (v := 3) (by decide) (by decide) (by decide) (by decide)
      (hne 6 1 (by decide)) s016 s126.le t610 (Or.inl (by decide)) (Or.inl (by decide))
  have t614 : 0 < det3 (x 1 - x 6) (x 4 - x 6) (x 6 - x 2) :=
    edgeStep T.t016 T.t126 _ (a := 6) (b := 1) (w := 0) (v := 4) (by decide) (by decide) (by decide) (by decide)
      (hne 6 1 (by decide)) s016 s126.le t610 (Or.inl (by decide)) (Or.inl (by decide))
  have t615 : 0 < det3 (x 1 - x 6) (x 5 - x 6) (x 6 - x 2) :=
    edgeStep T.t016 T.t126 _ (a := 6) (b := 1) (w := 0) (v := 5) (by decide) (by decide) (by decide) (by decide)
      (hne 6 1 (by decide)) s016 s126.le t610 (Or.inl (by decide)) (Or.inl (by decide))
  have t053 : 0 < det3 (x 5 - x 0) (x 3 - x 0) (x 6 - x 2) :=
    edgeStep F0345 T.t025 _ (a := 0) (b := 5) (w := 1) (v := 3) (by decide) (by decide) (by decide) (by decide)
      (hne 0 5 (by decide)) s0345 s025.le (by rw [← tcyc x _ 1 0 5]; exact t105) (Or.inl (by decide)) (Or.inl (by decide))
  have t054 : 0 < det3 (x 5 - x 0) (x 4 - x 0) (x 6 - x 2) :=
    edgeStep F0345 T.t025 _ (a := 0) (b := 5) (w := 1) (v := 4) (by decide) (by decide) (by decide) (by decide)
      (hne 0 5 (by decide)) s0345 s025.le (by rw [← tcyc x _ 1 0 5]; exact t105) (Or.inl (by decide)) (Or.inl (by decide))
  have t056 : 0 < det3 (x 5 - x 0) (x 6 - x 0) (x 6 - x 2) :=
    edgeStep F0345 T.t025 _ (a := 0) (b := 5) (w := 1) (v := 6) (by decide) (by decide) (by decide) (by decide)
      (hne 0 5 (by decide)) s0345 s025.le (by rw [← tcyc x _ 1 0 5]; exact t105) (Or.inl (by decide)) (Or.inl (by decide))
  have t531 : 0 < det3 (x 3 - x 5) (x 1 - x 5) (x 6 - x 2) :=
    edgeStep F0345 F235 _ (a := 5) (b := 3) (w := 0) (v := 1) (by decide) (by decide) (by decide) (by decide)
      (hne 5 3 (by decide)) s0345 s235.le (by rw [← tcyc x _ 0 5 3]; exact t053) (Or.inl (by decide)) (Or.inl (by decide))
  have t534 : 0 < det3 (x 3 - x 5) (x 4 - x 5) (x 6 - x 2) :=
    edgeStep F0345 F235 _ (a := 5) (b := 3) (w := 0) (v := 4) (by decide) (by decide) (by decide) (by decide)
      (hne 5 3 (by decide)) s0345 s235.le (by rw [← tcyc x _ 0 5 3]; exact t053) (Or.inl (by decide)) (Or.inl (by decide))
  have t536 : 0 < det3 (x 3 - x 5) (x 6 - x 5) (x 6 - x 2) :=
    edgeStep F0345 F235 _ (a := 5) (b := 3) (w := 0) (v := 6) (by decide) (by decide) (by decide) (by decide)
      (hne 5 3 (by decide)) s0345 s235.le (by rw [← tcyc x _ 0 5 3]; exact t053) (Or.inl (by decide)) (Or.inl (by decide))
  have t360 : 0 < det3 (x 6 - x 3) (x 0 - x 3) (x 6 - x 2) :=
    edgeStep F346 T.t236 _ (a := 3) (b := 6) (w := 1) (v := 0) (by decide) (by decide) (by decide) (by decide)
      (hne 3 6 (by decide)) s346 s236.le (by rw [← tcyc x _ 1 3 6, ← tcyc x _ 6 1 3]; exact t613) (Or.inl (by decide)) (Or.inl (by decide))
  have t364 : 0 < det3 (x 6 - x 3) (x 4 - x 3) (x 6 - x 2) :=
    edgeStep F346 T.t236 _ (a := 3) (b := 6) (w := 1) (v := 4) (by decide) (by decide) (by decide) (by decide)
      (hne 3 6 (by decide)) s346 s236.le (by rw [← tcyc x _ 1 3 6, ← tcyc x _ 6 1 3]; exact t613) (Or.inl (by decide)) (Or.inl (by decide))
  have t106 : 0 < det3 (x 0 - x 1) (x 6 - x 1) (x 6 - x 2) := (by rw [← tcyc x _ 6 1 0]; exact t610)
  have t051 : 0 < det3 (x 5 - x 0) (x 1 - x 0) (x 6 - x 2) := (by rw [← tcyc x _ 1 0 5]; exact t105)
  have t530 : 0 < det3 (x 3 - x 5) (x 0 - x 5) (x 6 - x 2) := (by rw [← tcyc x _ 0 5 3]; exact t053)
  have t361 : 0 < det3 (x 6 - x 3) (x 1 - x 3) (x 6 - x 2) := (by rw [← tcyc x _ 1 3 6, ← tcyc x _ 6 1 3]; exact t613)
  have t365 : 0 < det3 (x 6 - x 3) (x 5 - x 3) (x 6 - x 2) := (by rw [← tcyc x _ 5 3 6]; exact t536)
  refine ⟨by norm_num, one_ne_zero, ?_, ?_, ?_⟩
  · show x 2 = x 6 - (1 : ℝ) • (x 6 - x 2)
    rw [one_smul]; abel
  · obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
    have r0 : rim26 5 6 0 = 6 := rfl
    have r1 : rim26 5 6 1 = 1 := rfl
    have r2 : rim26 5 6 2 = 0 := rfl
    have r3 : rim26 5 6 3 = 5 := rfl
    have r4 : rim26 5 6 4 = 3 := rfl
    intro i j hj1 hj2
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [a0, a1, a2, a3, a4, r0, r1, r2, r3, r4] at hj1 hj2 ⊢ <;>
    first | exact absurd rfl hj1 | exact absurd rfl hj2 | assumption
  · obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
    have r0 : rim26 5 6 0 = 6 := rfl
    have r1 : rim26 5 6 1 = 1 := rfl
    have r2 : rim26 5 6 2 = 0 := rfl
    have r3 : rim26 5 6 3 = 5 := rfl
    have r4 : rim26 5 6 4 = 3 := rfl
    intro v hv hvr i
    have h0 := hvr 0; have h1 := hvr 1; have h2 := hvr 2; have h3 := hvr 3; have h4 := hvr 4
    rw [r0] at h0; rw [r1] at h1; rw [r2] at h2; rw [r3] at h3; rw [r4] at h4
    have hv5 : v = 4 := by
      clear hvr; fin_cases v <;> simp_all
    subst hv5
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    simp only [a0, a1, a2, a3, a4, r0, r1, r2, r3, r4] <;> assumption



/-! ### Link edge `02` -/

theorem det02A {x : Fin 7 → ℝ³} (T : Type24 x) (F0345 : Face16 x {0, 3, 4, 5}) (F235 : Face16 x {2, 3, 5}) (F346 : Face16 x {3, 4, 6}) (hM : 0 < det24 x)
    (hs : ⟪F346.N, x 2 - x 0⟫ < 0) : EdgeRimDet x (x 2 - x 0) 0 1 5 (rim02 2) := by
  have inj := T.inj
  have hne : ∀ a b : Fin 7, a ≠ b → x a ≠ x b := fun a b h e => h (inj e)
  have s012 := inner_zero (p := 0) (q := 2) T.t012 (by decide) (by decide)
  have s016 := inner_neg (p := 0) (q := 2) T.t016 (by decide) (by decide)
  have s016lt := s016
  have s025 := inner_zero (p := 0) (q := 2) T.t025 (by decide) (by decide)
  have s0345 := inner_neg (p := 0) (q := 2) F0345 (by decide) (by decide)
  have s0345lt := s0345
  have s126 := inner_pos (p := 0) (q := 2) T.t126 (by decide) (by decide)
  have s235 := inner_pos (p := 0) (q := 2) F235 (by decide) (by decide)
  have s236 := inner_pos (p := 0) (q := 2) T.t236 (by decide) (by decide)
  have s346 := hs
  have s346lt := s346
  have t216 := ref02216 hM
  have t213 : 0 < det3 (x 1 - x 2) (x 3 - x 2) (x 2 - x 0) :=
    edgeStep T.t126 T.t012 _ (a := 2) (b := 1) (w := 6) (v := 3) (by decide) (by decide) (by decide) (by decide)
      (hne 2 1 (by decide)) s126 s012.le t216 (Or.inl (by decide)) (Or.inl (by decide))
  have t214 : 0 < det3 (x 1 - x 2) (x 4 - x 2) (x 2 - x 0) :=
    edgeStep T.t126 T.t012 _ (a := 2) (b := 1) (w := 6) (v := 4) (by decide) (by decide) (by decide) (by decide)
      (hne 2 1 (by decide)) s126 s012.le t216 (Or.inl (by decide)) (Or.inl (by decide))
  have t215 : 0 < det3 (x 1 - x 2) (x 5 - x 2) (x 2 - x 0) :=
    edgeStep T.t126 T.t012 _ (a := 2) (b := 1) (w := 6) (v := 5) (by decide) (by decide) (by decide) (by decide)
      (hne 2 1 (by decide)) s126 s012.le t216 (Or.inl (by decide)) (Or.inl (by decide))
  have t163 : 0 < det3 (x 6 - x 1) (x 3 - x 1) (x 2 - x 0) :=
    edgeStep T.t126 T.t016 _ (a := 1) (b := 6) (w := 2) (v := 3) (by decide) (by decide) (by decide) (by decide)
      (hne 1 6 (by decide)) s126 s016.le (by rw [← tcyc x _ 2 1 6]; exact t216) (Or.inl (by decide)) (Or.inl (by decide))
  have t164 : 0 < det3 (x 6 - x 1) (x 4 - x 1) (x 2 - x 0) :=
    edgeStep T.t126 T.t016 _ (a := 1) (b := 6) (w := 2) (v := 4) (by decide) (by decide) (by decide) (by decide)
      (hne 1 6 (by decide)) s126 s016.le (by rw [← tcyc x _ 2 1 6]; exact t216) (Or.inl (by decide)) (Or.inl (by decide))
  have t165 : 0 < det3 (x 6 - x 1) (x 5 - x 1) (x 2 - x 0) :=
    edgeStep T.t126 T.t016 _ (a := 1) (b := 6) (w := 2) (v := 5) (by decide) (by decide) (by decide) (by decide)
      (hne 1 6 (by decide)) s126 s016.le (by rw [← tcyc x _ 2 1 6]; exact t216) (Or.inl (by decide)) (Or.inl (by decide))
  have t523 : 0 < det3 (x 2 - x 5) (x 3 - x 5) (x 2 - x 0) :=
    edgeStep F235 T.t025 _ (a := 5) (b := 2) (w := 1) (v := 3) (by decide) (by decide) (by decide) (by decide)
      (hne 5 2 (by decide)) s235 s025.le (by rw [← tcyc x _ 1 5 2, ← tcyc x _ 2 1 5]; exact t215) (Or.inl (by decide)) (Or.inl (by decide))
  have t524 : 0 < det3 (x 2 - x 5) (x 4 - x 5) (x 2 - x 0) :=
    edgeStep F235 T.t025 _ (a := 5) (b := 2) (w := 1) (v := 4) (by decide) (by decide) (by decide) (by decide)
      (hne 5 2 (by decide)) s235 s025.le (by rw [← tcyc x _ 1 5 2, ← tcyc x _ 2 1 5]; exact t215) (Or.inl (by decide)) (Or.inl (by decide))
  have t526 : 0 < det3 (x 2 - x 5) (x 6 - x 5) (x 2 - x 0) :=
    edgeStep F235 T.t025 _ (a := 5) (b := 2) (w := 1) (v := 6) (by decide) (by decide) (by decide) (by decide)
      (hne 5 2 (by decide)) s235 s025.le (by rw [← tcyc x _ 1 5 2, ← tcyc x _ 2 1 5]; exact t215) (Or.inl (by decide)) (Or.inl (by decide))
  have t351 : 0 < det3 (x 5 - x 3) (x 1 - x 3) (x 2 - x 0) :=
    edgeStep F235 F0345 _ (a := 3) (b := 5) (w := 2) (v := 1) (by decide) (by decide) (by decide) (by decide)
      (hne 3 5 (by decide)) s235 s0345.le (by rw [← tcyc x _ 2 3 5, ← tcyc x _ 5 2 3]; exact t523) (Or.inl (by decide)) (Or.inl (by decide))
  have t354 : 0 < det3 (x 5 - x 3) (x 4 - x 3) (x 2 - x 0) :=
    edgeStep F235 F0345 _ (a := 3) (b := 5) (w := 2) (v := 4) (by decide) (by decide) (by decide) (by decide)
      (hne 3 5 (by decide)) s235 s0345.le (by rw [← tcyc x _ 2 3 5, ← tcyc x _ 5 2 3]; exact t523) (Or.inl (by decide)) (Or.inr ⟨by decide, s0345lt⟩)
  have t356 : 0 < det3 (x 5 - x 3) (x 6 - x 3) (x 2 - x 0) :=
    edgeStep F235 F0345 _ (a := 3) (b := 5) (w := 2) (v := 6) (by decide) (by decide) (by decide) (by decide)
      (hne 3 5 (by decide)) s235 s0345.le (by rw [← tcyc x _ 2 3 5, ← tcyc x _ 5 2 3]; exact t523) (Or.inl (by decide)) (Or.inl (by decide))
  have t632 : 0 < det3 (x 3 - x 6) (x 2 - x 6) (x 2 - x 0) :=
    edgeStep T.t236 F346 _ (a := 6) (b := 3) (w := 1) (v := 2) (by decide) (by decide) (by decide) (by decide)
      (hne 6 3 (by decide)) s236 s346.le (by rw [← tcyc x _ 1 6 3]; exact t163) (Or.inl (by decide)) (Or.inl (by decide))
  have t634 : 0 < det3 (x 3 - x 6) (x 4 - x 6) (x 2 - x 0) :=
    edgeStep T.t236 F346 _ (a := 6) (b := 3) (w := 1) (v := 4) (by decide) (by decide) (by decide) (by decide)
      (hne 6 3 (by decide)) s236 s346.le (by rw [← tcyc x _ 1 6 3]; exact t163) (Or.inl (by decide)) (Or.inr ⟨by decide, s346lt⟩)
  have t162 : 0 < det3 (x 6 - x 1) (x 2 - x 1) (x 2 - x 0) := (by rw [← tcyc x _ 2 1 6]; exact t216)
  have t631 : 0 < det3 (x 3 - x 6) (x 1 - x 6) (x 2 - x 0) := (by rw [← tcyc x _ 1 6 3]; exact t163)
  have t635 : 0 < det3 (x 3 - x 6) (x 5 - x 6) (x 2 - x 0) := (by rw [← tcyc x _ 5 6 3, ← tcyc x _ 3 5 6]; exact t356)
  have t352 : 0 < det3 (x 5 - x 3) (x 2 - x 3) (x 2 - x 0) := (by rw [← tcyc x _ 2 3 5, ← tcyc x _ 5 2 3]; exact t523)
  have t521 : 0 < det3 (x 2 - x 5) (x 1 - x 5) (x 2 - x 0) := (by rw [← tcyc x _ 1 5 2, ← tcyc x _ 2 1 5]; exact t215)
  refine ⟨by norm_num, one_ne_zero, ?_, ?_, ?_⟩
  · show x 0 = x 2 - (1 : ℝ) • (x 2 - x 0)
    rw [one_smul]; abel
  · obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
    have r0 : rim02 2 0 = 2 := rfl
    have r1 : rim02 2 1 = 1 := rfl
    have r2 : rim02 2 2 = 6 := rfl
    have r3 : rim02 2 3 = 3 := rfl
    have r4 : rim02 2 4 = 5 := rfl
    intro i j hj1 hj2
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [a0, a1, a2, a3, a4, r0, r1, r2, r3, r4] at hj1 hj2 ⊢ <;>
    first | exact absurd rfl hj1 | exact absurd rfl hj2 | assumption
  · obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
    have r0 : rim02 2 0 = 2 := rfl
    have r1 : rim02 2 1 = 1 := rfl
    have r2 : rim02 2 2 = 6 := rfl
    have r3 : rim02 2 3 = 3 := rfl
    have r4 : rim02 2 4 = 5 := rfl
    intro v hv hvr i
    have h0 := hvr 0; have h1 := hvr 1; have h2 := hvr 2; have h3 := hvr 3; have h4 := hvr 4
    rw [r0] at h0; rw [r1] at h1; rw [r2] at h2; rw [r3] at h3; rw [r4] at h4
    have hv5 : v = 4 := by
      clear hvr; fin_cases v <;> simp_all
    subst hv5
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    simp only [a0, a1, a2, a3, a4, r0, r1, r2, r3, r4] <;> assumption


theorem det02B {x : Fin 7 → ℝ³} (T : Type24 x) (F0345 : Face16 x {0, 3, 4, 5}) (F235 : Face16 x {2, 3, 5}) (F346 : Face16 x {3, 4, 6}) (hM : 0 < det24 x)
    (hs : 0 < ⟪F346.N, x 2 - x 0⟫) : EdgeRimDet x (x 2 - x 0) 0 1 6 (rim02s 2) := by
  have inj := T.inj
  have hne : ∀ a b : Fin 7, a ≠ b → x a ≠ x b := fun a b h e => h (inj e)
  have s012 := inner_zero (p := 0) (q := 2) T.t012 (by decide) (by decide)
  have s016 := inner_neg (p := 0) (q := 2) T.t016 (by decide) (by decide)
  have s016lt := s016
  have s025 := inner_zero (p := 0) (q := 2) T.t025 (by decide) (by decide)
  have s0345 := inner_neg (p := 0) (q := 2) F0345 (by decide) (by decide)
  have s0345lt := s0345
  have s046 := inner_neg (p := 0) (q := 2) T.t046 (by decide) (by decide)
  have s046lt := s046
  have s126 := inner_pos (p := 0) (q := 2) T.t126 (by decide) (by decide)
  have s235 := inner_pos (p := 0) (q := 2) F235 (by decide) (by decide)
  have s346 := hs
  have t216 := ref02216 hM
  have t213 : 0 < det3 (x 1 - x 2) (x 3 - x 2) (x 2 - x 0) :=
    edgeStep T.t126 T.t012 _ (a := 2) (b := 1) (w := 6) (v := 3) (by decide) (by decide) (by decide) (by decide)
      (hne 2 1 (by decide)) s126 s012.le t216 (Or.inl (by decide)) (Or.inl (by decide))
  have t214 : 0 < det3 (x 1 - x 2) (x 4 - x 2) (x 2 - x 0) :=
    edgeStep T.t126 T.t012 _ (a := 2) (b := 1) (w := 6) (v := 4) (by decide) (by decide) (by decide) (by decide)
      (hne 2 1 (by decide)) s126 s012.le t216 (Or.inl (by decide)) (Or.inl (by decide))
  have t215 : 0 < det3 (x 1 - x 2) (x 5 - x 2) (x 2 - x 0) :=
    edgeStep T.t126 T.t012 _ (a := 2) (b := 1) (w := 6) (v := 5) (by decide) (by decide) (by decide) (by decide)
      (hne 2 1 (by decide)) s126 s012.le t216 (Or.inl (by decide)) (Or.inl (by decide))
  have t163 : 0 < det3 (x 6 - x 1) (x 3 - x 1) (x 2 - x 0) :=
    edgeStep T.t126 T.t016 _ (a := 1) (b := 6) (w := 2) (v := 3) (by decide) (by decide) (by decide) (by decide)
      (hne 1 6 (by decide)) s126 s016.le (by rw [← tcyc x _ 2 1 6]; exact t216) (Or.inl (by decide)) (Or.inl (by decide))
  have t164 : 0 < det3 (x 6 - x 1) (x 4 - x 1) (x 2 - x 0) :=
    edgeStep T.t126 T.t016 _ (a := 1) (b := 6) (w := 2) (v := 4) (by decide) (by decide) (by decide) (by decide)
      (hne 1 6 (by decide)) s126 s016.le (by rw [← tcyc x _ 2 1 6]; exact t216) (Or.inl (by decide)) (Or.inl (by decide))
  have t165 : 0 < det3 (x 6 - x 1) (x 5 - x 1) (x 2 - x 0) :=
    edgeStep T.t126 T.t016 _ (a := 1) (b := 6) (w := 2) (v := 5) (by decide) (by decide) (by decide) (by decide)
      (hne 1 6 (by decide)) s126 s016.le (by rw [← tcyc x _ 2 1 6]; exact t216) (Or.inl (by decide)) (Or.inl (by decide))
  have t523 : 0 < det3 (x 2 - x 5) (x 3 - x 5) (x 2 - x 0) :=
    edgeStep F235 T.t025 _ (a := 5) (b := 2) (w := 1) (v := 3) (by decide) (by decide) (by decide) (by decide)
      (hne 5 2 (by decide)) s235 s025.le (by rw [← tcyc x _ 1 5 2, ← tcyc x _ 2 1 5]; exact t215) (Or.inl (by decide)) (Or.inl (by decide))
  have t524 : 0 < det3 (x 2 - x 5) (x 4 - x 5) (x 2 - x 0) :=
    edgeStep F235 T.t025 _ (a := 5) (b := 2) (w := 1) (v := 4) (by decide) (by decide) (by decide) (by decide)
      (hne 5 2 (by decide)) s235 s025.le (by rw [← tcyc x _ 1 5 2, ← tcyc x _ 2 1 5]; exact t215) (Or.inl (by decide)) (Or.inl (by decide))
  have t526 : 0 < det3 (x 2 - x 5) (x 6 - x 5) (x 2 - x 0) :=
    edgeStep F235 T.t025 _ (a := 5) (b := 2) (w := 1) (v := 6) (by decide) (by decide) (by decide) (by decide)
      (hne 5 2 (by decide)) s235 s025.le (by rw [← tcyc x _ 1 5 2, ← tcyc x _ 2 1 5]; exact t215) (Or.inl (by decide)) (Or.inl (by decide))
  have t351 : 0 < det3 (x 5 - x 3) (x 1 - x 3) (x 2 - x 0) :=
    edgeStep F235 F0345 _ (a := 3) (b := 5) (w := 2) (v := 1) (by decide) (by decide) (by decide) (by decide)
      (hne 3 5 (by decide)) s235 s0345.le (by rw [← tcyc x _ 2 3 5, ← tcyc x _ 5 2 3]; exact t523) (Or.inl (by decide)) (Or.inl (by decide))
  have t354 : 0 < det3 (x 5 - x 3) (x 4 - x 3) (x 2 - x 0) :=
    edgeStep F235 F0345 _ (a := 3) (b := 5) (w := 2) (v := 4) (by decide) (by decide) (by decide) (by decide)
      (hne 3 5 (by decide)) s235 s0345.le (by rw [← tcyc x _ 2 3 5, ← tcyc x _ 5 2 3]; exact t523) (Or.inl (by decide)) (Or.inr ⟨by decide, s0345lt⟩)
  have t356 : 0 < det3 (x 5 - x 3) (x 6 - x 3) (x 2 - x 0) :=
    edgeStep F235 F0345 _ (a := 3) (b := 5) (w := 2) (v := 6) (by decide) (by decide) (by decide) (by decide)
      (hne 3 5 (by decide)) s235 s0345.le (by rw [← tcyc x _ 2 3 5, ← tcyc x _ 5 2 3]; exact t523) (Or.inl (by decide)) (Or.inl (by decide))
  have t431 : 0 < det3 (x 3 - x 4) (x 1 - x 4) (x 2 - x 0) :=
    edgeStep F346 F0345 _ (a := 4) (b := 3) (w := 5) (v := 1) (by decide) (by decide) (by decide) (by decide)
      (hne 4 3 (by decide)) s346 s0345.le (by rw [← tcyc x _ 5 4 3, ← tcyc x _ 3 5 4]; exact t354) (Or.inr ⟨by decide, s0345lt⟩) (Or.inl (by decide))
  have t432 : 0 < det3 (x 3 - x 4) (x 2 - x 4) (x 2 - x 0) :=
    edgeStep F346 F0345 _ (a := 4) (b := 3) (w := 5) (v := 2) (by decide) (by decide) (by decide) (by decide)
      (hne 4 3 (by decide)) s346 s0345.le (by rw [← tcyc x _ 5 4 3, ← tcyc x _ 3 5 4]; exact t354) (Or.inr ⟨by decide, s0345lt⟩) (Or.inl (by decide))
  have t436 : 0 < det3 (x 3 - x 4) (x 6 - x 4) (x 2 - x 0) :=
    edgeStep F346 F0345 _ (a := 4) (b := 3) (w := 5) (v := 6) (by decide) (by decide) (by decide) (by decide)
      (hne 4 3 (by decide)) s346 s0345.le (by rw [← tcyc x _ 5 4 3, ← tcyc x _ 3 5 4]; exact t354) (Or.inr ⟨by decide, s0345lt⟩) (Or.inl (by decide))
  have t642 : 0 < det3 (x 4 - x 6) (x 2 - x 6) (x 2 - x 0) :=
    edgeStep F346 T.t046 _ (a := 6) (b := 4) (w := 1) (v := 2) (by decide) (by decide) (by decide) (by decide)
      (hne 6 4 (by decide)) s346 s046.le (by rw [← tcyc x _ 1 6 4]; exact t164) (Or.inl (by decide)) (Or.inl (by decide))
  have t645 : 0 < det3 (x 4 - x 6) (x 5 - x 6) (x 2 - x 0) :=
    edgeStep F346 T.t046 _ (a := 6) (b := 4) (w := 1) (v := 5) (by decide) (by decide) (by decide) (by decide)
      (hne 6 4 (by decide)) s346 s046.le (by rw [← tcyc x _ 1 6 4]; exact t164) (Or.inl (by decide)) (Or.inl (by decide))
  have t162 : 0 < det3 (x 6 - x 1) (x 2 - x 1) (x 2 - x 0) := (by rw [← tcyc x _ 2 1 6]; exact t216)
  have t641 : 0 < det3 (x 4 - x 6) (x 1 - x 6) (x 2 - x 0) := (by rw [← tcyc x _ 1 6 4]; exact t164)
  have t643 : 0 < det3 (x 4 - x 6) (x 3 - x 6) (x 2 - x 0) := (by rw [← tcyc x _ 3 6 4, ← tcyc x _ 4 3 6]; exact t436)
  have t435 : 0 < det3 (x 3 - x 4) (x 5 - x 4) (x 2 - x 0) := (by rw [← tcyc x _ 5 4 3, ← tcyc x _ 3 5 4]; exact t354)
  have t352 : 0 < det3 (x 5 - x 3) (x 2 - x 3) (x 2 - x 0) := (by rw [← tcyc x _ 2 3 5, ← tcyc x _ 5 2 3]; exact t523)
  have t521 : 0 < det3 (x 2 - x 5) (x 1 - x 5) (x 2 - x 0) := (by rw [← tcyc x _ 1 5 2, ← tcyc x _ 2 1 5]; exact t215)
  refine ⟨by norm_num, one_ne_zero, ?_, ?_, ?_⟩
  · show x 0 = x 2 - (1 : ℝ) • (x 2 - x 0)
    rw [one_smul]; abel
  · obtain ⟨a0, a1, a2, a3, a4, a5⟩ := zmod6_add_one
    have r0 : rim02s 2 0 = 2 := rfl
    have r1 : rim02s 2 1 = 1 := rfl
    have r2 : rim02s 2 2 = 6 := rfl
    have r3 : rim02s 2 3 = 4 := rfl
    have r4 : rim02s 2 4 = 3 := rfl
    have r5 : rim02s 2 5 = 5 := rfl
    intro i j hj1 hj2
    rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [a0, a1, a2, a3, a4, a5, r0, r1, r2, r3, r4, r5] at hj1 hj2 ⊢ <;>
    first | exact absurd rfl hj1 | exact absurd rfl hj2 | assumption
  · obtain ⟨a0, a1, a2, a3, a4, a5⟩ := zmod6_add_one
    have r0 : rim02s 2 0 = 2 := rfl
    have r1 : rim02s 2 1 = 1 := rfl
    have r2 : rim02s 2 2 = 6 := rfl
    have r3 : rim02s 2 3 = 4 := rfl
    have r4 : rim02s 2 4 = 3 := rfl
    have r5 : rim02s 2 5 = 5 := rfl
    intro v hv hvr i
    have h0 := hvr 0; have h1 := hvr 1; have h2 := hvr 2; have h3 := hvr 3; have h4 := hvr 4; have h5 := hvr 5
    rw [r0] at h0; rw [r1] at h1; rw [r2] at h2; rw [r3] at h3; rw [r4] at h4; rw [r5] at h5
    exfalso
    clear hvr; fin_cases v <;> simp_all



theorem edgeRimDet26 {x : Fin 7 → ℝ³} (T : Type24 x) (F0345 : Face16 x {0, 3, 4, 5})
    (F235 : Face16 x {2, 3, 5}) (F346 : Face16 x {3, 4, 6}) (hM : 0 < det24 x)
    (hsp : det3 (x 4 - x 3) (x 5 - x 3) (x 6 - x 2) ≠ 0) :
    (EdgeRimDet x (x 6 - x 2) 2 1 5 (rim26 4 6) ∧ EdgeRimDet x (x 6 - x 2) 6 (-1) 5 (rim26 4 2)) ∨
    (EdgeRimDet x (x 6 - x 2) 2 1 5 (rim26 5 6) ∧ EdgeRimDet x (x 6 - x 2) 6 (-1) 5 (rim26 5 2)) := by
  have hN : F0345.N ≠ 0 := by
    intro h
    have e := Type24.f_eq_inner F0345 1 0
    rw [h, F0345.zero 0 (by decide)] at e
    have := F0345.neg 1 (by decide)
    simp at e; linarith
  have hp : ⟪F0345.N, x 4 - x 3⟫ = 0 := inner_zero F0345 (by decide) (by decide)
  have hq : ⟪F0345.N, x 5 - x 3⟫ = 0 := inner_zero F0345 (by decide) (by decide)
  obtain ⟨κ, hκ⟩ := cross_par_of_orth (x 4 - x 3) (x 5 - x 3) F0345.N hN
    (by rw [real_inner_comm]; exact hp) (by rw [real_inner_comm]; exact hq)
  have hd : det3 (x 4 - x 3) (x 5 - x 3) (x 6 - x 2) = κ * ⟪F0345.N, x 6 - x 2⟫ := by
    rw [det3, hκ, real_inner_smul_left]
  have hs0 : ⟪F0345.N, x 6 - x 2⟫ ≠ 0 := fun h => hsp (by rw [hd, h, mul_zero])
  rcases lt_or_gt_of_ne hs0 with hs | hs
  · left
    have hA := det26A T F0345 F346 hM hs
    exact ⟨hA, EdgeRimDet.transfer (by decide) rfl rfl hA⟩
  · right
    have hB := det26B T F0345 F235 F346 hM hs
    exact ⟨hB, EdgeRimDet.transfer (by decide) rfl rfl hB⟩

theorem edgeRimDet02 {x : Fin 7 → ℝ³} (T : Type24 x) (F0345 : Face16 x {0, 3, 4, 5})
    (F235 : Face16 x {2, 3, 5}) (F346 : Face16 x {3, 4, 6}) (hM : 0 < det24 x)
    (hsp : det3 (x 4 - x 3) (x 6 - x 3) (x 2 - x 0) ≠ 0) :
    (EdgeRimDet x (x 2 - x 0) 0 1 5 (rim02 2) ∧ EdgeRimDet x (x 2 - x 0) 2 (-1) 5 (rim02 0)) ∨
    (EdgeRimDet x (x 2 - x 0) 0 1 6 (rim02s 2) ∧ EdgeRimDet x (x 2 - x 0) 2 (-1) 6 (rim02s 0)) := by
  have hN : F346.N ≠ 0 := by
    intro h
    have e := Type24.f_eq_inner F346 1 3
    rw [h, F346.zero 3 (by decide)] at e
    have := F346.neg 1 (by decide)
    simp at e; linarith
  have hp : ⟪F346.N, x 4 - x 3⟫ = 0 := inner_zero F346 (by decide) (by decide)
  have hq : ⟪F346.N, x 6 - x 3⟫ = 0 := inner_zero F346 (by decide) (by decide)
  obtain ⟨κ, hκ⟩ := cross_par_of_orth (x 4 - x 3) (x 6 - x 3) F346.N hN
    (by rw [real_inner_comm]; exact hp) (by rw [real_inner_comm]; exact hq)
  have hd : det3 (x 4 - x 3) (x 6 - x 3) (x 2 - x 0) = κ * ⟪F346.N, x 2 - x 0⟫ := by
    rw [det3, hκ, real_inner_smul_left]
  have hs0 : ⟪F346.N, x 2 - x 0⟫ ≠ 0 := fun h => hsp (by rw [hd, h, mul_zero])
  rcases lt_or_gt_of_ne hs0 with hs | hs
  · left
    have hA := det02A T F0345 F235 F346 hM hs
    exact ⟨hA, EdgeRimDet.transfer (by decide) rfl rfl hA⟩
  · right
    have hB := det02B T F0345 F235 F346 hM hs
    exact ⟨hB, EdgeRimDet.transfer (by decide) rfl rfl hB⟩

end Link24R
end Minimality
