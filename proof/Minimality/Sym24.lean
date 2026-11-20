module

public import Minimality.R046
public import Minimality.Type02Frame
public import Minimality.R012W
public import Minimality.R012F
public import Minimality.R012M
public import Minimality.R012M3
public import Minimality.R046Cop
public import Minimality.Q45Tie
public import Minimality.RJ0E
public import Minimality.Q45J0
public import Minimality.RX16
public import Minimality.RF0345

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace Topology
open Filter Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.RimFromSigns
open Minimality.T24.Q45 Minimality.T24.R012 Minimality.T24.R046 Minimality.T24.RX16

namespace Minimality.T24.Sym

/-- Vertex involution `π = (2 6)(4 5)` (explicit table, so every evaluation is by `rfl`). -/
def pi24 : Equiv.Perm (Fin 7) where
  toFun := ![0, 1, 6, 3, 5, 4, 2]
  invFun := ![0, 1, 6, 3, 5, 4, 2]
  left_inv := by decide
  right_inv := by decide

/-- Facet involution `σ = (0 1)(2 4)(6 8)`. -/
def sig24 : Equiv.Perm (Fin 9) where
  toFun := ![1, 0, 4, 3, 2, 5, 8, 7, 6]
  invFun := ![1, 0, 4, 3, 2, 5, 8, 7, 6]
  left_inv := by decide
  right_inv := by decide

theorem s24_sym : ∀ (t : Fin 9) (i : Fin 7),
    i ∈ s0x_S24 t ↔ pi24 i ∈ s0x_S24 (sig24 t) := by decide

/-- The mirror facet data of `x ∘ π`. -/
noncomputable def sym24 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    S0xFac 9 s0x_S24 (x ∘ pi24) where
  f t := F.f (sig24 t)
  N t := F.N (sig24 t)
  hN _ y z := F.hN _ y z
  zero t i hi := F.zero _ _ ((s24_sym t i).1 hi)
  neg t i hi := F.neg _ _ (fun h => hi ((s24_sym t i).2 h))

@[simp] theorem sym24_N {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) :
    (sym24 F).N t = F.N (sig24 t) := rfl
@[simp] theorem sym24_f {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) :
    (sym24 F).f t = F.f (sig24 t) := rfl

/-- `IsRupert` transfers along the relabelling. -/
theorem isRupert_of_comp_pi24 {x : Fin 7 → ℝ³} (h : IsRupert (univ.image (x ∘ pi24))) :
    IsRupert (univ.image x) := by
  rwa [Minimality.CaseC18.isRupert_image_comp_perm] at h

/-- Generic transport of `FaceChordView` along a relabelling of vertices and facets. -/
theorem faceChordView_transport {N nf : ℕ} {S S' : Fin nf → Finset (Fin N)} {x : Fin N → ℝ³}
    (π : Equiv.Perm (Fin N)) (σ : Equiv.Perm (Fin nf))
    {F : S0xFac nf S x} {F' : S0xFac nf S' (x ∘ π)}
    (hN : ∀ t, F'.N t = F.N (σ t)) (hf : ∀ t, F'.f t = F.f (σ t))
    (hS : ∀ t i, i ∈ S' t ↔ π i ∈ S (σ t)) {t : Fin nf}
    (h : FaceChordView F' t) : FaceChordView F (σ t) := by
  rcases h with ⟨u, k, hne, r, a, w, ρ, hnu, hk, hA, hB, hρ, hcyc, hin, hmid, hinj, hz, hwS, hfar,
    hoff⟩
  have : NeZero k := hne
  refine ⟨u, k, hne, fun i => π (r i), a, w, ρ, ?_, hk, (hS _ _).1 hA, (hS _ _).1 hB, hρ,
    hcyc, ?_, ?_, hinj, hz, fun h => hwS ((hS _ _).2 h), ?_, ?_⟩
  · rw [← hN]; exact hnu
  · intro q hq hqr i
    obtain ⟨q', rfl⟩ := π.surjective q
    exact hin q' (fun h => hq ((hS _ _).1 h)) (fun j h => hqr j (by rw [h])) i
  · intro q hq hqr
    obtain ⟨q', rfl⟩ := π.surjective q
    exact hmid q' ((hS _ _).2 hq) (fun j h => hqr j (by rw [h]))
  · intro m hm hmS
    have := hfar m hm (fun h => hmS ((hS _ _).1 h))
    rwa [hf] at this
  · rw [← hN]; exact hoff

/-- `FaceChordView` of the mirror solid gives `FaceChordView` of `x` at facet `σ t`. -/
theorem faceChordView_sym {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {t : Fin 9}
    (h : FaceChordView (sym24 F) t) : FaceChordView F (sig24 t) :=
  faceChordView_transport pi24 sig24 (F := F) (F' := sym24 F) (fun _ => rfl) (fun _ => rfl)
    s24_sym h

theorem isRupert_of_faceChordView_sym {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {t : Fin 9}
    (h : FaceChordView (sym24 F) t) : IsRupert (univ.image x) :=
  isRupert_of_faceChordView F (faceChordView_sym F h)

/-! ### Demonstration 1: the 016 mirror of `q012_LC_plus` -/

/-- Mirror of `t_LC`: level-chord parameter on facet 1 (`016`), `u = u1 x t`. -/
noncomputable def t1_LC (x : Fin 7 → ℝ³) : ℝ :=
  - ⟪x 0 - x 6, x 0 - x 1⟫ / ⟪x 0 - x 6, x 6 - x 1⟫

/-- Mirror of `u_LC`. -/
noncomputable def u1_LC (x : Fin 7 → ℝ³) : ℝ³ := u1 x (t1_LC x)

/-- Mirror rim `(0, 5, 2, 3, 6)` of `rim012`. -/
def rim016 : ZMod 5 → Fin 7 := fun i => pi24 (rim012 i)

theorem q016_LC_plus (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x)
    (ht_pos : 0 < t1_LC x)
    (hN4 : ⟪F.N 2, u1_LC x⟫ < 0)
    (hN7 : ⟪F.N 7, u1_LC x⟫ < 0)
    (hN6 : 0 < ⟪F.N 8, u1_LC x⟫)
    (hN3 : 0 < ⟪F.N 3, u1_LC x⟫)
    (hN8 : 0 < ⟪F.N 6, u1_LC x⟫)
    (h_c3 : F.f 1 (x 2) < F.f 1 (x 3))
    (h_c4 : F.f 1 (x 2) < F.f 1 (x 5))
    (h_depth : ⟪x 5, u1_LC x⟫ < ⟪x 0, u1_LC x⟫)
    (hgen_LC : SingleAdjacentTie (fun i => x (rim016 i)) (u1_LC x) 4)
    (hdenom : ⟪x 0 - x 6, x 6 - x 1⟫ < 0)
    (hoff : ⟪F.N 1, cross (x 0 - x 6) (x 2 - x 6)⟫ ≠ 0 ∨
      ⟪x 2 - x 6, x 0 - x 6⟫ < 0 ∨ ⟪x 2 - x 0, x 6 - x 0⟫ < 0) :
    FaceChordView F 1 :=
  faceChordView_sym F (t := 0)
    (q012_LC_plus (x ∘ pi24) (sym24 F) ht_pos hN4 hN7 hN6 hN3 hN8 h_c3 h_c4 h_depth hgen_LC
      hdenom hoff)

/-! ### Demonstration 2: the 025 mirror of `q046_cross` -/

/-- Mirror of `omega3_012`. -/
noncomputable def omega3_016 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : ℝ :=
  - ⟪F.N 7, x 0 - x 1⟫ / ⟪F.N 7, x 6 - x 1⟫

/-- Mirror of `u47`. -/
noncomputable def u25 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : ℝ³ :=
  (- F.f 7 (x 5)) • (x 5 - x 0) + (F.f 7 (x 5) - F.f 7 (x 0)) • (x 5 - x 2)

theorem q025_cross (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x)
    (hi : 0 < ⟪F.N 5, x 5 - x 0⟫)
    (hii : 0 < ⟪F.N 8, u25 F⟫)
    (hiii : ⟪x 6, u1 x (omega3_016 F)⟫ ≤ ⟪x 0, u1 x (omega3_016 F)⟫)
    (hiv : ⟪x 2, u0 x (omega3_016 F)⟫ ≤ ⟪x 0, u0 x (omega3_016 F)⟫)
    (hob01 : ⟪x 0 - x 1, x 6 - x 1⟫ < 0) (hob02 : ⟪x 0 - x 1, x 2 - x 1⟫ < 0)
    (hob12 : ⟪x 6 - x 1, x 2 - x 1⟫ < 0)
    (hC5 : ⟪F.N 5, u25 F⟫ < 0) (hC2 : ⟪F.N 4, u25 F⟫ ≤ 0) (hC0 : ⟪F.N 1, u25 F⟫ ≤ 0)
    (hfar : F.f 2 (x 6) < F.f 2 (x 4))
    (hoff : ⟪F.N 2, cross (x 0 - x 2) (x 6 - x 2)⟫ ≠ 0 ∨
      ⟪x 6 - x 2, x 0 - x 2⟫ < 0 ∨ ⟪x 6 - x 0, x 2 - x 0⟫ < 0)
    (hgen : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 6) (x 2) (x 0) (x 4) i - quad (x 6) (x 2) (x 0) (x 4) j, u25 F⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 2) (x 0) (x 4) i - quad (x 6) (x 2) (x 0) (x 4) j, x 2 - x 0⟫ ≠ 0) :
    FaceChordView F 2 :=
  faceChordView_sym F (t := 4)
    (q046_cross (x := x ∘ pi24) (sym24 F) hi hii hiii hiv hob01 hob02 hob12 hC5 hC2 hC0 hfar
      hoff hgen)


/-! ### Mirror helper definitions for `016` and `0345` -/

/-- Mirror of `inv_omega4_012`. -/
noncomputable def inv_omega4_016 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : ℝ :=
  - ⟪F.N 2, x 0 - x 1⟫ / ⟪F.N 2, x 6 - x 1⟫

/-- Mirror of `omega4_012`. -/
noncomputable def omega4_016 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : ℝ :=
  - ⟪F.N 2, x 6 - x 1⟫ / ⟪F.N 2, x 0 - x 1⟫

/-- Mirror of `u08`. -/
noncomputable def u16_08 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : ℝ³ :=
  (F.f 1 (x 5) - F.f 1 (x 2)) • (x 3 - x 2) + (F.f 1 (x 2) - F.f 1 (x 3)) • (x 5 - x 2)

/-- Mirror of `Off012`. -/
def Off016 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (w : Fin 7) : Prop :=
  ⟪F.N 1, cross (x 0 - x 6) (x w - x 6)⟫ ≠ 0 ∨
    ⟪x w - x 6, x 0 - x 6⟫ < 0 ∨ ⟪x w - x 0, x 6 - x 0⟫ < 0

/-- Mirror of `FarOff012`. -/
def FarOff016 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ w : Fin 7, (w = 3 ∨ w = 5 ∨ w = 2) ∧
    (∀ m : Fin 7, (m = 3 ∨ m = 5 ∨ m = 2) → m ≠ w → F.f 1 (x w) < F.f 1 (x m)) ∧
    (⟪F.N 1, cross (x 0 - x 6) (x w - x 6)⟫ ≠ 0 ∨
      ⟪x w - x 6, x 0 - x 6⟫ < 0 ∨ ⟪x w - x 0, x 6 - x 0⟫ < 0)

/-! ### Mirrors on `016` (`sig24 0 = 1`) -/

private lemma pi24_pi24 (a : Fin 7) : pi24 (pi24 a) = a := by revert a; decide

theorem q016_w3_pos (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x)
    (hω3 : 0 < omega3_016 F)
    (hN4 : ⟪F.N 2, u1 x (omega3_016 F)⟫ < 0)
    (hN3 : 0 < ⟪F.N 3, u1 x (omega3_016 F)⟫)
    (hN8 : 0 < ⟪F.N 6, u1 x (omega3_016 F)⟫)
    (hbase : min ⟪x 5, u1 x (omega3_016 F)⟫ ⟪x 6, u1 x (omega3_016 F)⟫ <
      max ⟪x 0, u1 x (omega3_016 F)⟫ ⟪x 2, u1 x (omega3_016 F)⟫)
    (hfar : F.f 1 (x 5) ≠ F.f 1 (x 2))
    (hoff5 : F.f 1 (x 5) < F.f 1 (x 2) → Off016 F 5)
    (hoff2 : F.f 1 (x 2) < F.f 1 (x 5) → Off016 F 2)
    (hgen : Gen4 (quad (x 0) (x 5) (x 2) (x 6)) (u1 x (omega3_016 F)) (x 6 - x 1)) :
    FaceChordView F 1 :=
  faceChordView_sym F (t := 0)
    (q012_w3_pos (x := x ∘ pi24) (sym24 F) hω3 hN4 hN3 hN8 hbase hfar hoff5 hoff2 hgen)

theorem q016_w3_neg_A (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x)
    (hω3 : 0 < omega3_016 F)
    (hN4 : ⟪F.N 2, u1 x (omega3_016 F)⟫ < 0)
    (hN3 : 0 < ⟪F.N 3, u1 x (omega3_016 F)⟫)
    (hN6 : 0 < ⟪F.N 8, u1 x (omega3_016 F)⟫)
    (hN8 : ⟪F.N 6, u1 x (omega3_016 F)⟫ < 0)
    (hbase : min ⟪x 0, u1 x (omega3_016 F)⟫ ⟪x 3, u1 x (omega3_016 F)⟫ <
      max ⟪x 5, u1 x (omega3_016 F)⟫ ⟪x 6, u1 x (omega3_016 F)⟫)
    (hfar : F.f 1 (x 5) ≠ F.f 1 (x 3))
    (hoff5 : F.f 1 (x 5) < F.f 1 (x 3) → Off016 F 5)
    (hoff3 : F.f 1 (x 3) < F.f 1 (x 5) → Off016 F 3)
    (hgen : Gen4 (quad (x 0) (x 5) (x 3) (x 6)) (u1 x (omega3_016 F)) (x 6 - x 1)) :
    FaceChordView F 1 :=
  faceChordView_sym F (t := 0)
    (q012_w3_neg_A (x := x ∘ pi24) (sym24 F) hω3 hN4 hN3 hN6 hN8 hbase hfar hoff5 hoff3 hgen)

theorem q016_w3_neg_B (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x)
    (hω3 : 0 < omega3_016 F)
    (hN3 : ⟪F.N 3, u1 x (omega3_016 F)⟫ < 0)
    (hN6 : 0 < ⟪F.N 8, u1 x (omega3_016 F)⟫)
    (hbase : min ⟪x 4, u1 x (omega3_016 F)⟫ ⟪x 6, u1 x (omega3_016 F)⟫ <
      max ⟪x 0, u1 x (omega3_016 F)⟫ ⟪x 3, u1 x (omega3_016 F)⟫)
    (hfar : F.f 1 (x 4) ≠ F.f 1 (x 3))
    (hoff4 : F.f 1 (x 4) < F.f 1 (x 3) → Off016 F 4)
    (hoff3 : F.f 1 (x 3) < F.f 1 (x 4) → Off016 F 3)
    (hgen : Gen4 (quad (x 0) (x 4) (x 3) (x 6)) (u1 x (omega3_016 F)) (x 6 - x 1)) :
    FaceChordView F 1 :=
  faceChordView_sym F (t := 0)
    (q012_w3_neg_B (x := x ∘ pi24) (sym24 F) hω3 hN3 hN6 hbase hfar hoff4 hoff3 hgen)

theorem q016_w4_neg (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x)
    (hω4 : 0 < omega4_016 F)
    (hN7 : ⟪F.N 7, u1 x (inv_omega4_016 F)⟫ < 0)
    (hN6 : 0 < ⟪F.N 8, u1 x (inv_omega4_016 F)⟫)
    (hN8 : 0 < ⟪F.N 6, u1 x (inv_omega4_016 F)⟫)
    (hbase : min ⟪x 0, u1 x (inv_omega4_016 F)⟫ ⟪x 3, u1 x (inv_omega4_016 F)⟫ <
      max ⟪x 2, u1 x (inv_omega4_016 F)⟫ ⟪x 6, u1 x (inv_omega4_016 F)⟫)
    (hfar : F.f 1 (x 2) ≠ F.f 1 (x 3))
    (hoff2 : F.f 1 (x 2) < F.f 1 (x 3) → Off016 F 2)
    (hoff3 : F.f 1 (x 3) < F.f 1 (x 2) → Off016 F 3)
    (hgen : Gen4 (quad (x 0) (x 2) (x 3) (x 6)) (u1 x (inv_omega4_016 F)) (x 6 - x 1)) :
    FaceChordView F 1 :=
  faceChordView_sym F (t := 0)
    (q012_w4_neg (x := x ∘ pi24) (sym24 F) hω4 hN7 hN6 hN8 hbase hfar hoff2 hoff3 hgen)

theorem q016_f346_pos_A_4 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x)
    (hc3 : F.f 1 (x 3) < F.f 1 (x 2)) (hc5 : F.f 1 (x 2) < F.f 1 (x 5))
    (hN6 : 0 < ⟪F.N 8, u16_08 F⟫)
    (hN8 : F.f 6 (x 6) < F.f 6 (x 1))
    (hbase : min ⟪x 0, u16_08 F⟫ ⟪x 3, u16_08 F⟫ < max ⟪x 5, u16_08 F⟫ ⟪x 6, u16_08 F⟫)
    (hgen : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 0) (x 5) (x 3) (x 6) i - quad (x 0) (x 5) (x 3) (x 6) j, u16_08 F⟫ ≠ 0 ∨
      ⟪quad (x 0) (x 5) (x 3) (x 6) i - quad (x 0) (x 5) (x 3) (x 6) j, x 6 - x 1⟫ ≠ 0)
    (hoff : ⟪F.N 1, cross (x 0 - x 6) (x 3 - x 6)⟫ ≠ 0 ∨
      ⟪x 3 - x 6, x 0 - x 6⟫ < 0 ∨ ⟪x 3 - x 0, x 6 - x 0⟫ < 0) :
    FaceChordView F 1 :=
  faceChordView_sym F (t := 0)
    (q012_f346_pos_A_4 (x := x ∘ pi24) (sym24 F) hc3 hc5 hN6 hN8 hbase hgen hoff)

theorem q016_f346_B_4 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x)
    (hc5 : F.f 1 (x 5) < F.f 1 (x 2)) (hc3 : F.f 1 (x 2) < F.f 1 (x 3))
    (hN6 : 0 < ⟪F.N 8, -u16_08 F⟫)
    (hN8 : F.f 6 (x 1) < F.f 6 (x 6))
    (hbase : min ⟪x 0, -u16_08 F⟫ ⟪x 3, -u16_08 F⟫ < max ⟪x 5, -u16_08 F⟫ ⟪x 6, -u16_08 F⟫)
    (hgen : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 0) (x 5) (x 3) (x 6) i - quad (x 0) (x 5) (x 3) (x 6) j, -u16_08 F⟫ ≠ 0 ∨
      ⟪quad (x 0) (x 5) (x 3) (x 6) i - quad (x 0) (x 5) (x 3) (x 6) j, x 1 - x 6⟫ ≠ 0)
    (hoff : ⟪F.N 1, cross (x 0 - x 6) (x 5 - x 6)⟫ ≠ 0 ∨
      ⟪x 5 - x 6, x 0 - x 6⟫ < 0 ∨ ⟪x 5 - x 0, x 6 - x 0⟫ < 0) :
    FaceChordView F 1 :=
  faceChordView_sym F (t := 0)
    (q012_f346_B_4 (x := x ∘ pi24) (sym24 F) hc5 hc3 hN6 hN8 hbase hgen hoff)

theorem q016_m1_core (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x)
    (hN8 : 0 < ⟪F.N 6, x 0 - x 6⟫)
    (hU : UniM1 (x ∘ pi24) ∨ DSm1 (x ∘ pi24))
    (hgen : ∀ i j : ZMod 5, i ≠ j →
      ⟪(x ∘ pi24) (rimM1 i) - (x ∘ pi24) (rimM1 j), x 0 - x 6⟫ ≠ 0 ∨
      ⟪(x ∘ pi24) (rimM1 i) - (x ∘ pi24) (rimM1 j), x 1 - x 6⟫ ≠ 0)
    (w : ZMod 5) (hw : w = 1 ∨ w = 2 ∨ w = 3)
    (hfar : ∀ m : ZMod 5, m ≠ w → rimM1 m ∉ s0x_S24 0 →
      F.f 1 ((x ∘ pi24) (rimM1 w)) < F.f 1 ((x ∘ pi24) (rimM1 m)))
    (hoff : ⟪F.N 1, cross (x 1 - x 0) ((x ∘ pi24) (rimM1 w) - x 0)⟫ ≠ 0 ∨
      ⟪(x ∘ pi24) (rimM1 w) - x 0, x 1 - x 0⟫ < 0 ∨
      ⟪(x ∘ pi24) (rimM1 w) - x 1, x 0 - x 1⟫ < 0) :
    FaceChordView F 1 :=
  faceChordView_sym F (t := 0)
    (m1_core (x := x ∘ pi24) (sym24 F) hN8 hU hgen w hw hfar hoff)

theorem q016_m1_neg_pos (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x)
    (hN8 : 0 < ⟪F.N 6, x 0 - x 6⟫)
    (hk4 : 0 < det3 (x 0 - x 1) (x 6 - x 1) (x 2 - x 1) * det3 (x 3 - x 1) (x 4 - x 2) (x 1 - x 2))
    (hD0 : ¬ (lexD (x ∘ pi24) 6 1 ∧ lexD (x ∘ pi24) 1 0 ∧ lexD (x ∘ pi24) 6 3 ∧
      lexD (x ∘ pi24) 6 0 ∧ lexD (x ∘ pi24) 5 3 ∧ lexD (x ∘ pi24) 5 0))
    (hI1 : ¬ (lexD (x ∘ pi24) 1 6 ∧ lexD (x ∘ pi24) 6 3 ∧ lexD (x ∘ pi24) 5 3 ∧
      lexD (x ∘ pi24) 5 0 ∧ lexD (x ∘ pi24) 1 3 ∧ lexD (x ∘ pi24) 1 0))
    (hD2 : ¬ (lexD (x ∘ pi24) 5 3 ∧ lexD (x ∘ pi24) 3 6 ∧ lexD (x ∘ pi24) 5 0 ∧
      lexD (x ∘ pi24) 5 6 ∧ lexD (x ∘ pi24) 1 0 ∧ lexD (x ∘ pi24) 1 6))
    (hI3 : ¬ (lexD (x ∘ pi24) 3 5 ∧ lexD (x ∘ pi24) 5 0 ∧ lexD (x ∘ pi24) 1 0 ∧
      lexD (x ∘ pi24) 1 6 ∧ lexD (x ∘ pi24) 3 0 ∧ lexD (x ∘ pi24) 3 6))
    (hD4 : ¬ (lexD (x ∘ pi24) 1 0 ∧ lexD (x ∘ pi24) 0 5 ∧ lexD (x ∘ pi24) 1 6 ∧
      lexD (x ∘ pi24) 1 5 ∧ lexD (x ∘ pi24) 3 6 ∧ lexD (x ∘ pi24) 3 5))
    (hgen : ∀ i j : ZMod 5, i ≠ j →
      ⟪(x ∘ pi24) (rimM1 i) - (x ∘ pi24) (rimM1 j), x 0 - x 6⟫ ≠ 0 ∨
      ⟪(x ∘ pi24) (rimM1 i) - (x ∘ pi24) (rimM1 j), x 1 - x 6⟫ ≠ 0)
    (w : ZMod 5) (hw : w = 1 ∨ w = 2 ∨ w = 3)
    (hfar : ∀ m : ZMod 5, m ≠ w → rimM1 m ∉ s0x_S24 0 →
      F.f 1 ((x ∘ pi24) (rimM1 w)) < F.f 1 ((x ∘ pi24) (rimM1 m)))
    (hoff : ⟪F.N 1, cross (x 1 - x 0) ((x ∘ pi24) (rimM1 w) - x 0)⟫ ≠ 0 ∨
      ⟪(x ∘ pi24) (rimM1 w) - x 0, x 1 - x 0⟫ < 0 ∨
      ⟪(x ∘ pi24) (rimM1 w) - x 1, x 0 - x 1⟫ < 0) :
    FaceChordView F 1 :=
  faceChordView_sym F (t := 0)
    (q012_m1_neg_pos (x := x ∘ pi24) (sym24 F) hN8 hk4 hD0 hI1 hD2 hI3 hD4 hgen w hw hfar hoff)

theorem q016_m1_neg_neg (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x)
    (hN8 : 0 < ⟪F.N 6, x 0 - x 6⟫)
    (hk4 : det3 (x 0 - x 1) (x 6 - x 1) (x 2 - x 1) * det3 (x 3 - x 1) (x 4 - x 2) (x 1 - x 2) < 0)
    (hD0 : ¬ (lexD (x ∘ pi24) 6 1 ∧ lexD (x ∘ pi24) 1 0 ∧ lexD (x ∘ pi24) 6 3 ∧
      lexD (x ∘ pi24) 6 0 ∧ lexD (x ∘ pi24) 5 3 ∧ lexD (x ∘ pi24) 5 0))
    (hI1 : ¬ (lexD (x ∘ pi24) 1 6 ∧ lexD (x ∘ pi24) 6 3 ∧ lexD (x ∘ pi24) 5 3 ∧
      lexD (x ∘ pi24) 5 0 ∧ lexD (x ∘ pi24) 1 3 ∧ lexD (x ∘ pi24) 1 0))
    (hD2 : ¬ (lexD (x ∘ pi24) 5 3 ∧ lexD (x ∘ pi24) 3 6 ∧ lexD (x ∘ pi24) 5 0 ∧
      lexD (x ∘ pi24) 5 6 ∧ lexD (x ∘ pi24) 1 0 ∧ lexD (x ∘ pi24) 1 6))
    (hI3 : ¬ (lexD (x ∘ pi24) 3 5 ∧ lexD (x ∘ pi24) 5 0 ∧ lexD (x ∘ pi24) 1 0 ∧
      lexD (x ∘ pi24) 1 6 ∧ lexD (x ∘ pi24) 3 0 ∧ lexD (x ∘ pi24) 3 6))
    (hI4 : ¬ (lexD (x ∘ pi24) 5 0 ∧ lexD (x ∘ pi24) 0 1 ∧ lexD (x ∘ pi24) 6 1 ∧
      lexD (x ∘ pi24) 6 3 ∧ lexD (x ∘ pi24) 5 1 ∧ lexD (x ∘ pi24) 5 3))
    (hgen : ∀ i j : ZMod 5, i ≠ j →
      ⟪(x ∘ pi24) (rimM1 i) - (x ∘ pi24) (rimM1 j), x 0 - x 6⟫ ≠ 0 ∨
      ⟪(x ∘ pi24) (rimM1 i) - (x ∘ pi24) (rimM1 j), x 1 - x 6⟫ ≠ 0)
    (w : ZMod 5) (hw : w = 1 ∨ w = 2 ∨ w = 3)
    (hfar : ∀ m : ZMod 5, m ≠ w → rimM1 m ∉ s0x_S24 0 →
      F.f 1 ((x ∘ pi24) (rimM1 w)) < F.f 1 ((x ∘ pi24) (rimM1 m)))
    (hoff : ⟪F.N 1, cross (x 1 - x 0) ((x ∘ pi24) (rimM1 w) - x 0)⟫ ≠ 0 ∨
      ⟪(x ∘ pi24) (rimM1 w) - x 0, x 1 - x 0⟫ < 0 ∨
      ⟪(x ∘ pi24) (rimM1 w) - x 1, x 0 - x 1⟫ < 0) :
    FaceChordView F 1 :=
  faceChordView_sym F (t := 0)
    (q012_m1_neg_neg (x := x ∘ pi24) (sym24 F) hN8 hk4 hD0 hI1 hD2 hI3 hI4 hgen w hw hfar hoff)

theorem q016_m6_core (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x)
    (hN8 : ⟪F.N 6, x 0 - x 6⟫ < 0)
    (hU : (∃ t : ZMod 6, LexTop (fun i => (x ∘ pi24) (rimM6 i)) (x 0 - x 6) (x 1 - x 6) t) ∨
      ∃ a c : ZMod 6, c ≠ a ∧ c ≠ a + 1 ∧
        LexDS (fun i => (x ∘ pi24) (rimM6 i)) (-det3 (x 0 - x 1) (x 6 - x 1) (x 2 - x 1))
          (x 0 - x 6) (x 1 - x 6) a c)
    (hgen : ∀ i j : ZMod 6, i ≠ j →
      ⟪(x ∘ pi24) (rimM6 i) - (x ∘ pi24) (rimM6 j), x 0 - x 6⟫ ≠ 0 ∨
      ⟪(x ∘ pi24) (rimM6 i) - (x ∘ pi24) (rimM6 j), x 1 - x 6⟫ ≠ 0)
    (w : ZMod 6) (hw : w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5)
    (hfar : ∀ m : ZMod 6, m ≠ w → rimM6 m ∉ s0x_S24 0 →
      F.f 1 ((x ∘ pi24) (rimM6 w)) < F.f 1 ((x ∘ pi24) (rimM6 m)))
    (hoff : ⟪F.N 1, cross (x 1 - x 0) ((x ∘ pi24) (rimM6 w) - x 0)⟫ ≠ 0 ∨
      ⟪(x ∘ pi24) (rimM6 w) - x 0, x 1 - x 0⟫ < 0 ∨
      ⟪(x ∘ pi24) (rimM6 w) - x 1, x 0 - x 1⟫ < 0) :
    FaceChordView F 1 :=
  faceChordView_sym F (t := 0)
    (m6_core (x := x ∘ pi24) (sym24 F) hN8 hU hgen w hw hfar hoff)

theorem q016_m1p5_core (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x)
    (hN8 : 0 < ⟪F.N 6, x 0 - x 6⟫)
    (hU : (∃ t : ZMod 5, LexTop (fun i => (x ∘ pi24) (rimP5 i)) (x 0 - x 6) (x 6 - x 1) t) ∨
      ∃ a c : ZMod 5, c ≠ a ∧ c ≠ a + 1 ∧
        LexDS (fun i => (x ∘ pi24) (rimP5 i)) (-det3 (x 0 - x 1) (x 6 - x 1) (x 2 - x 1))
          (x 0 - x 6) (x 6 - x 1) a c)
    (hgen : ∀ i j : ZMod 5, i ≠ j →
      ⟪(x ∘ pi24) (rimP5 i) - (x ∘ pi24) (rimP5 j), x 0 - x 6⟫ ≠ 0 ∨
      ⟪(x ∘ pi24) (rimP5 i) - (x ∘ pi24) (rimP5 j), x 6 - x 1⟫ ≠ 0)
    (w : ZMod 5) (hw : w = 1 ∨ w = 2 ∨ w = 3)
    (hfar : ∀ m : ZMod 5, m ≠ w → rimP5 m ∉ s0x_S24 0 →
      F.f 1 ((x ∘ pi24) (rimP5 w)) < F.f 1 ((x ∘ pi24) (rimP5 m)))
    (hoff : ⟪F.N 1, cross (x 1 - x 6) ((x ∘ pi24) (rimP5 w) - x 6)⟫ ≠ 0 ∨
      ⟪(x ∘ pi24) (rimP5 w) - x 6, x 1 - x 6⟫ < 0 ∨
      ⟪(x ∘ pi24) (rimP5 w) - x 1, x 6 - x 1⟫ < 0) :
    FaceChordView F 1 :=
  faceChordView_sym F (t := 0)
    (m1p5_core (x := x ∘ pi24) (sym24 F) hN8 hU hgen w hw hfar hoff)

theorem q016_m1p6_core (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x)
    (hN8 : ⟪F.N 6, x 0 - x 6⟫ < 0)
    (hU : (∃ t : ZMod 6, LexTop (fun i => (x ∘ pi24) (rimP6 i)) (x 0 - x 6) (x 6 - x 1) t) ∨
      ∃ a c : ZMod 6, c ≠ a ∧ c ≠ a + 1 ∧
        LexDS (fun i => (x ∘ pi24) (rimP6 i)) (-det3 (x 0 - x 1) (x 6 - x 1) (x 2 - x 1))
          (x 0 - x 6) (x 6 - x 1) a c)
    (hgen : ∀ i j : ZMod 6, i ≠ j →
      ⟪(x ∘ pi24) (rimP6 i) - (x ∘ pi24) (rimP6 j), x 0 - x 6⟫ ≠ 0 ∨
      ⟪(x ∘ pi24) (rimP6 i) - (x ∘ pi24) (rimP6 j), x 6 - x 1⟫ ≠ 0)
    (w : ZMod 6) (hw : w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5)
    (hfar : ∀ m : ZMod 6, m ≠ w → rimP6 m ∉ s0x_S24 0 →
      F.f 1 ((x ∘ pi24) (rimP6 w)) < F.f 1 ((x ∘ pi24) (rimP6 m)))
    (hoff : ⟪F.N 1, cross (x 1 - x 6) ((x ∘ pi24) (rimP6 w) - x 6)⟫ ≠ 0 ∨
      ⟪(x ∘ pi24) (rimP6 w) - x 6, x 1 - x 6⟫ < 0 ∨
      ⟪(x ∘ pi24) (rimP6 w) - x 1, x 6 - x 1⟫ < 0) :
    FaceChordView F 1 :=
  faceChordView_sym F (t := 0)
    (m1p6_core (x := x ∘ pi24) (sym24 F) hN8 hU hgen w hw hfar hoff)

theorem q016_LC_minus (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x)
    (ht_pos : 0 < t1_LC x)
    (hN4 : ⟪F.N 2, u1_LC x⟫ < 0)
    (hN7 : ⟪F.N 7, u1_LC x⟫ < 0)
    (hN6 : 0 < ⟪F.N 8, u1_LC x⟫)
    (hN3 : 0 < ⟪F.N 3, u1_LC x⟫)
    (hN8 : 0 < ⟪F.N 6, u1_LC x⟫)
    (h_c3 : F.f 1 (x 2) < F.f 1 (x 3))
    (h_c4 : F.f 1 (x 2) < F.f 1 (x 5))
    (h_depth : ⟪x 3, u1_LC x⟫ < ⟪x 0, u1_LC x⟫)
    (hgen_LC : SingleAdjacentTie (fun i => x (rim016 i)) (u1_LC x) 4)
    (hdenom : ⟪x 0 - x 6, x 6 - x 1⟫ < 0)
    (hoff : ⟪F.N 1, cross (x 0 - x 6) (x 2 - x 6)⟫ ≠ 0 ∨
      ⟪x 2 - x 6, x 0 - x 6⟫ < 0 ∨ ⟪x 2 - x 0, x 6 - x 0⟫ < 0) :
    FaceChordView F 1 :=
  faceChordView_sym F (t := 0)
    (q012_LC_minus (x ∘ pi24) (sym24 F) ht_pos hN4 hN7 hN6 hN3 hN8 h_c3 h_c4 h_depth hgen_LC
      hdenom hoff)

theorem q016_LC_plus_gen (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x)
    (ht_pos : 0 < t1_LC x)
    (hN4 : ⟪F.N 2, u1_LC x⟫ < 0)
    (hN7 : ⟪F.N 7, u1_LC x⟫ < 0)
    (hN6 : 0 < ⟪F.N 8, u1_LC x⟫)
    (hN3 : 0 < ⟪F.N 3, u1_LC x⟫)
    (hN8 : 0 < ⟪F.N 6, u1_LC x⟫)
    (hfar : FarOff016 F)
    (h_depth : ⟪x 5, u1_LC x⟫ < ⟪x 0, u1_LC x⟫)
    (hgen_LC : SingleAdjacentTie (fun i => x (rim016 i)) (u1_LC x) 4)
    (hdenom : ⟪x 0 - x 6, x 6 - x 1⟫ < 0) :
    FaceChordView F 1 :=
  faceChordView_sym F (t := 0)
    (q012_LC_plus_gen (x ∘ pi24) (sym24 F) ht_pos hN4 hN7 hN6 hN3 hN8
      (by
        rcases hfar with ⟨w, hw, hmin, hoff⟩
        refine ⟨pi24 w, by rcases hw with rfl | rfl | rfl <;> decide, ?_,
          by rcases hw with rfl | rfl | rfl <;> exact hoff⟩
        intro m hm hne
        dsimp [sym24]; rw [pi24_pi24]
        exact hmin (pi24 m) (by rcases hm with rfl | rfl | rfl <;> decide)
          (fun h => hne (by rw [← h, pi24_pi24])))
      h_depth hgen_LC hdenom)

theorem q016_LC_minus_gen (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x)
    (ht_pos : 0 < t1_LC x)
    (hN4 : ⟪F.N 2, u1_LC x⟫ < 0)
    (hN7 : ⟪F.N 7, u1_LC x⟫ < 0)
    (hN6 : 0 < ⟪F.N 8, u1_LC x⟫)
    (hN3 : 0 < ⟪F.N 3, u1_LC x⟫)
    (hN8 : 0 < ⟪F.N 6, u1_LC x⟫)
    (hfar : FarOff016 F)
    (h_depth : ⟪x 3, u1_LC x⟫ < ⟪x 0, u1_LC x⟫)
    (hgen_LC : SingleAdjacentTie (fun i => x (rim016 i)) (u1_LC x) 4)
    (hdenom : ⟪x 0 - x 6, x 6 - x 1⟫ < 0) :
    FaceChordView F 1 :=
  faceChordView_sym F (t := 0)
    (q012_LC_minus_gen (x ∘ pi24) (sym24 F) ht_pos hN4 hN7 hN6 hN3 hN8
      (by
        rcases hfar with ⟨w, hw, hmin, hoff⟩
        refine ⟨pi24 w, by rcases hw with rfl | rfl | rfl <;> decide, ?_,
          by rcases hw with rfl | rfl | rfl <;> exact hoff⟩
        intro m hm hne
        dsimp [sym24]; rw [pi24_pi24]
        exact hmin (pi24 m) (by rcases hm with rfl | rfl | rfl <;> decide)
          (fun h => hne (by rw [← h, pi24_pi24])))
      h_depth hgen_LC hdenom)

theorem q016_x16_lo (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x)
    (hΔ : ⟪x 1 - x 2, x 6 - x 1⟫ ≠ 0) (ht : t16 (x ∘ pi24) < -1)
    (hN3 : ⟪F.N 3, u16 (x ∘ pi24)⟫ < 0) (hN4 : 0 < ⟪F.N 2, u16 (x ∘ pi24)⟫)
    (hN8 : ⟪F.N 6, u16 (x ∘ pi24)⟫ < 0)
    (hbr : 0 < (⟪x 1, u16 (x ∘ pi24)⟫ - ⟪x 0, u16 (x ∘ pi24)⟫) *
        (⟪x 1, u16 (x ∘ pi24)⟫ - ⟪x 5, u16 (x ∘ pi24)⟫) ∨
      0 < ⟪x 1 - x 2, x 6 - x 1⟫ * (⟪x 0, u16 (x ∘ pi24)⟫ - ⟪x 5, u16 (x ∘ pi24)⟫))
    (hgen : ∀ i j : ZMod 4, i ≠ j → (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
      ⟪quad (x 5) (x 0) (x 1) (x 2) i - quad (x 5) (x 0) (x 1) (x 2) j, u16 (x ∘ pi24)⟫ ≠ 0)
    (hfar : (F.f 1 (x 2) < F.f 1 (x 5) ∧
        (⟪F.N 1, cross (x 1 - x 0) (x 2 - x 0)⟫ ≠ 0 ∨
          ⟪x 2 - x 0, x 1 - x 0⟫ < 0 ∨ ⟪x 2 - x 1, x 0 - x 1⟫ < 0)) ∨
      (F.f 1 (x 5) < F.f 1 (x 2) ∧
        (⟪F.N 1, cross (x 1 - x 0) (x 5 - x 0)⟫ ≠ 0 ∨
          ⟪x 5 - x 0, x 1 - x 0⟫ < 0 ∨ ⟪x 5 - x 1, x 0 - x 1⟫ < 0))) :
    FaceChordView F 1 :=
  faceChordView_sym F (t := 0)
    (q012_x16_lo (x := x ∘ pi24) (sym24 F) hΔ ht hN3 hN4 hN8 hbr hgen hfar)

theorem q016_x16_hi (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x)
    (hΔ : ⟪x 1 - x 2, x 6 - x 1⟫ ≠ 0) (ht1 : -1 < t16 (x ∘ pi24)) (ht0 : t16 (x ∘ pi24) < 0)
    (hN6 : 0 < ⟪F.N 8, u16 (x ∘ pi24)⟫) (hN7 : ⟪F.N 7, u16 (x ∘ pi24)⟫ < 0)
    (hN8 : 0 < ⟪F.N 6, u16 (x ∘ pi24)⟫)
    (hbr : 0 < (⟪x 1, u16 (x ∘ pi24)⟫ - ⟪x 6, u16 (x ∘ pi24)⟫) *
        (⟪x 1, u16 (x ∘ pi24)⟫ - ⟪x 3, u16 (x ∘ pi24)⟫) ∨
      0 < -⟪x 1 - x 2, x 6 - x 1⟫ * (⟪x 6, u16 (x ∘ pi24)⟫ - ⟪x 3, u16 (x ∘ pi24)⟫))
    (hgen : ∀ i j : ZMod 4, i ≠ j → (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
      ⟪quad (x 3) (x 6) (x 1) (x 2) i - quad (x 3) (x 6) (x 1) (x 2) j, u16 (x ∘ pi24)⟫ ≠ 0)
    (hfar : (F.f 1 (x 2) < F.f 1 (x 3) ∧
        (⟪F.N 1, cross (x 1 - x 6) (x 2 - x 6)⟫ ≠ 0 ∨
          ⟪x 2 - x 6, x 1 - x 6⟫ < 0 ∨ ⟪x 2 - x 1, x 6 - x 1⟫ < 0)) ∨
      (F.f 1 (x 3) < F.f 1 (x 2) ∧
        (⟪F.N 1, cross (x 1 - x 6) (x 3 - x 6)⟫ ≠ 0 ∨
          ⟪x 3 - x 6, x 1 - x 6⟫ < 0 ∨ ⟪x 3 - x 1, x 6 - x 1⟫ < 0))) :
    FaceChordView F 1 :=
  faceChordView_sym F (t := 0)
    (q012_x16_hi (x := x ∘ pi24) (sym24 F) hΔ ht1 ht0 hN6 hN7 hN8 hbr hgen hfar)

theorem q016_f0345 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x)
    (ht : 0 < t3_f0345 (sym24 F))
    (hN4 : ⟪F.N 2, u0 (x ∘ pi24) (t3_f0345 (sym24 F))⟫ < 0)
    (hN7 : ⟪F.N 7, u0 (x ∘ pi24) (t3_f0345 (sym24 F))⟫ < 0)
    (hN6 : 0 < ⟪F.N 8, u0 (x ∘ pi24) (t3_f0345 (sym24 F))⟫)
    (hN8 : ⟪F.N 6, u0 (x ∘ pi24) (t3_f0345 (sym24 F))⟫ < 0)
    (htie : ¬ (⟪x 0, u0 (x ∘ pi24) (t3_f0345 (sym24 F))⟫ = ⟪x 6, u0 (x ∘ pi24) (t3_f0345 (sym24 F))⟫ ∧
      ⟪x 6, u0 (x ∘ pi24) (t3_f0345 (sym24 F))⟫ = ⟪x 3, u0 (x ∘ pi24) (t3_f0345 (sym24 F))⟫))
    (hfar43 : F.f 1 (x 5) ≠ F.f 1 (x 3))
    (hoff4 : F.f 1 (x 5) < F.f 1 (x 3) →
      ⟪F.N 1, cross (x 0 - x 6) (x 5 - x 6)⟫ ≠ 0 ∨
        ⟪x 5 - x 6, x 0 - x 6⟫ < 0 ∨ ⟪x 5 - x 0, x 6 - x 0⟫ < 0)
    (hoff3 : F.f 1 (x 3) < F.f 1 (x 5) →
      ⟪F.N 1, cross (x 0 - x 6) (x 3 - x 6)⟫ ≠ 0 ∨
        ⟪x 3 - x 6, x 0 - x 6⟫ < 0 ∨ ⟪x 3 - x 0, x 6 - x 0⟫ < 0)
    (hgenLo : Gen4 (quad (x 0) (x 5) (x 3) (x 6)) (u0 (x ∘ pi24) (t3_f0345 (sym24 F))) (x 6 - x 1))
    (hfar53 : F.f 1 (x 4) ≠ F.f 1 (x 3))
    (hoff5 : F.f 1 (x 4) < F.f 1 (x 3) →
      ⟪F.N 1, cross (x 0 - x 6) (x 4 - x 6)⟫ ≠ 0 ∨
        ⟪x 4 - x 6, x 0 - x 6⟫ < 0 ∨ ⟪x 4 - x 0, x 6 - x 0⟫ < 0)
    (hoff3' : F.f 1 (x 3) < F.f 1 (x 4) →
      ⟪F.N 1, cross (x 0 - x 6) (x 3 - x 6)⟫ ≠ 0 ∨
        ⟪x 3 - x 6, x 0 - x 6⟫ < 0 ∨ ⟪x 3 - x 0, x 6 - x 0⟫ < 0)
    (hgenHi : Gen4 (quad (x 0) (x 4) (x 3) (x 6)) (u0 (x ∘ pi24) (t3_f0345 (sym24 F))) (x 6 - x 1)) :
    FaceChordView F 1 :=
  faceChordView_sym F (t := 0)
    (q012_f0345 (x := x ∘ pi24) (sym24 F) ht hN4 hN7 hN6 hN8 htie hfar43 hoff4 hoff3 hgenLo
      hfar53 hoff5 hoff3' hgenHi)

/-! ### Mirrors on `025` (`sig24 4 = 2`) -/

theorem q025_coplanar (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x)
    (h2 : ⟪F.N 4, x 5 - x 2⟫ < 0) (h6 : ⟪F.N 8, x 5 - x 2⟫ < 0)
    (hfar : F.f 2 (x 3) ≠ F.f 2 (x 4))
    (hoff : ⟪F.N 2, cross (x 0 - x 5) (x (if F.f 2 (x 3) < F.f 2 (x 4) then 3 else 4) - x 5)⟫ ≠ 0 ∨
      ⟪x (if F.f 2 (x 3) < F.f 2 (x 4) then 3 else 4) - x 5, x 0 - x 5⟫ < 0 ∨
      ⟪x (if F.f 2 (x 3) < F.f 2 (x 4) then 3 else 4) - x 0, x 5 - x 0⟫ < 0)
    (hgen : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 5) (x 0) (x 4) (x 3) i - quad (x 5) (x 0) (x 4) (x 3) j, x 5 - x 2⟫ ≠ 0 ∨
      ⟪quad (x 5) (x 0) (x 4) (x 3) i - quad (x 5) (x 0) (x 4) (x 3) j, x 0 - x 2⟫ ≠ 0) :
    FaceChordView F 2 :=
  faceChordView_sym F (t := 4)
    (q046_coplanar (x := x ∘ pi24) (sym24 F) h2 h6 hfar
      (by
        have h := hoff
        dsimp [sym24, pi24, sig24]
        by_cases hlt : F.f 2 (x 3) < F.f 2 (x 4)
        · simp only [hlt, ite_true] at h ⊢; exact h
        · simp only [hlt, ite_false] at h ⊢; exact h)
      hgen)

theorem q025_cross_core_beta (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x)
    (hβ : 0 < F.f 7 (x 5) - F.f 7 (x 0))
    (hii : 0 < ⟪F.N 8, u25 F⟫)
    (hbase : min ⟪x 2, u25 F⟫ ⟪x 4, u25 F⟫ < max ⟪x 6, u25 F⟫ ⟪x 0, u25 F⟫)
    (hC5 : ⟪F.N 5, u25 F⟫ < 0) (hC2 : ⟪F.N 4, u25 F⟫ ≤ 0)
    (hfar : (F.f 2 (x 6) < F.f 2 (x 4) ∧
      (⟪F.N 2, cross (x 0 - x 2) (x 6 - x 2)⟫ ≠ 0 ∨
        ⟪x 6 - x 2, x 0 - x 2⟫ < 0 ∨ ⟪x 6 - x 0, x 2 - x 0⟫ < 0)) ∨
      (F.f 2 (x 4) < F.f 2 (x 6) ∧
      (⟪F.N 2, cross (x 0 - x 2) (x 4 - x 2)⟫ ≠ 0 ∨
        ⟪x 4 - x 2, x 0 - x 2⟫ < 0 ∨ ⟪x 4 - x 0, x 2 - x 0⟫ < 0)))
    (hgen : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 6) (x 2) (x 0) (x 4) i - quad (x 6) (x 2) (x 0) (x 4) j, u25 F⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 2) (x 0) (x 4) i - quad (x 6) (x 2) (x 0) (x 4) j, x 2 - x 0⟫ ≠ 0) :
    FaceChordView F 2 :=
  faceChordView_sym F (t := 4)
    (ropen_cross_core_beta (x := x ∘ pi24) (sym24 F) hβ hii hbase hC5 hC2 hfar hgen)

theorem q025_cross_core (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x)
    (hi : 0 < ⟪F.N 5, x 5 - x 0⟫)
    (hii : 0 < ⟪F.N 8, u25 F⟫)
    (hbase : ⟪x 2, u25 F⟫ < ⟪x 0, u25 F⟫)
    (hC5 : ⟪F.N 5, u25 F⟫ < 0) (hC2 : ⟪F.N 4, u25 F⟫ ≤ 0)
    (hfar : (F.f 2 (x 6) < F.f 2 (x 4) ∧
      (⟪F.N 2, cross (x 0 - x 2) (x 6 - x 2)⟫ ≠ 0 ∨
        ⟪x 6 - x 2, x 0 - x 2⟫ < 0 ∨ ⟪x 6 - x 0, x 2 - x 0⟫ < 0)) ∨
      (F.f 2 (x 4) < F.f 2 (x 6) ∧
      (⟪F.N 2, cross (x 0 - x 2) (x 4 - x 2)⟫ ≠ 0 ∨
        ⟪x 4 - x 2, x 0 - x 2⟫ < 0 ∨ ⟪x 4 - x 0, x 2 - x 0⟫ < 0)))
    (hgen : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 6) (x 2) (x 0) (x 4) i - quad (x 6) (x 2) (x 0) (x 4) j, u25 F⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 2) (x 0) (x 4) i - quad (x 6) (x 2) (x 0) (x 4) j, x 2 - x 0⟫ ≠ 0) :
    FaceChordView F 2 :=
  faceChordView_sym F (t := 4)
    (q046_cross_core (x := x ∘ pi24) (sym24 F) hi hii hbase hC5 hC2 hfar hgen)

theorem q025_cross_cbar (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x)
    (hi : 0 < ⟪F.N 5, x 5 - x 0⟫)
    (hii : 0 < ⟪F.N 8, u25 F⟫)
    (hbase : ⟪x 2, u25 F⟫ < ⟪x 0, u25 F⟫)
    (hCbar : 0 < omega3 (x ∘ pi24) ∧ 0 < omega4 (x ∘ pi24) ∧ 0 < omega5 (x ∘ pi24) ∧
      0 ≤ Delta24 (x ∘ pi24))
    (hfar : (F.f 2 (x 6) < F.f 2 (x 4) ∧
      (⟪F.N 2, cross (x 0 - x 2) (x 6 - x 2)⟫ ≠ 0 ∨
        ⟪x 6 - x 2, x 0 - x 2⟫ < 0 ∨ ⟪x 6 - x 0, x 2 - x 0⟫ < 0)) ∨
      (F.f 2 (x 4) < F.f 2 (x 6) ∧
      (⟪F.N 2, cross (x 0 - x 2) (x 4 - x 2)⟫ ≠ 0 ∨
        ⟪x 4 - x 2, x 0 - x 2⟫ < 0 ∨ ⟪x 4 - x 0, x 2 - x 0⟫ < 0)))
    (hgen : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 6) (x 2) (x 0) (x 4) i - quad (x 6) (x 2) (x 0) (x 4) j, u25 F⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 2) (x 0) (x 4) i - quad (x 6) (x 2) (x 0) (x 4) j, x 2 - x 0⟫ ≠ 0) :
    FaceChordView F 2 :=
  faceChordView_sym F (t := 4)
    (q046_cross_cbar (x := x ∘ pi24) (sym24 F) hi hii hbase hCbar hfar hgen)

/-! ### Mirrors on `0345` (`sig24 3 = 3`, `E4/e35` end) -/

private lemma sig24_three : sig24 3 = 3 := rfl

theorem q45_J0_tie45_sym (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) (s t : ℝ)
    (hs0 : 0 < s) (ht : 0 < t) (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 5 - x 0) + t • (x 4 - x 0))
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (h8 : 0 < α * (1 - s) + β * t) (h6 : 0 < α * s + β * (1 - t))
    (hN5 : 0 < ⟪F.N 5, u_Pi (x ∘ pi24) α β⟫)
    (htie : SingleAdjacentTie (quint (x 5) (x 4) (x 6) (x 1) (x 2)) (u_Pi (x ∘ pi24) α β) 0)
    (hnot : min ⟪x 2, u_Pi (x ∘ pi24) α β⟫ ⟪x 6, u_Pi (x ∘ pi24) α β⟫ <
      max ⟪x 5, u_Pi (x ∘ pi24) α β⟫ ⟪x 1, u_Pi (x ∘ pi24) α β⟫)
    (w : Fin 7) (hw : w = 1 ∨ w = 6 ∨ w = 2)
    (hmin : ∀ m : Fin 7, m ≠ w → (m = 1 ∨ m = 6 ∨ m = 2) → F.f 3 (x w) < F.f 3 (x m))
    (hoff : ⟪F.N 3, cross (x 4 - x 5) (x w - x 5)⟫ ≠ 0 ∨ ⟪x w - x 5, x 4 - x 5⟫ < 0 ∨
      ⟪x w - x 4, x 5 - x 4⟫ < 0) :
    FaceChordView F 3 :=
  faceChordView_sym F (t := 3)
    (q45_J0_tie45 (x := x ∘ pi24) (sym24 F) s t hs0 ht hst hdecomp α β hα hβ h8 h6 hN5
      htie hnot (pi24 w) (by rcases hw with rfl | rfl | rfl <;> decide)
      (fun m hm hm' => by
        have := hmin (pi24 m) (fun h => hm (by rw [← h, pi24_pi24]))
          (by rcases hm' with rfl | rfl | rfl <;> decide)
        simpa [pi24_pi24, sig24_three] using this)
      (by rcases hw with rfl | rfl | rfl <;> exact hoff))

theorem q45_J0_exp_end_ds_sym (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) (s t : ℝ)
    (hs0 : 0 < s) (ht : 0 < t) (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 5 - x 0) + t • (x 4 - x 0)) (hs : s ≤ 1)
    (hN5 : 0 < ⟪F.N 5, x 4 - x 0⟫)
    (hU : UniLex (x ∘ pi24) (x 4 - x 0) (x 5 - x 4) ∨ DSany (x ∘ pi24) (x 4 - x 0) (x 5 - x 4))
    (hgen : ∀ i j : ZMod 5, i ≠ j →
      ⟪rimJ0 (x ∘ pi24) i - rimJ0 (x ∘ pi24) j, x 4 - x 0⟫ ≠ 0 ∨
      ⟪rimJ0 (x ∘ pi24) i - rimJ0 (x ∘ pi24) j, x 5 - x 4⟫ ≠ 0)
    (w : Fin 7) (hw : w = 1 ∨ w = 6 ∨ w = 2)
    (hmin : ∀ m : Fin 7, m ≠ w → (m = 1 ∨ m = 6 ∨ m = 2) → F.f 3 (x w) < F.f 3 (x m))
    (hoff : ⟪F.N 3, cross (x 4 - x 5) (x w - x 5)⟫ ≠ 0 ∨ ⟪x w - x 5, x 4 - x 5⟫ < 0 ∨
      ⟪x w - x 4, x 5 - x 4⟫ < 0) :
    FaceChordView F 3 :=
  faceChordView_sym F (t := 3)
    (q45_J0_exp_end_ds (x := x ∘ pi24) (sym24 F) s t hs0 ht hst hdecomp hs hN5 hU hgen
      (pi24 w) (by rcases hw with rfl | rfl | rfl <;> decide)
      (fun m hm hm' => by
        have := hmin (pi24 m) (fun h => hm (by rw [← h, pi24_pi24]))
          (by rcases hm' with rfl | rfl | rfl <;> decide)
        simpa [pi24_pi24, sig24_three] using this)
      (by rcases hw with rfl | rfl | rfl <;> exact hoff))

theorem q45_J0_exp_end_ds_gt_sym (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) (s t : ℝ)
    (hs0 : 0 < s) (ht : 0 < t) (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 5 - x 0) + t • (x 4 - x 0)) (hs : 1 < s)
    (hN5 : 0 < ⟪F.N 5, x 3 - x 5⟫)
    (hU : UniLex (x ∘ pi24) (x 3 - x 5) (x 5 - x 0) ∨ DSany (x ∘ pi24) (x 3 - x 5) (x 5 - x 0))
    (hgen : ∀ i j : ZMod 5, i ≠ j →
      ⟪rimJ0 (x ∘ pi24) i - rimJ0 (x ∘ pi24) j, x 3 - x 5⟫ ≠ 0 ∨
      ⟪rimJ0 (x ∘ pi24) i - rimJ0 (x ∘ pi24) j, x 5 - x 0⟫ ≠ 0)
    (w : Fin 7) (hw : w = 1 ∨ w = 6 ∨ w = 2)
    (hmin : ∀ m : Fin 7, m ≠ w → (m = 1 ∨ m = 6 ∨ m = 2) → F.f 3 (x w) < F.f 3 (x m))
    (hoff : ⟪F.N 3, cross (x 4 - x 5) (x w - x 5)⟫ ≠ 0 ∨ ⟪x w - x 5, x 4 - x 5⟫ < 0 ∨
      ⟪x w - x 4, x 5 - x 4⟫ < 0) :
    FaceChordView F 3 :=
  faceChordView_sym F (t := 3)
    (q45_J0_exp_end_ds_gt (x := x ∘ pi24) (sym24 F) s t hs0 ht hst hdecomp hs hN5 hU hgen
      (pi24 w) (by rcases hw with rfl | rfl | rfl <;> decide)
      (fun m hm hm' => by
        have := hmin (pi24 m) (fun h => hm (by rw [← h, pi24_pi24]))
          (by rcases hm' with rfl | rfl | rfl <;> decide)
        simpa [pi24_pi24, sig24_three] using this)
      (by rcases hw with rfl | rfl | rfl <;> exact hoff))

theorem rj0h_Kminus_e5_sym (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x)
    (ha5 : ⟪F.N 5, x 4 - x 0⟫ < 0)
    (s t : ℝ) (hs0 : 0 < s) (ht : 0 < t) (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 5 - x 0) + t • (x 4 - x 0))
    (hk : 0 < det3 (x 4 - x 2) (x 6 - x 2) (x 5 - x 2) * det3 (x 0 - x 1) (x 6 - x 1) (x 2 - x 1))
    (hs : s ≤ 1)
    (h2lo : min ⟪x 5, x 4 - x 0⟫ ⟪x 6, x 4 - x 0⟫ < max ⟪x 2, x 4 - x 0⟫ ⟪x 4, x 4 - x 0⟫)
    (hS2 : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 2) (x 5) (x 4) (x 6) i - quad (x 2) (x 5) (x 4) (x 6) j, x 4 - x 0⟫ ≠ 0 ∨
      ⟪quad (x 2) (x 5) (x 4) (x 6) i - quad (x 2) (x 5) (x 4) (x 6) j, x 5 - x 0⟫ ≠ 0)
    (hS3 : F.f 3 (x 6) ≠ F.f 3 (x 2))
    (hS4 : ⟪F.N 3, cross (x 4 - x 5) (x (if F.f 3 (x 6) < F.f 3 (x 2) then 6 else 2) - x 5)⟫ ≠ 0 ∨
           ⟪x (if F.f 3 (x 6) < F.f 3 (x 2) then 6 else 2) - x 5, x 4 - x 5⟫ < 0 ∨
           ⟪x (if F.f 3 (x 6) < F.f 3 (x 2) then 6 else 2) - x 4, x 5 - x 4⟫ < 0) :
    FaceChordView F 3 :=
  faceChordView_sym F (t := 3)
    (rj0h_Kminus_e5 (x := x ∘ pi24) (sym24 F) ha5 s t hs0 ht hst hdecomp hk hs h2lo hS2 hS3
      (by
        have hs4 := hS4
        dsimp [sym24, pi24, sig24]
        by_cases hlt : F.f 3 (x 6) < F.f 3 (x 2)
        · simp only [hlt, ite_true] at hs4 ⊢
          exact hs4
        · simp only [hlt, ite_false] at hs4 ⊢
          exact hs4))

theorem rj0h_Kminus_e34_sym (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x)
    (ha34 : ⟪F.N 5, x 3 - x 5⟫ < 0)
    (s t : ℝ) (hs0 : 0 < s) (ht : 0 < t) (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 5 - x 0) + t • (x 4 - x 0))
    (hk : 0 < det3 (x 4 - x 2) (x 6 - x 2) (x 5 - x 2) * det3 (x 0 - x 1) (x 6 - x 1) (x 2 - x 1))
    (hs : 1 < s)
    (h2lo : min ⟪x 5, x 3 - x 5⟫ ⟪x 6, x 3 - x 5⟫ < max ⟪x 2, x 3 - x 5⟫ ⟪x 4, x 3 - x 5⟫)
    (hS2 : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 2) (x 5) (x 4) (x 6) i - quad (x 2) (x 5) (x 4) (x 6) j, x 3 - x 5⟫ ≠ 0 ∨
      ⟪quad (x 2) (x 5) (x 4) (x 6) i - quad (x 2) (x 5) (x 4) (x 6) j, x 5 - x 0⟫ ≠ 0)
    (hS3 : F.f 3 (x 6) ≠ F.f 3 (x 2))
    (hS4 : ⟪F.N 3, cross (x 4 - x 5) (x (if F.f 3 (x 6) < F.f 3 (x 2) then 6 else 2) - x 5)⟫ ≠ 0 ∨
           ⟪x (if F.f 3 (x 6) < F.f 3 (x 2) then 6 else 2) - x 5, x 4 - x 5⟫ < 0 ∨
           ⟪x (if F.f 3 (x 6) < F.f 3 (x 2) then 6 else 2) - x 4, x 5 - x 4⟫ < 0) :
    FaceChordView F 3 :=
  faceChordView_sym F (t := 3)
    (rj0h_Kminus_e34 (x := x ∘ pi24) (sym24 F) ha34 s t hs0 ht hst hdecomp hk hs h2lo hS2 hS3
      (by
        have hs4 := hS4
        dsimp [sym24, pi24, sig24]
        by_cases hlt : F.f 3 (x 6) < F.f 3 (x 2)
        · simp only [hlt, ite_true] at hs4 ⊢
          exact hs4
        · simp only [hlt, ite_false] at hs4 ⊢
          exact hs4))

end Minimality.T24.Sym

