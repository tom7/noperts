module

public import Minimality.Type16ArcA

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace H16A
open Minimality.H21 Minimality.H16U Minimality.V2

variable {x : Fin 7 → ℝ³}

def h16a_c1 : ZMod 5 → Fin 7 := ![5, 2, 0, 6, 1]
def h16a_ea1 : ZMod 5 → Fin 8 := ![7, 2, 4, 6, 5]
def h16a_eb1 : ZMod 5 → Fin 8 := ![0, 0, 3, 1, 1]
noncomputable def h16a_u1 (T : Type16 x) : ℝ³ :=
  h16a_u (x 1 - x 0) (x 4 - x 3)
    (x 0 - x 6) (cross (x 0 - x 2) (x 5 - x 2))
def H16AL1 (T : Type16 x) : Prop := H16ALeaf T h16a_c1 h16a_ea1 h16a_eb1 (h16a_u1 T)
theorem h16a_L1 (T : Type16 x) (h : H16AL1 T) : IsRupert (univ.image x) :=
  h16a_leaf_gen T (by norm_num) h16a_c1 (by decide) h16a_ea1 h16a_eb1 _
    (by decide) (by decide) (by decide) h
theorem h16a_L1s (T : Type16 x) (h : H16AL1 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a_L1 T.sigma h)

def h16a_c2 : ZMod 5 → Fin 7 := ![6, 0, 2, 4, 1]
def h16a_ea2 : ZMod 5 → Fin 8 := ![4, 2, 2, 6, 6]
def h16a_eb2 : ZMod 5 → Fin 8 := ![3, 0, 7, 5, 1]
noncomputable def h16a_u2 (T : Type16 x) : ℝ³ :=
  h16a_u (x 5 - x 3) (T.fN 4)
    (cross (x 4 - x 2) (x 5 - x 2)) (x 1 - x 6)
def H16AL2 (T : Type16 x) : Prop := H16ALeaf T h16a_c2 h16a_ea2 h16a_eb2 (h16a_u2 T)
theorem h16a_L2 (T : Type16 x) (h : H16AL2 T) : IsRupert (univ.image x) :=
  h16a_leaf_gen T (by norm_num) h16a_c2 (by decide) h16a_ea2 h16a_eb2 _
    (by decide) (by decide) (by decide) h
theorem h16a_L2s (T : Type16 x) (h : H16AL2 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a_L2 T.sigma h)

def h16a_c3 : ZMod 5 → Fin 7 := ![0, 2, 5, 1, 6]
def h16a_ea3 : ZMod 5 → Fin 8 := ![2, 7, 5, 6, 4]
def h16a_eb3 : ZMod 5 → Fin 8 := ![0, 0, 1, 1, 3]
noncomputable def h16a_u3 (T : Type16 x) : ℝ³ :=
  h16a_u (x 1 - x 0) (x 4 - x 3)
    (x 0 - x 6) (x 1 - x 6)
def H16AL3 (T : Type16 x) : Prop := H16ALeaf T h16a_c3 h16a_ea3 h16a_eb3 (h16a_u3 T)
theorem h16a_L3 (T : Type16 x) (h : H16AL3 T) : IsRupert (univ.image x) :=
  h16a_leaf_gen T (by norm_num) h16a_c3 (by decide) h16a_ea3 h16a_eb3 _
    (by decide) (by decide) (by decide) h
theorem h16a_L3s (T : Type16 x) (h : H16AL3 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a_L3 T.sigma h)

def h16a_c4 : ZMod 4 → Fin 7 := ![5, 4, 0, 3]
def h16a_ea4 : ZMod 4 → Fin 8 := ![5, 4, 3, 1]
def h16a_eb4 : ZMod 4 → Fin 8 := ![7, 2, 0, 0]
noncomputable def h16a_u4 (T : Type16 x) : ℝ³ :=
  h16a_u (x 2 - x 1) (cross (T.fN 2) (T.fN 5))
    (x 4 - x 5) (cross (x 4 - x 5) (x 2 - x 5))
def H16AL4 (T : Type16 x) : Prop := H16ALeaf T h16a_c4 h16a_ea4 h16a_eb4 (h16a_u4 T)
theorem h16a_L4 (T : Type16 x) (h : H16AL4 T) : IsRupert (univ.image x) :=
  h16a_leaf_gen T (by norm_num) h16a_c4 (by decide) h16a_ea4 h16a_eb4 _
    (by decide) (by decide) (by decide) h
theorem h16a_L4s (T : Type16 x) (h : H16AL4 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a_L4 T.sigma h)

def h16a_c5 : ZMod 4 → Fin 7 := ![5, 4, 0, 3]
def h16a_ea5 : ZMod 4 → Fin 8 := ![5, 4, 3, 1]
def h16a_eb5 : ZMod 4 → Fin 8 := ![7, 2, 0, 0]
noncomputable def h16a_u5 (T : Type16 x) : ℝ³ :=
  h16a_u (x 2 - x 1) (cross (T.fN 2) (T.fN 5))
    (cross (x 4 - x 5) (x 1 - x 5)) (cross (x 0 - x 4) (x 6 - x 4))
def H16AL5 (T : Type16 x) : Prop := H16ALeaf T h16a_c5 h16a_ea5 h16a_eb5 (h16a_u5 T)
theorem h16a_L5 (T : Type16 x) (h : H16AL5 T) : IsRupert (univ.image x) :=
  h16a_leaf_gen T (by norm_num) h16a_c5 (by decide) h16a_ea5 h16a_eb5 _
    (by decide) (by decide) (by decide) h
theorem h16a_L5s (T : Type16 x) (h : H16AL5 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a_L5 T.sigma h)

def h16a_c6 : ZMod 5 → Fin 7 := ![0, 2, 5, 1, 6]
def h16a_ea6 : ZMod 5 → Fin 8 := ![2, 7, 5, 6, 4]
def h16a_eb6 : ZMod 5 → Fin 8 := ![0, 0, 1, 1, 3]
noncomputable def h16a_u6 (T : Type16 x) : ℝ³ :=
  h16a_u (x 1 - x 0) (x 4 - x 3)
    (cross (x 2 - x 0) (x 4 - x 0)) (x 5 - x 2)
def H16AL6 (T : Type16 x) : Prop := H16ALeaf T h16a_c6 h16a_ea6 h16a_eb6 (h16a_u6 T)
theorem h16a_L6 (T : Type16 x) (h : H16AL6 T) : IsRupert (univ.image x) :=
  h16a_leaf_gen T (by norm_num) h16a_c6 (by decide) h16a_ea6 h16a_eb6 _
    (by decide) (by decide) (by decide) h
theorem h16a_L6s (T : Type16 x) (h : H16AL6 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a_L6 T.sigma h)

def h16a_c7 : ZMod 4 → Fin 7 := ![4, 5, 3, 0]
def h16a_ea7 : ZMod 4 → Fin 8 := ![7, 0, 0, 2]
def h16a_eb7 : ZMod 4 → Fin 8 := ![5, 1, 3, 4]
noncomputable def h16a_u7 (T : Type16 x) : ℝ³ :=
  h16a_u (x 2 - x 1) (cross (T.fN 2) (T.fN 5))
    (cross (x 4 - x 0) (x 6 - x 0)) (cross (x 3 - x 5) (x 1 - x 5))
def H16AL7 (T : Type16 x) : Prop := H16ALeaf T h16a_c7 h16a_ea7 h16a_eb7 (h16a_u7 T)
theorem h16a_L7 (T : Type16 x) (h : H16AL7 T) : IsRupert (univ.image x) :=
  h16a_leaf_gen T (by norm_num) h16a_c7 (by decide) h16a_ea7 h16a_eb7 _
    (by decide) (by decide) (by decide) h
theorem h16a_L7s (T : Type16 x) (h : H16AL7 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a_L7 T.sigma h)

def h16a_c8 : ZMod 4 → Fin 7 := ![5, 4, 0, 3]
def h16a_ea8 : ZMod 4 → Fin 8 := ![7, 2, 0, 0]
def h16a_eb8 : ZMod 4 → Fin 8 := ![5, 4, 3, 1]
noncomputable def h16a_u8 (T : Type16 x) : ℝ³ :=
  h16a_u (x 6 - x 0) (cross (T.fN 2) (T.fN 6))
    (x 3 - x 5) (cross (x 5 - x 3) (x 6 - x 3))
def H16AL8 (T : Type16 x) : Prop := H16ALeaf T h16a_c8 h16a_ea8 h16a_eb8 (h16a_u8 T)
theorem h16a_L8 (T : Type16 x) (h : H16AL8 T) : IsRupert (univ.image x) :=
  h16a_leaf_gen T (by norm_num) h16a_c8 (by decide) h16a_ea8 h16a_eb8 _
    (by decide) (by decide) (by decide) h
theorem h16a_L8s (T : Type16 x) (h : H16AL8 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a_L8 T.sigma h)

def h16a_c9 : ZMod 4 → Fin 7 := ![3, 0, 4, 5]
def h16a_ea9 : ZMod 4 → Fin 8 := ![0, 2, 7, 0]
def h16a_eb9 : ZMod 4 → Fin 8 := ![3, 4, 5, 1]
noncomputable def h16a_u9 (T : Type16 x) : ℝ³ :=
  h16a_u (x 2 - x 1) (cross (T.fN 2) (T.fN 5))
    (cross (x 5 - x 4) (x 1 - x 4)) (cross (x 4 - x 0) (x 6 - x 0))
def H16AL9 (T : Type16 x) : Prop := H16ALeaf T h16a_c9 h16a_ea9 h16a_eb9 (h16a_u9 T)
theorem h16a_L9 (T : Type16 x) (h : H16AL9 T) : IsRupert (univ.image x) :=
  h16a_leaf_gen T (by norm_num) h16a_c9 (by decide) h16a_ea9 h16a_eb9 _
    (by decide) (by decide) (by decide) h
theorem h16a_L9s (T : Type16 x) (h : H16AL9 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a_L9 T.sigma h)

def h16a_c10 : ZMod 4 → Fin 7 := ![0, 4, 5, 3]
def h16a_ea10 : ZMod 4 → Fin 8 := ![2, 7, 0, 0]
def h16a_eb10 : ZMod 4 → Fin 8 := ![4, 5, 1, 3]
noncomputable def h16a_u10 (T : Type16 x) : ℝ³ :=
  h16a_u (x 2 - x 1) (cross (T.fN 2) (T.fN 5))
    (cross (x 4 - x 0) (x 6 - x 0)) (cross (x 5 - x 4) (x 1 - x 4))
def H16AL10 (T : Type16 x) : Prop := H16ALeaf T h16a_c10 h16a_ea10 h16a_eb10 (h16a_u10 T)
theorem h16a_L10 (T : Type16 x) (h : H16AL10 T) : IsRupert (univ.image x) :=
  h16a_leaf_gen T (by norm_num) h16a_c10 (by decide) h16a_ea10 h16a_eb10 _
    (by decide) (by decide) (by decide) h
theorem h16a_L10s (T : Type16 x) (h : H16AL10 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a_L10 T.sigma h)

def h16a_c11 : ZMod 4 → Fin 7 := ![5, 4, 0, 3]
def h16a_ea11 : ZMod 4 → Fin 8 := ![7, 2, 0, 0]
def h16a_eb11 : ZMod 4 → Fin 8 := ![5, 4, 3, 1]
noncomputable def h16a_u11 (T : Type16 x) : ℝ³ :=
  h16a_u (x 6 - x 0) (cross (T.fN 2) (T.fN 6))
    (cross (x 4 - x 5) (x 1 - x 5)) (cross (x 4 - x 5) (x 2 - x 5))
def H16AL11 (T : Type16 x) : Prop := H16ALeaf T h16a_c11 h16a_ea11 h16a_eb11 (h16a_u11 T)
theorem h16a_L11 (T : Type16 x) (h : H16AL11 T) : IsRupert (univ.image x) :=
  h16a_leaf_gen T (by norm_num) h16a_c11 (by decide) h16a_ea11 h16a_eb11 _
    (by decide) (by decide) (by decide) h
theorem h16a_L11s (T : Type16 x) (h : H16AL11 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a_L11 T.sigma h)

def h16a_c12 : ZMod 5 → Fin 7 := ![1, 5, 2, 0, 6]
def h16a_ea12 : ZMod 5 → Fin 8 := ![5, 7, 2, 4, 6]
def h16a_eb12 : ZMod 5 → Fin 8 := ![1, 0, 0, 3, 1]
noncomputable def h16a_u12 (T : Type16 x) : ℝ³ :=
  h16a_u (x 1 - x 0) (x 4 - x 0)
    (x 5 - x 1) (x 5 - x 2)
def H16AL12 (T : Type16 x) : Prop := H16ALeaf T h16a_c12 h16a_ea12 h16a_eb12 (h16a_u12 T)
theorem h16a_L12 (T : Type16 x) (h : H16AL12 T) : IsRupert (univ.image x) :=
  h16a_leaf_gen T (by norm_num) h16a_c12 (by decide) h16a_ea12 h16a_eb12 _
    (by decide) (by decide) (by decide) h
theorem h16a_L12s (T : Type16 x) (h : H16AL12 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a_L12 T.sigma h)

def h16a_c13 : ZMod 4 → Fin 7 := ![5, 4, 0, 3]
def h16a_ea13 : ZMod 4 → Fin 8 := ![7, 2, 0, 0]
def h16a_eb13 : ZMod 4 → Fin 8 := ![5, 4, 3, 1]
noncomputable def h16a_u13 (T : Type16 x) : ℝ³ :=
  h16a_u (x 6 - x 0) (cross (T.fN 2) (T.fN 6))
    (x 3 - x 5) (cross (x 4 - x 5) (x 2 - x 5))
def H16AL13 (T : Type16 x) : Prop := H16ALeaf T h16a_c13 h16a_ea13 h16a_eb13 (h16a_u13 T)
theorem h16a_L13 (T : Type16 x) (h : H16AL13 T) : IsRupert (univ.image x) :=
  h16a_leaf_gen T (by norm_num) h16a_c13 (by decide) h16a_ea13 h16a_eb13 _
    (by decide) (by decide) (by decide) h
theorem h16a_L13s (T : Type16 x) (h : H16AL13 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a_L13 T.sigma h)

def h16a_c14 : ZMod 4 → Fin 7 := ![4, 0, 3, 5]
def h16a_ea14 : ZMod 4 → Fin 8 := ![4, 3, 1, 5]
def h16a_eb14 : ZMod 4 → Fin 8 := ![2, 0, 0, 7]
noncomputable def h16a_u14 (T : Type16 x) : ℝ³ :=
  h16a_u (x 2 - x 1) (cross (T.fN 2) (T.fN 5))
    (cross (x 5 - x 3) (x 1 - x 3)) (cross (x 0 - x 4) (x 6 - x 4))
def H16AL14 (T : Type16 x) : Prop := H16ALeaf T h16a_c14 h16a_ea14 h16a_eb14 (h16a_u14 T)
theorem h16a_L14 (T : Type16 x) (h : H16AL14 T) : IsRupert (univ.image x) :=
  h16a_leaf_gen T (by norm_num) h16a_c14 (by decide) h16a_ea14 h16a_eb14 _
    (by decide) (by decide) (by decide) h
theorem h16a_L14s (T : Type16 x) (h : H16AL14 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a_L14 T.sigma h)

def h16a_c15 : ZMod 5 → Fin 7 := ![0, 6, 1, 5, 2]
def h16a_ea15 : ZMod 5 → Fin 8 := ![3, 1, 1, 0, 0]
def h16a_eb15 : ZMod 5 → Fin 8 := ![4, 6, 5, 7, 2]
noncomputable def h16a_u15 (T : Type16 x) : ℝ³ :=
  h16a_u (x 1 - x 0) (x 4 - x 0)
    (x 2 - x 5) (cross (x 5 - x 1) (x 4 - x 1))
def H16AL15 (T : Type16 x) : Prop := H16ALeaf T h16a_c15 h16a_ea15 h16a_eb15 (h16a_u15 T)
theorem h16a_L15 (T : Type16 x) (h : H16AL15 T) : IsRupert (univ.image x) :=
  h16a_leaf_gen T (by norm_num) h16a_c15 (by decide) h16a_ea15 h16a_eb15 _
    (by decide) (by decide) (by decide) h
theorem h16a_L15s (T : Type16 x) (h : H16AL15 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a_L15 T.sigma h)

def h16a_c16 : ZMod 5 → Fin 7 := ![6, 0, 3, 5, 1]
def h16a_ea16 : ZMod 5 → Fin 8 := ![3, 3, 1, 1, 1]
def h16a_eb16 : ZMod 5 → Fin 8 := ![4, 0, 0, 5, 6]
noncomputable def h16a_u16 (T : Type16 x) : ℝ³ :=
  h16a_u (x 1 - x 0) (x 4 - x 0)
    (x 0 - x 6) (cross (x 6 - x 1) (x 4 - x 1))
def H16AL16 (T : Type16 x) : Prop := H16ALeaf T h16a_c16 h16a_ea16 h16a_eb16 (h16a_u16 T)
theorem h16a_L16 (T : Type16 x) (h : H16AL16 T) : IsRupert (univ.image x) :=
  h16a_leaf_gen T (by norm_num) h16a_c16 (by decide) h16a_ea16 h16a_eb16 _
    (by decide) (by decide) (by decide) h
theorem h16a_L16s (T : Type16 x) (h : H16AL16 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a_L16 T.sigma h)

def h16a_c17 : ZMod 4 → Fin 7 := ![4, 5, 3, 0]
def h16a_ea17 : ZMod 4 → Fin 8 := ![7, 0, 0, 2]
def h16a_eb17 : ZMod 4 → Fin 8 := ![5, 1, 3, 4]
noncomputable def h16a_u17 (T : Type16 x) : ℝ³ :=
  h16a_u (x 2 - x 1) (cross (T.fN 2) (T.fN 5))
    (x 3 - x 0) (cross (x 0 - x 3) (x 6 - x 3))
def H16AL17 (T : Type16 x) : Prop := H16ALeaf T h16a_c17 h16a_ea17 h16a_eb17 (h16a_u17 T)
theorem h16a_L17 (T : Type16 x) (h : H16AL17 T) : IsRupert (univ.image x) :=
  h16a_leaf_gen T (by norm_num) h16a_c17 (by decide) h16a_ea17 h16a_eb17 _
    (by decide) (by decide) (by decide) h
theorem h16a_L17s (T : Type16 x) (h : H16AL17 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a_L17 T.sigma h)

def h16a_c18 : ZMod 5 → Fin 7 := ![6, 4, 2, 5, 3]
def h16a_ea18 : ZMod 5 → Fin 8 := ![6, 7, 7, 1, 1]
def h16a_eb18 : ZMod 5 → Fin 8 := ![4, 2, 0, 0, 3]
noncomputable def h16a_u18 (T : Type16 x) : ℝ³ :=
  h16a_u (x 2 - x 0) (x 3 - x 0)
    (x 2 - x 4) (x 4 - x 6)
def H16AL18 (T : Type16 x) : Prop := H16ALeaf T h16a_c18 h16a_ea18 h16a_eb18 (h16a_u18 T)
theorem h16a_L18 (T : Type16 x) (h : H16AL18 T) : IsRupert (univ.image x) :=
  h16a_leaf_gen T (by norm_num) h16a_c18 (by decide) h16a_ea18 h16a_eb18 _
    (by decide) (by decide) (by decide) h
theorem h16a_L18s (T : Type16 x) (h : H16AL18 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a_L18 T.sigma h)

def h16a_c19 : ZMod 5 → Fin 7 := ![0, 4, 1, 5, 3]
def h16a_ea19 : ZMod 5 → Fin 8 := ![4, 6, 1, 1, 3]
def h16a_eb19 : ZMod 5 → Fin 8 := ![2, 5, 5, 0, 0]
noncomputable def h16a_u19 (T : Type16 x) : ℝ³ :=
  h16a_u (x 6 - x 2) (cross (T.fN 0) (T.fN 6))
    (x 0 - x 3) (x 0 - x 4)
def H16AL19 (T : Type16 x) : Prop := H16ALeaf T h16a_c19 h16a_ea19 h16a_eb19 (h16a_u19 T)
theorem h16a_L19 (T : Type16 x) (h : H16AL19 T) : IsRupert (univ.image x) :=
  h16a_leaf_gen T (by norm_num) h16a_c19 (by decide) h16a_ea19 h16a_eb19 _
    (by decide) (by decide) (by decide) h
theorem h16a_L19s (T : Type16 x) (h : H16AL19 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a_L19 T.sigma h)

def h16a_c20 : ZMod 5 → Fin 7 := ![4, 0, 3, 5, 1]
def h16a_ea20 : ZMod 5 → Fin 8 := ![4, 3, 1, 1, 6]
def h16a_eb20 : ZMod 5 → Fin 8 := ![2, 0, 0, 5, 5]
noncomputable def h16a_u20 (T : Type16 x) : ℝ³ :=
  h16a_u (x 6 - x 0) (cross (T.fN 2) (T.fN 6))
    (x 0 - x 3) (x 1 - x 4)
def H16AL20 (T : Type16 x) : Prop := H16ALeaf T h16a_c20 h16a_ea20 h16a_eb20 (h16a_u20 T)
theorem h16a_L20 (T : Type16 x) (h : H16AL20 T) : IsRupert (univ.image x) :=
  h16a_leaf_gen T (by norm_num) h16a_c20 (by decide) h16a_ea20 h16a_eb20 _
    (by decide) (by decide) (by decide) h
theorem h16a_L20s (T : Type16 x) (h : H16AL20 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a_L20 T.sigma h)

def h16a_c21 : ZMod 5 → Fin 7 := ![0, 4, 1, 5, 3]
def h16a_ea21 : ZMod 5 → Fin 8 := ![4, 6, 1, 1, 3]
def h16a_eb21 : ZMod 5 → Fin 8 := ![2, 5, 5, 0, 0]
noncomputable def h16a_u21 (T : Type16 x) : ℝ³ :=
  h16a_u (x 3 - x 1) (cross (T.fN 1) (T.fN 2))
    (x 4 - x 1) (x 0 - x 3)
def H16AL21 (T : Type16 x) : Prop := H16ALeaf T h16a_c21 h16a_ea21 h16a_eb21 (h16a_u21 T)
theorem h16a_L21 (T : Type16 x) (h : H16AL21 T) : IsRupert (univ.image x) :=
  h16a_leaf_gen T (by norm_num) h16a_c21 (by decide) h16a_ea21 h16a_eb21 _
    (by decide) (by decide) (by decide) h
theorem h16a_L21s (T : Type16 x) (h : H16AL21 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a_L21 T.sigma h)

def h16a_c22 : ZMod 5 → Fin 7 := ![1, 4, 2, 0, 6]
def h16a_ea22 : ZMod 5 → Fin 8 := ![6, 2, 2, 4, 6]
def h16a_eb22 : ZMod 5 → Fin 8 := ![5, 7, 0, 3, 1]
noncomputable def h16a_u22 (T : Type16 x) : ℝ³ :=
  h16a_u (x 1 - x 0) (x 4 - x 3)
    (cross (x 2 - x 4) (x 5 - x 4)) (x 2 - x 0)
def H16AL22 (T : Type16 x) : Prop := H16ALeaf T h16a_c22 h16a_ea22 h16a_eb22 (h16a_u22 T)
theorem h16a_L22 (T : Type16 x) (h : H16AL22 T) : IsRupert (univ.image x) :=
  h16a_leaf_gen T (by norm_num) h16a_c22 (by decide) h16a_ea22 h16a_eb22 _
    (by decide) (by decide) (by decide) h
theorem h16a_L22s (T : Type16 x) (h : H16AL22 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a_L22 T.sigma h)

def h16a_c23 : ZMod 5 → Fin 7 := ![4, 0, 3, 5, 1]
def h16a_ea23 : ZMod 5 → Fin 8 := ![2, 0, 0, 5, 5]
def h16a_eb23 : ZMod 5 → Fin 8 := ![4, 3, 1, 1, 6]
noncomputable def h16a_u23 (T : Type16 x) : ℝ³ :=
  h16a_u (x 6 - x 0) (cross (T.fN 2) (T.fN 6))
    (x 0 - x 3) (cross (x 1 - x 5) (x 6 - x 5))
def H16AL23 (T : Type16 x) : Prop := H16ALeaf T h16a_c23 h16a_ea23 h16a_eb23 (h16a_u23 T)
theorem h16a_L23 (T : Type16 x) (h : H16AL23 T) : IsRupert (univ.image x) :=
  h16a_leaf_gen T (by norm_num) h16a_c23 (by decide) h16a_ea23 h16a_eb23 _
    (by decide) (by decide) (by decide) h
theorem h16a_L23s (T : Type16 x) (h : H16AL23 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a_L23 T.sigma h)

def h16a_c24 : ZMod 5 → Fin 7 := ![3, 6, 4, 2, 5]
def h16a_ea24 : ZMod 5 → Fin 8 := ![1, 6, 7, 7, 1]
def h16a_eb24 : ZMod 5 → Fin 8 := ![3, 4, 2, 0, 0]
noncomputable def h16a_u24 (T : Type16 x) : ℝ³ :=
  h16a_u (x 1 - x 0) (x 4 - x 0)
    (x 2 - x 5) (cross (x 4 - x 6) (x 0 - x 6))
def H16AL24 (T : Type16 x) : Prop := H16ALeaf T h16a_c24 h16a_ea24 h16a_eb24 (h16a_u24 T)
theorem h16a_L24 (T : Type16 x) (h : H16AL24 T) : IsRupert (univ.image x) :=
  h16a_leaf_gen T (by norm_num) h16a_c24 (by decide) h16a_ea24 h16a_eb24 _
    (by decide) (by decide) (by decide) h
theorem h16a_L24s (T : Type16 x) (h : H16AL24 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a_L24 T.sigma h)

def h16a_c25 : ZMod 5 → Fin 7 := ![5, 1, 6, 0, 2]
def h16a_ea25 : ZMod 5 → Fin 8 := ![1, 1, 3, 0, 0]
def h16a_eb25 : ZMod 5 → Fin 8 := ![5, 6, 4, 2, 7]
noncomputable def h16a_u25 (T : Type16 x) : ℝ³ :=
  h16a_u (x 2 - x 0) (x 3 - x 0)
    (x 0 - x 2) (x 5 - x 2)
def H16AL25 (T : Type16 x) : Prop := H16ALeaf T h16a_c25 h16a_ea25 h16a_eb25 (h16a_u25 T)
theorem h16a_L25 (T : Type16 x) (h : H16AL25 T) : IsRupert (univ.image x) :=
  h16a_leaf_gen T (by norm_num) h16a_c25 (by decide) h16a_ea25 h16a_eb25 _
    (by decide) (by decide) (by decide) h
theorem h16a_L25s (T : Type16 x) (h : H16AL25 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a_L25 T.sigma h)

def H16AAny (T : Type16 x) : Prop :=
  H16AL1 T ∨ H16AL2 T ∨ H16AL3 T ∨ H16AL4 T ∨ H16AL5 T ∨ H16AL6 T ∨ H16AL7 T ∨ H16AL8 T ∨ H16AL9 T ∨ H16AL10 T ∨ H16AL11 T ∨ H16AL12 T ∨ H16AL13 T ∨ H16AL14 T ∨ H16AL15 T ∨ H16AL16 T ∨ H16AL17 T ∨ H16AL18 T ∨ H16AL19 T ∨ H16AL20 T ∨ H16AL21 T ∨ H16AL22 T ∨ H16AL23 T ∨ H16AL24 T ∨ H16AL25 T ∨ H16AL1 T.sigma ∨ H16AL2 T.sigma ∨ H16AL3 T.sigma ∨ H16AL4 T.sigma ∨ H16AL5 T.sigma ∨ H16AL6 T.sigma ∨ H16AL7 T.sigma ∨ H16AL8 T.sigma ∨ H16AL9 T.sigma ∨ H16AL10 T.sigma ∨ H16AL11 T.sigma ∨ H16AL12 T.sigma ∨ H16AL13 T.sigma ∨ H16AL14 T.sigma ∨ H16AL15 T.sigma ∨ H16AL16 T.sigma ∨ H16AL17 T.sigma ∨ H16AL18 T.sigma ∨ H16AL19 T.sigma ∨ H16AL20 T.sigma ∨ H16AL21 T.sigma ∨ H16AL22 T.sigma ∨ H16AL23 T.sigma ∨ H16AL24 T.sigma ∨ H16AL25 T.sigma

theorem h16a_any_isRupert (T : Type16 x) (h : H16AAny T) : IsRupert (univ.image x) := by
  unfold H16AAny at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact h16a_L1 T h
  · exact h16a_L2 T h
  · exact h16a_L3 T h
  · exact h16a_L4 T h
  · exact h16a_L5 T h
  · exact h16a_L6 T h
  · exact h16a_L7 T h
  · exact h16a_L8 T h
  · exact h16a_L9 T h
  · exact h16a_L10 T h
  · exact h16a_L11 T h
  · exact h16a_L12 T h
  · exact h16a_L13 T h
  · exact h16a_L14 T h
  · exact h16a_L15 T h
  · exact h16a_L16 T h
  · exact h16a_L17 T h
  · exact h16a_L18 T h
  · exact h16a_L19 T h
  · exact h16a_L20 T h
  · exact h16a_L21 T h
  · exact h16a_L22 T h
  · exact h16a_L23 T h
  · exact h16a_L24 T h
  · exact h16a_L25 T h
  · exact h16a_L1s T h
  · exact h16a_L2s T h
  · exact h16a_L3s T h
  · exact h16a_L4s T h
  · exact h16a_L5s T h
  · exact h16a_L6s T h
  · exact h16a_L7s T h
  · exact h16a_L8s T h
  · exact h16a_L9s T h
  · exact h16a_L10s T h
  · exact h16a_L11s T h
  · exact h16a_L12s T h
  · exact h16a_L13s T h
  · exact h16a_L14s T h
  · exact h16a_L15s T h
  · exact h16a_L16s T h
  · exact h16a_L17s T h
  · exact h16a_L18s T h
  · exact h16a_L19s T h
  · exact h16a_L20s T h
  · exact h16a_L21s T h
  · exact h16a_L22s T h
  · exact h16a_L23s T h
  · exact h16a_L24s T h
  · exact h16a_L25s T h

/-- The residual of the arc cells: the residual `H16VResid` of the lex-cell rule, and no arc leaf
(R5 version `H16ALn`, or its `σ`-image for R3) applies. -/
def H16ArcResid (T : Type16 x) : Prop := H16VResid T ∧ ¬ H16AAny T

theorem h16a_rule_isRupert (T : Type16 x) (h : ¬ H16ArcResid T) : IsRupert (univ.image x) := by
  by_cases hv : H16VResid T
  · have : H16AAny T := by
      by_contra hn; exact h ⟨hv, hn⟩
    exact h16a_any_isRupert T this
  · exact h16v_rule_isRupert T hv

/-- Contradiction form for the skeleton. -/
theorem h16a_rule_false (hN : IsNopert (Finset.univ.image x)) (T : Type16 x)
    (h : ¬ H16ArcResid T) : False :=
  hN.2 (h16a_rule_isRupert T h)

end H16A
end Minimality
