module

public import Minimality.Type16Arc2A

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

def H16A2L1 (T : Type16 x) : Prop := H16A2Leaf T h16a_c1 h16a_ea1 h16a_eb1 (h16a_u1 T)
theorem h16a2_L1 (T : Type16 x) (h : H16A2L1 T) : IsRupert (univ.image x) :=
  h16a2_leaf_gen T (by norm_num) h16a_c1 (by decide) h16a_ea1 h16a_eb1 _
    (by decide) (by decide) (by decide) h
theorem h16a2_L1s (T : Type16 x) (h : H16A2L1 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a2_L1 T.sigma h)
theorem h16a2_L1_of (T : Type16 x) (h : H16AL1 T) : H16A2L1 T := h16a2_leaf_of T _ _ _ _ h

def H16A2L2 (T : Type16 x) : Prop := H16A2Leaf T h16a_c2 h16a_ea2 h16a_eb2 (h16a_u2 T)
theorem h16a2_L2 (T : Type16 x) (h : H16A2L2 T) : IsRupert (univ.image x) :=
  h16a2_leaf_gen T (by norm_num) h16a_c2 (by decide) h16a_ea2 h16a_eb2 _
    (by decide) (by decide) (by decide) h
theorem h16a2_L2s (T : Type16 x) (h : H16A2L2 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a2_L2 T.sigma h)
theorem h16a2_L2_of (T : Type16 x) (h : H16AL2 T) : H16A2L2 T := h16a2_leaf_of T _ _ _ _ h

def H16A2L3 (T : Type16 x) : Prop := H16A2Leaf T h16a_c3 h16a_ea3 h16a_eb3 (h16a_u3 T)
theorem h16a2_L3 (T : Type16 x) (h : H16A2L3 T) : IsRupert (univ.image x) :=
  h16a2_leaf_gen T (by norm_num) h16a_c3 (by decide) h16a_ea3 h16a_eb3 _
    (by decide) (by decide) (by decide) h
theorem h16a2_L3s (T : Type16 x) (h : H16A2L3 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a2_L3 T.sigma h)
theorem h16a2_L3_of (T : Type16 x) (h : H16AL3 T) : H16A2L3 T := h16a2_leaf_of T _ _ _ _ h

def H16A2L4 (T : Type16 x) : Prop := H16A2Leaf T h16a_c4 h16a_ea4 h16a_eb4 (h16a_u4 T)
theorem h16a2_L4 (T : Type16 x) (h : H16A2L4 T) : IsRupert (univ.image x) :=
  h16a2_leaf_gen T (by norm_num) h16a_c4 (by decide) h16a_ea4 h16a_eb4 _
    (by decide) (by decide) (by decide) h
theorem h16a2_L4s (T : Type16 x) (h : H16A2L4 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a2_L4 T.sigma h)
theorem h16a2_L4_of (T : Type16 x) (h : H16AL4 T) : H16A2L4 T := h16a2_leaf_of T _ _ _ _ h

def H16A2L5 (T : Type16 x) : Prop := H16A2Leaf T h16a_c5 h16a_ea5 h16a_eb5 (h16a_u5 T)
theorem h16a2_L5 (T : Type16 x) (h : H16A2L5 T) : IsRupert (univ.image x) :=
  h16a2_leaf_gen T (by norm_num) h16a_c5 (by decide) h16a_ea5 h16a_eb5 _
    (by decide) (by decide) (by decide) h
theorem h16a2_L5s (T : Type16 x) (h : H16A2L5 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a2_L5 T.sigma h)
theorem h16a2_L5_of (T : Type16 x) (h : H16AL5 T) : H16A2L5 T := h16a2_leaf_of T _ _ _ _ h

def H16A2L6 (T : Type16 x) : Prop := H16A2Leaf T h16a_c6 h16a_ea6 h16a_eb6 (h16a_u6 T)
theorem h16a2_L6 (T : Type16 x) (h : H16A2L6 T) : IsRupert (univ.image x) :=
  h16a2_leaf_gen T (by norm_num) h16a_c6 (by decide) h16a_ea6 h16a_eb6 _
    (by decide) (by decide) (by decide) h
theorem h16a2_L6s (T : Type16 x) (h : H16A2L6 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a2_L6 T.sigma h)
theorem h16a2_L6_of (T : Type16 x) (h : H16AL6 T) : H16A2L6 T := h16a2_leaf_of T _ _ _ _ h

def H16A2L7 (T : Type16 x) : Prop := H16A2Leaf T h16a_c7 h16a_ea7 h16a_eb7 (h16a_u7 T)
theorem h16a2_L7 (T : Type16 x) (h : H16A2L7 T) : IsRupert (univ.image x) :=
  h16a2_leaf_gen T (by norm_num) h16a_c7 (by decide) h16a_ea7 h16a_eb7 _
    (by decide) (by decide) (by decide) h
theorem h16a2_L7s (T : Type16 x) (h : H16A2L7 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a2_L7 T.sigma h)
theorem h16a2_L7_of (T : Type16 x) (h : H16AL7 T) : H16A2L7 T := h16a2_leaf_of T _ _ _ _ h

def H16A2L8 (T : Type16 x) : Prop := H16A2Leaf T h16a_c8 h16a_ea8 h16a_eb8 (h16a_u8 T)
theorem h16a2_L8 (T : Type16 x) (h : H16A2L8 T) : IsRupert (univ.image x) :=
  h16a2_leaf_gen T (by norm_num) h16a_c8 (by decide) h16a_ea8 h16a_eb8 _
    (by decide) (by decide) (by decide) h
theorem h16a2_L8s (T : Type16 x) (h : H16A2L8 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a2_L8 T.sigma h)
theorem h16a2_L8_of (T : Type16 x) (h : H16AL8 T) : H16A2L8 T := h16a2_leaf_of T _ _ _ _ h

def H16A2L9 (T : Type16 x) : Prop := H16A2Leaf T h16a_c9 h16a_ea9 h16a_eb9 (h16a_u9 T)
theorem h16a2_L9 (T : Type16 x) (h : H16A2L9 T) : IsRupert (univ.image x) :=
  h16a2_leaf_gen T (by norm_num) h16a_c9 (by decide) h16a_ea9 h16a_eb9 _
    (by decide) (by decide) (by decide) h
theorem h16a2_L9s (T : Type16 x) (h : H16A2L9 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a2_L9 T.sigma h)
theorem h16a2_L9_of (T : Type16 x) (h : H16AL9 T) : H16A2L9 T := h16a2_leaf_of T _ _ _ _ h

def H16A2L10 (T : Type16 x) : Prop := H16A2Leaf T h16a_c10 h16a_ea10 h16a_eb10 (h16a_u10 T)
theorem h16a2_L10 (T : Type16 x) (h : H16A2L10 T) : IsRupert (univ.image x) :=
  h16a2_leaf_gen T (by norm_num) h16a_c10 (by decide) h16a_ea10 h16a_eb10 _
    (by decide) (by decide) (by decide) h
theorem h16a2_L10s (T : Type16 x) (h : H16A2L10 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a2_L10 T.sigma h)
theorem h16a2_L10_of (T : Type16 x) (h : H16AL10 T) : H16A2L10 T := h16a2_leaf_of T _ _ _ _ h

def H16A2L11 (T : Type16 x) : Prop := H16A2Leaf T h16a_c11 h16a_ea11 h16a_eb11 (h16a_u11 T)
theorem h16a2_L11 (T : Type16 x) (h : H16A2L11 T) : IsRupert (univ.image x) :=
  h16a2_leaf_gen T (by norm_num) h16a_c11 (by decide) h16a_ea11 h16a_eb11 _
    (by decide) (by decide) (by decide) h
theorem h16a2_L11s (T : Type16 x) (h : H16A2L11 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a2_L11 T.sigma h)
theorem h16a2_L11_of (T : Type16 x) (h : H16AL11 T) : H16A2L11 T := h16a2_leaf_of T _ _ _ _ h

def H16A2L12 (T : Type16 x) : Prop := H16A2Leaf T h16a_c12 h16a_ea12 h16a_eb12 (h16a_u12 T)
theorem h16a2_L12 (T : Type16 x) (h : H16A2L12 T) : IsRupert (univ.image x) :=
  h16a2_leaf_gen T (by norm_num) h16a_c12 (by decide) h16a_ea12 h16a_eb12 _
    (by decide) (by decide) (by decide) h
theorem h16a2_L12s (T : Type16 x) (h : H16A2L12 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a2_L12 T.sigma h)
theorem h16a2_L12_of (T : Type16 x) (h : H16AL12 T) : H16A2L12 T := h16a2_leaf_of T _ _ _ _ h

def H16A2L13 (T : Type16 x) : Prop := H16A2Leaf T h16a_c13 h16a_ea13 h16a_eb13 (h16a_u13 T)
theorem h16a2_L13 (T : Type16 x) (h : H16A2L13 T) : IsRupert (univ.image x) :=
  h16a2_leaf_gen T (by norm_num) h16a_c13 (by decide) h16a_ea13 h16a_eb13 _
    (by decide) (by decide) (by decide) h
theorem h16a2_L13s (T : Type16 x) (h : H16A2L13 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a2_L13 T.sigma h)
theorem h16a2_L13_of (T : Type16 x) (h : H16AL13 T) : H16A2L13 T := h16a2_leaf_of T _ _ _ _ h

def H16A2L14 (T : Type16 x) : Prop := H16A2Leaf T h16a_c14 h16a_ea14 h16a_eb14 (h16a_u14 T)
theorem h16a2_L14 (T : Type16 x) (h : H16A2L14 T) : IsRupert (univ.image x) :=
  h16a2_leaf_gen T (by norm_num) h16a_c14 (by decide) h16a_ea14 h16a_eb14 _
    (by decide) (by decide) (by decide) h
theorem h16a2_L14s (T : Type16 x) (h : H16A2L14 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a2_L14 T.sigma h)
theorem h16a2_L14_of (T : Type16 x) (h : H16AL14 T) : H16A2L14 T := h16a2_leaf_of T _ _ _ _ h

def H16A2L15 (T : Type16 x) : Prop := H16A2Leaf T h16a_c15 h16a_ea15 h16a_eb15 (h16a_u15 T)
theorem h16a2_L15 (T : Type16 x) (h : H16A2L15 T) : IsRupert (univ.image x) :=
  h16a2_leaf_gen T (by norm_num) h16a_c15 (by decide) h16a_ea15 h16a_eb15 _
    (by decide) (by decide) (by decide) h
theorem h16a2_L15s (T : Type16 x) (h : H16A2L15 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a2_L15 T.sigma h)
theorem h16a2_L15_of (T : Type16 x) (h : H16AL15 T) : H16A2L15 T := h16a2_leaf_of T _ _ _ _ h

def H16A2L16 (T : Type16 x) : Prop := H16A2Leaf T h16a_c16 h16a_ea16 h16a_eb16 (h16a_u16 T)
theorem h16a2_L16 (T : Type16 x) (h : H16A2L16 T) : IsRupert (univ.image x) :=
  h16a2_leaf_gen T (by norm_num) h16a_c16 (by decide) h16a_ea16 h16a_eb16 _
    (by decide) (by decide) (by decide) h
theorem h16a2_L16s (T : Type16 x) (h : H16A2L16 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a2_L16 T.sigma h)
theorem h16a2_L16_of (T : Type16 x) (h : H16AL16 T) : H16A2L16 T := h16a2_leaf_of T _ _ _ _ h

def H16A2L17 (T : Type16 x) : Prop := H16A2Leaf T h16a_c17 h16a_ea17 h16a_eb17 (h16a_u17 T)
theorem h16a2_L17 (T : Type16 x) (h : H16A2L17 T) : IsRupert (univ.image x) :=
  h16a2_leaf_gen T (by norm_num) h16a_c17 (by decide) h16a_ea17 h16a_eb17 _
    (by decide) (by decide) (by decide) h
theorem h16a2_L17s (T : Type16 x) (h : H16A2L17 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a2_L17 T.sigma h)
theorem h16a2_L17_of (T : Type16 x) (h : H16AL17 T) : H16A2L17 T := h16a2_leaf_of T _ _ _ _ h

def H16A2L18 (T : Type16 x) : Prop := H16A2Leaf T h16a_c18 h16a_ea18 h16a_eb18 (h16a_u18 T)
theorem h16a2_L18 (T : Type16 x) (h : H16A2L18 T) : IsRupert (univ.image x) :=
  h16a2_leaf_gen T (by norm_num) h16a_c18 (by decide) h16a_ea18 h16a_eb18 _
    (by decide) (by decide) (by decide) h
theorem h16a2_L18s (T : Type16 x) (h : H16A2L18 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a2_L18 T.sigma h)
theorem h16a2_L18_of (T : Type16 x) (h : H16AL18 T) : H16A2L18 T := h16a2_leaf_of T _ _ _ _ h

def H16A2L19 (T : Type16 x) : Prop := H16A2Leaf T h16a_c19 h16a_ea19 h16a_eb19 (h16a_u19 T)
theorem h16a2_L19 (T : Type16 x) (h : H16A2L19 T) : IsRupert (univ.image x) :=
  h16a2_leaf_gen T (by norm_num) h16a_c19 (by decide) h16a_ea19 h16a_eb19 _
    (by decide) (by decide) (by decide) h
theorem h16a2_L19s (T : Type16 x) (h : H16A2L19 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a2_L19 T.sigma h)
theorem h16a2_L19_of (T : Type16 x) (h : H16AL19 T) : H16A2L19 T := h16a2_leaf_of T _ _ _ _ h

def H16A2L20 (T : Type16 x) : Prop := H16A2Leaf T h16a_c20 h16a_ea20 h16a_eb20 (h16a_u20 T)
theorem h16a2_L20 (T : Type16 x) (h : H16A2L20 T) : IsRupert (univ.image x) :=
  h16a2_leaf_gen T (by norm_num) h16a_c20 (by decide) h16a_ea20 h16a_eb20 _
    (by decide) (by decide) (by decide) h
theorem h16a2_L20s (T : Type16 x) (h : H16A2L20 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a2_L20 T.sigma h)
theorem h16a2_L20_of (T : Type16 x) (h : H16AL20 T) : H16A2L20 T := h16a2_leaf_of T _ _ _ _ h

def H16A2L21 (T : Type16 x) : Prop := H16A2Leaf T h16a_c21 h16a_ea21 h16a_eb21 (h16a_u21 T)
theorem h16a2_L21 (T : Type16 x) (h : H16A2L21 T) : IsRupert (univ.image x) :=
  h16a2_leaf_gen T (by norm_num) h16a_c21 (by decide) h16a_ea21 h16a_eb21 _
    (by decide) (by decide) (by decide) h
theorem h16a2_L21s (T : Type16 x) (h : H16A2L21 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a2_L21 T.sigma h)
theorem h16a2_L21_of (T : Type16 x) (h : H16AL21 T) : H16A2L21 T := h16a2_leaf_of T _ _ _ _ h

def H16A2L22 (T : Type16 x) : Prop := H16A2Leaf T h16a_c22 h16a_ea22 h16a_eb22 (h16a_u22 T)
theorem h16a2_L22 (T : Type16 x) (h : H16A2L22 T) : IsRupert (univ.image x) :=
  h16a2_leaf_gen T (by norm_num) h16a_c22 (by decide) h16a_ea22 h16a_eb22 _
    (by decide) (by decide) (by decide) h
theorem h16a2_L22s (T : Type16 x) (h : H16A2L22 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a2_L22 T.sigma h)
theorem h16a2_L22_of (T : Type16 x) (h : H16AL22 T) : H16A2L22 T := h16a2_leaf_of T _ _ _ _ h

def H16A2L23 (T : Type16 x) : Prop := H16A2Leaf T h16a_c23 h16a_ea23 h16a_eb23 (h16a_u23 T)
theorem h16a2_L23 (T : Type16 x) (h : H16A2L23 T) : IsRupert (univ.image x) :=
  h16a2_leaf_gen T (by norm_num) h16a_c23 (by decide) h16a_ea23 h16a_eb23 _
    (by decide) (by decide) (by decide) h
theorem h16a2_L23s (T : Type16 x) (h : H16A2L23 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a2_L23 T.sigma h)
theorem h16a2_L23_of (T : Type16 x) (h : H16AL23 T) : H16A2L23 T := h16a2_leaf_of T _ _ _ _ h

def H16A2L24 (T : Type16 x) : Prop := H16A2Leaf T h16a_c24 h16a_ea24 h16a_eb24 (h16a_u24 T)
theorem h16a2_L24 (T : Type16 x) (h : H16A2L24 T) : IsRupert (univ.image x) :=
  h16a2_leaf_gen T (by norm_num) h16a_c24 (by decide) h16a_ea24 h16a_eb24 _
    (by decide) (by decide) (by decide) h
theorem h16a2_L24s (T : Type16 x) (h : H16A2L24 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a2_L24 T.sigma h)
theorem h16a2_L24_of (T : Type16 x) (h : H16AL24 T) : H16A2L24 T := h16a2_leaf_of T _ _ _ _ h

def H16A2L25 (T : Type16 x) : Prop := H16A2Leaf T h16a_c25 h16a_ea25 h16a_eb25 (h16a_u25 T)
theorem h16a2_L25 (T : Type16 x) (h : H16A2L25 T) : IsRupert (univ.image x) :=
  h16a2_leaf_gen T (by norm_num) h16a_c25 (by decide) h16a_ea25 h16a_eb25 _
    (by decide) (by decide) (by decide) h
theorem h16a2_L25s (T : Type16 x) (h : H16A2L25 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a2_L25 T.sigma h)
theorem h16a2_L25_of (T : Type16 x) (h : H16AL25 T) : H16A2L25 T := h16a2_leaf_of T _ _ _ _ h

def h16a2_c26 : ZMod 5 → Fin 7 := ![6, 4, 2, 0, 3]
def h16a2_ea26 : ZMod 5 → Fin 8 := ![4, 2, 2, 3, 3]
def h16a2_eb26 : ZMod 5 → Fin 8 := ![6, 7, 0, 0, 1]
noncomputable def h16a2_u26 (T : Type16 x) : ℝ³ :=
  h16a_u (x 1 - x 0) (cross (T.fN 6) (T.fN 7))
    (cross (x 0 - x 2) (x 5 - x 2)) (x 4 - x 2)
def H16A2L26 (T : Type16 x) : Prop := H16A2Leaf T h16a2_c26 h16a2_ea26 h16a2_eb26 (h16a2_u26 T)
theorem h16a2_L26 (T : Type16 x) (h : H16A2L26 T) : IsRupert (univ.image x) :=
  h16a2_leaf_gen T (by norm_num) h16a2_c26 (by decide) h16a2_ea26 h16a2_eb26 _
    (by decide) (by decide) (by decide) h
theorem h16a2_L26s (T : Type16 x) (h : H16A2L26 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a2_L26 T.sigma h)

def h16a2_c27 : ZMod 6 → Fin 7 := ![0, 6, 1, 4, 5, 2]
def h16a2_ea27 : ZMod 6 → Fin 8 := ![3, 1, 5, 5, 0, 0]
def h16a2_eb27 : ZMod 6 → Fin 8 := ![4, 6, 6, 7, 7, 2]
noncomputable def h16a2_u27 (T : Type16 x) : ℝ³ :=
  h16a_u (x 2 - x 1) (x 5 - x 4)
    (x 6 - x 1) (x 0 - x 6)
def H16A2L27 (T : Type16 x) : Prop := H16A2Leaf T h16a2_c27 h16a2_ea27 h16a2_eb27 (h16a2_u27 T)
theorem h16a2_L27 (T : Type16 x) (h : H16A2L27 T) : IsRupert (univ.image x) :=
  h16a2_leaf_gen T (by norm_num) h16a2_c27 (by decide) h16a2_ea27 h16a2_eb27 _
    (by decide) (by decide) (by decide) h
theorem h16a2_L27s (T : Type16 x) (h : H16A2L27 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a2_L27 T.sigma h)

def h16a2_c28 : ZMod 5 → Fin 7 := ![4, 6, 3, 0, 2]
def h16a2_ea28 : ZMod 5 → Fin 8 := ![4, 3, 3, 2, 2]
def h16a2_eb28 : ZMod 5 → Fin 8 := ![6, 1, 0, 0, 7]
noncomputable def h16a2_u28 (T : Type16 x) : ℝ³ :=
  h16a_u (x 1 - x 0) (x 4 - x 0)
    (x 3 - x 6) (cross (x 0 - x 3) (x 2 - x 3))
def H16A2L28 (T : Type16 x) : Prop := H16A2Leaf T h16a2_c28 h16a2_ea28 h16a2_eb28 (h16a2_u28 T)
theorem h16a2_L28 (T : Type16 x) (h : H16A2L28 T) : IsRupert (univ.image x) :=
  h16a2_leaf_gen T (by norm_num) h16a2_c28 (by decide) h16a2_ea28 h16a2_eb28 _
    (by decide) (by decide) (by decide) h
theorem h16a2_L28s (T : Type16 x) (h : H16A2L28 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a2_L28 T.sigma h)

def h16a2_c29 : ZMod 5 → Fin 7 := ![6, 4, 2, 0, 3]
def h16a2_ea29 : ZMod 5 → Fin 8 := ![4, 2, 2, 3, 3]
def h16a2_eb29 : ZMod 5 → Fin 8 := ![6, 7, 0, 0, 1]
noncomputable def h16a2_u29 (T : Type16 x) : ℝ³ :=
  h16a_u (x 1 - x 0) (cross (T.fN 2) (T.fN 6))
    (x 3 - x 6) (x 4 - x 2)
def H16A2L29 (T : Type16 x) : Prop := H16A2Leaf T h16a2_c29 h16a2_ea29 h16a2_eb29 (h16a2_u29 T)
theorem h16a2_L29 (T : Type16 x) (h : H16A2L29 T) : IsRupert (univ.image x) :=
  h16a2_leaf_gen T (by norm_num) h16a2_c29 (by decide) h16a2_ea29 h16a2_eb29 _
    (by decide) (by decide) (by decide) h
theorem h16a2_L29s (T : Type16 x) (h : H16A2L29 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a2_L29 T.sigma h)

def h16a2_c30 : ZMod 5 → Fin 7 := ![6, 4, 2, 5, 3]
def h16a2_ea30 : ZMod 5 → Fin 8 := ![4, 2, 0, 0, 3]
def h16a2_eb30 : ZMod 5 → Fin 8 := ![6, 7, 7, 1, 1]
noncomputable def h16a2_u30 (T : Type16 x) : ℝ³ :=
  h16a_u (x 1 - x 0) (x 5 - x 4)
    (x 3 - x 6) (cross (x 3 - x 5) (x 0 - x 5))
def H16A2L30 (T : Type16 x) : Prop := H16A2Leaf T h16a2_c30 h16a2_ea30 h16a2_eb30 (h16a2_u30 T)
theorem h16a2_L30 (T : Type16 x) (h : H16A2L30 T) : IsRupert (univ.image x) :=
  h16a2_leaf_gen T (by norm_num) h16a2_c30 (by decide) h16a2_ea30 h16a2_eb30 _
    (by decide) (by decide) (by decide) h
theorem h16a2_L30s (T : Type16 x) (h : H16A2L30 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a2_L30 T.sigma h)

def h16a2_c31 : ZMod 5 → Fin 7 := ![4, 0, 3, 5, 1]
def h16a2_ea31 : ZMod 5 → Fin 8 := ![2, 0, 0, 5, 5]
def h16a2_eb31 : ZMod 5 → Fin 8 := ![4, 3, 1, 1, 6]
noncomputable def h16a2_u31 (T : Type16 x) : ℝ³ :=
  h16a_u (x 1 - x 0) (cross (T.fN 3) (T.fN 7))
    (cross (x 5 - x 3) (x 6 - x 3)) (x 3 - x 0)
def H16A2L31 (T : Type16 x) : Prop := H16A2Leaf T h16a2_c31 h16a2_ea31 h16a2_eb31 (h16a2_u31 T)
theorem h16a2_L31 (T : Type16 x) (h : H16A2L31 T) : IsRupert (univ.image x) :=
  h16a2_leaf_gen T (by norm_num) h16a2_c31 (by decide) h16a2_ea31 h16a2_eb31 _
    (by decide) (by decide) (by decide) h
theorem h16a2_L31s (T : Type16 x) (h : H16A2L31 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a2_L31 T.sigma h)

def h16a2_c32 : ZMod 5 → Fin 7 := ![6, 4, 2, 0, 3]
def h16a2_ea32 : ZMod 5 → Fin 8 := ![4, 2, 2, 3, 3]
def h16a2_eb32 : ZMod 5 → Fin 8 := ![6, 7, 0, 0, 1]
noncomputable def h16a2_u32 (T : Type16 x) : ℝ³ :=
  h16a_u (x 1 - x 0) (x 6 - x 5)
    (x 3 - x 6) (cross (x 3 - x 0) (x 5 - x 0))
def H16A2L32 (T : Type16 x) : Prop := H16A2Leaf T h16a2_c32 h16a2_ea32 h16a2_eb32 (h16a2_u32 T)
theorem h16a2_L32 (T : Type16 x) (h : H16A2L32 T) : IsRupert (univ.image x) :=
  h16a2_leaf_gen T (by norm_num) h16a2_c32 (by decide) h16a2_ea32 h16a2_eb32 _
    (by decide) (by decide) (by decide) h
theorem h16a2_L32s (T : Type16 x) (h : H16A2L32 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a2_L32 T.sigma h)

def h16a2_c33 : ZMod 5 → Fin 7 := ![4, 0, 3, 5, 1]
def h16a2_ea33 : ZMod 5 → Fin 8 := ![2, 0, 0, 5, 5]
def h16a2_eb33 : ZMod 5 → Fin 8 := ![4, 3, 1, 1, 6]
noncomputable def h16a2_u33 (T : Type16 x) : ℝ³ :=
  h16a_u (T.fN 5) (T.fN 6)
    (x 3 - x 0) (x 0 - x 4)
def H16A2L33 (T : Type16 x) : Prop := H16A2Leaf T h16a2_c33 h16a2_ea33 h16a2_eb33 (h16a2_u33 T)
theorem h16a2_L33 (T : Type16 x) (h : H16A2L33 T) : IsRupert (univ.image x) :=
  h16a2_leaf_gen T (by norm_num) h16a2_c33 (by decide) h16a2_ea33 h16a2_eb33 _
    (by decide) (by decide) (by decide) h
theorem h16a2_L33s (T : Type16 x) (h : H16A2L33 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a2_L33 T.sigma h)

def h16a2_c34 : ZMod 5 → Fin 7 := ![4, 6, 3, 0, 2]
def h16a2_ea34 : ZMod 5 → Fin 8 := ![4, 3, 3, 2, 2]
def h16a2_eb34 : ZMod 5 → Fin 8 := ![6, 1, 0, 0, 7]
noncomputable def h16a2_u34 (T : Type16 x) : ℝ³ :=
  h16a_u (x 1 - x 0) (x 4 - x 2)
    (x 3 - x 6) (x 4 - x 2)
def H16A2L34 (T : Type16 x) : Prop := H16A2Leaf T h16a2_c34 h16a2_ea34 h16a2_eb34 (h16a2_u34 T)
theorem h16a2_L34 (T : Type16 x) (h : H16A2L34 T) : IsRupert (univ.image x) :=
  h16a2_leaf_gen T (by norm_num) h16a2_c34 (by decide) h16a2_ea34 h16a2_eb34 _
    (by decide) (by decide) (by decide) h
theorem h16a2_L34s (T : Type16 x) (h : H16A2L34 T.sigma) : IsRupert (univ.image x) :=
  h16a_sigma (h16a2_L34 T.sigma h)

def H16A2Any (T : Type16 x) : Prop :=
  H16A2L1 T ∨ H16A2L2 T ∨ H16A2L3 T ∨ H16A2L4 T ∨ H16A2L5 T ∨ H16A2L6 T ∨ H16A2L7 T ∨ H16A2L8 T ∨ H16A2L9 T ∨ H16A2L10 T ∨ H16A2L11 T ∨ H16A2L12 T ∨ H16A2L13 T ∨ H16A2L14 T ∨ H16A2L15 T ∨ H16A2L16 T ∨ H16A2L17 T ∨ H16A2L18 T ∨ H16A2L19 T ∨ H16A2L20 T ∨ H16A2L21 T ∨ H16A2L22 T ∨ H16A2L23 T ∨ H16A2L24 T ∨ H16A2L25 T ∨ H16A2L26 T ∨ H16A2L27 T ∨ H16A2L28 T ∨ H16A2L29 T ∨ H16A2L30 T ∨ H16A2L31 T ∨ H16A2L32 T ∨ H16A2L33 T ∨ H16A2L34 T ∨ H16A2L1 T.sigma ∨ H16A2L2 T.sigma ∨ H16A2L3 T.sigma ∨ H16A2L4 T.sigma ∨ H16A2L5 T.sigma ∨ H16A2L6 T.sigma ∨ H16A2L7 T.sigma ∨ H16A2L8 T.sigma ∨ H16A2L9 T.sigma ∨ H16A2L10 T.sigma ∨ H16A2L11 T.sigma ∨ H16A2L12 T.sigma ∨ H16A2L13 T.sigma ∨ H16A2L14 T.sigma ∨ H16A2L15 T.sigma ∨ H16A2L16 T.sigma ∨ H16A2L17 T.sigma ∨ H16A2L18 T.sigma ∨ H16A2L19 T.sigma ∨ H16A2L20 T.sigma ∨ H16A2L21 T.sigma ∨ H16A2L22 T.sigma ∨ H16A2L23 T.sigma ∨ H16A2L24 T.sigma ∨ H16A2L25 T.sigma ∨ H16A2L26 T.sigma ∨ H16A2L27 T.sigma ∨ H16A2L28 T.sigma ∨ H16A2L29 T.sigma ∨ H16A2L30 T.sigma ∨ H16A2L31 T.sigma ∨ H16A2L32 T.sigma ∨ H16A2L33 T.sigma ∨ H16A2L34 T.sigma

theorem h16a2_any_isRupert (T : Type16 x) (h : H16A2Any T) : IsRupert (univ.image x) := by
  unfold H16A2Any at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact h16a2_L1 T h
  · exact h16a2_L2 T h
  · exact h16a2_L3 T h
  · exact h16a2_L4 T h
  · exact h16a2_L5 T h
  · exact h16a2_L6 T h
  · exact h16a2_L7 T h
  · exact h16a2_L8 T h
  · exact h16a2_L9 T h
  · exact h16a2_L10 T h
  · exact h16a2_L11 T h
  · exact h16a2_L12 T h
  · exact h16a2_L13 T h
  · exact h16a2_L14 T h
  · exact h16a2_L15 T h
  · exact h16a2_L16 T h
  · exact h16a2_L17 T h
  · exact h16a2_L18 T h
  · exact h16a2_L19 T h
  · exact h16a2_L20 T h
  · exact h16a2_L21 T h
  · exact h16a2_L22 T h
  · exact h16a2_L23 T h
  · exact h16a2_L24 T h
  · exact h16a2_L25 T h
  · exact h16a2_L26 T h
  · exact h16a2_L27 T h
  · exact h16a2_L28 T h
  · exact h16a2_L29 T h
  · exact h16a2_L30 T h
  · exact h16a2_L31 T h
  · exact h16a2_L32 T h
  · exact h16a2_L33 T h
  · exact h16a2_L34 T h
  · exact h16a2_L1s T h
  · exact h16a2_L2s T h
  · exact h16a2_L3s T h
  · exact h16a2_L4s T h
  · exact h16a2_L5s T h
  · exact h16a2_L6s T h
  · exact h16a2_L7s T h
  · exact h16a2_L8s T h
  · exact h16a2_L9s T h
  · exact h16a2_L10s T h
  · exact h16a2_L11s T h
  · exact h16a2_L12s T h
  · exact h16a2_L13s T h
  · exact h16a2_L14s T h
  · exact h16a2_L15s T h
  · exact h16a2_L16s T h
  · exact h16a2_L17s T h
  · exact h16a2_L18s T h
  · exact h16a2_L19s T h
  · exact h16a2_L20s T h
  · exact h16a2_L21s T h
  · exact h16a2_L22s T h
  · exact h16a2_L23s T h
  · exact h16a2_L24s T h
  · exact h16a2_L25s T h
  · exact h16a2_L26s T h
  · exact h16a2_L27s T h
  · exact h16a2_L28s T h
  · exact h16a2_L29s T h
  · exact h16a2_L30s T h
  · exact h16a2_L31s T h
  · exact h16a2_L32s T h
  · exact h16a2_L33s T h
  · exact h16a2_L34s T h

/-- Every strict arc leaf (the first 25 of the list) implies its robust version. -/
theorem h16a2_any_of (T : Type16 x) (h : H16AAny T) : H16A2Any T := by
  unfold H16AAny at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl (h16a2_L1_of T h)
  · exact Or.inr (Or.inl (h16a2_L2_of T h))
  · exact Or.inr (Or.inr (Or.inl (h16a2_L3_of T h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L4_of T h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L5_of T h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L6_of T h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L7_of T h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L8_of T h))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L9_of T h)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L10_of T h))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L11_of T h)))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L12_of T h))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L13_of T h)))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L14_of T h))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L15_of T h)))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L16_of T h))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L17_of T h)))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L18_of T h))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L19_of T h)))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L20_of T h))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L21_of T h)))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L22_of T h))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L23_of T h)))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L24_of T h))))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L25_of T h)))))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L1_of T.sigma h)))))))))))))))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L2_of T.sigma h))))))))))))))))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L3_of T.sigma h)))))))))))))))))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L4_of T.sigma h))))))))))))))))))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L5_of T.sigma h)))))))))))))))))))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L6_of T.sigma h))))))))))))))))))))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L7_of T.sigma h)))))))))))))))))))))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L8_of T.sigma h))))))))))))))))))))))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L9_of T.sigma h)))))))))))))))))))))))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L10_of T.sigma h))))))))))))))))))))))))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L11_of T.sigma h)))))))))))))))))))))))))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L12_of T.sigma h))))))))))))))))))))))))))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L13_of T.sigma h)))))))))))))))))))))))))))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L14_of T.sigma h))))))))))))))))))))))))))))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L15_of T.sigma h)))))))))))))))))))))))))))))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L16_of T.sigma h))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L17_of T.sigma h)))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L18_of T.sigma h))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L19_of T.sigma h)))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L20_of T.sigma h))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L21_of T.sigma h)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L22_of T.sigma h))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L23_of T.sigma h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L24_of T.sigma h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h16a2_L25_of T.sigma h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- The robust residual: `H16VResid` and no robust arc leaf applies. -/
def H16ArcResid2 (T : Type16 x) : Prop := H16VResid T ∧ ¬ H16A2Any T

theorem h16a2_resid2_imp_resid (T : Type16 x) (h : H16ArcResid2 T) : H16ArcResid T :=
  ⟨h.1, fun ha => h.2 (h16a2_any_of T ha)⟩

theorem h16a2_rule_isRupert (T : Type16 x) (h : ¬ H16ArcResid2 T) : IsRupert (univ.image x) := by
  by_cases hv : H16VResid T
  · have : H16A2Any T := by
      by_contra hn; exact h ⟨hv, hn⟩
    exact h16a2_any_isRupert T this
  · exact h16v_rule_isRupert T hv

theorem h16a2_rule_false (hN : IsNopert (Finset.univ.image x)) (T : Type16 x)
    (h : ¬ H16ArcResid2 T) : False :=
  hN.2 (h16a2_rule_isRupert T h)

end H16A
end Minimality
