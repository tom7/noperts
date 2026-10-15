# The deltoidal hexecontahedron's search: its model files and own tools
# here, the shared code in ../common (rules: ../common/common.mk).
include ../common/common.mk

# Unit tests.
default : $(TESTS:%=%.exe)

# Every program of the pipeline (rebuild.sh runs it).
all: default qtube s5d codebdd.exe icoprune-check.exe halfturn-check.exe tietube.exe dfwhere.exe capleaf-check.exe capcert.exe

# Identity tube:
#  codebdd: exact rational model, codes and code triangles (codebdd.json).
#  tubecode: restartable (journaled) Tag 1 tree synthesis per code.
#  tuberefine: refines tube leaves to larger certified radii (monotone).
#  export-codetrees-pack: tube trees -> Lean tube packs (+ manifest).
qtube: tubecode.exe tuberefine.exe export-codetrees-pack.exe

# 5D search:
#  search5d: parallel journaled search per (code triangle, chart) job.
#  pack5d: journals -> Lean packs, one per code (checked by
#    ../../proof's constructDeltoidalHexecontahedron).
#  scoreboard5d: per-job status from the journals and packs.
#  icoprune-check: floating-point check of the icosahedral prune leaves
#    (icoprune-check.exe --journals DIR).
#  halfturn-check: floating-point check of the half-turn prune (centrally
#    symmetric solids: the group, the reduction's invariance, sampled boxes).
s5d: search5d.exe pack5d.exe scoreboard5d.exe

# This solid's own tools:
#  capcert: cap certificates for the special views (the caps stage).
#  tietube: exact tie tubes (the ties stage; dh-tie-data.py).
# and the shared diagnostics dfwhere and capleaf-check. halfturn-check uses
# rigidity-margin's passage clearance.
halfturn-check.exe : halfturn-check.o rigidity-margin.o $(OBJECTS_CORE) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

.PHONY : qtube s5d
