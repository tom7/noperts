# The snub cube's search: its model files and own tools here, the shared code
# in ../common (rules: ../common/common.mk).
include ../common/common.mk

# Unit tests.
default : $(TESTS:%=%.exe)

# Every program (rebuild.sh runs the pipeline ones).
all: default sc-model.exe qtube s5d codebdd.exe capleaf-check.exe dfwhere.exe sccapcert.exe

# The model (sc-model.txt, symmetry-neighbors.h): no shared objects, since
# the shared code needs the headers that codebdd generates from the model.
sc-model.exe : sc-model.o $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

# Identity tube:
#  codebdd: exact rational model, codes and code triangles (codebdd.json).
#  tubecode: restartable (journaled) Tag 1 tree synthesis per code.
#  tuberefine: refines tube leaves to larger certified radii (monotone).
#  export-codetrees-pack: tube trees -> Lean tube packs (+ manifest).
qtube: tubecode.exe tuberefine.exe export-codetrees-pack.exe

# 5D search:
#  search5d: parallel journaled search per (code triangle, chart) job.
#  pack5d: journals -> Lean packs, one per code.
#  scoreboard5d: per-job status from the journals and packs.
s5d: search5d.exe pack5d.exe scoreboard5d.exe

# Caps:
#  sccapcert: exact cap certificates at u* and the tie tube (the caps stage),
#  and the main search's cap domains (--caps, for search5d --trib_caps).

.PHONY : qtube s5d
