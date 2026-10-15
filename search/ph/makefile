# The pentagonal hexecontahedron's search: its model files here, the shared code in
# ../common (rules: ../common/common.mk).
include ../common/common.mk

# Unit tests.
default : $(TESTS:%=%.exe)

# Every program of the pipeline (rebuild.sh runs it).
all: default qtube s5d codebdd.exe icoprune-check.exe

# Identity tube:
#  codebdd: exact rational model, codes and code triangles (codebdd.json).
#  tubecode: restartable (journaled) Tag 1 tree synthesis per code.
#  tuberefine: refines tube leaves to larger certified radii (monotone).
#  export-codetrees-pack: tube trees -> Lean tube packs (+ manifest).
qtube: tubecode.exe tuberefine.exe export-codetrees-pack.exe

# 5D search:
#  search5d: parallel journaled search per (code triangle, chart) job.
#  pack5d: journals -> Lean packs, one per code (checked by
#    ../../proof's constructPentagonalHexecontahedron).
#  scoreboard5d: per-job status from the journals and packs.
#  icoprune-check: floating-point check of the icosahedral prune leaves
#    (icoprune-check.exe --journals DIR).
s5d: search5d.exe pack5d.exe scoreboard5d.exe

.PHONY : qtube s5d
