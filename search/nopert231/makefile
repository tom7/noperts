# Candidate #231's search: its model files, its own codebdd.cc and its tests
# here, the shared code in ../common (rules: ../common/common.mk).
include ../common/common.mk

# Unit tests (make; `make test` runs them): the shared ones and #231's own.
TESTS += model231_test tube231_test
default : $(TESTS:%=%.exe)

# Every program of the pipeline (rebuild.sh runs it; see README.md).
all: default qtube s5d codebdd.exe

# Rational model and identity tube:
#  codebdd (codebdd.cc here, #231's own): exact rational model
#    (model_vertices.*), codes and code triangles (codebdd.json).
#  tubecode: restartable (journaled) Tag 1 tree synthesis per code.
#  tuberefine: refines tube leaves to larger certified radii (monotone).
#  export_codetrees_pack: tube trees -> Lean packs (constructNopert231).
qtube: tubecode.exe tuberefine.exe export_codetrees_pack.exe

# 5D search:
#  search5d: parallel journaled search per (code triangle, chart) job.
#  pack5d: journals -> Lean packs, one per code (checked by
#    ../../proof's constructNopert231).
#  scoreboard5d: per-job status from the journals and packs.
s5d: search5d.exe pack5d.exe scoreboard5d.exe

.PHONY : qtube s5d
