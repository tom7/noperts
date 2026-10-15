# The Septopert's search: its model files and own tools here, the shared code
# in ../common (rules: ../common/common.mk).
include ../common/common.mk

# Unit tests.
default : $(TESTS:%=%.exe)

# Every program (rebuild.sh runs the pipeline ones).
all: default qtube s5d codebdd.exe capcert_septopert.exe dfwhere.exe capleaf_check.exe

# Identity tube:
#  codebdd: exact rational model, codes and code triangles (codebdd.json).
#  tubecode: restartable (journaled) Tag 1 tree synthesis per code.
#  tuberefine: refines tube leaves to larger certified radii (monotone).
#  export_codetrees_pack: tube trees -> Lean tube packs (+ manifest).
#  idcap: identity blow-up certificates; replaces tube subtrees by blow-up
#    rows (Lean Row.idcap) where they certify (rebuild.sh stage idcap).
qtube: tubecode.exe tuberefine.exe idcap.exe export_codetrees_pack.exe

# 5D search:
#  search5d: parallel journaled search per (code triangle, chart) job.
#  pack5d: journals -> Lean packs, one per code (checked by constructSeptopert).
#  scoreboard5d: per-job status from the journals and packs.
s5d: search5d.exe pack5d.exe scoreboard5d.exe

# Diagnostics: dfwhere (where a 5D job's deferred leaves are) and
# capleaf_check (an exact re-check of the 5D journals' cap leaves).
# capcert_septopert: the Septopert's cap certificate at its mirror normal.

.PHONY : qtube s5d
