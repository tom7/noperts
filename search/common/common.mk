# Build rules shared by the solids' makefiles (search/<solid>/makefile, which
# include this file and then list their targets).
#
# The shared sources are in this directory. A solid's directory holds its own
# sources and its model headers (model_vertices.h, symmetry_neighbors.h,
# solid.h, ...), which the shared code includes by name, so each solid
# compiles the shared code itself: the objects and executables are built in
# the solid's directory (make -C search/<solid>).

COMMON := ../common
CC_LIB := ../../cc-lib
# Only for renderings (shadowanim.exe, tieviz.exe): tom7misc's codec, next to
# cc-lib (or make ... CODEC=/path/to/codec).
CODEC := ../../codec

# Sources not in the solid's directory are taken from COMMON.
vpath %.cc $(COMMON)
vpath %.h $(COMMON)

.DEFAULT_GOAL := default

# The unit tests (`make`; `make test` runs them).
TESTS := exact5d_test geom5d_test contacts5d_test cert5d_test tubeatlas5d_test rows5d_test solve5d_test lp5d_test tubetree_test model_test tube_test

UNAME := $(shell uname -o)
ifeq ($(findstring Linux,$(UNAME)),Linux)
CC=clang
CXX=clang++
endif

# This is optional; if you want to use plain C++ code, just
# comment it out. But GMP is much faster.
GMP_LFLAGS=-lgmp
GMP_CFLAGS=-DBIG_USE_GMP

# On Mac, this is how I get them
ifeq ($(findstring Darwin,$(UNAME)),Darwin)
GMP_LFLAGS=`pkg-config --libs gmp`
GMP_CFLAGS=`pkg-config --cflags gmp` -DBIG_USE_GMP
endif

# Detect mimalloc if available, otherwise leave off
MALLOC_LFLAGS := $(shell echo 'int main(){}' | clang -x c - -lmimalloc -o /dev/null 2>/dev/null && echo -lmimalloc)

# for profiling (Very Sleepy)
# OPT=-O -g -gcodeview
OPT=-O3 -flto=thin -g
# ASAN=-g -fsanitize=address -fsanitize=undefined
# OPT=-O

# REMARKS=-Rpass=loop-vectorize -Rpass-missed=loop-vectorize -Rpass-analysis=loop-vectorize

CXXFLAGS=$(REMARKS) $(ASAN) $(OPT) $(GMP_CFLAGS) -march=native -mtune=native -Wall -Wno-psabi -Wno-unused-function -Wno-sign-compare -I. -I$(COMMON) -I$(CC_LIB) --std=c++23
LFLAGS=$(ASAN) $(GMP_LFLAGS) -flto -lz $(MALLOC_LFLAGS)

CC_LIB_OBJECTS=$(CC_LIB)/util.o $(CC_LIB)/arcfour.o $(CC_LIB)/factorization.o $(CC_LIB)/base/stringprintf.o $(CC_LIB)/base/logging.o $(CC_LIB)/stb_image.o $(CC_LIB)/stb_image_write.o $(CC_LIB)/stb_truetype.o $(CC_LIB)/color-util.o $(CC_LIB)/image.o $(CC_LIB)/ansi.o  $(CC_LIB)/atomic-util.o $(CC_LIB)/status-bar.o $(CC_LIB)/zip.o $(CC_LIB)/miniz.o $(CC_LIB)/ansi-image.o $(CC_LIB)/image-resize.o $(CC_LIB)/opt/opt.o $(CC_LIB)/opt/large-optimizer.o $(CC_LIB)/bounds.o $(CC_LIB)/interval-cover.o $(CC_LIB)/interval-cover-util.o $(CC_LIB)/bignum/big.o $(CC_LIB)/bignum/bigz.o $(CC_LIB)/bignum/bign.o $(CC_LIB)/bignum/bigq.o $(CC_LIB)/bignum/big-numbers.o $(CC_LIB)/bignum/polynomial.o $(CC_LIB)/bignum/big-interval.o $(CC_LIB)/textsvg.o $(CC_LIB)/hexdump.o $(CC_LIB)/integer-voronoi.o $(CC_LIB)/crypt/sha256.o $(CC_LIB)/process-util.o $(CC_LIB)/numbers.o $(CC_LIB)/nice.o $(CC_LIB)/png.o $(CC_LIB)/geom/mesh.o $(CC_LIB)/geom/polygons.o $(CC_LIB)/geom/hull-3d.o $(CC_LIB)/geom/polyhedra.o $(CC_LIB)/geom/symmetry-groups.o $(CC_LIB)/geom/hull-2d.o $(CC_LIB)/z3/z3.o $(CC_LIB)/dirty.o

OBJECTS=$(CC_LIB_OBJECTS)

# Only for renderings (animations of polyhedra).
CODEC_OBJECTS=$(CODEC)/mov.o $(CODEC)/mov-recorder.o

# Library objects shared by the tools. No OpenCL.
OBJECTS_CORE=model.o tube.o tubetree.o tieatlas5d.o exact5d.o geom5d.o contacts5d.o bounds5d.o cert5d.o tubeatlas5d.o rows5d.o solve5d.o lp5d.o

# Every object depends on every header (the solid's and the shared ones).
HEADERS := $(wildcard *.h) $(wildcard $(COMMON)/*.h)

$(CC_LIB)/%.o : $(CC_LIB)/%.cc
	@$(CXX) $(CXXFLAGS) -c $< -o $@
	@echo -n "."

$(CODEC)/%.o : $(CODEC)/%.cc
	@$(CXX) $(CXXFLAGS) -I$(CODEC) -c $< -o $@
	@echo -n "."

shadowanim.o tieviz.o : CXXFLAGS += -I$(CODEC)

%.o : %.cc $(HEADERS) makefile $(COMMON)/common.mk
	@$(CXX) $(CXXFLAGS) -c $< -o $@
	@echo -n "."

# Generic pattern rule for executables.
%.exe : %.o $(OBJECTS_CORE) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

# Renderings (not part of the proofs):
#  viewmap: the first-order margin, search density or tube radius over all
#    views, as an equirectangular image and a UDIM-textured OBJ of the solid.
#  shadowanim: an animation of first-order rigidity (shadowanim.txt); also
#    needs tom7misc's codec (CODEC above).
viewmap.exe : viewmap.o rigidity-margin.o $(OBJECTS_CORE) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

shadowanim.exe : shadowanim.o rigidity-margin.o $(OBJECTS_CORE) $(OBJECTS) $(CODEC_OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

# Runs every unit test. Tests that need generated data (codebdd.json, tube
# trees, the Lean exact5d_golden executable) skip when it is absent; see the
# tests for the environment variables that point them at it.
test : default
	@failed=""; for t in $(TESTS); do echo "== $$t"; ./$$t.exe || failed="$$failed $$t"; done; \
	  if [ -n "$$failed" ]; then echo "FAILED:$$failed"; exit 1; fi; echo "all tests passed"

clean :
	rm -f *.o *.exe

.PHONY : default all test clean
