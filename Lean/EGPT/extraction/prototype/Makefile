# Makefile — reproduce the #extract_to_c end-to-end demo.
#
# Pass B: per-theorem subdirectories under prototype/<Theorem_Name>/.
# `make all` iterates every subdirectory, compiles extracted.c against
# libegpt_num, runs the binary, and byte-compares stdout to expected.
#
# Prereqs:
#   - FRAQTL with feat/egpt-num-cffi merged. Two clone layouts probed:
#       ~/Code/EGPT-research/...  (sibling of Unkamon)  → ../../../../../Unkamon/FRAQTL
#       ~/Code/Unkamon/EGPT/...  (Unkamon submodule)   → ../../../../../FRAQTL
#     Override with `make FRAQTL_ROOT=/abs/path/to/FRAQTL` if neither matches.
#   - `cargo build --release -p egpt_num` (or `make runtime`).
#   - `lake build InformationTheory.EntropyNumber.ContinuumHypothesis`
#     (or `make extract` — regenerates all extracted.c files).

ifeq ($(wildcard ../../../../../Unkamon/FRAQTL/fat),)
FRAQTL_ROOT ?= $(abspath ../../../../../FRAQTL)
else
FRAQTL_ROOT ?= $(abspath ../../../../../Unkamon/FRAQTL)
endif
EGPT_NUM    := $(FRAQTL_ROOT)/fat/crates/egpt_num
RUST_TARGET := $(FRAQTL_ROOT)/fat/target/release
INCLUDE_DIR := $(EGPT_NUM)/include
LEAN_ROOT   := $(abspath ../..)

CC      ?= cc
CFLAGS  ?= -Wall -Wextra -O2

# Discover per-theorem subdirectories.
TARGETS := $(wildcard */extracted.c)
BINS    := $(TARGETS:%/extracted.c=%/extracted_bin)

.PHONY: all extract runtime diff clean

all: diff

extract:
	@echo ">>> #extract_to_c (via lake env lean)"
	@cd $(LEAN_ROOT) && lake env lean extraction/ExtractionCommand.lean

runtime:
	@echo ">>> cargo build --release -p egpt_num"
	@cd $(FRAQTL_ROOT)/fat && cargo build --release -p egpt_num

%/extracted_bin: %/extracted.c
	@echo ">>> cc $<"
	$(CC) $(CFLAGS) -o $@ $< \
	    -I $(INCLUDE_DIR) \
	    -L $(RUST_TARGET) \
	    -legpt_num \
	    -Wl,-rpath,$(RUST_TARGET)

diff: $(BINS)
	@set -e; for dir in $(TARGETS:%/extracted.c=%); do \
	    echo ">>> $$dir"; \
	    ./$$dir/extracted_bin > /tmp/$$dir.out 2>&1; \
	    diff $$dir/expected_output.txt /tmp/$$dir.out && \
	        echo "  ✓ $$dir byte-equivalent"; \
	done

clean:
	@rm -f */extracted_bin /tmp/Extraction_*.out
