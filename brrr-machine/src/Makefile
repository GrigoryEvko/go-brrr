# BrrrMachine F* Build
#
# Verified static analysis framework

FSTAR_HOME ?= $(shell dirname $(shell which fstar.exe))/..
FSTAR = fstar.exe

# Include paths for module resolution
INCLUDE_PATHS = \
	--include cpg \
	--include query \
	--include analysis

# F* verification options (following HACL*/EverParse patterns)
FSTAR_OPTIONS = \
	--cache_checked_modules \
	--cache_dir _cache \
	--odir _output \
	--z3rlimit 50 \
	--max_fuel 0 \
	--max_ifuel 0 \
	$(INCLUDE_PATHS)

# ============================================================================
# Source files in dependency order
# ============================================================================

# Code Property Graph - foundation
CPG_SOURCES = \
	cpg/CPG.fst

# Query/traversal layer
QUERY_SOURCES = \
	query/Traversal.fst

# Analysis algorithms
ANALYSIS_SOURCES = \
	analysis/Dataflow.fst \
	analysis/Taint.fst \
	analysis/GaloisConnection.fst \
	analysis/IFDS.fst \
	analysis/IFDSTaint.fst \
	analysis/IncrementalTaint.fst

# All sources
ALL_SOURCES = $(CPG_SOURCES) $(QUERY_SOURCES) $(ANALYSIS_SOURCES)

# Interface files (.fsti)
INTERFACE_FILES = \
	analysis/IFDS.fsti \
	analysis/IFDSTaint.fsti

# ============================================================================
# Targets
# ============================================================================

.PHONY: all verify clean extract stats

all: verify

# Verify all F* modules
verify:
	@mkdir -p _cache _output
	@echo "Verifying BrrrMachine modules..."
	@echo "  Using F* options: --z3rlimit 50 --max_fuel 0 --max_ifuel 0"
	@for src in $(ALL_SOURCES); do \
		echo "  Checking $$src"; \
		$(FSTAR) $(FSTAR_OPTIONS) $$src || exit 1; \
	done
	@echo ""
	@echo "All modules verified successfully."

# Verify specific modules with dependencies
cpg/CPG.fst.checked: cpg/CPG.fst
	$(FSTAR) $(FSTAR_OPTIONS) $<

query/Traversal.fst.checked: query/Traversal.fst cpg/CPG.fst.checked
	$(FSTAR) $(FSTAR_OPTIONS) $<

analysis/Dataflow.fst.checked: analysis/Dataflow.fst cpg/CPG.fst.checked
	$(FSTAR) $(FSTAR_OPTIONS) $<

analysis/Taint.fst.checked: analysis/Taint.fst analysis/Dataflow.fst.checked
	$(FSTAR) $(FSTAR_OPTIONS) $<

analysis/GaloisConnection.fst.checked: analysis/GaloisConnection.fst
	$(FSTAR) $(FSTAR_OPTIONS) $<

analysis/IFDS.fst.checked: analysis/IFDS.fst analysis/IFDS.fsti cpg/CPG.fst.checked
	$(FSTAR) $(FSTAR_OPTIONS) $<

analysis/IFDSTaint.fst.checked: analysis/IFDSTaint.fst analysis/IFDSTaint.fsti analysis/IFDS.fst.checked
	$(FSTAR) $(FSTAR_OPTIONS) $<

analysis/IncrementalTaint.fst.checked: analysis/IncrementalTaint.fst analysis/IFDS.fst.checked
	$(FSTAR) $(FSTAR_OPTIONS) $<

# Extract to OCaml
extract: verify
	@echo "Extracting to OCaml..."
	@for src in $(ALL_SOURCES); do \
		$(FSTAR) $(FSTAR_OPTIONS) --codegen OCaml $$src; \
	done

# Clean build artifacts
clean:
	rm -rf _cache _output
	rm -f *.checked
	rm -f **/*.checked

# Statistics
stats:
	@echo "=== BrrrMachine F* Statistics ==="
	@echo ""
	@echo "Source files:"
	@ls -la $(ALL_SOURCES) 2>/dev/null | wc -l
	@echo ""
	@echo "Interface files:"
	@ls -la $(INTERFACE_FILES) 2>/dev/null | wc -l
	@echo ""
	@echo "Lines of F* code:"
	@wc -l $(ALL_SOURCES) $(INTERFACE_FILES) 2>/dev/null
	@echo ""
	@echo "Unverified admits:"
	@grep -c "admit()" $(ALL_SOURCES) 2>/dev/null || echo "0 (fully verified)"
	@echo ""
	@echo "Lemmas defined:"
	@grep -c "^val\|^let rec\|^let " $(ALL_SOURCES) 2>/dev/null | tail -1
