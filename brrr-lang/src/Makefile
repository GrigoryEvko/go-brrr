# BrrrLang F* Implementation
# Makefile for verification

FSTAR_HOME ?= $(HOME)/.local/bin/lib/fstar
FSTAR = fstar.exe

# F* include paths
INCLUDE_PATHS = \
	--include $(FSTAR_HOME)/ulib \
	--include axioms \
	--include core \
	--include analysis \
	--include security \
	--include lang \
	--include physical

# Z3 options for complex proofs
Z3_OPTIONS = --z3rlimit 100

# F* options
FSTAR_OPTIONS = \
	--cache_checked_modules \
	--cache_dir _cache \
	--odir _output \
	$(INCLUDE_PATHS) \
	$(Z3_OPTIONS)

# Source files in dependency order
AXIOM_SOURCES = \
	axioms/Axioms.fst

CORE_SOURCES = \
	core/Primitives.fst \
	core/Modes.fst \
	core/Effects.fst \
	core/BrrrTypes.fst \
	core/Expressions.fst \
	core/Values.fst \
	core/Eval.fst \
	core/Async.fst \
	core/Continuations.fst \
	core/DependentTypes.fst \
	core/SeparationLogic.fst \
	core/ComputeArch.fst

ANALYSIS_SOURCES = \
	analysis/CFG.fst \
	analysis/Dataflow.fst \
	analysis/Taint.fst

SECURITY_SOURCES = \
	security/InfoFlow.fst \
	security/Contracts.fst

PHYSICAL_SOURCES = \
	physical/Interning.fst \
	physical/Columnar.fst

ALL_SOURCES = $(CORE_SOURCES) $(ANALYSIS_SOURCES) $(SECURITY_SOURCES) $(PHYSICAL_SOURCES)

# Currently implemented
IMPLEMENTED = $(AXIOM_SOURCES) $(CORE_SOURCES)

# Targets
.PHONY: all verify verify-core clean extract stats

all: verify-core

# Verify only implemented modules
verify-core: $(CORE_SOURCES)
	@mkdir -p _cache _output
	@echo "Verifying BrrrLang core modules..."
	@for src in $(IMPLEMENTED); do \
		if [ -f "$$src" ]; then \
			echo "  Checking $$src"; \
			$(FSTAR) $(FSTAR_OPTIONS) $$src || exit 1; \
		fi \
	done
	@echo "Core modules verified."

# Verify all modules
verify: $(ALL_SOURCES)
	@mkdir -p _cache _output
	@echo "Verifying all BrrrLang modules..."
	@for src in $(ALL_SOURCES); do \
		if [ -f "$$src" ]; then \
			echo "  Checking $$src"; \
			$(FSTAR) $(FSTAR_OPTIONS) $$src || exit 1; \
		fi \
	done
	@echo "All modules verified."

# Verify single file
%.fst.checked: %.fst
	$(FSTAR) $(FSTAR_OPTIONS) $<
	@touch $@

# Extract to OCaml
extract: verify
	@echo "Extracting to OCaml..."
	@for src in $(IMPLEMENTED); do \
		if [ -f "$$src" ]; then \
			$(FSTAR) $(FSTAR_OPTIONS) --codegen OCaml $$src; \
		fi \
	done

# Clean build artifacts
clean:
	rm -rf _cache _output
	rm -f *.checked core/*.checked analysis/*.checked security/*.checked

# Statistics
stats:
	@echo "=== BrrrLang Implementation Stats ==="
	@echo ""
	@echo "Lines of F* code:"
	@wc -l $(IMPLEMENTED) 2>/dev/null | tail -1 || echo "0"
	@echo ""
	@echo "Unverified admits:"
	@grep -c "admit()" $(IMPLEMENTED) 2>/dev/null || echo "0"
	@echo ""
	@echo "Verified lemmas:"
	@grep -c "^val\|^let.*Lemma" $(IMPLEMENTED) 2>/dev/null || echo "0"
	@echo ""
	@echo "Type definitions:"
	@grep -c "^type\|^noeq type" $(IMPLEMENTED) 2>/dev/null || echo "0"

# Interactive mode
interactive:
	$(FSTAR) $(FSTAR_OPTIONS) --ide

# Help
help:
	@echo "BrrrLang F* Makefile"
	@echo ""
	@echo "Targets:"
	@echo "  verify-core  - Verify core modules (default)"
	@echo "  verify       - Verify all modules"
	@echo "  extract      - Extract to OCaml"
	@echo "  clean        - Remove build artifacts"
	@echo "  stats        - Show code statistics"
	@echo "  interactive  - Start F* IDE mode"
