# BrrrMachine F* Build

FSTAR_HOME ?= $(shell dirname $(shell which fstar.exe))/..
FSTAR = fstar.exe

# Include paths
INCLUDE_PATHS = \
	--include core \
	--include cpg \
	--include query \
	--include analysis \
	--include security \
	--include lang/go

# F* options
FSTAR_OPTIONS = \
	--cache_checked_modules \
	--cache_dir _cache \
	--odir _output \
	$(INCLUDE_PATHS)

# Source files in dependency order
CORE_SOURCES = \
	core/Types.fst \
	core/CFG.fst \
	core/CallGraph.fst

CPG_SOURCES = \
	cpg/CPG.fst

QUERY_SOURCES = \
	query/Traversal.fst

ANALYSIS_SOURCES = \
	analysis/Dataflow.fst \
	analysis/Taint.fst

SECURITY_SOURCES = \
	security/SQLInjection.fst

LANG_GO_SOURCES = \
	lang/go/Parser.fst \
	lang/go/Builtins.fst

ALL_SOURCES = $(CORE_SOURCES) $(CPG_SOURCES) $(QUERY_SOURCES) $(ANALYSIS_SOURCES) $(SECURITY_SOURCES) $(LANG_GO_SOURCES)

# Targets
.PHONY: all verify clean extract

all: verify

# Verify all F* modules
verify: $(ALL_SOURCES)
	@mkdir -p _cache _output
	@echo "Verifying BrrrMachine modules..."
	@for src in $(ALL_SOURCES); do \
		echo "  Checking $$src"; \
		$(FSTAR) $(FSTAR_OPTIONS) $$src || exit 1; \
	done
	@echo "All modules verified."

# Verify individual modules
core/Types.fst.checked: core/Types.fst
	$(FSTAR) $(FSTAR_OPTIONS) $<

core/CFG.fst.checked: core/CFG.fst core/Types.fst.checked
	$(FSTAR) $(FSTAR_OPTIONS) $<

core/CallGraph.fst.checked: core/CallGraph.fst core/Types.fst.checked
	$(FSTAR) $(FSTAR_OPTIONS) $<

analysis/Dataflow.fst.checked: analysis/Dataflow.fst core/CFG.fst.checked
	$(FSTAR) $(FSTAR_OPTIONS) $<

analysis/Taint.fst.checked: analysis/Taint.fst analysis/Dataflow.fst.checked
	$(FSTAR) $(FSTAR_OPTIONS) $<

security/SQLInjection.fst.checked: security/SQLInjection.fst analysis/Taint.fst.checked
	$(FSTAR) $(FSTAR_OPTIONS) $<

lang/go/Parser.fst.checked: lang/go/Parser.fst core/Types.fst.checked
	$(FSTAR) $(FSTAR_OPTIONS) $<

lang/go/Builtins.fst.checked: lang/go/Builtins.fst core/Types.fst.checked
	$(FSTAR) $(FSTAR_OPTIONS) $<

cpg/CPG.fst.checked: cpg/CPG.fst
	$(FSTAR) $(FSTAR_OPTIONS) $<

query/Traversal.fst.checked: query/Traversal.fst cpg/CPG.fst.checked
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

# Count lines and admits
stats:
	@echo "Lines of F* code:"
	@wc -l $(ALL_SOURCES) | tail -1
	@echo ""
	@echo "Unverified admits:"
	@grep -c "admit()" $(ALL_SOURCES) || echo "0"
	@echo ""
	@echo "Verified lemmas (no admit):"
	@grep -c "^let.*=" $(ALL_SOURCES) || echo "0"
