# Brrr-Lang F* Project Makefile
# Based on FStar's mk/test.mk pattern

# ============================================================================
# CONFIGURATION - Edit these for your environment
# ============================================================================

FSTAR_HOME ?= /home/grigory/Downloads/FStar
FSTAR_EXE  ?= $(FSTAR_HOME)/bin/fstar.exe

# Output directories
OUTPUT_DIR = _output
CACHE_DIR  = _cache

# Source directories (add more as needed)
SOURCE_DIRS = src/core

# ============================================================================
# F* FLAGS
# ============================================================================

FSTAR_INCLUDES = $(addprefix --include , $(SOURCE_DIRS))

# Default: Extensive verification (for powerful machines)
Z3_RLIMIT        ?= 500
Z3_RLIMIT_FACTOR ?= 8
FUEL             ?= 8
MAX_FUEL         ?= 16
IFUEL            ?= 4
MAX_IFUEL        ?= 8
RETRY            ?= 5

SMT_OPTIONS = \
  --z3rlimit $(Z3_RLIMIT) \
  --z3rlimit_factor $(Z3_RLIMIT_FACTOR) \
  --fuel $(FUEL) \
  --max_fuel $(MAX_FUEL) \
  --ifuel $(IFUEL) \
  --max_ifuel $(MAX_IFUEL) \
  --retry $(RETRY) \
  --smtencoding.elim_box true \
  --smtencoding.l_arith_repr native \
  --smtencoding.nl_arith_repr native \
  --ext optimize_let_vc

FSTAR_FLAGS = \
  --cache_dir $(CACHE_DIR) \
  --odir $(OUTPUT_DIR) \
  --warn_error -321 \
  $(SMT_OPTIONS) \
  $(FSTAR_INCLUDES)

FSTAR = $(FSTAR_EXE) $(FSTAR_FLAGS)

# ============================================================================
# SOURCE FILES
# ============================================================================

# Find all .fst and .fsti files
FSTAR_FILES = $(foreach dir,$(SOURCE_DIRS),$(wildcard $(dir)/*.fst) $(wildcard $(dir)/*.fsti))

# Checked files go in cache dir, preserving directory structure
CHECKED_FILES = $(patsubst %.fst,$(CACHE_DIR)/%.fst.checked,$(FSTAR_FILES))
CHECKED_FILES += $(patsubst %.fsti,$(CACHE_DIR)/%.fsti.checked,$(filter %.fsti,$(FSTAR_FILES)))

# ============================================================================
# TARGETS
# ============================================================================

.PHONY: all verify clean depend world

all: verify

# Dependency analysis - creates .depend file
.depend: $(FSTAR_FILES)
	@mkdir -p $(CACHE_DIR) $(OUTPUT_DIR)
	@echo "DEPEND"
	$(FSTAR) --dep full $(FSTAR_FILES) -o $@

# Include generated dependencies (if they exist)
ifneq ($(MAKECMDGOALS),clean)
-include .depend
endif

# Verify all files (default: extensive)
verify: .depend
	@echo "VERIFY [extensive]"
	@for f in $(FSTAR_FILES); do \
		echo "  Checking $$f"; \
		$(FSTAR) $$f || exit 1; \
	done
	@echo "All files verified."

# Quick verification for development
quick:
	$(MAKE) verify Z3_RLIMIT=50 Z3_RLIMIT_FACTOR=2 FUEL=2 MAX_FUEL=4 IFUEL=1 MAX_IFUEL=2 RETRY=1

# Verify single file
check:
	$(FSTAR) $(F)

# Verify single file (quick mode)
check-quick:
	$(FSTAR_EXE) $(FSTAR_INCLUDES) --cache_dir $(CACHE_DIR) --odir $(OUTPUT_DIR) \
		--z3rlimit 50 --z3rlimit_factor 2 --fuel 2 --max_fuel 4 --ifuel 1 --max_ifuel 2 --retry 1 \
		--smtencoding.elim_box true --ext optimize_let_vc $(F)

# Rule for .checked files
$(CACHE_DIR)/%.fst.checked: %.fst
	@mkdir -p $(dir $@)
	$(FSTAR) $<
	@touch $@

$(CACHE_DIR)/%.fsti.checked: %.fsti
	@mkdir -p $(dir $@)
	$(FSTAR) $<
	@touch $@

# Extract to OCaml
extract: verify
	@echo "EXTRACT"
	@for f in $(FSTAR_FILES); do \
		echo "  Extracting $$f"; \
		$(FSTAR) --codegen OCaml $$f; \
	done

# Clean
clean:
	rm -rf $(OUTPUT_DIR) $(CACHE_DIR) .depend

# Full rebuild
world: clean all

# ============================================================================
# EDITOR INTEGRATION (for fstar-mode.el)
# ============================================================================

# This target is called by fstar-mode.el to get F* arguments
%.fst-in %.fsti-in:
	@echo $(FSTAR_FLAGS)

# ============================================================================
# HELP
# ============================================================================

help:
	@echo "Brrr-Lang F* Makefile"
	@echo ""
	@echo "Targets:"
	@echo "  verify         - Extensive verification (default)"
	@echo "  quick          - Quick verification for development"
	@echo "  check F=X      - Verify single file (extensive)"
	@echo "  check-quick F=X- Verify single file (quick)"
	@echo "  extract        - Extract to OCaml"
	@echo "  clean          - Remove build artifacts"
	@echo "  world          - Clean and rebuild"
	@echo ""
	@echo "Environment:"
	@echo "  FSTAR_HOME=$(FSTAR_HOME)"
