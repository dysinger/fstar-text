# text — dev-loop build (F* verify + KaRaMeL extract)
# Usage: nix develop, then make check / make krml.
# Requires CODEC_SRC (the codec source directory), defaulting to the
# vendored ./codec.

FSTAR ?= fstar.exe
KRML  ?= krml

CODEC_SRC ?= ./codec

ULIB       ?= $(shell $(FSTAR) --locate_lib 2>/dev/null || echo /none)/ulib
KRM_LIB_DIR ?= $(or $(KRML_HOME)/krmllib,$(KRM_LIB))

FSTAR_FLAGS = --no_default_includes \
  --include $(ULIB) \
  --include ./src \
  --include $(CODEC_SRC)/src \
  --include $(KRM_LIB_DIR) \
  --include $(KRM_LIB_DIR)/obj

# Only Low* modules extracted to C (src/ only)
KRML_MODS := $(shell grep -h '^module ' src/*.fst 2>/dev/null | \
  grep '\.Low' | sed 's/^module //' | sort)

.PHONY: check krml clean guard-env

# Fail fast if required source-path env vars are unset (the nix devShell sets them).
REQUIRED_VARS := CODEC_SRC
guard-env:
	@for v in $(REQUIRED_VARS); do \
	  eval val=\$$$$v; \
	  if [ -z "$$val" ]; then \
	    echo "ERROR: $$$v is not set; run 'nix develop' (or set $$$v manually)" >&2; \
	    exit 1; \
	  fi; \
	done

SRC_MODS := $(shell grep -h '^module ' src/*.fst 2>/dev/null | \
  grep -v '^module .* = ' | sed 's/^module //' | sort)
TST_MODS := $(shell grep -h '^module ' test/*.fst 2>/dev/null | \
  grep -v '^module .* = ' | sed 's/^module //' | sort)

check: guard-env $(addprefix out/checked/,$(addsuffix .checked,$(SRC_MODS))) \
       $(addprefix out/checked/,$(addsuffix .checked,$(TST_MODS)))

out/checked/%.checked: src/%.fst
	@mkdir -p out/checked
	@echo "=== $* ==="
	$(FSTAR) $(FSTAR_FLAGS) \
	  --z3rlimit 80 \
	  --cache_checked_modules --cache_dir out/checked \
	  --odir out/checked $<

out/checked/%.checked: test/%.fst
	@mkdir -p out/checked
	@echo "=== $* ==="
	$(FSTAR) $(FSTAR_FLAGS) --include ./test \
	  --z3rlimit 80 \
	  --cache_checked_modules --cache_dir out/checked \
	  --odir out/checked $<

krml: guard-env check $(addprefix out/krml/,$(addsuffix .krml,$(subst .,_,$(KRML_MODS))))

# Per-module krml extraction — dots in source, underscores in output
define KRML_RULE
out/krml/$(subst .,_,$(1)).krml: src/$(1).fst
	@mkdir -p out/krml
	$(FSTAR) $(FSTAR_FLAGS) \
	  --cache_checked_modules --cache_dir out/checked \
	  --odir out/krml --codegen krml \
	  --extract_module $(1) $$<
endef
$(foreach mod,$(KRML_MODS),$(eval $(call KRML_RULE,$(mod))))

clean:
	rm -rf out
