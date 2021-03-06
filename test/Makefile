# ghc=~/bin/new-ghc/ghc
ghc=ghc

shaped = ../../shaped-types
circat = ../../circat

default: go
# default: suite

suite:
	cd .. ; make suite

check-ghc:
	ghc --version

go: Tests Makefile ../dist
	./Tests

plugin=ReificationRules.Plugin

GhcFlags += -fplugin=$(plugin)

GhcFlags += -fexpose-all-unfoldings
GhcFlags += -dcore-lint
GhcFlags += -fforce-recomp
# GhcFlags += -dppr-case-as-let

# GhcFlags += -ddump-simpl

# GhcFlags += -frule-check reify

# GhcFlags += -ddump-simpl-iterations

# GhcFlags += -dshow-passes

# GhcFlags += -ddump-inlinings

GhcFlags += -dsuppress-idinfo
# GhcFlags += -dsuppress-module-prefixes
# GhcFlags += -dsuppress-uniques

# GhcFlags += -dsuppress-type-signatures
# GhcFlags += -dsuppress-type-applications

# GhcFlags += -dsuppress-all

# GhcFlags += -ddump-rule-rewrites

# # Occasionally this one instead (just shows rule names)
# GhcFlags += -ddump-rule-firings

# GhcFlags += -ddump-rules

# GhcFlags += -ddump-spec

# GhcFlags += -ddump-simpl-trace

# GhcFlags += -dverbose-core2core

# GhcFlags += -fprint-explicit-kinds -fprint-equality-relations

GhcFlags += -fsimpl-tick-factor=200

# GhcFlags += -ddump-simpl-stats

# GhcFlags += -funfolding-keeness-factor=0 -funfolding-use-threshold=0

# Specialization blows up transpose code exponentially. Revisit when we reify partially.
GhcFlags += -fno-specialise

# Experiment
GhcFlags += -fno-pre-inlining

# # Trace reification
# GhcFlags += -fplugin-opt=$(plugin):trace

compile=time $(ghc) -O $(GhcFlags)

Tests: ../dist $(circat)/dist $(shaped)/dist Tests.hs Makefile
	$(compile) $@

ReTest: ../dist $(circat)/dist $(shaped)/dist Tests.hs Makefile
	$(compile) $@

# RuleTest: ../dist RuleTest.hs Makefile
# 	$(compile) $@

# RT: ../dist RT.hs Makefile
# 	$(compile) $@

libs: circat shaped compile

shaped:
	cd $(shaped) ; make

compile:
	cd .. ; make

circat:
	cd $(circat) ; make
	make compile

%.iface: %.hi
	$(ghc) --show-iface $*.hi > $*.iface

SHAPED_HI_DIR = ../../shaped-types/dist/build/ShapedTypes

%.iface: $(SHAPED_HI_DIR)/%.hi
	$(ghc) --show-iface $(SHAPED_HI_DIR)/$*.hi > $*.iface

SHAPED_HI_DIR = $(shaped)/dist/build/ShapedTypes

CIRCAT_HI_DIR = $(circat)/dist/build/Circat

HI_DIR = ../dist/build/ReificationRules

%.iface: $(HI_DIR)/%.hi
	$(ghc) --show-iface $(HI_DIR)/$*.hi > $*.iface

# %.iface: $(CIRCAT_HI_DIR)/%.hi
# 	$(ghc) --show-iface $(CIRCAT_HI_DIR)/$*.hi > $*.iface

ifaces: HOS.iface Pair.iface Circuit.iface Rep.iface
