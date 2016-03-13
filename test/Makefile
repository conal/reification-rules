ghc = ~/bin/new-ghc/ghc

default: go

check-ghc:
	ghc --version

go: Tests Makefile ../dist
	./Tests

GhcFlags += -fexpose-all-unfoldings
GhcFlags += -dcore-lint
GhcFlags += -fforce-recomp

# GhcFlags += -ddump-simpl

# GhcFlags += -ddump-simpl-iterations

# GhcFlags += -dshow-passes
# GhcFlags += -ddump-inlinings

GhcFlags += -dsuppress-idinfo
GhcFlags += -dsuppress-module-prefixes
GhcFlags += -dsuppress-uniques

# GhcFlags += -dsuppress-type-signatures
# GhcFlags += -dsuppress-type-applications

# GhcFlags += -dsuppress-all

# GhcFlags += -ddump-rule-rewrites

# GhcFlags += -ddump-rules

# GhcFlags += -ddump-rule-firings
# GhcFlags += -ddump-simpl-trace

# GhcFlags += -dverbose-core2core

GhcFlags += -fprint-explicit-kinds -fprint-equality-relations

Tests: ../dist Tests.hs Makefile
	$(ghc) -O -fplugin=ReificationRules.Plugin $(GhcFlags) $@

RuleTest: ../dist RuleTest.hs Makefile
	$(ghc) -O -fplugin=ReificationRules.Plugin $(GhcFlags) $@

RT: ../dist RT.hs Makefile
	$(ghc) -O -fplugin=ReificationRules.Plugin $(GhcFlags) $@

# -ddump-rule-rewrites

shaped:
	cd ../../shaped-types ; make

compile:
	cd .. ; make

circat:
	cd ../../circat ; make
	make compile

HI_DIR = ../dist/build/ReificationRules

%.iface: $(HI_DIR)/%.hi
	$(ghc) --show-iface $(HI_DIR)/$*.hi > $*.iface

CIRCAT_HI_DIR = ../../circat/dist/build/Circat

%.iface: $(CIRCAT_HI_DIR)/%.hi
	$(ghc) --show-iface $(CIRCAT_HI_DIR)/$*.hi > $*.iface

ifaces: HOS.iface Pair.iface


