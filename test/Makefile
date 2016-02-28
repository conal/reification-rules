ghc = ~/bin/new-ghc/ghc

default: Tests

check-ghc:
	ghc --version

go: Tests Makefile ../dist
	./Tests

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

GhcFlags += -ddump-rule-rewrites
# GhcFlags += -ddump-rule-firings
# GhcFlags += -ddump-simpl-trace

# GhcFlags += -dverbose-core2core

Tests: ../dist Tests.hs Makefile
	$(ghc) -O -fplugin=ReificationRules.Plugin $(GhcFlags) Tests 

# -ddump-rule-rewrites

shaped:
	cd ../../shaped-types ; make

compile:
	cd .. ; make

circat:
	cd ../../circat ; make
	make compile

