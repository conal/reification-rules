ghc = ~/bin/new-ghc/ghc

default: Tests

check-ghc:
	ghc --version

go: Tests
	./Tests

GhcFlags += -dcore-lint
GhcFlags += -fforce-recomp
GhcFlags += -ddump-simpl

GhcFlags += -dsuppress-idinfo
GhcFlags += -dsuppress-module-prefixes
# GhcFlags += -dsuppress-type-signatures
GhcFlags += -dsuppress-uniques

GhcFlags += -ddump-rule-rewrites
GhcFlags += -ddump-rule-firings

GhcFlags += -dverbose-core2core

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

