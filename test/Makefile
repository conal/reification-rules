default: Tests

check-ghc:
	which ghc

go: Tests
	./Tests

Tests: ../dist Tests.hs Makefile
	ghc -O -fforce-recomp -fplugin=ReificationRules.Plugin Tests 

shaped:
	cd ../../shaped-types ; make

compile:
	cd .. ; make

lam:
	cd ../../lambda-ccc ; make
	make compile

circat:
	cd ../../circat ; make
	make mono

extras:
	cd ../../hermit-extras ; make
	make mono

mono:
	cd ../../monomorph ; make
	make lam

unregister-all:
	@echo "Unregistering:"
	@ghc-pkg unregister lambda-ccc    --force || true
	@ghc-pkg unregister monomorph     --force || true
	@ghc-pkg unregister hermit-extras --force || true
	@ghc-pkg unregister circat        --force || true

recompile-all: unregister-all
	cd ../../circat	       ; cabal clean && cabal install
	cd ../../hermit-extras ; cabal clean && cabal install
	cd ../../monomorph     ; cabal clean && cabal install
	cd ..		       ; cabal clean && cabal install
