## GHC Core reification via rules

This project contains a Haskell-to-hardware compiler structured as a GHC plugin.

To install, you'll need a few non-Hackage libraries from GitHub:

*   [HERMIT](https://github.com/ku-fpg/hermit)
*   [netlist libs](https://github.com/ku-fpg/netlist)
*   [circat](https://github.com/conal/circat)
*   [shaped-types](https://github.com/conal/shaped-types) (for examples)

You'll also need [graphviz](http://www.graphviz.org/) for rendering the circuit diagrams. For instance, "brew install graphv" on Mac OS, if you have [homebrew](http://brew.sh/) installed.

## Testing

The easiest way to test is simply `cabal test`. If you're on Mac OS (or another OS that supports "open") and if everything is working, you'll see a displayed PDF. The PDF gets saved in out/. Edit test/Suite.hs to enable/disable test examples (via un/commenting).

You can do the same by `cd`ing to test/, and typing `make suite`.
Alternatively, in test/, type `make go`, which compiles and runs an example in test/Tests.hs. In this case, generated PDFs end up in test/out/. (In general, in ./out/.)

