## GHC Core reification via rules

This project contains a Haskell-to-hardware compiler structured as a GHC plugin.

To install, you'll need a few non-Hackage libraries from GitHub:

*   [HERMIT](https://github.com/ku-fpg/hermit)
*   [netlist libs](https://github.com/ku-fpg/netlist)
*   [circat](https://github.com/conal/circat)
*   [shaped-types](https://github.com/conal/shaped-types) (for examples)

## Testing

The easiest way to test is simply `cabal test`.
Edit test/Suite.hs to enable/disable test examples (via un/commenting).

You can do the same by `cd`ing to test/, and typing `make suite`.
Alternatively, in test/, type `make go`, which compiles and runs an example in test/Tests.hs.


