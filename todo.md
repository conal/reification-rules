## To-do items

*   Replace `AbsTyImports` with a module that re-exports.


* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *

The code contains several "`TODO`" comments, some of which are also listed below.

*   Factor generated reification rules into `reifyP`-free code (definition) and `reifyP` residuals, to reduce code size and compilation time.
*   Reboxing or handling unboxed types.
*   Improved reifiability test.
    I currently reject a handful of type constructors.
*   Detect whether we'll never be able to complete reification.
*   Simplify generated code, either during or after reification
*   More variable renaming for ease of reading
*   Reify case-of-sum.
*   Restore sums in circat, and do some examples.
*   Pretty-print with layout/indentation
*   Better way to recognize constant expressions of primitive type, to turn them into literals in the reified representation.
*   In `Plugin`, explore adding a stack of unreified arguments.
    When reifying a lambda, try to make a `let`.
    Hm. I don't know how to keep a stack, since I want to reification to work via rewrite rules invoked by the simplifier.
*   Alternatively (I think), try unfolding (inlining application head) earlier.
    Doing so might result in much simpler generated code by avoiding many beta-redexes.
    If I do, take care not to inline "primitives".
    I think it'd be fairly easy.
*   Any other issues mentioned in the "Non-working examples" section of test/Tests.hs.
*   Now that I have *non-recursive* reification working well, consider converting some aspects back to separate, syntax-based rules (with the `RULES` pragma).
*   Simplify *after* reifying.
    Since inlining and case-removal will have happened, I think results will improve.
    If so, do less during reification (including some `let`-avoidance).
*   Eliminate `MonoPrims` in favor of building dictionaries on the fly.

Did:

*   Generate reification code and rules as with lambda-ccc
*   Automated testing.
*   More examples:
    *   Linear algebra: dot product, linear transformation application and composition.
    *   Scan
    *   FFT
    *   Polynomial evaluation
*   Reification breakages:
    *   Unfold reify argument.
    *   `Double`: switch from `Doubli` to `Double` in circat.
*   In `Plugin`, learn how to look up types and tycons directly, as I do with (value) identifiers.
    Then remove the code that extract types and tycons from the types of looked-up identifiers (`expTyFromReifyTy` etc).
