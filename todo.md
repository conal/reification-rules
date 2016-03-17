## To-do items

The code contains several "`TODO`" comments, some of which are also listed below.

*   In `Plugin`, explore adding a stack of unreified arguments.
    When reifying a lambda, try to make a `let`.
*   Alternatively (I think), try unfolding (inlining application head) earlier.
    Doing so might result in much simpler generated code by avoiding many beta-redexes.
    If I do, take care not to inline "primitives".
    I think it'd be fairly easy.
*   Reification breakages:
    *   Unfold reify argument.
    *   `Double`: switch from `Doubli` to `Double` in circat.
*   Any other issues mentioned in the "Non-working examples" section of test/Tests.hs.
*   Now that I have *non-recursive* reification working well, consider converting some aspects back to separate, syntax-based rules (with the `RULES` pragma).
*   In `Plugin`, learn how to look up types and tycons directly, as I do with (value) identifiers.
    Then remove the code that extract types and tycons from the types of looked-up identifiers (`expTyFromReifyTy` etc).
*   Simplify *after* reifying.
    Since inlining and case-removal will have happened, I think results will improve.
    If so, do less during reification (including some `let`-avoidance).
