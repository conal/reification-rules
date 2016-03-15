## To-do items

The code contains several "`TODO`" comments, some of which are also listed below.


*   In `Plugin`, add and stack of unreified arguments.
    When reifying a lambda, try to make a `let`.
*   Reification breakages:
    *   Unfold reify argument.
    *   `Double`: switch from `Doubli` to `Double` in circat.
*   Any other issues mentioned in the "Non-working examples" section of test/Tests.hs.
*   Now that I have *non-recursive* reification working well, consider converting some aspects back to separate, syntax-based rules (with the `RULES` pragma).
*   In `Plugin`, learn how to look up types and tycons directly, as I do with (value) identifiers.
    Then remove the code that extract types and tycons from the types of looked-up identifiers (`expTyFromReifyTy` etc).

