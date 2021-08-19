# Overlapping and Order-Independent Patterns

The ideas in this directory are based mainly on the paper [Overlapping and Order-Independent Patterns
Definitional Equality for All](https://link.springer.com/content/pdf/10.1007%2F978-3-642-54833-8_6.pdf)

In short, from now on we have two kinds of pattern matching: the usual one with _first-match_ semantics and the new one, in which patterns can be _overlapping_ and whose semantics don't depend on the _order_ in which the patterns appear in code.

With this, we may get more definitional equalities for free. For example, besides the usual `0 + n = n` and `s n + m = s (n + m)` we can also have `n + 0 = n` and `n + s m = s (n + m)`. This greatly reduces the number of rewrites we need to do in proofs and makes dependently-typed programming much easier in some cases (like `v ++ []` now being of type `Vec A n` instead of `Vec A (n + 0)`).