## Some desirable abstract properties of Maker

1. Minted dai and `woe` are correctly balanced

2. `chi` global accumulator method is equivalent to the naive calculation.

3. `rpow` is approximately correct (found error bounds!)

4. All time-evolution which depends on `rpow` is therefore also approximately correct (find error bounds!)

5. `frob` mechanics are safe, for example:
a. the `lad` can only trade with the system at worse than the `mat`-rate if the `cup` ends up safe.
b. if the `cup` starts and ends unsafe, then the `lad` can only trade with the system at above the `mat`-rate.
c. any `frob` can be expressed as a composition of finitely many operations taken from `lock`, `free`, `draw`, and `wipe`. This is actually false with the previous version, but will probably be true in the future version.
d. ?

6. `frob` rounding is safe for the system, regardless of gas price available to attacker (I would very much like this to be true, though it isn't at the moment I think...).

## Some desirable properties that are not-core

1. `vox` is correct
a. `par` is approximately correct, and all time-evolution which depends on `par` is therefore also approximately correct (find error bounds!)
b. `way` is approximately correct, which depends on the approximation `1 - 1/(1 - x) ≈ x` for small `x`, equivalently `1/y ≈ y` for `y` close to 1. Moreover, we have to assume that `prod` happens reasonably often, and the error will depend on the (in)frequency! (find error bounds!)
c. All time-evolution which depends on `par` is therefore approximately correct (find error bounds!)