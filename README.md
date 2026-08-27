# Formalization of the solution to the Hopf problem

The six-sphere admits a complex manifold structure compatible with its standard topology.

Based on [*A compact complex threefold fibred by tori over the projective line, and the six-sphere*](https://alpo.ge/s6.pdf), originally [shared on X](https://x.com/__alpoge__/status/2091639597193368014) by [Levent Alpöge](https://alpo.ge/).

The repository includes a Comparator setup, with the statement adapted from the [Formal Conjectures project](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Mathoverflow/1973.lean).

```sh
lake update
lake exe cache get
lake build lean4export
lake exe comparator comparator/config.json
```

[Type-check it online!](https://live.lean-lang.org/#project=mathlib-stable&url=https%3A%2F%2Fraw.githubusercontent.com%2Fplby%2FHopfProblem%2Frefs%2Fheads%2Fmaster%2FSolution.lean)
