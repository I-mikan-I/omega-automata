# ω-Automata

This rust library implements decision procedures and algorithms on
__omega-automata__. __Omega-automata__ are similar to the better-known finite
automata (NFA/DFA/...) except they operate on *infinite* words. They are
commonly used to model systems that can run for an infinite time, such as most
algorithms, protocols, and more.

For example, model checking temporal logic properties (commonly used in formal
hardware verification) can be implemented with an optimal worst-case time
complexity via omega automata.

## Features

Currently, this crate supports the following:

- LTL to VWABW (*very weak alternating büchi automata*) translation.
- VWABW to GBW (*generalized büchi automata*) translation.

## Planned features

- GBW to NBW (*non-deterministic büchi automata*) translation.
- NBW emptiness check.

With the planned features, it will be possible to check LTL formulas for
satisfiability.


## Resources

1. [Clarke et al. *Handbook of Model Checking*](https://doi.org/10.1007/978-3-319-10575-8)
2. [Gastin and Oddoux *Fast LTL to Büchi Automata Translation*](https://doi.org/10.1007/3-540-44585-4_6)