# Finite

This is a small library for working with finite sets, based on some of the constructs in [\[1\]][1]: a set is considered finite if there's a list that can be shown to contain all of its elements. A form of the finite pigeonhole theorem is implemented in [`Finite.Pigeonhole`](src/Finite/Pigeonhole.agda) (with code based on [\[2\]][2]): any vector of length `n` with elements drawn from a finite set with cardinality less than `n` must have at least one element at two different indices.

1. [Dependently Typed Programming with Finite Sets (Denis Firsov & Tarmo Uustalu, Institute of Cybernetics at Tallinn University of Technology)][1]
2. https://github.com/effectfully/random-stuff/blob/master/pigeonhole.agda

[1]: http://firsov.ee/finset/finset.pdf
[2]: https://github.com/effectfully/random-stuff/blob/master/pigeonhole.agda

# How to build
Building requires the [Agda standard library](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Libraries.StandardLibrary) to be installed and associated with the name `standard-libarary` in an Agda [`libraries` file](http://agda.readthedocs.io/en/v2.5.3/tools/package-system.html).

This code has been tested against Agda version 2.5.4 and standard library version 0.16.
