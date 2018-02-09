# Finite

This is a small library for working with finite sets, based on some of the constructs in [\[1\]][1]: a set is considered finite if there's a list that can be shown to contain all of its elements. A form of the finite pigeonhole theorem is implemented in [`Finite.Pigeonhole`](src/Finite/Pigeonhole.agda) (with code based on [\[2\]][2]): any vector that has more elements than the total number in a finite set must have at least one element at two different indices.

1. [Dependently Typed Programming with Finite Sets (Denis Firsov & Tarmo Uustalu, Institute of Cybernetics at Tallinn University of Technology][1]
2. https://github.com/effectfully/random-stuff/blob/master/pigeonhole.agda

[1]: http://firsov.ee/finset/finset.pdf
[2]: https://github.com/effectfully/random-stuff/blob/master/pigeonhole.agda

# How to build
Building requires the Agda standard library to be installed and associated with the name `standard-libarary` in an Agda [`defaults` file](http://agda.readthedocs.io/en/v2.5.3/tools/package-system.html).
