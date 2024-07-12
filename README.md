# Finite

This is a small library for working with finite sets, based on some of the constructs in [\[1\]][1]: a set is considered finite if there's a list that can be shown to contain all of its elements. A form of the finite pigeonhole theorem is implemented in [`Finite.Pigeonhole`](src/Finite/Pigeonhole.agda): any vector of length `n` with elements drawn from a finite set with cardinality less than `n` must contain at least one element that occurs at least twice.

1. [Dependently Typed Programming with Finite Sets (Denis Firsov & Tarmo Uustalu, Institute of Cybernetics at Tallinn University of Technology)][1]

[1]: http://firsov.ee/finset/finset.pdf

# How to build
Building requires the [Agda standard library](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Libraries.StandardLibrary) to be installed and associated with the name `standard-libarary` in an Agda [`libraries` file](http://agda.readthedocs.io/en/v2.5.3/tools/package-system.html).

This code is tested against development versions of the Agda compiler and standard library, and was last tested working on July 11, 2024.
