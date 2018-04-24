The FPC kernel extended with copy-clauses

This supports outer-deskolemization and other client/kernel term
rewriting techniques.

----

Accompanying paper:

Kaustuv Chaudhuri, Matteo Manighetti, Dale Miller, "A proof-theoretic
approach to certifying deskolemization", 2018.
http://chaudhuri.info/papers/draft18skolem.pdf

----

# Contents of the repository

### General utilities

- Makefile
- lib.mod
- lib.sig

### Basic support for logic and the kernel

- classical.mod
- classical.sig
- lkf-certificates.sig
- lkf-formulas.mod
- lkf-formulas.sig
- lkf-kernel.mod
- lkf-kernel.sig

### Example 1: Geometric axioms

- geo-fpc.mod
- geo-fpc.sig
- geo-examples.mod
- geo-examples.sig

### Example 2: Expansion trees

- exp-fpc.mod
- exp-fpc.sig
- exp-examples.mod
- exp-examples.sig
