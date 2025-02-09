# Consistency of classical propositional natural deduction

My solution to the MPRI Proof assistants (PRFA 2-7-2) course project, but in Agda

- [course webpage](https://mpri-prfa.github.io/)
- [task specifications. year 2024](https://mpri-prfa.github.io/2024/project24.pdf)

## build environment

- Agda version 2.6.3
- agda-stdlib 2.1

## progress

1. **DONE** Natural deduction for classical and minimal propositional logic
    - formalizing the natural deduction systems for classical logic and minimal logic
    - proving one crucial structural rule: weakening
    - Friedman's translation (encoding double negation elimination in minimal logic)
    - deriving that ground formula are equally provable in classical logic and minimal logic
2. **DONE** Hilbert systems and combinatory logic
    - formalizing one Hilbert style proof system for minimal logic
    - demonstrating that the Hilbert system and minimal logic have the same provability power
    - encoding the SKI combinatory logic in the system
    - proving that terms in combinatory logic can be regarded as proof terms of the Hilbert system
    - formalizing the subject reduction property, the preservation property, and the progress property of the combinatory logic
    - defining a semantic typing relation (a logical relation) that captures the normalisation property of terms
    - deriving the result that all closed and well-type terms are in the logical relation
    - demonstrating that no term has the bottom type
    - proving the consistency of proof systems
3. **TODO** Mini projects
    - simplify proofs
    - enriching the syntactic constructions of well-formed formulas
    - showing the decidability of classical natural deduction by defining a sound and complete boolean semantics
    - using simply typed lambda calculus as proof terms for the minimal logic
    - showing the decidability of STLC type checking
    - devising a simulation relation between STLC and combinatory logic
    - introducing reflection techniques in proofs
