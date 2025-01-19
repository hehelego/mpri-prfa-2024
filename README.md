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
2. **WIP** Hilbert systems and combinatory logic
    - formalizing one Hilbert style proof system for minimal logic
    - demonstrating that the Hilbert system and minimal logic have the same provability power.
    - encoding SKI combinators in the system
3. Mini projects
