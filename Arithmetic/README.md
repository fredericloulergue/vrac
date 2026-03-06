# RAC of Arithmetic Properties

Formalisation et vérification en Coq d'un vérification d'assertions arithmétiques à l'exécution.

Formalisation et preuve "papier": Thibaut Benjamin, Julien Signoles, Formalizing an Efficient Runtime Assertion Checker for an Arithmetic Language with Functions and Predicates, ACM Symposium on Applied Computing, 2023

## Main Files

- Theorems.v: Main theorems.
- Translation.v: Mini-FSL to Mini-GMP translation.
- Macros.v: Macro definitions, semantics, and lemmas.
- Oracle.v: Oracle signature used for variables value's interval inference.
- Invariants.v : Invariants for routine translation (depends on the oracle).
- Environment.v: Mappings and relations.
