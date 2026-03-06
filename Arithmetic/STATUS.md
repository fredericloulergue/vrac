# Current Progress

## Languages (Appendix A & B)

- Syntax and semantics defined for all three languages.

- No semantics defined for a complete program, yet required to state some theorems.

- Mini-C syntax and semantics are parameterized inductive datatypes. They contain an extra constructor to enrich it with Mini-FSL and Mini-GMP constructors.

- Because predicate and terms are mutually defined, they require a custom induction principle.

- Unclear how to clearly define what a well-formed program is.

|  Languages | Mini-C | Mini-GMP | Mini-FSL
| :----: | :----: | :------: | :----: |
| **Syntax** |$\checkmark$ |$\checkmark$ |$\checkmark$ |
| **Semantics** |$\checkmark$ |$\checkmark$ |$\checkmark$ |


## Environment

- Mix of *MSets* and *MMaps* and handwritten code.

### Machine Integers

- Encoded as a dependent sum type (the integer and a proof it is within bounds).

### Oracle

 - The article states that the oracle must have a convergence property for predicates, but the oracle domain is over terms, not predicates.

### Partial Order

- Tweaked version (i.e. null pointers must stay null) with isomorphism on the mpz adresses.
- One variant with stronger constraints on $\Omega$: two environments are in relation iff any assigned variable in the first stays the same in the second (up to isomorphism).


### Weakening Lemmas (Appendix C)

N/A : Non-Applicable
N/P : Non-Provable

| Lemmas / Languages | Mini-C | Mini-GMP |
| :----------------: | :----: | :------: | 
| **C.1**            | $\checkmark$ | N/A |
| **C.1-3 (strong)** | $\checkmark$ | N/A |
| **C.2.1**          | $\approx$ 90% | N/P |
| **C.2.1 (strong)** | $\times$ | $\approx$ 40% |
| **C.2.2**          |$\approx$ 60% | N/P |
| **C.2.2 (strong)** | $\times$ | $\times$ |
| **C.2.3** | N/P | N/P |
| **C.2.3 (strong)** | $\approx$ 90% | $\approx$ 90%  |


## Translation

- Fully written using *coq-equations*, but a proof of termination remains.

- The translation is a functor taking an *Oracle* as parameter.

- It uses a *State* monad for fresh variables. The lack of a *Maybe* monad requires proving definitions and variables look-up never fail (i.e. *fenv_build* contains all declarations and *fst g* contains all declared variables).

- The article's translation uses a *scope* syntax allowing to have declarations and instructions for the asserts. It has not been mentioned in the syntax. It is not possible to add a scope constructor in mini-gmp because the more general mini-c+mini_gmp syntax must be allowed inside. So, the constructor is added to mini-c itself.





### Structural Properties (Appendix D)

- Those lemmas are very hard to state by themselves. It is better to wait until they are needed to see how to proceed.

| Theorems | Status |
| :-----: | :----: |
| D.1| $\times$ |
| D.2 | $\times$ |
| D.3 | $\times$ |
| D.4 | $\times$ |
| D.5 | $\times$ |
| D.6.1 | $\times$ |
| D.6.2 | $\times$ |

### Macro Proofs (Appendix E)

Footnotes are additional required assumptions not present in the paper.

| Theorems | Status |
| :-----: | :----: |
| E.1| $\checkmark$ |
| E.2 | $\checkmark$ |
| E.3 | $\checkmark$ |
| E.4 | $\checkmark$[^1][^2] |
| E.5 ($\tau$ = int) | $\checkmark$ [^1] [^2] |
| E.5 ($\tau$ = mpz) | $\checkmark$ [^2] |

[^1]: c must be a machine integer.
[^2]: Two different variables cannot hold the same pointer. The variable v1 cannot be used inside the expression e2. v1 and v2 must be different.

### Invariants (Appendix F)

- All invariants stated.

- The first case of the notation introduced implies being able to tell if $z \in U_{int}$ and convert it into a machine integer. How to encode that ?

- The oracle only infers interval for a term, but the suitability invariant assumes it works for predicates. Also, for any $p$ and $\Gamma_I$, wouldn't $\mathcal{T}(p,\Gamma_I)$ always return $int$?

### Semantics Preservation (Appendix G)

- Depends on being able to use the functional induction principle *coq-equations* generates. After many trial and error, it is generated, but it is non-trivial to use it. This is because of the 3-way mutual recursion.


| Theorems | Status |
| :-----: | :----: |
| G.1| $\times$ |
| G.2 | $\times$ |
| G.3 | $\times$ |
| G.4 | $\times$ |
| G.5 | $\times$ |
