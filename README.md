[中文](./README.zh-CN.md) 👈

# Set-Theory

This project is a Coq formalization of the textbook Elements of Set Theory - Herbert B. Enderton. It is basically written in the order of the textbook, without considering modularity. It is suitable as an aid to the learning of set theory, not as a general mathematical library.

## Build
```
./build_all.sh
```

## ZFC0.v
- Metatheory
  - Law of excluded middle
  - Hilbert's ε-operator
- Axiom of extensionality
- Axiom of empty set
- Axiom of union
- Axiom of power set
- Axiom schema of replacement

## ZFC1.v
- Pair
- Singleton
- Binary union
- Union of a family of sets

## ZFC2.v
- Set comprehension
- Intersaction, binary intersaction
- Ordered pair
- Cartesian product

## ZFC3.v
- Axiom of infinity
- Hilbert's ε-operator implies AC

## EST2.v
- Complement
- Proper subset
- Algebra of sets

## EST3_1.v
- Relation, function
- Inverse, composition

## EST3_2.v
- Injection, surjection, bijection
- Left inverse and right inverse of function
- Restriction, image
- Function space
- Infinite Cartesian product
- AC equivalent form 1: Function has right inverse iff surjective
- AC equivalent form 2: Infinite Cartesian product of nonempty sets is nonempty

## EST3_3.v
- Binary relation
- Equivalence relation, equivalence class, quotient set
- Trichotomy, linear order

## EST4_1.v
- Natural number
- Induction principle
- Transitive set
- Peano structure
- Recursion theorem

## EST4_2.v
- Embedding of type-theoretic nat
- Natural number arithmetic: addition, multiplication, exponentiation

## EST4_3.v
- Linear ordering of ω
- Well ordering of ω
- Strong induction principle

## EST5_1.v
- Integer
- Integer arithmetic: addition, additive inverse

## EST5_2.v
- Multiplication of integers
- Order of integers
- Embedding of the natural numbers

## EST5_3.v
- Rational number
- Rational number arithmetic: addition, additive inverse, multiplication, multiplicative inverse

## EST5_4.v
- Order of rational numbers
- Embedding of the integers
- Algebra regarding to inverse

## EST5_5.v
- Real number (Dedekind cut)
- Order of real numbers
- Completeness of the real numbers
- Real number arithmetic: addition, additive inverse

## EST5_6.v
- Absolute value of real number
- Multiplication of non-negative real numbers
- Multiplicative inverse of positive real number

## EST5_6.v
- Arithmetic of rational numbers: multiplication, multiplicative inverse
- Embedding of the rational numbers
- Density of the real numbers

## EST6_1.v
- Equinumerous
- Cantor's theorem
- Pigeonhole principle
- Finite cardinal

## EST6_2.v
- Infinite cardinal
- Cardinal arithmetic: addition, multiplication, exponentiation

## EST6_3.v
- Dominate
- Schröder–Bernstein theorem
- Order of cardinals
- Aleph Zero

## EST6_4.v
- Systematic discussion on AC
  - Uniformization
  - Choice function
  - Cardinal comparability
  - Zorn's lemma
  - Tukey's lemma
  - Hausdorff maximal principle
- Aleph Zero is the least infinite cardinal
- Dedekind infinite
- Infinite sum of cardinals
- Infinite product of cardinals

## EST6_5.v
- Countable set
  - Countable union of countable sets is countable

## EST6_6.v
- Algebra of infinite cardinals
  - Cardinal multiplied by itself equals to itself
  - Absortion law of cardinal addition and multiplication

## EST7_1.v
- Partial order, linear order
- Minimal, minimum, maximal, maximum
- Bound, supremum, infimum

## EST7_2.v
- Well order
- Transfinite induction principle
- Transfinite recursion theorem
- Transitive closure of set

## EST7_3.v
- Order structure
- Isomorphism
- Epsilon image

## EST7_4.v
- Ordinal
- Order of ordinals
- Burali-Forti's paradox
- Successor ordinal, limit ordinal
- Transfinite induction schema on ordinals

## EST7_5.v
- Hartog's number
- Equivalence between well order theorem, AC and Zorn's lemma
- von Neumann cardinal assignment
- Initial cardinal, successor cardinal

## EST7_6.v
- Transfinite recursion schema on ordinals
- von Neumann universe
- Rank
- Axiom of regularity

## EST8_1.v (TODO)
- Aleph number

## EX{n}.v
- Solution to exercises of Chapter n
