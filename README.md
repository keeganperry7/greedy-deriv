# Lean Formalization of Greedy Regular Expression Matching using Derivatives of Regular Expressions

This repository contains the formalization of a derivative based regular
expression matching engine supporting JavaScript match semantics.

## File Overview
- `Regex`: defines regexes and the derivative based matching algorithm.
- `Greedy`: defines the greedy match semantics, along with proofs for properties
  of the semantics.
- `Locations`: defines locations and spans.
- `Correctness`: proves the equivalence between the derivative matching
  algorithm and the greedy match semantics.
- `Examples`: examples using the matching algorithm.