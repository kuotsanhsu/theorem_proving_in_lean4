1. Go back to the exercises in [Chapter Propositions and
Proofs](./propositions_and_proofs.md) and
[Chapter Quantifiers and Equality](./quantifiers_and_equality.md) and
redo as many as you can now with tactic proofs, using also ``rw``
and ``simp`` as appropriate.

2. Use tactic combinators to obtain a one line proof of the following:

```lean
example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  admit
```
