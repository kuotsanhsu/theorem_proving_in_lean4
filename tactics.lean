/-
1. Go back to the exercises in [Chapter Propositions and
Proofs](./propositions_and_proofs.md) and
[Chapter Quantifiers and Equality](./quantifiers_and_equality.md) and
redo as many as you can now with tactic proofs, using also ``rw``
and ``simp`` as appropriate.
-/

section propositions_and_proofs
section
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  admit
example : p ∨ q ↔ q ∨ p := by
  admit

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  admit
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  admit

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  admit
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  admit

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  admit
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  admit
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  admit
example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  admit
example : ¬(p ∧ ¬p) := by
  admit
example : p ∧ ¬q → ¬(p → q) := by
  admit
example : ¬p → (p → q) := by
  admit
example : (¬p ∨ q) → (p → q) := by
  admit
example : p ∨ False ↔ p := by
  admit
example : p ∧ False ↔ False := by
  admit
example : (p → q) → (¬q → ¬p) := by
  admit
end

section
open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  admit
example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  admit
example : ¬(p → q) → p ∧ ¬q := by
  admit
example : (p → q) → (¬p ∨ q) := by
  admit
example : (¬q → ¬p) → (p → q) := by
  admit
example : p ∨ ¬p := by
  admit
example : (((p → q) → p) → p) := by
  admit
end

/-
Prove ``¬(p ↔ ¬p)`` without using classical logic.
-/
example : ¬(p ↔ ¬p) := by
  admit
end propositions_and_proofs

section quantifiers_and_equality
section
open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := by
  admit
example (a : α) : r → (∃ x : α, r) := by
  admit
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  admit
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  admit

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  admit
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
  admit
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  admit
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
  admit

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
  admit
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
  admit
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
  admit
end

section
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  admit
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  admit
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  admit
end

section
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := by
  admit
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  admit
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  admit
end

section
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
  admit
end
end quantifiers_and_equality

/-
2. Use tactic combinators to obtain a one line proof of the following:
-/

example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  admit
