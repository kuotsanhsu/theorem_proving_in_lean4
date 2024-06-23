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
  constructor <;> intro ⟨h, k⟩ ; solve_by_elim*
example : p ∨ q ↔ q ∨ p := by
  constructor <;> intro h <;> cases h ; solve_by_elim* [Or.inr]

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  constructor
  . intro ⟨⟨hp, hq⟩, hr⟩ ; solve_by_elim
  . intro ⟨hp, hq, hr⟩ ; solve_by_elim
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  constructor
  . intro | .inl (.inl _) | .inl (.inr _) | .inr _ => solve_by_elim [Or.inr]
  . intro | .inl _ | .inr (.inl _) | .inr (.inr _) => solve_by_elim [Or.inr]

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  . intro ⟨hp, h⟩ ; cases h ; solve_by_elim* [Or.inr]
  . intro | .inl h | .inr h => cases h ; solve_by_elim [Or.inr]
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  constructor
  . intro | .inl _ | .inr ⟨_, _⟩ => solve_by_elim [Or.inr]
  . intro ⟨h, k⟩ ; cases h <;> cases k ; solve_by_elim* [Or.inr]

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  constructor
  . intro _ ⟨_, _⟩ ; solve_by_elim
  . intros ; solve_by_elim
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  constructor
  . intros ; constructor ; solve_by_elim* [Or.inr]
  . intro ⟨_, _⟩ h ; cases h ; solve_by_elim*
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  constructor
  . intros ; constructor ; solve_by_elim* [Or.inr]
  . intro ⟨_, _⟩ h ; cases h <;> contradiction
example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro h ⟨_, _⟩ ; cases h <;> contradiction
example : ¬(p ∧ ¬p) := by
  intro ⟨_, _⟩ ; contradiction
example : p ∧ ¬q → ¬(p → q) := by
  intro ⟨_, _⟩ _ ; solve_by_elim
example : ¬p → (p → q) := by
  intro _ _ ; contradiction
example : (¬p ∨ q) → (p → q) := by
  intro h _ ; cases h <;> solve_by_elim
example : p ∨ False ↔ p := by
  simp
example : p ∧ False ↔ False := by
  simp
example : (p → q) → (¬q → ¬p) := by
  intro h hnq hp ; solve_by_elim
end

section
open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro h ; by_cases q
  case pos hq => left ; solve_by_elim
  case neg hnq => right ; intro hp ; cases h hp <;> solve_by_elim
example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro h ; by_cases p
  case neg => solve_by_elim
  case pos hp => right ; intro ; apply h ; solve_by_elim
example : ¬(p → q) → p ∧ ¬q := by
  intro h ; by_cases p <;> constructor <;> try solve_by_elim
  . exfalso ; apply h ; intro ; contradiction
example : (p → q) → (¬p ∨ q) := by
  intro h ; by_cases p
  . right ; solve_by_elim
  . left ; assumption
example : (¬q → ¬p) → (p → q) := by
  intro h hp ; false_or_by_contra ; solve_by_elim
example : p ∨ ¬p := by
  exact em p
example : (((p → q) → p) → p) := by
  intro h ; by_cases p
  . assumption
  . apply h ; intro ; contradiction
end

/-
Prove ``¬(p ↔ ¬p)`` without using classical logic.
-/
example : ¬(p ↔ ¬p) := by
  intro h ; cases h ; suffices ¬p by solve_by_elim
  solve_by_elim
end propositions_and_proofs

section quantifiers_and_equality
section
open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := by
  intro ⟨x, hr⟩ ; exact hr
example (a : α) : r → (∃ x : α, r) := by
  solve_by_elim
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  constructor
  case mp => intro ⟨x, hpx, hr⟩ ; solve_by_elim
  case mpr => intro ⟨⟨x, hpx⟩, hr⟩ ; solve_by_elim
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  constructor
  case mp => intro
    | ⟨x, .inl hp⟩ => solve_by_elim
    | ⟨x, .inr hq⟩ => right ; solve_by_elim
  case mpr => intro
    | .inl ⟨x, hp⟩ => solve_by_elim
    | .inr ⟨x, hq⟩ => constructor ; right ; exact hq

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  constructor
  case mp => intro h ⟨x, k⟩ ; solve_by_elim
  case mpr => intro h x ; false_or_by_contra ; solve_by_elim
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
  constructor
  case mp => intro ⟨x, h⟩ k ; solve_by_elim
  case mpr => intro h ; false_or_by_contra ; apply h ; intro x h ; solve_by_elim
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  constructor
  case mp => intro h x ; solve_by_elim
  case mpr => intro h ⟨x, k⟩ ; solve_by_elim
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
  constructor
  case mpr => intro ⟨x, h⟩ k ; solve_by_elim
  case mp =>
    intro h ; false_or_by_contra ; apply h
    intro x ; false_or_by_contra ; solve_by_elim

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
  constructor
  case mp => intro h ⟨x, k⟩ ; solve_by_elim
  case mpr => intro h x k ; solve_by_elim
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
  constructor
  case mp => intro ⟨x, h⟩ k ; solve_by_elim
  case mpr =>
    intro h ; false_or_by_contra ; apply_assumption ; apply Exists.intro a
    intro ; apply h
    intro x ; false_or_by_contra ; apply_assumption ; apply Exists.intro x
    intro ; contradiction
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
  constructor
  case mp => intro ⟨x, h⟩ hr ; solve_by_elim
  case mpr =>
    intro h ; by_cases ∃ x, p x
    case pos k => cases k ; solve_by_elim
    case neg k' => apply Exists.intro a ; intro hr ; solve_by_elim
end

section
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  constructor
  case mpr => intro ⟨hp, hq⟩ x ; solve_by_elim
  case mp =>
    intro h ; constructor
    case left => intro x ; apply And.left ; apply h
    case right => intro x ; apply And.right ; apply h
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro h hp x ; solve_by_elim
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro
  | .inl hp, x => left ; apply hp
  | .inr hq, x => right ; apply hq
end

section
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := by
  intro a ; constructor <;> solve_by_elim
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  constructor
  case mpr => intro
    | .inl h, _ => left ; apply h
    | .inr hr, _ => right ; exact hr
  case mp =>
    intro h ; by_cases r
    case pos hr => right ; exact hr
    case neg => left ; intro x ; cases h x <;> solve_by_elim
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  constructor
  case mp => intro h hr x ; solve_by_elim
  case mpr => intro h x hr ; solve_by_elim
end

section
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
  cases h barber
  suffices shaves barber barber by solve_by_elim
  solve_by_elim
end
end quantifiers_and_equality

/-
2. Use tactic combinators to obtain a one line proof of the following:
-/

example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  and_intros ; repeat (first | left ; assumption | right | assumption)
