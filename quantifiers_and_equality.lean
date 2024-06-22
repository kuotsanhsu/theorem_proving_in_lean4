/-
What follows are some common identities involving the existential
quantifier. In the exercises below, we encourage you to prove as many
as you can. We also leave it to you to determine which are
nonconstructive, and hence require some form of classical reasoning.
-/

section
open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := fun ⟨_, hr⟩ => hr
example (a : α) : r → (∃ x : α, r) := (⟨a, ·⟩)
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  ⟨fun ⟨x, h, hr⟩ => ⟨⟨x, h⟩, hr⟩, fun ⟨⟨x, h⟩, hr⟩ => ⟨x, h, hr⟩⟩
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  ⟨fun ⟨x, h⟩ => h.rec (.inl ⟨x, ·⟩) (.inr ⟨x, ·⟩),
    Or.rec (fun ⟨x, h⟩ => ⟨x, .inl h⟩) (fun ⟨x, h⟩ => ⟨x, .inr h⟩)⟩

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  ⟨fun h ⟨x, k⟩ => k (h x), (byContradiction fun k => · ⟨·, k⟩)⟩
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  ⟨fun ⟨x, h⟩ k => k x h, (byContradiction fun k => · (k ⟨·, ·⟩))⟩
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  ⟨(· ⟨·, ·⟩), fun h ⟨x, k⟩ => h x k⟩
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := Iff.symm
  ⟨fun ⟨x, h⟩ k => h (k x), fun h => byContradiction fun k =>
    h fun x => byContradiction (k ⟨x, ·⟩)⟩

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  ⟨fun h ⟨x, k⟩ => h x k, (· ⟨·, ·⟩)⟩
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  ⟨fun ⟨x, h⟩ k => h (k x), fun h => byContradiction fun k =>
    k ⟨a, fun _ => h fun x => byContradiction (k ⟨x, False.rec ∘ ·⟩)⟩⟩
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  ⟨fun ⟨x, h⟩ k => ⟨x, h k⟩,
    fun h => byCases (fun ⟨x, k⟩ => ⟨x, fun _ => k⟩) (⟨a, False.rec ∘ · ∘ h⟩)⟩
end

/-
1. Prove these equivalences:
-/

section
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  ⟨fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩, fun h x => ⟨h.1 x, h.2 x⟩⟩
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := fun h k x => h x (k x)
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := Or.rec (.inl <| · ·) (.inr <| · ·)
end

/-
You should also try to understand why the reverse implication is not derivable in the last example.

2. It is often possible to bring a component of a formula outside a
   universal quantifier, when it does not depend on the quantified
   variable. Try proving these (one direction of the second of these
   requires classical logic):
-/

section
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := (⟨letFun ·, (fun _ => ·)⟩)
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  ⟨fun h => Classical.byCases .inr fun k => .inl (Or.rec id (absurd · k) <| h ·),
    fun h x => h.rec (.inl <| · x) .inr⟩
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := ⟨(fun x => · x ·), (fun hr => · hr ·)⟩
end

/-
3. Consider the "barber paradox," that is, the claim that in a certain
   town there is a (male) barber that shaves all and only the men who
   do not shave themselves. Prove that this is a contradiction:
-/

section
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  (h barber).rec (have (h) := · h h ; this <| · this)
end

/-
4. Remember that, without any parameters, an expression of type
   ``Prop`` is just an assertion. Fill in the definitions of ``prime``
   and ``Fermat_prime`` below, and construct each of the given
   assertions. For example, you can say that there are infinitely many
   primes by asserting that for every natural number ``n``, there is a
   prime number greater than ``n``. Goldbach's weak conjecture states
   that every odd number greater than 5 is the sum of three
   primes. Look up the definition of a Fermat prime or any of the
   other statements, if necessary.
-/

section
def even (n : Nat) : Prop := ∃ m : Nat, m + m = n

def prime (n : Nat) : Prop := ∀ m k : Nat, m * k = n → m = 1 ∨ k = 1

private def inifinitely_many (h : Nat → Prop) : Prop := ∀ n : Nat, ∃ p : Subtype h, n ≤ p

def infinitely_many_primes : Prop := inifinitely_many prime

def Fermat_prime (n : Nat) : Prop := prime n ∧ ∃ m : Nat, 2^2^m + 1 = n

def infinitely_many_Fermat_primes : Prop := inifinitely_many Fermat_prime

def goldbach_conjecture : Prop :=
  ∀ n : Nat, even n ∧ 2 < n → ∃ a b : Subtype prime, a + b = n

def Goldbach's_weak_conjecture : Prop :=
  ∀ n : Nat, ¬even n ∧ 5 < n → ∃ a b c : Subtype prime, a + b + c = n

def Fermat's_last_theorem : Prop :=
  ∀ n : Nat, 2 < n → ¬∃ a b c : Nat, 0 < a ∧ 0 < b ∧ 0 < c ∧ a^n + b^n = c^n
end

/-
5. Prove as many of the identities listed in the Existential
   Quantifier section as you can.
-/
