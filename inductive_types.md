```lean
# namespace Hidden
# inductive Nat where
#  | zero : Nat
#  | succ : Nat → Nat
#  deriving Repr
namespace Nat

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

instance : Add Nat where
  add := add

theorem add_zero (m : Nat) : m + zero = m := rfl
theorem add_succ (m n : Nat) : m + succ n = succ (m + n) := rfl

end Nat
# end Hidden
```

```lean
# namespace Hidden
open Nat

theorem zero_add (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := fun x => 0 + x = x) n
    rfl
    (fun n ih => by simp [add_succ, ih])
# end Hidden
```

```lean
open Nat
theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) :=
  Nat.recOn (motive := fun k => m + n + k = m + (n + k)) k
    rfl
    (fun k ih => by simp [Nat.add_succ, ih])
```

```lean
# namespace Hidden
open Nat
theorem succ_add (n m : Nat) : succ n + m = succ (n + m) :=
  Nat.recOn (motive := fun x => succ n + x = succ (n + x)) m
    rfl
    (fun m ih => by simp only [add_succ, ih])

theorem add_comm (m n : Nat) : m + n = n + m :=
  Nat.recOn (motive := fun x => m + x = x + m) n
    (by simp)
    (fun m ih => by simp [add_succ, succ_add, ih])
# end Hidden
```

1. Try defining other operations on the natural numbers, such as
   multiplication, the predecessor function (with ``pred 0 = 0``),
   truncated subtraction (with ``n - m = 0`` when ``m`` is greater
   than or equal to ``n``), and exponentiation. Then try proving some
   of their basic properties, building on the theorems we have already
   proved.

   Since many of these are already defined in Lean's core library, you
   should work within a namespace named ``Hidden``, or something like
   that, in order to avoid name clashes.

2. Define some operations on lists, like a ``length`` function or the
   ``reverse`` function. Prove some properties, such as the following:

   a. ``length (s ++ t) = length s + length t``

   b. ``length (reverse t) = length t``

   c. ``reverse (reverse t) = t``

3. Define an inductive data type consisting of terms built up from the following constructors:

   - ``const n``, a constant denoting the natural number ``n``
   - ``var n``, a variable, numbered ``n``
   - ``plus s t``, denoting the sum of ``s`` and ``t``
   - ``times s t``, denoting the product of ``s`` and ``t``

   Recursively define a function that evaluates any such term with respect to an assignment of values to the variables.

4. Similarly, define the type of propositional formulas, as well as
   functions on the type of such formulas: an evaluation function,
   functions that measure the complexity of a formula, and a function
   that substitutes another formula for a given variable.
