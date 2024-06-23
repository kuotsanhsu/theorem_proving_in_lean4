namespace Hidden
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
  deriving Repr

namespace Nat
def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

instance : Add Nat where
  add := add

theorem add_zero (m : Nat) : m + zero = m := rfl
theorem add_succ (m n : Nat) : m + succ n = succ (m + n) := rfl

instance : OfNat Nat 0 where
  ofNat := zero

theorem zero_add (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := fun x => 0 + x = x) n
    rfl
    (fun n ih => by simp [add_succ, ih])

theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) :=
  Nat.recOn (motive := fun k => m + n + k = m + (n + k)) k
    rfl
    (fun k ih => by simp [Nat.add_succ, ih])

theorem succ_add (n m : Nat) : succ n + m = succ (n + m) :=
  Nat.recOn (motive := fun x => succ n + x = succ (n + x)) m
    rfl
    (fun m ih => by simp only [add_succ, ih])

theorem add_comm (m n : Nat) : m + n = n + m :=
  Nat.recOn (motive := fun x => m + x = x + m) n
    (zero_add m).symm
    (fun m ih => by simp [add_succ, succ_add, ih])
end Nat
end Hidden

/-
1. Try defining other operations on the natural numbers, such as
   multiplication, the predecessor function (with ``pred 0 = 0``),
   truncated subtraction (with ``n - m = 0`` when ``m`` is greater
   than or equal to ``n``), and exponentiation. Then try proving some
   of their basic properties, building on the theorems we have already
   proved.

   Since many of these are already defined in Lean's core library, you
   should work within a namespace named ``Hidden``, or something like
   that, in order to avoid name clashes.
-/

namespace Hidden.Nat
instance : OfNat Nat 1 where
  ofNat := succ 0
instance : OfNat Nat 2 where
  ofNat := succ 1

def mul (n : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => n + mul n m
instance : Mul Nat where
  mul := mul

def pred : Nat → Nat
  | 0 => 0
  | n + 1 => n
example : pred 0 = 0 := rfl
example : pred 1 = 0 := rfl
example : pred 2 = 1 := rfl

def sub : Nat → Nat → Nat
  | 0, _ => 0
  | n@(_ + 1), 0 => n
  | n + 1, m + 1 => sub n m
instance : Sub Nat where
  sub := sub
example : 0 - 0 = 0 := rfl
example : 1 - 0 = 1 := rfl
example : 0 - 1 = 0 := rfl
example : 1 - 1 = 0 := rfl
example : 1 - 2 = 0 := rfl
example : 2 - 1 = 1 := rfl

def pow (n : Nat) : Nat → Nat
  | 0 => 1
  | m + 1 => n * pow n m
instance : Pow Nat Nat where
  pow := pow

theorem mul_succ (a b : Nat) : a * b.succ = a + a * b := rfl
theorem succ_mul (a b : Nat) : a.succ * b = a * b + b := by
  induction b with
  | zero => rfl
  | succ b h => rw [mul_succ, mul_succ, h, succ_add, add_succ, add_assoc]
theorem zero_mul (a : Nat) : zero * a = zero := by
  induction a with
  | zero => rfl
  | succ a h => rw [mul_succ, h] ; rfl
theorem mul_comm (a b : Nat) : a * b = b * a := by
  induction b with
  | zero => rw [zero_mul] ; rfl
  | succ b h => rw [mul_succ, succ_mul, h, add_comm]
theorem add_mul (a b c : Nat) : (a + b) * c = a * c + b * c := by
  induction c with
  | zero => rfl
  | succ c h => simp [mul_succ, h]
                conv =>
                  lhs ; rw [←add_assoc]
                  lhs ; rw [add_assoc, add_comm b _, ←add_assoc]
                rw [add_assoc]
theorem mul_add (a b c : Nat) : a * (b + c) = a * b + a * c := by
  rw [mul_comm, add_mul, mul_comm, mul_comm c]
theorem mul_assoc (a b c : Nat) : a * b * c = a * (b * c) := by
  induction c with
  | zero => rfl
  | succ c h => rw [mul_succ, mul_succ, mul_add, h]

local notation a "²" => a^(2:Nat)
theorem square (a : Nat) : a * a = a² := rfl
theorem double (a : Nat) : a + a = 2 * a := by rw [mul_comm] ; rfl

example (a b : Nat) : (a + b)² = a² + 2 * a * b + b² :=
  calc (a + b) * (a + b)
   _ = a * (a + b) + b * (a + b) := by rw [add_mul]
   _ = a² + (a * b + b * a) + b² := by simp [mul_add, add_assoc, square]
   _ = a² + 2 * a * b + b² := by rw [mul_comm b, double, mul_assoc]

end Hidden.Nat

/-
2. Define some operations on lists, like a ``length`` function or the
   ``reverse`` function. Prove some properties, such as the following:

   a. ``length (s ++ t) = length s + length t``

   b. ``length (reverse t) = length t``

   c. ``reverse (reverse t) = t``
-/

section
def length : List α → Nat
  | [] => 0
  | a::as => length as + 1

def reverse : List α → List α
  | [] => []
  | a::as => (reverse as).concat a

theorem length_append : length (s ++ t) = length s + length t :=
  match s with
  | [] => (Nat.zero_add _).symm
  | a::s => show length (s ++ t) + 1 = length s + 1 + length t by
    rw [length_append, Nat.add_assoc, Nat.add_comm _ 1, Nat.add_assoc]

theorem length_reverse : length (reverse t) = length t :=
  match t with
  | [] => rfl
  | a::s => show length ((reverse s).concat a) = length s + 1 by
    rw [length_concat, length_reverse]
where length_concat {α a} : {as : List α} → length (as.concat a) = length as + 1
  | [] => rfl
  | b::bs => show length (bs.concat a) + 1 = length bs + 1 + 1 by
    rw [length_concat]

theorem reverse_reverse : reverse (reverse t) = t :=
  match t with
  | [] => rfl
  | a::as => show reverse ((reverse as).concat a) = a :: as by
    rw [reverse_concat, reverse_reverse]
where reverse_concat {α a} : {as : List α} → reverse (as.concat a) = a :: reverse as
  | [] => rfl
  | b::bs => show (reverse (bs.concat a)).concat b = (a :: reverse bs).concat b by
    rw [reverse_concat]
end

/-
3. Define an inductive data type consisting of terms built up from the following constructors:

   - ``const n``, a constant denoting the natural number ``n``
   - ``var n``, a variable, numbered ``n``
   - ``plus s t``, denoting the sum of ``s`` and ``t``
   - ``times s t``, denoting the product of ``s`` and ``t``

   Recursively define a function that evaluates any such term with respect to an assignment of values to the variables.
-/

section
inductive Term
  | const (n : Nat)
  | var (n : Nat)
  | plus (s t : Term)
  | times (s t : Term)

variable (assignment : Nat → Nat)
def Term.evaluate : Term → Nat
  | const n => n
  | var n => assignment n
  | plus s t => s.evaluate + t.evaluate
  | times s t => s.evaluate * t.evaluate
end

/-
4. Similarly, define the type of propositional formulas, as well as
   functions on the type of such formulas: an evaluation function,
   functions that measure the complexity of a formula, and a function
   that substitutes another formula for a given variable.
-/

section
variable (V) (assignment : V → Bool)

inductive Formula
  /-- The constant ``true``. -/
  | tt
  /-- The constant ``false``. -/
  | ff
  | var (v : V)
  | not (p : Formula)
  | and (p q : Formula)
  | or (p q : Formula)
  | imp (p q : Formula)
  | iff (p q : Formula)

def Formula.evaluate : Formula V → Bool
  | tt => true
  | ff => false
  | var v => assignment v
  | not p => ¬p.evaluate
  | and p q => p.evaluate ∧ q.evaluate
  | or p q => p.evaluate ∨ q.evaluate
  | imp p q => p.evaluate → q.evaluate
  | iff p q => p.evaluate ↔ q.evaluate

/--
Complexity is the number of connectives.
See page 5 of https://www.cs.cmu.edu/~mheule/15217-f21/slides/prop.pdf
-/
def Formula.complexity : Formula V → Nat
  | var _ | tt | ff => 0
  | not p => p.complexity + 1
  | and p q | or p q | imp p q | iff p q => p.complexity + q.complexity + 1

variable [DecidableEq V] (v : V) (q : Formula V)
/-- Substitutes ``q`` for ``v`` in ``p``. -/
def Formula.substitute : Formula V → Formula V
  | p@(tt) | p@(ff) => p
  | p@(var u) => if u = v then q else p
  | not p => p.substitute
  | and p q => and p.substitute q.substitute
  | or p q => or p.substitute q.substitute
  | imp p q => imp p.substitute q.substitute
  | iff p q => iff p.substitute q.substitute

end
