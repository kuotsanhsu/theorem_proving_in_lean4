inductive Vector (α : Type u) : Nat → Type u
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)

namespace Vector
def map (f : α → β → γ) {n : Nat} (as : Vector α n) (bs : Vector β n) : Vector γ n :=
  sorry
end Vector

/-
The ``map`` function is even more tedious to define by hand than the
``tail`` function. We encourage you to try it, using ``recOn``,
``casesOn`` and ``noConfusion``.
-/

/-
1. Open a namespace ``Hidden`` to avoid naming conflicts, and use the
   equation compiler to define addition, multiplication, and
   exponentiation on the natural numbers. Then use the equation
   compiler to derive some of their basic properties.
-/

/-
2. Similarly, use the equation compiler to define some basic
   operations on lists (like the ``reverse`` function) and prove
   theorems about lists by induction (such as the fact that
   ``reverse (reverse xs) = xs`` for any list ``xs``).
-/

/-
3. Define your own function to carry out course-of-value recursion on
   the natural numbers. Similarly, see if you can figure out how to
   define ``WellFounded.fix`` on your own.
-/

/-
4. Following the examples in [Section Dependent Pattern Matching](#dependent-pattern-matching),
   define a function that will append two vectors.
   This is tricky; you will have to define an auxiliary function.
-/

def Vector.append : Vector α m → Vector α n → Vector α (m + n)
  | nil, ys => Nat.zero_add .. ▸ ys
  | cons x xs, ys => Nat.succ_add .. ▸ cons x (xs.append ys)

/-
5. Consider the following type of arithmetic expressions. The idea is
   that ``var n`` is a variable, ``vₙ``, and ``const n`` is the
   constant whose value is ``n``.
-/

inductive Expr where
  | const : Nat → Expr
  | var : Nat → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr
  deriving Repr

open Expr

def sampleExpr : Expr :=
  plus (times (var 0) (const 7)) (times (const 2) (var 1))

/-
Here ``sampleExpr`` represents ``(v₀ * 7) + (2 * v₁)``.

Write a function that evaluates such an expression, evaluating each ``var n`` to ``v n``.
-/

def eval (v : Nat → Nat) : Expr → Nat
  | const n     => n
  | var n       => v n
  | plus e₁ e₂  => eval v e₁ + eval v e₂
  | times e₁ e₂ => eval v e₁ * eval v e₂

def sampleVal : Nat → Nat
  | 0 => 5
  | 1 => 6
  | _ => 0

-- Try it out. You should get 47 here.
#eval eval sampleVal sampleExpr

/-
Implement "constant fusion," a procedure that simplifies subterms like
``5 + 7`` to ``12``. Using the auxiliary function ``simpConst``,
define a function "fuse": to simplify a plus or a times, first
simplify the arguments recursively, and then apply ``simpConst`` to
try to simplify the result.
-/

def simpConst : Expr → Expr
  | plus (const n₁) (const n₂)  => const (n₁ + n₂)
  | times (const n₁) (const n₂) => const (n₁ * n₂)
  | e                           => e

def fuse : Expr → Expr :=
  fun
  | e@(const _) | e@(var _) => e
  | plus e₁ e₂  => simpConst (plus (fuse e₁) (fuse e₂))
  | times e₁ e₂ => simpConst (times (fuse e₁) (fuse e₂))

theorem simpConst_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (simpConst e) = eval v e :=
  fun
  | plus .. | times .. => by
    unfold simpConst ; split ; repeat (first | simp only [*] | trivial)
  | const .. | var .. => rfl

theorem fuse_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (fuse e) = eval v e :=
  fun
  | plus .. | times .. => by simp only [fuse, simpConst_eq, eval, fuse_eq]
  | const .. | var .. => rfl

/-
The last two theorems show that the definitions preserve the value.
-/
