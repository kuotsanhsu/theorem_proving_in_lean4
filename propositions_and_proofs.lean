/-
Prove the following identities, replacing the "sorry" placeholders with actual proofs.
-/

section
variable (p q r : Prop)

-- commutativity of ∧ and ∨
private theorem comm {f : Prop → Prop → Prop} (h : ∀ {p q}, f p q → f q p)
  : ∀ {p q}, f p q ↔ f q p := ⟨h, h⟩
example : p ∧ q ↔ q ∧ p := comm fun h => ⟨h.2, h.1⟩
example : p ∨ q ↔ q ∨ p := comm fun h => h.rec .inr .inl

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  ⟨fun ⟨⟨hp, hq⟩, hr⟩ => ⟨hp, hq, hr⟩, fun ⟨hp, hq, hr⟩ => ⟨⟨hp, hq⟩, hr⟩⟩
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := .intro
  fun | .inl (.inl hp) => .inl hp
      | .inl (.inr hq) => .inr (.inl hq)
      | .inr hr => .inr (.inr hr)
  fun | .inl hp => .inl (.inl hp)
      | .inr (.inl hq) => .inl (.inr hq)
      | .inr (.inr hr) => .inr hr

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := .intro
  fun | ⟨hp, .inl hq⟩ => .inl ⟨hp, hq⟩
      | ⟨hp, .inr hr⟩ => .inr ⟨hp, hr⟩
  fun | .inl ⟨hp, hq⟩ => ⟨hp, .inl hq⟩
      | .inr ⟨hp, hr⟩ => ⟨hp, .inr hr⟩
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := .intro
  fun | .inl hp => ⟨.inl hp, .inl hp⟩
      | .inr ⟨hq, hr⟩ => ⟨.inr hq, .inr hr⟩
  fun | ⟨.inr hq, .inr hr⟩ => .inr ⟨hq, hr⟩
      | ⟨.inl hp, _⟩ | ⟨_, .inl hp⟩ => .inl hp

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := ⟨And.rec, (· ⟨·, ·⟩)⟩
private theorem _or_imp : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  ⟨fun h => ⟨h ∘ .inl, h ∘ .inr⟩, And.rec Or.rec⟩
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := _or_imp ..
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := _or_imp ..
example : ¬p ∨ ¬q → ¬(p ∧ q) := fun h k => h.rec (· k.1) (· k.2)
example : ¬(p ∧ ¬p) := And.rec absurd
example : p ∧ ¬q → ¬(p → q) := fun h k => h.2 (k h.1)
example : ¬p → (p → q) := Function.comp False.rec
example : (¬p ∨ q) → (p → q) := fun h k => h.rec (absurd k) id
example : p ∨ False ↔ p := ⟨Or.rec id False.rec, .inl⟩
example : p ∧ False ↔ False := ⟨And.right, False.rec⟩
example : (p → q) → (¬q → ¬p) := fun h => (· ∘ h)
end

/-
Prove the following identities, replacing the "sorry" placeholders
with actual proofs. These require classical reasoning.
-/

section
open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  (byCases (.inl fun _ => ·) fun hnq => .inr <| Or.rec (absurd · hnq) id ∘ ·)
example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  fun h => byCases (fun hp => byCases (absurd ⟨hp, ·⟩ h) .inr) .inl
example : ¬(p → q) → p ∧ ¬q :=
  fun h => byCases (False.rec ∘ h ∘ (fun _ => ·))
    fun hnq => byCases (⟨·, hnq⟩) fun hnp => absurd (absurd · hnp) h
example : (p → q) → (¬p ∨ q) := fun h => byCases (.inr ∘ h) .inl
example : (¬q → ¬p) → (p → q) := (byContradiction fun k => · k ·)
example : p ∨ ¬p := em p
example : (((p → q) → p) → p) := (byCases id fun hnp => · (absurd · hnp))
end

/-
Prove ``¬(p ↔ ¬p)`` without using classical logic.
-/
example : ¬(p ↔ ¬p) := Iff.rec (have (hp) := · hp hp ; this <| · this)
