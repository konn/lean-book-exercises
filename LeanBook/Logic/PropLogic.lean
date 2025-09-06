#check Prop

#check (1 + 1 = 3 : Prop)

#check (fun n => n + 3 = 39 : Nat → Prop)

#check True

#check False

example : True := by trivial

example (P: Prop) (h : P) : P := by exact h

example (P: Prop) (h : P) : P := by assumption

example (h: False) : ∀ x y z n: Nat,
  n ≥ 3 → x ^ n + y ^ n = z^n → x * y * z = 0 := by
  trivial

example (P Q R: Prop) : (P → Q → R) = (P → (Q → R)) := by rfl


#eval True → True
#eval True → False
#eval False →  True
#eval False → False

example (P Q: Prop) (h: P → Q) (hp : P) : Q := by
  apply h
  apply hp

example (P Q: Prop) (h: P → Q) (hp : P) : Q := by
  exact h hp

example (P Q : Prop) (hq : Q) : P → Q := by
  intro hp
  exact hq

#eval ¬ True
#eval ¬ False

example (P: Prop) : (¬ P) = (P → False) := by rfl

example (P: Prop) (hnp : ¬ P) (hp: P) : False := by
  apply hnp
  exact hp

example (P Q : Prop) (h: P → ¬ Q) : Q → ¬ P := by
  intro hq
  intro hp
  exact h hp hq

example (P : Prop) (hnp: ¬ P) (hp : P) : False := by
  contradiction

example (P Q : Prop) (hnp : ¬ P) (hp : P) : Q := by
  exfalso
  contradiction

#eval True ↔ True
#eval True ↔ False
#eval False ↔ True
#eval False ↔ False


example (P Q: Prop) (h1: P → Q) (h2: Q → P) : P ↔ Q := by
  constructor
  · exact h1
  · exact h2

example (P Q : Prop) (hq : Q) : (Q → P) ↔ P := by
  constructor
  case mp =>
    intro h
    exact h hq

  case mpr =>
    intro hp hq
    exact hp

example (P Q : Prop) (hq : Q) : (Q → P) ↔ P := by
  constructor <;> intro h
  case mp =>
    exact h hq

  case mpr =>
    intro  hq
    exact h

example (P Q : Prop) (h : P ↔ Q) (hq : Q) : P := by
  rw [h]
  exact hq

example (P Q : Prop) (h : P ↔ Q) (hp : P) : Q := by
  rw [← h]
  exact hp

example (P Q : Prop) (h : P ↔ Q) : P = Q := by
  rw [h]

#eval True ∧ True
#eval True ∧ False
#eval False ∧ True
#eval False ∧ False

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp
  · exact hq

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  exact ⟨hp, hq⟩

example (P Q : Prop) (h : P ∧ Q) : P := by
  exact h.left

example (P Q : Prop) (h : P ∧ Q) : Q := by
  exact h.right

#eval True ∨ True
#eval True ∨ False
#eval False ∨ True
#eval False ∨ False

example (P Q : Prop) (hp : P) : P ∨ Q := by
  left
  exact hp

example (P Q : Prop) (hq : Q) : P ∨ Q := by
  right
  exact hq

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hp => right; assumption
  | inr hq => left; assumption

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h
  case inl hp => right; assumption
  case inr hq => left; assumption

example (P Q: Prop) : (¬ P ∨ Q) → (P → Q) := by
  intro hnpOrQ hp
  cases hnpOrQ with
  | inl hnp => contradiction
  | inr hq => exact hq

example (P Q: Prop) : ¬(P ∨ Q) ↔ (¬ P ∧ ¬ Q) := by
  constructor
  · intro hnpq
    constructor <;> intro h
    · apply hnpq
      left; assumption
    · apply hnpq
      right; assumption

  · intro hnpnq hpq
    cases hpq with
    | inl hp => apply hnpnq.left; assumption
    | inr hq => apply hnpnq.right; assumption
