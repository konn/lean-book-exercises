def P (n : Nat) : Prop := n = n

example : ∀ a : Nat, P a := by
  intro a
  dsimp [P]

example (P: Nat → Prop) (h : ∀ x : Nat, P x) : P 0 := by
  exact h 0

def even (n : Nat) : Prop := ∃ m : Nat, n = m + m

example : even 4 := by exists 2

example (α : Type) (P Q : α → Prop) (h : ∃ x: α, P x ∧ Q x)
  : ∃ x : α, Q x := by
    obtain ⟨y, hy⟩ := h
    exists y
    exact hy.right

opaque Human : Type

/-- Love relationship -/
opaque Love : Human → Human → Prop

@[inherit_doc] infix:50 " -♥→ " => Love

def IdolExists : Prop := ∃ idol : Human , ∀ h: Human, h -♥→ idol

def EverybodyLovesSomebody : Prop := ∀ h : Human, ∃ tgt : Human, h -♥→ tgt

#check ∃ philan : Human, ∀ h : Human, philan -♥→ h

def PhilanExists : Prop := ∃ philan : Human, ∀ h : Human, philan -♥→ h

def EveryoneLoved : Prop := ∀ h : Human, ∃ lover : Human, lover -♥→ h

example : PhilanExists → EveryoneLoved := by
  intro h

  obtain ⟨philan, h⟩ := h
  dsimp [EveryoneLoved]
  intro human
  exists philan
  exact h human

example : IdolExists → EverybodyLovesSomebody := by
  intro hidol
  obtain ⟨idol, h⟩ := hidol
  dsimp [EverybodyLovesSomebody]
  intro human
  exists idol
  exact h human
