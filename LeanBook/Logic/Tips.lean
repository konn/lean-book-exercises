example (P : Prop) : ¬¬¬P → ¬P := by
  intro hn3p hp
  have hn2p: ¬¬P := by
    intro hnp
    contradiction

  contradiction

example (P : Prop) : ¬¬¬P → ¬P := by
  intro hn3p hp
  have : ¬¬P := by
    intro hnp
    contradiction

  guard_hyp this: ¬¬P

  contradiction

example (P: Prop): ¬¬(P ∨ ¬P) := by
  intro h

  suffices hyp: ¬P from by
    have : P ∨ ¬ P := by
      right
      assumption
    contradiction

  guard_target =ₛ ¬P

  intro hp

  have: P ∨ ¬P := by
    left
    assumption

  contradiction

example (P: Prop) : (P → True) ↔ True := by
  exact imp_true_iff P

example (P: Prop) : (True → P) ↔ P := by
  exact true_imp_iff

example (P Q: Prop) (h: ¬P ↔ Q) : (P → False) ↔ Q := by
  rw [show (P → False) ↔ ¬ P by rfl]
  rw [h]

example : P → P := by
  intro hp
  exact hp

example (P: Prop) : ¬ (P ↔ ¬P) := by
  intro h
  have hpnp : P → ¬ P := h.mp
  have hnpp : ¬ P → P := h.mpr
  have hnp: ¬ P := by
    intro hp
    apply hpnp hp
    assumption

  have hp: P := by
    apply hnpp
    exact hnp

  contradiction
