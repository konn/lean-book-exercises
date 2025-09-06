example (P : Prop) : ¬¬P → P := by
  intro hn2p
  by_cases h: P

  · exact h
  · contradiction

example (P: Prop): ¬¬ P → P := by
  by_cases h: P
  · intro hn2p; exact h
  · intro hp; contradiction

example (P Q: Prop) : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q := by
  constructor

  · guard_target =ₛ ¬ (P ∧ Q) → ¬ P ∨ ¬ Q
    intro h
    by_cases hp: P
    · guard_hyp hp: P
      by_cases hq: Q
      · guard_hyp hq: Q
        have hpq : P ∧ Q := ⟨hp, hq⟩
        contradiction

      · guard_hyp hq: ¬Q; right; assumption

    · guard_hyp hp: ¬P; left; assumption

  · intro hnpq
    intro hpq
    obtain ⟨hp, hq⟩ := hpq
    cases hnpq <;> contradiction

example (P Q : Prop) : (P → Q) ↔ (¬ Q → ¬ P) := by
  constructor

  · guard_target =ₛ (P → Q) → (¬ Q → ¬ P)
    intro hpq hnq hp
    apply hnq
    apply hpq
    exact hp

  · guard_target =ₛ (¬ Q → ¬ P) → (P → Q)
    intro hnqnp hp
    by_cases h: Q
    · guard_hyp h: Q
      assumption
    · guard_hyp h: ¬Q
      have hnp: ¬P := hnqnp h
      contradiction
