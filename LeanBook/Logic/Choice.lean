#check Classical.em

#print axioms Classical.em

#check Classical.choice

def Surjective {X Y: Type} (f : X → Y) : Prop :=
  ∀ y: Y, ∃ x: X, f x = y

example : Surjective (fun x: Nat => x)  := by
  dsimp[Surjective]
  intro y
  exists y

variable {X Y: Type}

noncomputable def inverse (f: X → Y) (hf: Surjective f) : Y → X := by
  intro y

  have: Nonempty {x // f x = y} := by
    let ⟨x, hx⟩ := hf y
    exact (⟨x, hx⟩)

  have x := Classical.choice this
  exact x.val

theorem double_negation_of_contra_equiv (P: Prop)
  (contra_equiv : ∀ (P Q : Prop), (¬ P → ¬ Q) ↔ (Q → P))
  : ¬¬P → P := by
  intro hn2p
  obtain ⟨h, _⟩ := (contra_equiv P (¬¬P))
  suffices hn3p: ¬P → ¬¬¬P from by
    apply h
    apply hn3p
    assumption

  guard_target =ₛ ¬P → ¬¬¬P
  intro hp
  contradiction

#print axioms double_negation_of_contra_equiv
