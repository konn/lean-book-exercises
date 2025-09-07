import LeanBook.NatOrder.NotationSimp
import LeanBook.NatOrder.CompatibleTag

variable {a b m n : MyNat}

theorem MyNat.add_le_add_left (h: n ≤ m) (l: MyNat) : l + n ≤ l + m := by
  rw [MyNat.le_iff_add] at *
  obtain ⟨k, hk⟩ := h
  exists k
  rw [← hk]
  ac_rfl
theorem MyNat.add_le_add_right (h: m ≤ n) (l: MyNat) : m + l ≤ n + l := calc
  _ = l + m := by ac_rfl
  _ ≤ l + n := MyNat.add_le_add_left h l
  _ = n + l := by ac_rfl

theorem MyNat.add_le_add (h1: m ≤ n) (h2: a ≤ b): m + a ≤ n + b := calc
  _ ≤ m + b := by exact add_le_add_left h2 m
  _ ≤ n + b := by exact add_le_add_right h1 b

example (h: n ≤ m): l + n ≤ l + m := by
  apply MyNat.add_le_add_left <;> assumption

example (h: m ≤ n): m + l ≤ n + l := by
  apply MyNat.add_le_add_right <;> assumption

example (h1: m ≤ n) (h2 : a ≤ b): m + a ≤ n + b := by
  apply MyNat.add_le_add <;> assumption

syntax "compatible" : tactic

open Lean Elab Tactic in
elab "compatible" : tactic => do
  let taggedDecls ← labelled `compatible
  if taggedDecls.isEmpty then
    throwError "No theorem attributed with `[compatible]` found."

  for decl in taggedDecls do
    let declStx := mkIdent decl
    try
      evalTactic <| ← `(tactic| apply $declStx <;> assumption)

      -- Terminate if successful
      return ()
    catch _ =>
      -- Go on to the next declaration
      pure ()

  throwError "No applicable theorem found among `[compatible]`-tagged theorems."

attribute [compatible]
  MyNat.add_le_add_left
  MyNat.add_le_add_right
  MyNat.add_le_add

example (h: n ≤ m): l + n ≤ l + m := by compatible
example (h: m ≤ n): m + l ≤ n + l := by compatible
example (h1: m ≤ n) (h2 : a ≤ b): m + a ≤ n + b := by compatible

@[compatible] theorem MyNat.add_lt_add_left {m n: MyNat} (h: m < n) (k : MyNat) : k + m < k + n := by
  have : k + m + 1 ≤ k + n := calc
    _ = k + (m + 1) := by ac_rfl
    _ ≤ k + n       := by compatible
  assumption

@[compatible] theorem MyNat.add_lt_add_right {m n: MyNat} (h: m < n) (k : MyNat) : m + k < n + k := calc
  _ = k + m := by ac_rfl
  _ < k + n := by compatible
  _ = n + k := by ac_rfl

section
  variable (m n k : MyNat)

  theorem MyNat.le_of_add_le_add_left : k + m ≤ k + n → m ≤ n := by
    intro h
    rw [MyNat.le_iff_add] at *
    obtain ⟨d, hd⟩ := h
    exists d
    have : m + d + k = n + k := calc
      _ = m + d + k := by rfl
      _ = k + m + d := by ac_rfl
      _ = k + n     := by rw [hd]
      _ = n + k     := by ac_rfl
    simp_all

  theorem MyNat.le_add_of_le_add_right : m + k ≤ n + k → m ≤ n := by
    rw [add_comm m k, add_comm n k]
    apply MyNat.le_of_add_le_add_left

  @[simp] theorem MyNat.add_le_add_iff_left : k + m ≤ k + n ↔ m ≤ n := by
    constructor
    · apply MyNat.le_of_add_le_add_left
    · intro h; compatible

  @[simp] theorem MyNat.add_le_add_iff_right : m + k ≤ n + k ↔ m ≤ n := by
    constructor
    · apply MyNat.le_add_of_le_add_right
    · intro h; compatible
end

variable (m₁ m₂ n₁ n₂ l₁ l₂ : MyNat)

example (h1: m₁ ≤ m₂) (h2 : n₁ ≤ n₂) (h3 : l₁ ≤ l₂): l₁ + m₁ + n₁ ≤ l₂ + m₂ + n₂ := by
  have : l₁ + m₁ ≤ l₂ + m₂ := by compatible
  have : l₁ + m₁ + n₁ ≤ l₂ + m₂ + n₂ := by compatible
  assumption
