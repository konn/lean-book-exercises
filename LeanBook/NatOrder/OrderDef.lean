import LeanBook.NatOrder.AddCancel

inductive MyNat.le (n : MyNat) : MyNat → Prop where
  | refl : MyNat.le n n
  | step {m: MyNat} : MyNat.le n m → MyNat.le n (m + 1)

instance : LE MyNat where
  le := MyNat.le

@[induction_eliminator]
def MyNat.le.recAux {n b: MyNat}
  {motive: (a: MyNat) → n ≤ a → Prop}
  (refl : motive n MyNat.le.refl)
  (step : ∀ {m: MyNat} (a : n ≤ m),
    motive m a → motive (m + 1) (MyNat.le.step a)
  )
  (t : n ≤ b) : motive b t := by
  induction t with
  | refl => exact refl
  | @step mc h ih => exact step (a := h) ih

theorem MyNat.le_refl (n: MyNat) : n ≤ n := by
  exact MyNat.le.refl

variable {m n k : MyNat}

theorem MyNat.le_step (h: n ≤ m) : n ≤ m + 1 := MyNat.le.step h
theorem MyNat.le_trans (hnm : n ≤ m) (hmk : m ≤ k) : n ≤ k := by
  induction hmk with
  | refl => exact hnm
  | @step k hmk ih => exact MyNat.le_step ih

attribute [refl] MyNat.le_refl

theorem MyNat.le_add_one_right (n : MyNat): n ≤ n + 1 := by
  apply MyNat.le_step
  rfl


instance : Trans (· ≤ · : MyNat → MyNat → Prop) (· ≤ ·) (· ≤ ·) where
  trans := MyNat.le_trans

theorem MyNat.le_add_one_left (n : MyNat): n ≤ 1 + n := calc
  _ ≤ n + 1 := by apply le_add_one_right
  _ = 1 + n := by ac_rfl

attribute [simp] MyNat.le_refl MyNat.le_add_one_right MyNat.le_add_one_left

theorem MyNat.le.dest (h: n ≤ m) : ∃ k, n + k = m := by
  induction h with
  | refl => exists 0
  | @step l h ih =>
      obtain ⟨k, ih⟩ := ih
      exists k + 1
      rw [← ih]
      ac_rfl

theorem MyNat.le_add_right (n m: MyNat) : n ≤ n + m := by
  induction m with
  | zero => rfl
  | succ k ih =>
      rw [show n + (k + 1) = n + k + 1 from by ac_rfl]
      exact MyNat.le_step ih

theorem MyNat.le.intro (h: n + k = m) : n ≤ m := by
  rw [← h]
  exact MyNat.le_add_right n k


theorem MyNat.le_iff_add : n ≤ m ↔ ∃ k, n + k = m := by
  constructor <;> intro h
  · exact MyNat.le.dest h
  · obtain ⟨k, h⟩ := h
    exact MyNat.le.intro h

example  : 1 ≤ 4 := by
  apply MyNat.le.intro (k := 3)
  distrib
