import LeanBook.NatOrder.OrderDef

def MyNat.lt (m n: MyNat) : Prop := (m + 1) ≤ n

instance : LT MyNat where
  lt := MyNat.lt

example (m n: MyNat): m < n ↔ (m + 1) ≤ n := by rfl

@[simp] theorem MyNat.one_neq_zero : 1 ≠ 0 := by
  intro h
  injection h

@[simp] theorem MyNat.zero_neq_one : 0 ≠ 1 := by intro h; injection h

@[simp] theorem MyNat.zero_le (n: MyNat) : 0 ≤ n := by
  rw [MyNat.le_iff_add]
  exists n
  simp

theorem MyNat.zero_of_le_zero {n: MyNat} (h: n ≤ 0) : n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exfalso
      rw [MyNat.le_iff_add] at h
      obtain ⟨k, h⟩ := h
      simp_all


@[simp] theorem MyNat.le_zero {n: MyNat} : n ≤ 0 ↔ n= 0 := by
  constructor <;> intro h
  · apply MyNat.zero_of_le_zero h
  · simp_all

theorem MyNat.eq_zero_or_pos (n: MyNat) : n = 0 ∨ 0 < n := by
  induction n with
  | zero => simp
  | succ n ih =>
      dsimp [(· < ·), MyNat.lt] at *
      simp_all
      cases ih with
      | inl ih => simp_all
      | inr ih => simp_all [MyNat.le_step]

theorem MyNat.eq_or_lt_of_le {m n: MyNat} : n ≤ m → n = m ∨ n < m := by
  intro h
  dsimp [(· < ·), MyNat.lt]
  rw [MyNat.le_iff_add] at *
  obtain ⟨k, h⟩ := h
  induction k with
  | zero => simp_all
  | succ k ih =>
      have : ∃ k, n + 1 + k = m := by
        exists k; rw [← h]; ac_rfl
      simp_all


theorem MyNat.le_of_lt {a b: MyNat} (h : a < b) : a ≤ b := by
  dsimp [(· < ·), MyNat.lt] at h
  calc
    a ≤ a + 1 := by simp
    _ ≤ b     := by assumption

theorem MyNat.le_of_eq_or_lt{n m: MyNat}: n = m ∨ n < m → n ≤ m := by
  intro h
  cases h with
  | inl h => rw [h]
  | inr h => exact MyNat.le_of_lt h

theorem MyNat.le_iff_eq_or_lt {m n : MyNat}: n ≤ m ↔ n = m ∨ n < m := by
  constructor
  · apply MyNat.eq_or_lt_of_le
  · apply MyNat.le_of_eq_or_lt

theorem MyNat.lt_or_ge (a b: MyNat) : a < b ∨ b ≤ a := by
  dsimp [(· < ·), MyNat.lt]
  induction a with
  | zero =>
      simp_all
      have: b = 0 ∨ 0 < b := MyNat.eq_zero_or_pos b
      dsimp [(· < ·), MyNat.lt] at this
      cases this <;> simp_all

  | succ a ih =>
    cases ih with
    | inr h =>
      right; exact MyNat.le_step h
    | inl h =>
      simp [MyNat.le_iff_eq_or_lt] at h
      cases h with
      | inl h => simp_all
      | inr h =>
        dsimp [(· < ·), MyNat.lt] at h
        left
        assumption

theorem MyNat.lt_of_not_le {a b : MyNat} (h: ¬ a ≤ b) : b < a := by
  cases MyNat.lt_or_ge b a with
  | inl h => assumption
  | inr h => contradiction


theorem MyNat.not_le_of_lt {a b: MyNat} (h: a < b) : ¬ b ≤ a := by
  intro hle

  dsimp [(· < ·), MyNat.lt] at h
  have : a + 1 ≤ a := calc
    _ ≤ b     := by assumption
    _ ≤ a     := by assumption
  rw [MyNat.le_iff_add] at this
  obtain ⟨k, hk⟩ := this
  rw [show a + 1 + k = a + (k + 1) from by ac_rfl] at hk
  simp_all

theorem MyNat.lt_iff_le_not_le (a b: MyNat) : a < b ↔ a ≤ b ∧ ¬ b ≤ a := by
  constructor <;> intro h
  · simp_all [not_le_of_lt, le_of_lt]
  · simp_all [lt_of_not_le]

theorem MyNat.le_total (a b: MyNat) : a ≤ b ∨ b ≤ a := by
  cases (MyNat.lt_or_ge a b) <;> simp_all [MyNat.le_of_lt]

example (a: MyNat): a ≠ a + 1 := by
  intro h
  suffices _: 0 = 1 from by contradiction
  suffices h: a + 0 = a + 1 from by simp_all
  simp_all

example (n: MyNat): ¬ n < 0 := by
  dsimp [(· < ·), MyNat.lt]
  intro h
  have : n + 1 = 0 := by exact MyNat.zero_of_le_zero h
  injection this
