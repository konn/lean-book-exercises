import LeanBook.IntMathLib.LinearOrder

variable {a b c : MyInt}

theorem MyInt.lt.dest (h: a < b) : ∃ k : MyNat, a + (↑ k + 1) = b := by
  notation_simp at h
  obtain ⟨⟨k, hk⟩, h⟩ := h

  induction k with
  | zero =>
      exfalso
      replace hk: a = b := by simp_all
      apply h
      exists 0
      simp_all
  | succ k _ => use k; assumption

theorem MyInt.le.intro (a: MyInt) (b: MyNat) : a ≤ a + ↑b := by
  use b

theorem MyInt.lt.intro (h :∃ k : MyNat, a + (k + 1) = b) : a < b := by
  obtain ⟨k, hk⟩ := h
  notation_simp
  constructor
  · use k + 1; assumption
  · intro h
    obtain ⟨s, hs⟩ := h
    have goal : a = a + ↑(s + k + 1) := calc
      _ = a                   := by rfl
      _ = b + ↑s              := by rw [hs]
      _ = a + (↑k + 1) + ↑s   := by rw [hk]
      _ = a + (↑s + ↑k + ↑1)  := by ac_rfl
      _ = a + ↑(s + k + 1)    := by norm_cast
    simp at goal

theorem MyInt.lt_iff_add : a < b ↔ ∃ k : MyNat, a + (k + 1) = b := by
  constructor <;> intro h
  case mp => exact MyInt.lt.dest h
  case mpr => exact MyInt.lt.intro h

@[push_cast]
theorem MyInt.ofMyNat_mul (m n: MyNat) : ↑(n * m) = (m : MyInt) * (n : MyInt) := by
  dsimp [MyInt.ofMyNat]
  apply Quotient.sound
  notation_simp
  ring

theorem MyInt.mul_pos (ha: 0 < a) (hb : 0 < b) : 0 < a * b := by
  rw [MyInt.lt_iff_add] at *
  obtain ⟨c, hc⟩ := ha
  obtain ⟨d, hd⟩ := hb
  rw [← hc, ← hd]
  exists c * d + c + d
  push_cast
  ring

theorem MyInt.sub_pos : 0 < a - b ↔ b < a := by
  constructor <;> intro h
  · rw [MyInt.lt_iff_add] at *
    obtain ⟨k, hk⟩ := h
    simp at hk
    use k
    rw [hk]
    abel
  · rw [MyInt.lt_iff_add] at *
    obtain ⟨k, hk⟩ := h
    use k
    rw [← hk]
    abel

theorem MyInt.mul_lt_mul_of_pos_left (h : a < b) (pos : 0 < c)
  : c * a < c * b := by
  suffices 0 < c * (b - a) from by
    rw [MyInt.lt_iff_add] at this ⊢
    obtain ⟨k, hk⟩ := this
    simp at hk
    use k
    rw [hk]
    ring

  replace h: 0 < b - a := by
    rw [MyInt.sub_pos]
    assumption

  apply MyInt.mul_pos (ha := pos) (hb := h)

theorem MyInt.mul_lt_mul_of_pos_right (h : a < b) (pos : 0 < c)
  : a * c < b * c := by
  simp [MyInt.mul_comm a c, MyInt.mul_comm b c]
  exact mul_lt_mul_of_pos_left h pos

instance : IsStrictOrderedRing MyInt where
  zero_le_one := by decide
  exists_pair_ne := by exists 0, 1
  mul_lt_mul_of_pos_left := by apply MyInt.mul_lt_mul_of_pos_left
  mul_lt_mul_of_pos_right := by apply MyInt.mul_lt_mul_of_pos_right

example (a b c : MyInt) (h : a < b) : a + c < b + c := by
  linarith

example (a b : MyInt) (h1 : 2 * a - b = 1) (h2 : a + b = 5) : a = 2 := by
  linarith

theorem MyInt.mul_le_mul_of_nonneg_left (h: a ≤ b) (nneg: 0 ≤ c) : c * a ≤ c * b := by nlinarith

theorem MyInt.mul_le_mul_of_nonneg_right (h: a ≤ b) (nneg: 0 ≤ c) : a * c ≤ b * c := by nlinarith

instance : IsOrderedRing MyInt where
  zero_le_one := by decide
  mul_le_mul_of_nonneg_left := by apply MyInt.mul_le_mul_of_nonneg_left
  mul_le_mul_of_nonneg_right := by apply MyInt.mul_le_mul_of_nonneg_right

example (a b : MyInt) (h1 : 3 * a - 2 * b = 5) (h2 : 6 * a - 5 * b = 11)
  : b = -1 := by
  linarith
