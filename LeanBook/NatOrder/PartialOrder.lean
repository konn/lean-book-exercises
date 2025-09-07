import LeanBook.NatOrder.OrdMonoid

variable {n m k: MyNat}

theorem MyNat.lt_of_le_of_lt (h₁ : n ≤ m) (h₂ : m < k) : n < k := by
  notation_simp at *
  have : n + 1 ≤ k := calc
    _ = n + 1 := by rfl
    _ ≤ m + 1 := by compatible
    _ ≤ k     := h₂
  assumption

theorem MyNat.lt_of_lt_of_le (h₁ : n < m) (h₂ : m ≤ k) : n < k := by
  notation_simp at *
  have : n + 1 ≤ k := calc
    _ = n + 1 := by rfl
    _ ≤ m     := h₁
    _ ≤ k     := h₂
  assumption

instance : Trans (· < · : MyNat → MyNat → Prop) (· < ·) (· < ·) where
  trans := MyNat.lt_trans

instance : Trans (· ≤ · : MyNat → MyNat → Prop) (· < ·) (· < ·) where
  trans := MyNat.lt_of_le_of_lt

instance : Trans (· < · : MyNat → MyNat → Prop) (· ≤ ·) (· < ·) where
  trans := MyNat.lt_of_lt_of_le
