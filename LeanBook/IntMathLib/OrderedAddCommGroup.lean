import LeanBook.IntMathLib.PartialOrder

theorem MyInt.add_le_add_left (a b: MyInt) (h: a ≤ b) (c : MyInt)
    : c + a ≤ c + b := by
  notation_simp at *
  obtain ⟨m, hm⟩ := h
  use m
  have: c + a + ↑m = c + b := calc
    _ = c + a + ↑m         := by rfl
    _ = c + (a + ↑m)       := by ac_rfl
    _ = c + b              := by rw [hm]
  assumption

instance : IsOrderedAddMonoid MyInt where
  add_le_add_left := MyInt.add_le_add_left

example {a: MyInt} (nneg: 0 ≤ a): ∃ k : MyNat, a = ↑k := by
  notation_simp at *
  obtain ⟨k, hk⟩ := nneg
  simp at hk
  exists k
  simp_all
