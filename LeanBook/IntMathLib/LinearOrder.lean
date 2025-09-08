import LeanBook.IntMathLib.DecidableOrd

theorem MyInt.nonneg_or_nonneg_neg {a: MyInt} : 0 ≤ a ∨ 0 ≤ -a := by
  induction a using Quotient.inductionOn with
  | h a =>
    obtain ⟨m, n⟩ := a

    have : n ≤ m ∨ m ≤ n := by
      apply MyNat.le_total

    cases this with
    | inl h => left;  simp [mk_def]; norm_cast
    | inr h => right; simp [mk_def]; norm_cast

theorem MyInt.le_total (a b: MyInt) : a ≤ b ∨ b ≤ a := by
  suffices goal: 0 ≤ b - a ∨ 0 ≤ -(b - a) from by
    cases goal with
    | inl h => left; rw [← sub_nonneg]; assumption
    | inr h =>
      right
      rw [← sub_nonneg]
      rw [show -(b - a) = a - b from by abel] at h
      assumption
  exact MyInt.nonneg_or_nonneg_neg

instance : LinearOrder MyInt where
  toDecidableLE := by infer_instance
  le_total := MyInt.le_total

theorem MyInt.eq_or_lt_of_le {a b: MyInt} (h: a ≤ b) : a = b ∨ a < b := by
  by_cases hor: a = b
  case pos => left; assumption
  case neg => right; order

theorem MyInt.le_of_eq_or_lt {a b : MyInt} (h: a = b ∨ a < b) : a ≤ b := by
  cases h <;> order

theorem MyInt.lt_iff_eq_or_lt {a b: MyInt} : a ≤ b ↔ a = b ∨ a < b := by
  constructor
  · apply MyInt.eq_or_lt_of_le
  · apply MyInt.le_of_eq_or_lt

example {a b: MyInt} (h: b < a): ¬ a ≤ b := by
  order

example {a: MyInt} (neg: a ≤ 0): -a ≥ 0 := by
  have: 0 ≤ -a ∨ 0 ≤ a := by
    rw [show a = (- -a) from by abel, show (- - - a) = -a from by abel]
    apply MyInt.nonneg_or_nonneg_neg
  cases this with
  | inl h => assumption
  | inr h =>
      rw [show a = 0 from by order]
      simp_all
