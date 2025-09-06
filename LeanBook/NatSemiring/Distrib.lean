import LeanBook.NatSemiring.Mult

theorem unfoldNatLit (x : Nat)
  : (OfNat.ofNat (x + 2) : MyNat) = (OfNat.ofNat (x + 1) : MyNat) + 1 :=
  rfl

macro "expand_num" : tactic => `(tactic| focus
  try simp only [unfoldNatLit]

  try simp only [Nat.reduceAdd]

  try dsimp only [OfNat.ofNat]
  try simp only [
    show MyNat.ofNat 1 = 1 from rfl,
    show MyNat.ofNat 0 = 0 from rfl,
  ]
)

macro "distrib" : tactic => `(tactic| focus
  expand_num
  try simp only [
    MyNat.mul_add,
    MyNat.add_mul,
    MyNat.mul_zero,
    MyNat.zero_mul,
    MyNat.mul_one,
    MyNat.one_mul,
  ]
  try ac_rfl
)

example (n: MyNat) : 3 * n = 2 * n + 1 * n := by
  expand_num
  guard_target =ₛ (1 + 1 + 1) * n = (1 + 1) * n + 1 * n
  simp only [MyNat.add_mul]

example (m n : MyNat): m * (n + 1) + 2 * (m + n) = m * n + 3 * m + 2 * n := by
  distrib


example (m n : MyNat): m * (n + 1) + (2 + m) * m = m * n + 3 * m + m * m := by
  distrib

example (m n : MyNat): m * (n + 1) + (2 + n) * n = m * n + m + 2 * n + n * n := by
  distrib

example (m n : MyNat) : m * n + n * n = (m + n) * n := by
  distrib

/-
-- We can Just use "trivial" factor here, but this should not be what the author wants :-):

example (n : MyNat) : ∃ s t : MyNat, s * t = n * n + 8 * n + 16 := by
  exists 1
  exists n * n + 8 * n + 16
  simp
 -/

example (n : MyNat) : ∃ s t : MyNat, s * t = n * n + 8 * n + 16 := by
  exists (n + 4)
  exists (n + 4)
  distrib
