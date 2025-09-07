import LeanBook.NatOrder.PartialOrder

deriving instance DecidableEq for MyNat

example : 32 + 13 ≠ 46 := by decide

#eval 1 ≠ 2

def MyNat.ble (a b: MyNat) : Bool :=
  match a, b with
  | 0, _ => true
  | _ + 1, 0 => false
  | a + 1, b + 1 => MyNat.ble a b

#eval MyNat.ble 0 1
#eval MyNat.ble 4 3
#eval MyNat.ble 3 12

#check MyNat.ble.induct

@[simp] theorem MyNat.ble_zero_left (n: MyNat) : MyNat.ble 0 n = true := by rfl

@[simp] theorem MyNat.ble_zero_right (n: MyNat) : MyNat.ble (n + 1) 0 = false := by rfl

@[simp] theorem MyNat.ble_succ (m n: MyNat) :
  MyNat.ble (m + 1) (n + 1) = MyNat.ble m n := by rfl

def MyNat.ble.inductAux (motive: MyNat → MyNat → Prop)
  (case1: ∀(n : MyNat), motive 0 n)
  (case2: ∀(n : MyNat), motive (n + 1) 0)
  (case3: ∀(m n : MyNat), motive m n → motive (m + 1) (n + 1))
  (m n: MyNat) : motive m n := by
  induction m, n using MyNat.ble.induct with
  | case1 n => apply case1
  | case2 n => apply case2
  | case3 m n ih => apply case3; assumption


theorem MyNat.le_impl (m n: MyNat) : MyNat.ble m n = true ↔ m ≤ n := by
  induction m, n using MyNat.ble.inductAux with
  | case1 n => simp
  | case2 n => simp
  | case3 m n ih =>
    simp [ih]

instance : DecidableLE MyNat := fun a b =>
  decidable_of_iff (MyNat.ble a b = true) (MyNat.le_impl a b)

#eval 1 ≤ 3
#eval 3 ≤ 1

example : 1 ≤ 9 := by decide
example : 32 ≤ 47 := by decide

theorem MyNat.lt_impl (m n: MyNat) : MyNat.ble (m + 1) n ↔ m < n := by
  rw [MyNat.le_impl]
  rfl

instance : DecidableLT MyNat := fun a b =>
  decidable_of_iff (MyNat.ble (a + 1) b = true) (MyNat.lt_impl a b)

example : 1 < 4 := by decide

example: 23 < 32 ∧ 12 ≤ 24 := by constructor <;> decide
