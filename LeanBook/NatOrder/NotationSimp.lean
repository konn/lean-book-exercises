import LeanBook.NatOrder.StrictOrder
import LeanBook.NatOrder.NotationSimpTag

theorem MyNat.lt_def (m n: MyNat) : m < n ↔ m + 1 ≤ n := by rfl

section
  open Lean Parser Tactic

  syntax "notation_simp" (simpArgs)? (location)? : tactic

  macro_rules
  | `(tactic| notation_simp $[[$simpArgs,*]]? $[at $location]?) =>
    let args := simpArgs.map (·.getElems) |>.getD #[]
    `(tactic| simp only [notation_simp, $args,*] $[at $location]?)
end

attribute [notation_simp] MyNat.lt_def

example (m n: MyNat) (h: m < n): m + 1 ≤ n := by
  notation_simp at *
  assumption

section
  open Lean Parser Tactic

  syntax "notation_simp?" (simpArgs)? (location)? : tactic

  macro_rules
  | `(tactic| notation_simp? $[[$simpArgs,*]]? $[at $location]?) =>
    let args := simpArgs.map (·.getElems) |>.getD #[]
    `(tactic| simp? only [notation_simp, $args,*] $[at $location]?)
end

theorem MyNat.lt_irreflex (n: MyNat) : ¬ (n < n) := by
  notation_simp at *
  intro h
  rw [MyNat.le_iff_add] at h
  obtain ⟨k, hk⟩ := h
  rw [show n + 1 + k = n + (k + 1) from by ac_rfl] at hk
  have hk: n + (k + 1) = n + 0 := by simp_all
  simp_all

theorem MyNat.lt_trans {a b c: MyNat} (hab: a < b) (hbc: b < c) : a < c := calc
  a + 1 ≤ b     := hab
  _     ≤ b + 1 := by simp [MyNat.le_add_one_right]
  _     ≤ c     := hbc

example (a b: MyNat) (h1: a < b) (h2: b < a): False := by
  suffices a < a from by simp [MyNat.lt_irreflex] at *
  exact MyNat.lt_trans h1 h2
