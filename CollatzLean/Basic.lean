/-
Copyright (c) 2026 Tim Speer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Speer
-/

import Mathlib.Tactic.Cases
import CollatzLean.Defs

/-!
-/

theorem collatz_conjecture : ∀n : ℕ+, col_min n = 1 := by
  sorry

theorem collatz_conjecture2 : ∀n : ONat, syr_min n = 1 := by
  sorry


theorem col_pow_zero_self (n : ℕ+) : col_pow 0 n = n := by
  rw [col_pow]
  trivial

theorem col_pow_succ (k : ℕ) (n : ℕ+) : col_pow (k + 1) n = col (col_pow k n) := by
  rw [col_pow]
  trivial

theorem col_pow_one : ∀(k : ℕ), col_pow k 1 ∈ ({ 1, 2, 4 } : Set ℕ+) := by
  intro k
  induction k
  -- Base Case k = 0
  · rw [col_pow_zero_self 1]
    trivial
  -- General Case k > 0
  · rename_i k ih
    rw [col_pow_succ]
    rcases ih with one | two | four
    · rw [one]
      trivial
    · rw [two]
      trivial
    · rw [four]
      trivial

theorem col_orbit_one : col_orbit 1 = { 1, 2, 4 } := by
  apply Set.ext
  intro x
  constructor
  -- Show col_orbit 1 is a subset of { 1, 2, 4 }
  · intro x_in_orbit
    rcases x_in_orbit with ⟨k, h⟩
    rw [← h]
    exact col_pow_one k
  -- Show { 1, 2, 4 } is a subset of col_orbit 1
  · intro x_in_S
    rw [col_orbit]
    rcases x_in_S with one | two | four
    -- x = 1
    · use 0
      rw [one, col_pow]
      trivial
    -- x = 2
    · use 2
      rw [two]
      iterate 3
        rw [col_pow]
      trivial
    -- x = 4
    · use 1
      rw [four]
      iterate 2
        rw [col_pow]
      trivial

def one : ONat := ⟨1, Nat.odd_iff.mpr rfl⟩

theorem syr_orbit_one : syr_orbit one = { one } := by
  sorry

theorem col_min_in_orb (n : ℕ+) : col_min n ∈ sPNat_to_sNat (col_orbit n) := by
  apply Nat.sInf_mem _
  have h₁ : n ∈ col_orbit n := by
    use 0
    rw [col_pow]
    simp
  use n
  solve_by_elim

theorem col_min_one_iff_one_in_orb (n : ℕ+): col_min n = 1 ↔ 1 ∈ col_orbit n := by
  constructor
  · intro col_min_one
    sorry
  sorry
