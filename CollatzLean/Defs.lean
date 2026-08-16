/-
Copyright (c) 2026 Tim Speer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Speer
-/

import Mathlib.Data.PNat.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Max
import Mathlib.Order.Lattice.Nat

def col (n : ℕ+) : ℕ+ :=
  if (n % 2 : ℕ) = 0 then
    PNat.divExact n 2
  else
    3 * n + 1

def col_two (n : ℕ+) : ℕ+ :=
  if (n % 2 : ℕ) = 0 then
    PNat.divExact n 2
  else
    PNat.divExact (3 * n + 1) 2

def col_pow (k : ℕ) : ℕ+ → ℕ+ :=
  if k = 0 then
    id
  else
    col ∘ col_pow (k - 1)

def col_orbit (n : ℕ+) : Set ℕ+ := { col_pow k n | k : ℕ }

def sPNat_to_sNat (S : Set ℕ+) : Set ℕ := { ↑n | n ∈ S }

noncomputable
def col_min (n : ℕ+) : ℕ := sInf (sPNat_to_sNat (col_orbit n))

def ONat : Type := { n : ℕ+ // Odd n.val }

def odd_div (n : ℕ+) : Finset ℕ := { d ∈ n.val.divisors | Odd d }

theorem odd_div_nonempty (n : ℕ+) : (odd_div n).Nonempty := by
  use 1
  rw [odd_div]
  simp

def max_odd_div (n : ℕ+) : ONat := by
  let m := Finset.max' (odd_div n) (odd_div_nonempty n)
  have m_in_odd_div_n : m ∈ odd_div n := by
    exact Finset.max'_mem (odd_div n) (odd_div_nonempty n)
  have m_dvd_n : m ∣ n := by
    grind [= odd_div]
  have m_pos : 0 < m := by
    exact PNat.pos_of_div_pos m_dvd_n
  have m_odd : Odd m := by
    grind [= odd_div]
  exact ⟨⟨m, m_pos⟩, m_odd⟩

def syr (n : ONat) : ONat :=
  max_odd_div (3 * n.val + 1)

def syr_pow (k : ℕ) : ONat → ONat :=
  if k = 0 then
    id
  else
    syr ∘ syr_pow (k - 1)
