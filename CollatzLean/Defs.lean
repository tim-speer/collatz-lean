/-
Copyright (c) 2026 Tim Speer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Speer
-/

import Mathlib.Data.PNat.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Max
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Linarith

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

theorem odd_div_le_max_odd_div (n : ℕ+) : ∀ d ∈ odd_div n, d ≤ (max_odd_div n).val := by
  intro d d_odd_div
  exact Finset.le_max' (odd_div n) d d_odd_div

theorem max_odd_div_odd_div (n : ℕ+) : (max_odd_div n).val.val ∈ odd_div n := by
  rw [odd_div, max_odd_div]
  grind only [odd_div.eq_def, PNat.mk_coe, Finset.max'_eq_iff]

theorem max_odd_div_dvd_n (n : ℕ+) : (max_odd_div n).val ∣ n := by
  have h₁ : (max_odd_div n).val.val ∈ odd_div n := by
    exact max_odd_div_odd_div n
  grind only [odd_div.eq_def, PNat.dvd_iff, = Finset.mem_filter, = Nat.mem_divisors]

theorem max_odd_div_odd_eq_self (n : ℕ+) (n_odd : Odd n.val) : (max_odd_div n).val = n := by
  have h₁ : (max_odd_div n).val.val ∈ odd_div n := by
    exact max_odd_div_odd_div n
  have h₂ : (max_odd_div n).val ∣ n := by
    exact max_odd_div_dvd_n n
  have max_odd_div_le_n : (max_odd_div n).val ≤ n := by
    grind only [PNat.le_of_dvd]
  have n_odd_div : n.val ∈ odd_div n := by
    rw [odd_div]
    simp_all
  have max_odd_div_ge_n : (max_odd_div n).val ≥ n := by
    rw [max_odd_div]
    grind only [max_odd_div.eq_def, Finset.max'_eq_iff, PNat.mk_coe, PNat.coe_le_coe]
  grind only

theorem max_odd_div_two_eq_max_odd_div (n : ℕ+) :
  (max_odd_div (2 * n)).val = (max_odd_div n).val := by
  let m₁ := (max_odd_div n).val
  let m₂ := (max_odd_div (2 * n)).val
  have h₁ : ∃ k, n = m₁ * k := by
    exact dvd_def.mp (max_odd_div_dvd_n n)
  obtain ⟨k, h₁⟩ := h₁
  have h₂ : 2 * n = 2 * k * m₁ := by
    grind
  have h₃ : m₁ ∣ 2 * n := by
    exact Dvd.intro_left (2 * k) (id (Eq.symm h₂))
  have h₄ : m₁.val ∈ odd_div (2 * n) := by
    grind only [usr Subtype.property, odd_div.eq_def, PNat.dvd_iff, PNat.ne_zero,
      = Finset.mem_filter, = Nat.mem_divisors]
  have m₁_le_m₂ : ↑m₁ ≤ ↑m₂ := by
    apply odd_div_le_max_odd_div (2 * n)
    assumption
  have h₅ : ∃ j, 2 * n = m₂ * j := by
    exact dvd_def.mp (max_odd_div_dvd_n (2 * n))
  obtain ⟨j, h₅⟩ := h₅
  have m₂_odd : Odd m₂.val := by
    grind
  have m₂_mul_j_even : Even (m₂ * j).val := by
    rw [← h₅]
    simp
  have m₂_even_or_j_even : Even m₂.val ∨ Even j.val := by
    exact Nat.even_mul.mp m₂_mul_j_even
  have j_even : Even j.val := by
    rcases m₂_even_or_j_even with left | right
    · apply Nat.not_odd_iff_even.mpr at left
      contradiction
    · assumption
  have j_mul_two : ∃ i : ℕ+, j = 2 * i := by
    have temp : ∃ i : ℕ, j = 2 * i := by
      exact even_iff_exists_two_mul.mp j_even
    obtain ⟨i, temp⟩ := temp
    have i_pos : 0 < i := by
      grind only [PNat.ne_zero]
    use ⟨i, i_pos⟩
    exact PNat.eq temp
  obtain ⟨i, j_mul_two⟩ := j_mul_two
  rw [j_mul_two, mul_comm m₂, mul_assoc] at h₅
  apply mul_left_cancel at h₅
  have h₇ : m₂ ∣ n := by
    exact Dvd.intro_left i (id (Eq.symm h₅))
  have h₈ : m₂.val ∈ odd_div n := by
    grind only [usr Subtype.property, odd_div.eq_def, PNat.dvd_iff, PNat.ne_zero,
      = Finset.mem_filter, = Nat.mem_divisors]
  have m₂_le_m₁ : ↑m₂ ≤ ↑m₁ := by
    apply odd_div_le_max_odd_div n
    assumption
  grind

theorem eq_pow_two_times_max_odd_div (n : ℕ+) : ∃ k : ℕ, n = 2 ^ k * (max_odd_div n).val := by
  induction n using PNat.strongInductionOn
  rename_i i ih
  by_cases h₁ : Odd i.val
  · rw [max_odd_div_odd_eq_self i h₁]
    use 0
    simp
  have i_even : Even i.val := by
    exact Nat.not_odd_iff_even.mp h₁
  have h₂ : ∃ q, i.val = 2 * q := by
    exact even_iff_exists_two_mul.mp i_even
  obtain ⟨q, h₂⟩ := h₂
  have h₃ : 0 < q := by
    grind only [PNat.ne_zero]
  let r : ℕ+ := ⟨q, h₃⟩
  have h₄ : i = 2 * r := by
    exact PNat.eq h₂
  have r_lt_i : r < i := by
    simp_all
  obtain ihr := ih r r_lt_i
  obtain ⟨j, ihr⟩ := ihr
  use (j + 1)
  rw [h₄, max_odd_div_two_eq_max_odd_div]
  have h₅ : (2 ^ (j + 1) : ℕ+) = 2 * 2 ^ j := by
    exact pow_succ' 2 j
  rw [h₅, mul_assoc, ← ihr]

def syr (n : ONat) : ONat := max_odd_div (3 * n.val + 1)

def syr_pow (k : ℕ) : ONat → ONat :=
  if k = 0 then
    id
  else
    syr ∘ syr_pow (k - 1)

def syr_orbit (n : ONat) : Set ONat := { syr_pow k n | k : ℕ }

def ONat_to_PNat (n : ONat) : ℕ+ := n.val
def sONat_to_sPNat (S : Set ONat) : Set ℕ+ := { ONat_to_PNat n | n ∈ S }

theorem col_pow_two_mul_col (n : ONat) : ∃ k : ℕ+, col n.val = 2 ^ (k.val) * (syr n).val := by
  have h₁ : col n.val = 3 * n.val + 1 := by
    grind [= col]
  rw [h₁]
  sorry

theorem col_pow_two_times_syr (n : ONat) : ∃ k : ℕ+, (syr n).val = col_pow k n.val := by
  sorry

theorem syr_sub_col (n : ONat) : sONat_to_sPNat (syr_orbit n) ⊆ col_orbit n.val := by
  sorry
