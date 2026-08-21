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

theorem col_of_odd_even (n : ℕ+) (n_odd : Odd n.val) : Even (col n).val := by
  have h₁ : Odd (3 * n).val := by
    apply Nat.odd_mul.mpr
    exact if_false_right.mp n_odd
  grind only [col.eq_def, PNat.one_coe, Nat.even_or_odd, Nat.not_odd_iff,
    PNat.add_coe]

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

theorem max_odd_div_odd (n : ℕ+) : Odd (max_odd_div n).val.val := by
  grind

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

theorem col_pow_two_mul_syr (n : ONat) : ∃ k : ℕ+, col n.val = 2 ^ (k.val) * (syr n).val := by
  let col_n := 3 * n.val + 1
  have h₁ : col n.val = col_n := by
    grind [= col]
  obtain ⟨j, h₂⟩ := eq_pow_two_times_max_odd_div col_n
  have col_n_even : Even col_n.val := by
    rw [← h₁]
    apply col_of_odd_even
    let ⟨_, n_odd⟩ := n
    exact n_odd
  have h₄ : 0 < j := by
    apply Nat.pos_of_ne_zero
    by_contra j_eq_zero
    rw [j_eq_zero] at h₂
    simp only [pow_zero, one_mul] at h₂
    have col_n_odd : Odd col_n.val := by
      rw [h₂]
      exact max_odd_div_odd col_n
    exact Nat.not_odd_iff_even.mpr col_n_even col_n_odd
  let i : ℕ+ := ⟨j, h₄⟩
  use i
  rw [h₁]
  trivial

theorem col_pow_suc (n : ℕ+) (k : ℕ) : col_pow (k + 1) n = col_pow k (col n) := by
  induction k
  · rw [col_pow, col_pow]
    rfl
  rename_i i ih
  grind only [col_pow.eq_def, Function.comp_def]

theorem col_two_pow_suc (n : ℕ+) (k : ℕ) : col (2 ^ (k + 1) * n) = 2 ^ k * n := by
  have h₁ : 2 ∣ (2 ^ (k + 1) * n).val := by
    rw [pow_succ]
    nth_rw 2 [mul_comm]
    rw [mul_assoc]
    simp
  have h₂ : Even (2 ^ (k + 1) * n).val := by
    exact even_iff_two_dvd.mpr h₁
  have h₃ : 2 * ((2 ^ (k + 1) * n).divExact 2) = 2 * (2 ^ k * n) := by
    rw [← mul_assoc]
    nth_rw 4 [mul_comm]
    rw [← pow_succ]
    grind only [PNat.mul_div_exact, PNat.mul_coe, PNat.pow_coe, usr Nat.div_pow_of_pos,
      PNat.dvd_iff, usr Nat.dvd_mul_right_of_dvd]
  have h₄ : (2 ^ (k + 1) * n).divExact 2 = 2 ^ k * n := by
    exact mul_left_cancel h₃
  rw [col, Nat.even_iff.mp]
  · assumption
  grind only [even_iff_exists_add_self, PNat.add_coe]

theorem col_pow_of_pow_two_eq_id (n : ℕ+) (k : ℕ) : col_pow k (2 ^ k * n) = n := by
  induction k
  · rw [col_pow]
    simp
  rename_i i ih
  rw [col_pow_suc, col_two_pow_suc]
  assumption

theorem pow_of_col_eq_syr (n : ONat) : ∃ k : ℕ+, col_pow k n.val = (syr n).val := by
  have h₁ : ∃ k : ℕ+, col n.val = 2 ^ (k.val) * (syr n).val := by
    exact col_pow_two_mul_syr n
  obtain ⟨j, h₁⟩ := h₁
  use j + 1
  have h₂ : (↑j + 1 : ℕ) = ↑(j + 1) := by
    rfl
  rw [← h₂, col_pow_suc n.val j, h₁]
  exact col_pow_of_pow_two_eq_id (syr n).val ↑j

theorem syr_sub_col (n : ONat) : sONat_to_sPNat (syr_orbit n) ⊆ col_orbit n.val := by
  sorry
