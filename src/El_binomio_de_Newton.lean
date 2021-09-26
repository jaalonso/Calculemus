-- El_binomio_de_Newton.lean
-- El binomio de Newton
-- José A. Alonso Jiménez
-- Sevilla, 24 de septiembre de 2021
-- ---------------------------------------------------------------------

import tactic.find

-- Ref: https://bit.ly/2XHhtFl

import data.real.basic
import algebra.big_operators.intervals
import algebra.big_operators.ring
import tactic
open nat
open finset
open_locale big_operators
set_option pp.structure_projections false

variables {a b c : ℝ}
variables {n k : ℕ}

lemma aux1a1a
  (hk : k ≤ n)
  : n - k + 1 = n + 1 - k :=
(nat.sub_add_comm hk).symm

lemma aux1a1
  (hk : k  ≤ n)
  : a^(n-k) * a = a^(n+1-k):=
begin
  calc a^(n-k) * a
       = a^succ (n-k) : by rw pow_succ'
   ... = a^(n-k+1)    : by ring_exp
   ... = a^(n+1-k)    : by {congr; rw aux1a1a hk}
end

lemma aux1a
  (hk : k ≤ n)
  : c * a^(n-k) * a * b = c * a^(n+1-k) * b :=
calc c * a^(n-k) * a * b
     = c * (a^(n-k) * a) * b  : by ring
 ... = c * a^(n+1-k) * b      : by simp [aux1a1 hk]

lemma aux1 :
  ∑ k in range (n+1), ↑(choose n k) * a^(n-k) * b^k * a =
  ∑ k in range (n+1), ↑(choose n k) * a^(n+1-k) * b^k :=
begin
  apply sum_congr rfl,
  intros k hk,
  rw mem_range_succ_iff at hk,
  calc ↑(choose n k) * a ^(n-k) * b^k * a
       = ↑(choose n k) * a ^(n-k) * a * b^k : by ring
   ... = ↑(choose n k) * a^(n+1-k) * b^k    : aux1a hk,
end

lemma aux2 :
  ∑ k in range (n+1), ↑(choose n k) * a^(n-k) * b^k * b =
  ∑ k in range (n+1), ↑(choose n k) * a^(n-k) * b^(k+1) :=
begin
  apply sum_congr rfl,
  intros k hk,
  rw mem_range_succ_iff at hk,
  by ring_nf,
end

lemma aux3a1
  (f : ℕ → ℝ)
  : ∑ k in Ico 0 n, f (k+1) = ∑ k in Ico 1 (n+1), f k :=
begin
  convert sum_Ico_add f 0 n 1,
  funext,
  exact congr_arg f (add_comm k 1),
end

lemma aux3a :
  ∑ k in range n, ↑(choose n (k+1)) * a^(n+1-(k+1)) * b^(k+1) =
  (∑ k in Ico 1 (n+1), ↑(choose n k) * a^(n+1-k) * b^k) :=
calc ∑ k in range n, ↑(choose n (k+1)) * a^(n+1-(k+1)) * b^(k+1)
     = ∑ k in Ico 0 n, ↑(choose n (k+1)) * a^(n+1-(k+1)) * b^(k+1)
         : by simp [range_eq_Ico]
 ... = (∑ k in Ico 1 (n+1), ↑(choose n k) * a^(n+1-k) * b^k)
         : by {convert aux3a1 _ ; funext; refl}

lemma aux3 :
  ∑ k in range (n+1), ↑(choose n k) * a^(n+1-k) * b^k =
  ↑(choose n 0) * a^(n+1) * b^0 +
    (∑ k in Ico 1 (n+1), ↑(choose n k) * a^(n+1-k) * b^k) :=
calc ∑ k in range (n+1), ↑(choose n k) * a^(n+1-k) * b^k
     = ∑ k in range n, ↑(choose n (k+1)) * a^(n+1-(k+1)) * b^(k+1) +
       ↑(choose n 0) * a^(n+1) * b^0
         : by apply sum_range_succ'
 ... = ↑(choose n 0) * a^(n+1) * b^0 +
       ∑ k in range n, ↑(choose n (k+1)) * a^(n+1-(k+1)) * b^(k+1)
         : add_comm _ _
 ... = ↑(choose n 0) * a^(n+1) * b^0 +
       (∑ k in Ico 1 (n+1), ↑(choose n k) * a^(n+1-k) * b^k)
         : congr_arg2 (+) rfl aux3a

lemma aux4 :
  ∑ k in range (n+1), ↑(choose n k) * a^(n-k) * b^(k+1) =
  ∑ k in range n, ↑(choose n k) * a^(n-k) * b^(k+1) +
    ↑(choose n n) * a^0 * b^(n+1) :=
begin
  convert sum_range_succ _ _,
  simp,
end

lemma aux5a :
  (choose n 0) = 1 :=
by simp

lemma aux5 :
  ↑(choose n 0) * a ^ (n + 1) * b ^ 0 =
  ↑(choose (n + 1) 0) * a ^ (n + 1) * b ^ 0 :=
calc ↑(choose n 0) * a ^ (n + 1) * b ^ 0
     = a ^ (n + 1) * b ^ 0
         : by norm_num
 ... = ↑(choose (n + 1) 0) * a ^ (n + 1) * b ^ 0
         : by norm_num

lemma aux6a1 :
  range n = Ico 0 n :=
range_eq_Ico n

lemma aux6a :
  ∑ k in range n, ↑(choose n k) * a^(n-k) * b^(k+1) =
  ∑ k in Ico 1 (n+1), ↑(choose n (k-1)) * a^(n-(k-1)) * b^k :=
calc ∑ k in range n, ↑(choose n k) * a^(n-k) * b^(k+1)
     = ∑ k in Ico 0 n, ↑(choose n k) * a^(n-k) * b^(k+1)
        : by simp [range_eq_Ico n]
 ... = ∑ k in Ico 1 (n+1), ↑(choose n (k-1)) * a^(n-(k-1)) * b^k
        : by {convert sum_Ico_add _ 0 n 1; funext; congr; sorry}

lemma aux6 :
  ∑ k in range n, ↑(choose n k) * a^(n-k) * b^(k+1) +
    ↑(choose n n) * a^0 * b^(n+1) =
  ∑ k in Ico 1 (n+1), ↑(choose n (k-1)) * a^(n-(k-1)) * b^k +
    ↑(choose (n+1) (n+1)) * a^0 * b^(n+1) :=
congr_arg2 (+) aux6a (by simp)

example :
  (a + b)^n = ∑ k in range (n+1), (choose n k) * a^(n-k) * b^k :=
begin
  induction n with n HI,
  { simp, },
  { calc (a + b)^(succ n)
         = (a + b)^n * (a + b)
             : pow_succ' (a + b) n
     ... = (∑ k in range (n+1), (choose n k) * a^(n-k) * b^k) * (a + b)
             : by {congr; rw HI}
     ... = (∑ k in range (n+1), (choose n k) * a^(n-k) * b^k) * a +
           (∑ k in range (n+1), (choose n k) * a^(n-k) * b^k) * b
             : mul_add _ a b
     ... = ∑ k in range (n+1), (choose n k) * a^(n-k) * b^k * a +
           ∑ k in range (n+1), (choose n k) * a^(n-k) * b^k * b
             : by {congr; exact sum_mul}
     ... = ∑ k in range (n+1), (choose n k) * a^(n+1-k) * b^k +
           ∑ k in range (n+1), (choose n k) * a^(n-k) * b^(k+1)
             : congr_arg2 (+) aux1 aux2
     ... = ((choose n 0) * a^(n+1) * b^0 +
            ∑ k in Ico 1 (n+1), (choose n k) * a^(n+1-k) * b^k) +
           (∑ k in range n, (choose n k) * a^(n-k) * b^(k+1) +
            (choose n n) * a^0 * b^(n+1))
             : congr_arg2 (+) aux3 aux4
     ... = ((choose (n+1) 0) * a^(n+1) * b^0 +
            (∑ k in Ico 1 (n+1), (choose n k) * a^(n+1-k) * b^k)) +
           (∑ k in Ico 1 (n+1), (choose n (k-1)) * a^(n-(k-1)) * b^k +
            (choose (n+1) (n+1)) * a^0 * b^(n+1))
             : congr_arg2 (+) (congr_arg2 (+) aux5 rfl)
                              sorry
     ... = (choose (n+1) 0) * a^(n+1) * b^0 +
           (∑ k in Ico 1 (n+1), (choose n k + choose n (k-1)) * a^(n+1-k) * b^k) +
           (choose (n+1) (n+1)) * a^0 * b^(n+1)
             : sorry
     ... = (choose (n+1) 0) * a^(n+1) * b^0 +
           (∑ k in Ico 1 (n+1), (choose (n+1) k) * a^(n+1-k) * b^k) +
           (choose (n+1) (n+1)) * a^0 * b^(n+1)
             : sorry
     ... = ∑ k in range (succ n + 1), (choose (succ n) k) * a^(succ n - k) * b^k
             : sorry },
end

example (n k : ℕ) :
  choose (succ n) (succ k) = choose n k + choose n (succ k) :=
choose_succ_succ n k


lemma auxiliar1
  (h : n ≠ 0)
  : ∃ j, n = succ j :=
begin
  cases n with m,
  { contradiction, },
  { use m, },
end

example
  (k : ℕ)
  (h : k ≠ 0)
  : choose (n+1) k = choose n k + choose n (k-1) :=
begin
  cases (auxiliar1 k h) with j hj,
  have h1 : k - 1 = j, from
    calc k - 1 = succ j - 1 : by rw hj
           ... = j          : succ_sub_one j,
  calc choose (n+1) k
       = choose (succ n) (succ j)       : by simp [hj]
   ... = choose n j + choose n (succ j) : choose_succ_succ n j
   ... = choose n (k-1) + choose n k    : by simp [h1, hj]
   ... = choose n k + choose n (k-1)    : add_comm _ _,
end
