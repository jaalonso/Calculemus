-- Suma_de_cubos_de_impares.lean
-- Suma de cubos de impares
-- José A. Alonso Jiménez
-- Sevilla, 26 de septiembre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    1³ + 3³ + 5³ + ... + (2n-1)³ = n²(2n²-1)
-- ---------------------------------------------------------------------

import algebra.big_operators
import tactic
open finset nat

open_locale big_operators
set_option pp.structure_projections false

variable (n : ℕ)

example :
  ∑ k in Ico 1 (n+1), (2*k-1)^3 = n^2*(2*n^2-1) :=
begin
  induction n with n HI,
  { simp, },
  { calc ∑ k in Ico 1 (succ n + 1), (2*k - 1)^3
         = (∑ k in Ico 1 (succ n), (2*k - 1)^3) + (2 * succ n - 1)^3
             : sum_Ico_succ_top (succ_pos n) (λ k, (2*k - 1)^3)
     ... = n^2 * (2*n^2 - 1) + (2 * succ n - 1)^3
             : by {congr; rw HI}
     ... = n^2 * (2*n^2 - 1) + (2*n + 1)^3
             : by congr
     ... = n^2 * (2*n^2 - 1) + (1 + 6*n + 12*n^2 + 8*n^3)
             : by nlinarith
     ... = (2*n^4 - n^2) + (1 + 6*n + 12*n^2 + 8*n^3)
             : by {congr' 1; zify; sorry}
     ... = 2*n^4 + 8*n^3 + 11*n^2 + 6*n + 1
             : sorry
     ... = succ n ^ 2 * (2 * succ n ^ 2 - 1)
             : sorry },
end

example : n * (n - 1) = n^2 - n := sorry
example : n^2 * (2*n^2 - 1) = n^2*2*n^2 - n^2*1 := sorry

example : (n + 1) ^ 2 = n^2 + 2*n + 1 := by nlinarith

example : (2 * n + 1) ^ 3 = 1 + 6*n + 12*n^2 + 8*n^3 := by nlinarith

-- Referencia: "Sum of sequence of odd cubes" https://bit.ly/3EPWocw en
-- ProofWiki.
