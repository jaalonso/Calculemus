-- Prueba_de_1:(1x2)+1:(2x3)+1:(3x4)+...+1:(nx(n+1))_es_n:(n+1).lean
-- Prueba de 1/(1x2)+1/(2x3)+1/(3x4)+...+1/(nx(n+1)) = n/(n+1)
-- José A. Alonso Jiménez
-- Sevilla, 26 de septiembre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    1/(1*2)+1/(2*3)+1/(3*4)+...+1/(n*(n+1)) = n/(n+1)
-- ---------------------------------------------------------------------

import data.rat.basic
import algebra.big_operators
import tactic
open finset nat rat

open_locale big_operators
open_locale rat
set_option pp.structure_projections false

variable (n : ℕ)

example : 1 ≤ succ n := succ_pos n

example (b : ℤ) (h : b ≠ 0) : b /. b = 1 := by norm_cast at *

example (a b : ℕ) (ha : a > 0) (hb : b > 0) : n / a = (n * b) / (a * b) :=
begin
  calc n / a
       = (n / a) * 1       : by ring
   ... = (n / a) * (b / b) : by finish [nat.div_self]
   ... = (n * b) / (a * b) : sorry,
end



example
  : ∑ k in Ico 1 (succ n), 1 / (k * (k + 1)) = n / (n + 1) :=
begin
  induction n with n HI,
  { simp, },
  { calc ∑ k in Ico 1 (succ n + 1), 1 / (k * (k + 1))
         = (∑ k in Ico 1 (succ n), 1 / (k * (k + 1))) +
           1 / (succ n * (succ n + 1))
             : sum_Ico_succ_top (succ_pos n) (λ k, 1 / (k * (k + 1)))
     ... = n / (n + 1) + 1 / (succ n * (succ n + 1))
             : by {congr; rw HI}
     ... = n / (n + 1) + 1 / ((n + 1) * (n + 2))
             : by simp
     ... = (n * (n + 2)) / ((n + 1) * (n + 2)) + 1 / ((n + 1) * (n + 2))
             : by {congr' 1 ; by suggest}
     ... = succ n / (succ n + 1)
             : sorry },
end

-- Referencia: "El método de la inducción matemática" de I.S. Sominski
-- p. 13.
