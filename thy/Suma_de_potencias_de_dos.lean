-- Suma_de_potencias_de_dos.lean
-- Suma de potencias de dos
-- José A. Alonso Jiménez
-- Sevilla, 25 de septiembre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    1 + 2 + 2² + 2³ + ... + 2⁽ⁿ⁻¹⁾ = 2ⁿ - 1
-- ---------------------------------------------------------------------

import algebra.big_operators
import tactic
open finset nat

open_locale big_operators
set_option pp.structure_projections false

variable (n : ℕ)

-- 1ª demostración
example :
  ∑ k in range n, 2^k = 2^n - 1 :=
begin
  induction n with n HI,
  { simp, },
  { calc ∑ k in range (succ n), 2^k
         = ∑ k in range n, 2^k + 2^n
             : sum_range_succ (λ x, 2 ^ x) n
     ... = (2^n - 1) + 2^n
             : congr_arg2 (+) HI rfl
     ... = (2^n + 2^n) - 1
             : by omega
     ... = 2^n * 2 - 1
             : by {congr; simp}
     ... = 2^(succ n) - 1
             : by {congr' 1; ring_nf}, },
end
