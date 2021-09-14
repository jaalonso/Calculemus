-- Suma_de_los_primeros_n_numeros_naturales.lean
-- Suma de los primeros n números naturales
-- José A. Alonso Jiménez
-- Sevilla, 18 de septiembre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que la suma de los números naturales
--    0 + 1 + 2 + 3 + ··· + n
-- es n × (n + 1)/2
-- ---------------------------------------------------------------------

import data.nat.basic
import tactic
open nat

variable (n : ℕ)

set_option pp.structure_projections false

@[simp]
def suma : ℕ → ℕ
| 0     := 0
| (n+1) := suma n + (n+1)

-- ?ª demostración
example :
  2 * suma n = n * (n + 1) :=
begin
  induction n with n HI,
  { calc 2 * suma 0
         = 2 * 0       : congr_arg ((*) 2) suma.equations._eqn_1
     ... = 0           : mul_zero 2
     ... = 0 * (0 + 1) : zero_mul (0 + 1), },
  { calc 2 * suma (n + 1)
         = 2 * (suma n + (n + 1))    : congr_arg ((*) 2) (suma.equations._eqn_2 n)
     ... = 2 * suma n + 2 * (n + 1)  : mul_add 2 (suma n) (n + 1)
     ... = n * (n + 1) + 2 * (n + 1) : congr_arg2 (+) HI rfl
     ... = (n + 2) * (n + 1)         : (add_mul n 2 (n + 1)).symm
     ... = (n + 1) * (n + 2)         : mul_comm (n + 2) (n + 1) },
end

-- ?ª demostración
example :
  2 * suma n = n * (n + 1) :=
begin
  induction n with n HI,
  { calc 2 * suma 0
         = 2 * 0       : rfl
     ... = 0           : rfl
     ... = 0 * (0 + 1) : rfl, },
  { calc 2 * suma (n + 1)
         = 2 * (suma n + (n + 1))    : rfl
     ... = 2 * suma n + 2 * (n + 1)  : by ring
     ... = n * (n + 1) + 2 * (n + 1) : by simp [HI]
     ... = (n + 2) * (n + 1)         : by ring
     ... = (n + 1) * (n + 2)         : by ring, },
end

-- ?ª demostración
example :
  2 * suma n = n * (n + 1) :=
begin
  induction n with n HI,
  { simp, },
  { calc 2 * suma (n + 1)
         = 2 * (suma n + (n + 1))    : rfl
     ... = 2 * suma n + 2 * (n + 1)  : by ring
     ... = n * (n + 1) + 2 * (n + 1) : by simp [HI]
     ... = (n + 1) * (n + 2)         : by ring, },
end
