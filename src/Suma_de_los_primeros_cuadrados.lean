-- Suma_de_los_primeros_cuadrados.lean
-- Suma de los primeros cuadrados
-- José A. Alonso Jiménez
-- Sevilla, 21 de septiembre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que la suma de los primeros cuadrados
--    0² + 1² + 2² + 3² + ··· + n²
-- es n(n+1)(2n+1)/6
-- ---------------------------------------------------------------------

import data.nat.basic
import tactic
open nat

variable (n : ℕ)

set_option pp.structure_projections false

@[simp]
def sumaCuadrados : ℕ → ℕ
| 0     := 0
| (n+1) := sumaCuadrados n + (n+1)^2

-- 1ª demostración
example :
  6 * sumaCuadrados n = n* (n + 1) * (2 * n + 1) :=
begin
  induction n with n HI,
  { simp, },
  { calc 6 * sumaCuadrados (succ n)
         = 6 * (sumaCuadrados n + (n+1)^2)
           : by simp
     ... = 6 * sumaCuadrados n + 6 * (n+1)^2
           : by ring_nf
     ... = n * (n + 1) * (2 * n + 1) + 6 * (n+1)^2
           : by {congr; rw HI}
     ... = (n + 1) * (n * (2 * n + 1) + 6 * (n+1))
           : by ring_nf
     ... = (n + 1) * (2 * n^2 + 7 * n + 6)
           : by ring_nf
     ... = (n + 1) * (n + 2) * (2 * n + 3)
           : by ring_nf
     ... = succ n * (succ n + 1) * (2 * succ n + 1)
           : by refl, },
end

-- 2ª demostración
example :
  6 * sumaCuadrados n = n* (n + 1) * (2 * n + 1) :=
begin
  induction n with n HI,
  { simp, },
  { calc 6 * sumaCuadrados (succ n)
         = 6 * (sumaCuadrados n + (n+1)^2)
           : by simp
     ... = 6 * sumaCuadrados n + 6 * (n+1)^2
           : by ring_nf
     ... = n * (n + 1) * (2 * n + 1) + 6 * (n+1)^2
           : by {congr; rw HI}
     ... = (n + 1) * (n + 2) * (2 * n + 3)
           : by ring_nf
     ... = succ n * (succ n + 1) * (2 * succ n + 1)
           : by refl, },
end

-- Referencia:
-- ¿Qué es la Matemática? https://bit.ly/3lrPKAp de R. Courant y
-- H. Robbins p. 21
