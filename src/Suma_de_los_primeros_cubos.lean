-- Suma_de_los_primeros_cubos.lean
-- Suma de los primeros cubos
-- José A. Alonso Jiménez
-- Sevilla, 22 de septiembre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que la suma de los primeros cubos
--    0³ + 1³ + 2³ + 3³ + ··· + n³
-- es (n(n+1)/2)²
-- ---------------------------------------------------------------------

import data.nat.basic
import tactic
open nat

variable (n : ℕ)

set_option pp.structure_projections false

@[simp]
def sumaCubos : ℕ → ℕ
| 0     := 0
| (n+1) := sumaCubos n + (n+1)^3

-- 1ª demostración
example :
  4 * sumaCubos n = (n*(n+1))^2 :=
begin
  induction n with n HI,
  { simp, },
  { calc 4 * sumaCubos (succ n)
         = 4 * (sumaCubos n + (n+1)^3)
           : by simp
     ... = 4 * sumaCubos n + 4*(n+1)^3
           : by ring
     ... = (n*(n+1))^2 + 4*(n+1)^3
           : by {congr; rw HI}
     ... = (n+1)^2*(n^2+4*n+4)
           : by ring
     ... = (n+1)^2*(n+2)^2
           : by ring
     ... = ((n+1)*(n+2))^2
           : by ring
     ... = (succ n * (succ n + 1)) ^ 2
           : by simp, },
end

-- 2ª demostración
example :
  4 * sumaCubos n = (n*(n+1))^2 :=
begin
  induction n with n HI,
  { simp, },
  { calc 4 * sumaCubos (succ n)
         = 4 * sumaCubos n + 4*(n+1)^3
           : by {simp ; ring}
     ... = (n*(n+1))^2 + 4*(n+1)^3
           : by {congr; rw HI}
     ... = ((n+1)*(n+2))^2
           : by ring
     ... = (succ n * (succ n + 1)) ^ 2
           : by simp, },
end

-- Referencia:
-- ¿Qué es la Matemática? https://bit.ly/3lrPKAp de R. Courant y
-- H. Robbins p. 22
