-- Suma_de_progresion_aritmetica.lean
-- Suma de progresión aritmética
-- José A. Alonso Jiménez
-- Sevilla, 19 de septiembre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que la suma de los términos de la progresión aritmética
--    a + (a + d) + (a + 2 × d) + ··· + (a + n × d)
-- es (n + 1) × (2 × a + n × d) / 2.
-- ---------------------------------------------------------------------

import data.real.basic
open nat

variable  (n : ℕ)
variables (a d : ℝ)

set_option pp.structure_projections false

@[simp]
def sumaPA : ℝ → ℝ → ℕ → ℝ
| a d 0       := a
| a d (n + 1) := sumaPA a d n + (a + (n + 1) * d)

example :
  2 * sumaPA a d n = (n + 1) * (2 * a + n * d) :=
begin
  induction n with n HI,
  { simp, },
  { calc 2 * sumaPA a d (succ n)
         = 2 * (sumaPA a d n + (a + (n + 1) * d))
           : rfl
     ... = 2 * sumaPA a d n + 2 * (a + (n + 1) * d)
           : by ring_nf
     ... = ((n + 1) * (2 * a + n * d)) + 2 * (a + (n + 1) * d)
           : by {congr; rw HI}
     ... = (n + 2) * (2 * a + (n + 1) * d)
           : by ring_nf
     ... = (succ n + 1) * (2 * a + succ n * d)
           : congr_arg2 (*) (by norm_cast) rfl, },
end
