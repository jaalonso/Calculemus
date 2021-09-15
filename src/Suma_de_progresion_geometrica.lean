-- Suma_de_progresion_geometrica.lean
-- Suma de progresión geométrica
-- José A. Alonso Jiménez
-- Sevilla, 20 de septiembre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que la suma de los términos de la progresión geomética
--    a + aq + aq² + ··· + aqⁿ
-- es
--      a(1 - qⁿ⁺¹)
--    --------------
--        1 - q
-- ---------------------------------------------------------------------

import data.real.basic
open nat

variable  (n : ℕ)
variables (a q : ℝ)

set_option pp.structure_projections false

@[simp]
def sumaPG : ℝ → ℝ → ℕ → ℝ
| a q 0       := a
| a q (n + 1) := sumaPG a q n + (a * q^(n + 1))

example :
  (1 - q) * sumaPG a q n = a * (1 - q^(n + 1)) :=
begin
  induction n with n HI,
  { simp,
    ac_refl, },
  { calc (1 - q) * sumaPG a q (succ n)
         = (1 - q) * (sumaPG a q n + (a * q^(n + 1)))
           : rfl
     ... = (1 - q) * sumaPG a q n + (1 - q) * (a * q^(n + 1))
           : by ring_nf
     ... = a * (1 - q ^ (n + 1)) + (1 - q) * (a * q^(n + 1))
           : by {congr ; rw HI}
     ... = a * (1 - q ^ (succ n + 1))
           : by ring_nf },
end
