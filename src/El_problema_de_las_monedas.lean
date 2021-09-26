-- El_problema_de_las_monedas.lean
-- El problema de las monedas
-- José A. Alonso Jiménez
-- Sevilla, 26 de septiembre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que con monedas de 3 y 5 se puede obtener cualquier
-- cantidad que sea mayor o igual a 8.
-- ---------------------------------------------------------------------

import tactic
open nat

variable (n : ℕ)

example :
  ∃ a b, n + 8 = 3*a + 5*b :=
begin
  induction n with n HI,
  { use [1, 1],
    simp, },
  { rcases HI with ⟨a, b, h⟩,
    by_cases hb : (b = 0),
    { have ha : a ≥ 3 := sorry,
      use [a-3, 2],
      calc succ n + 8
           = (n + 8) + 1
               : by simp
       ... = (3 * a + 5 * b) + 1
               : by rw h
       ... = (3 * a + 5 * 0) + 1
               : by rw hb
       ... = 3 * a + 1
               : by simp
       ... = 3 * (a - 3) + 5 * 2
               : sorry, },
    { use [a+2, b-1],
sorry }},
end

example (a : ℕ) : 3 * (a + 3) = 3 * a + 9 := by linarith
example (a : ℕ) : 3 * (a + 2) = 3 * a + 6 := by linarith

example (a : ℕ) (ha : a ≥ 3) : 3 * (a - 3) = 3 * a - 9 := by nlinarith
