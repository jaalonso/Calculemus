-- Opuesto_se_cancela_con_la_suma_por_la_derecha.lean
-- Opuesto se cancela con la suma por la derecha
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 30-agosto-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si R es un anillo, entonces
--    ∀ a b : R, (a + b) + -b = a
-- ---------------------------------------------------------------------

import algebra.ring

variables {R : Type*} [ring R]
variables a b : R

-- 1ª demostración
-- ===============

example : (a + b) + -b = a :=
calc (a + b) + -b
     = a + (b + -b) : by rw add_assoc
 ... = a + 0        : by rw add_right_neg
 ... = a            : by rw add_zero

-- 2ª demostración
-- ===============

example : (a + b) + -b = a :=
begin
  rw add_assoc,
  rw add_right_neg,
  rw add_zero,
end

-- 3ª demostración
-- ===============

example : (a + b) + -b = a :=
by rw [add_assoc, add_right_neg, add_zero]

-- 4ª demostración
-- ===============

example : (a + b) + -b = a :=
-- by library_search
add_neg_eq_of_eq_add rfl

-- 5ª demostración
-- ===============

example : (a + b) + -b = a :=
-- by hint
by finish
