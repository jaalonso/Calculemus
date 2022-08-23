-- Opuesto_se_cancela_con_la_suma_por_la_derecha.lean
-- Opuesto se cancela con la suma por la derecha
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 30-agosto-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean, se declara que R es un anillo mediante la expresión
--    variables {R : Type*} [ring R]
-- Como consecuencia, se tiene los siguientes axiomas
--    add_assoc    : ∀ a b c : R, (a + b) + c = a + (b + c)
--    add_comm     : ∀ a b : R,   a + b = b + a
--    zero_add     : ∀ a : R,     0 + a = a
--    add_left_neg : ∀ a : R,     -a + a = 0
--    mul_assoc    : ∀ a b c : R, a * b * c = a * (b * c)
--    mul_one      : ∀ a : R,     a * 1 = a
--    one_mul      : ∀ a : R,     1 * a = a
--    mul_add      : ∀ a b c : R, a * (b + c) = a * b + a * c
--    add_mul      : ∀ a b c : R, (a + b) * c = a * c + b * c
--
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
