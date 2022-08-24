-- Cancelativa_de_la_suma_por_la_derecha.lean
-- Cancelativa de la suma por la derecha.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 1-septiembre-2022
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
-- Demostrar que si R es un anillo y a, b, c ∈ R tales que
--    a + b = c + b
-- entonces
--    a = c
-- ---------------------------------------------------------------------

import algebra.ring
import tactic

variables {R : Type*} [ring R]
variables {a b c : R}

-- 1ª demostración
-- ===============

example
  (h : a + b = c + b)
  : a = c :=
calc a
     = a + 0        : by rw add_zero
 ... = a + (b + -b) : by rw add_right_neg
 ... = (a + b) + -b : by rw add_assoc
 ... = (c + b) + -b : by rw h
 ... = c + (b + -b) : by rw ← add_assoc
 ... = c + 0        : by rw ← add_right_neg
 ... = c            : by rw add_zero

-- 2ª demostración
-- ===============

example
  (h : a + b = c + b)
  : a = c :=
calc a
     = a + 0        : by simp
 ... = a + (b + -b) : by simp
 ... = (a + b) + -b : by simp
 ... = (c + b) + -b : by rw h
 ... = c + (b + -b) : by simp
 ... = c + 0        : by simp
 ... = c            : by simp

-- 3ª demostración
-- ===============

lemma aux : (a + b) + -b = a :=
by finish

example
  (h : a + b = c + b)
  : a = c :=
calc a
     = (a + b) + -b : aux.symm
 ... = (c + b) + -b : congr_arg (λ x, x + -b) h
 ... = c            : aux

-- 4ª demostración
-- ===============

example
  (h : a + b = c + b)
  : a = c :=
by finish
