-- Cancelativa_de_la_suma_por_la_derecha.lean
-- Cancelativa de la suma por la derecha.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 1-septiembre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
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
