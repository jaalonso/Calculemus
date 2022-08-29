-- Cancelativa_de_la_suma_por_la_izquierda.lean
-- Cancelativa de la suma por la izquierda.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 31-agosto-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si R es un anillo y a, b, c ∈ R tales que
--    a + b = a + c
-- entonces
--    b = c
-- ---------------------------------------------------------------------

import algebra.ring
import tactic

variables {R : Type*} [ring R]
variables {a b c : R}

-- 1ª demostración
-- ===============

example
  (h : a + b = a + c)
  : b = c :=
calc b
     = 0 + b        : by rw zero_add
 ... = (-a + a) + b : by rw add_left_neg
 ... = -a + (a + b) : by rw add_assoc
 ... = -a + (a + c) : by rw h
 ... = (-a + a) + c : by rw ←add_assoc
 ... = 0 + c        : by rw add_left_neg
 ... = c            : by rw zero_add

-- 2ª demostración
-- ===============

example
  (h : a + b = a + c)
  : b = c :=
calc b
     = 0 + b        : by simp
 ... = (-a + a) + b : by simp
 ... = -a + (a + b) : by simp
 ... = -a + (a + c) : by rw h
 ... = (-a + a) + c : by simp
 ... = 0 + c        : by simp
 ... = c            : by simp

-- 3ª demostración
-- ===============

lemma aux : -a + (a + b) = b :=
by finish

example
  (h : a + b = a + c)
  : b = c :=
calc b
     = -a + (a + b) : aux.symm
 ... = -a + (a + c) : congr_arg (λ x, -a + x) h
 ... = c            : aux

-- 4ª demostración
-- ===============

example
  (h : a + b = a + c)
  : b = c :=
-- by library_search
(add_right_inj a).mp h

-- 4ª demostración
-- ===============

example
  (h : a + b = a + c)
  : b = c :=
-- by hint
by finish
