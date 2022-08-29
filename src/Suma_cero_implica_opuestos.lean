-- Suma_cero_implica_opuestos.lean
-- Si R es un anillo y a,b∈R tales que a+b=0, entonces -a=b.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 6-septiembre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si R es un anillo y a, b ∈ R tales que
--    a + b = 0
-- entonces
--    -a = b
-- ----------------------------------------------------------------------

import algebra.ring

variables {R : Type*} [ring R]
variables {a b : R}

-- 1ª demostración
-- ===============

example
  (h : a + b = 0)
  : -a = b :=
calc
  -a  = -a + 0       : (add_zero (-a)).symm
  ... = -a + (a + b) : congr_arg (λ x, -a +x) h.symm
  ... = b            : neg_add_cancel_left a b

-- 2ª demostración
-- ===============

example
  (h : a + b = 0)
  : -a = b :=
calc
  -a  = -a + 0       : by rw add_zero
  ... = -a + (a + b) : by rw h
  ... = b            : by rw neg_add_cancel_left

-- 3ª demostración
-- ===============

example
  (h : a + b = 0)
  : -a = b :=
calc
  -a  = -a + 0       : by simp
  ... = -a + (a + b) : by simp [h]
  ... = b            : by simp

-- 4ª demostración
-- ===============

example
  (h : a + b = 0)
  : -a = b :=
-- by library_search
add_eq_zero_iff_neg_eq.mp h
