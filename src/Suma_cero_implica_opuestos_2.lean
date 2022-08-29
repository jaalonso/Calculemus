-- Suma_cero_implica_opuestos_2.lean
-- Si R es un anillo y a,b∈R tales que a+b=0, entonces a=-b.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 7-septiembre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si R es un anillo y a, b ∈ R tales que
--    a + b = 0
-- entonces
--    a = -b
-- ----------------------------------------------------------------------

import algebra.ring

variables {R : Type*} [ring R]
variables {a b : R}

example : 0 = b + -b := (add_neg_self b).symm

-- 1ª demostración
-- ===============

example
  (h : a + b = 0)
  : a = -b :=
calc
  a   = a + 0        : (add_zero a).symm
  ... = a + (b + -b) : congr_arg (λ x, a + x) (add_neg_self b).symm
  ... = (a + b) + -b : (add_assoc a b (-b)).symm
  ... = 0 + -b       : congr_arg (λ x, x + -b) h
  ... = -b           : zero_add (-b)

-- 2ª demostración
-- ===============

example
  (h : a + b = 0)
  : a = -b :=
calc
  a   = a + 0        : by rw add_zero
  ... = a + (b + -b) : by {congr ; rw add_neg_self}
  ... = (a + b) + -b : by rw add_assoc
  ... = 0 + -b       : by {congr; rw h}
  ... = -b           : by rw zero_add

-- 3ª demostración
-- ===============

example
  (h : a + b = 0)
  : a = -b :=
calc
  a   = a + 0        : by simp
  ... = a + (b + -b) : by simp
  ... = (a + b) + -b : by simp
  ... = 0 + -b       : by simp [h]
  ... = -b           : by simp

-- 4ª demostración
-- ===============

example
  (h : a + b = 0)
  : a = -b :=
-- by library_search
add_eq_zero_iff_eq_neg.mp h
