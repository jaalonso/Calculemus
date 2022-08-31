-- Subtraccion_en_anillos.lean
-- Si R es un anillo y a, b ∈ R, entonces a - b = a + -b
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 12-septiembre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si R es un anillo y a, b ∈ R entonces
--    a - b = a + -b
-- ----------------------------------------------------------------------

import algebra.ring

variables {R : Type*} [ring R]
variables {a b : R}

-- 1ª demostración
-- ===============

example : a - b = a + -b :=
begin
  apply sub_eq_iff_eq_add.mpr,
  calc a
       = a + 0        : (add_zero a).symm
   ... = a + (-b + b) : congr_arg (λ x, a + x) (neg_add_self b).symm
   ... = a + -b + b   : (add_assoc a (-b) b).symm
end

-- 2ª demostración
-- ===============

example : a - b = a + -b :=
begin
  apply sub_eq_iff_eq_add.mpr,
  calc a
       = a + 0        : by rw add_zero
   ... = a + (-b + b) : by {congr; rw neg_add_self}
   ... = a + -b + b   : by rw add_assoc
end

-- 3ª demostración
-- ===============

example : a - b = a + -b :=
begin
  rw sub_eq_iff_eq_add,
  rw add_assoc,
  rw neg_add_self,
  rw add_zero,
end

-- 4ª demostración
-- ===============

example : a - b = a + -b :=
by rw [sub_eq_iff_eq_add, add_assoc, neg_add_self, add_zero]

-- 5ª demostración
-- ===============

example : a - b = a + -b :=
by simp [sub_eq_iff_eq_add]

-- 6ª demostración
-- ===============

example : a - b = a + -b :=
-- by library_search
sub_eq_add_neg a b
