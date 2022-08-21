-- Asociativa_conmutativa_de_los_reales.lean
-- Asociativa conmutativa de los reales.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 22-agosto-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que los números reales tienen la siguente propiedad
--    (a * b) * c = b * (a * c)
-- ---------------------------------------------------------------------

import data.real.basic

variables a b c : ℝ

-- 1ª demostración
-- ===============

example : (a * b) * c = b * (a * c) :=
begin
  rw mul_comm a b,
  rw mul_assoc b a c,
end

-- 2ª demostración
-- ===============

example : (a * b) * c = b * (a * c) :=
calc (a * b) * c
     = (b * a) * c : by rw mul_comm a b
 ... = b * (a * c) : by rw mul_assoc b a c

-- 3ª demostración
-- ===============

example : (a * b) * c = b * (a * c) :=
calc (a * b) * c
     = (b * a) * c : by ring
 ... = b * (a * c) : by ring

-- 4ª demostración
-- ===============

example : (a * b) * c = b * (a * c) :=
by ring
