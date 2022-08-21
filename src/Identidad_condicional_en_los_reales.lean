-- Identidad_condicional_en_los_reales.lean
-- Identidad condicional en los reales.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 23-agosto-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si a, b, c, d, e y f son números reales
-- tales que
--    a * b = c * d
--    e = f
-- Entonces,
--    a * (b * e) = c * (d * f)
-- ---------------------------------------------------------------------

import data.real.basic

variables a b c d e f : ℝ

-- 1ª demostración
example
  (h1 : a * b = c * d)
  (h2 : e = f)
  : a * (b * e) = c * (d * f) :=
begin
  rw h2,
  rw ←mul_assoc,
  rw h1,
  rw mul_assoc,
end

-- 2ª demostración
example
  (h1 : a * b = c * d)
  (h2 : e = f)
  : a * (b * e) = c * (d * f) :=
calc a * (b * e)
     = a * (b * f) : by rw h2
 ... = (a * b) * f : by rw ←mul_assoc
 ... = (c * d) * f : by rw h1
 ... = c * (d * f) : by rw mul_assoc

-- 3ª demostración
example
  (h1 : a * b = c * d)
  (h2 : e = f)
  : a * (b * e) = c * (d * f) :=
calc a * (b * e)
     = a * (b * f) : by rw h2
 ... = (a * b) * f : by ring
 ... = (c * d) * f : by rw h1
 ... = c * (d * f) : by ring

-- 4ª demostración
example
  (h1 : a * b = c * d)
  (h2 : e = f)
  : a * (b * e) = c * (d * f) :=
by finish
