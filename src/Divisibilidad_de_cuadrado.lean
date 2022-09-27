-- Divisibilidad_de_cuadrado.lean
-- Si x ∈ ℕ, entonces x ∣ x^2.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 7-octubre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si x ∈ ℕ, entonces
--    x ∣ x^2
-- ----------------------------------------------------------------------

import data.nat.pow
variable x : ℕ

-- 1ª demostración
-- ===============

example : x ∣ x^2 :=
begin
  rw pow_two,
  apply dvd_mul_right,
end

-- 2ª demostración
-- ===============

example : x ∣ x^2 :=
by apply dvd_mul_right
