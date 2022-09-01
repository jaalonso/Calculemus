-- Ejercicio_sobre_orden.lean
-- Si a, b, c, d, e ∈ ℝ tales que a ≤ b, b < c, c ≤ d, d < e, entonces a < e
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 20-septiembre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si a, b, c, d, e ∈ ℝ tales que
--    a ≤ b
--    b < c
--    c ≤ d
--    d < e
-- entonces
--    a < e
-- ----------------------------------------------------------------------

import data.real.basic

variables a b c d e : ℝ

-- 1ª demostración
-- ===============

example
  (h₀ : a ≤ b)
  (h₁ : b < c)
  (h₂ : c ≤ d)
  (h₃ : d < e) :
  a < e :=
calc a ≤ b : h₀
   ... < c : h₁
   ... ≤ d : h₂
   ... < e : h₃

-- 2ª demostración
-- ===============

example
  (h₀ : a ≤ b)
  (h₁ : b < c)
  (h₂ : c ≤ d)
  (h₃ : d < e) :
  a < e :=
begin
  apply lt_of_le_of_lt h₀,
  apply lt_trans h₁,
  apply lt_of_le_of_lt h₂,
  exact h₃,
end

-- 3ª demostración
-- ===============

example
  (h₀ : a ≤ b)
  (h₁ : b < c)
  (h₂ : c ≤ d)
  (h₃ : d < e) :
  a < e :=
by finish

-- 4ª demostración
-- ===============

example
  (h₀ : a ≤ b)
  (h₁ : b < c)
  (h₂ : c ≤ d)
  (h₃ : d < e) :
  a < e :=
by linarith
