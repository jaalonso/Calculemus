-- Suma_constante_es_inyectiva.lean
-- Para todo c ∈ ℝ, la función f(x) = x+c es inyectiva.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 22-noviembre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que, para todo c la función
--    f(x) = x + c
-- es inyectiva
-- ----------------------------------------------------------------------

import data.real.basic

open function

variable {c : ℝ}

-- 1ª demostración
-- ===============

example : injective (λ x, x + c) :=
begin
  assume x1 : ℝ,
  assume x2 : ℝ,
  assume h1 : (λ x, x + c) x1 = (λ x, x + c) x2,
  have h2 : x1 + c = x2 + c := h1,
  show x1 = x2,
    by exact (add_left_inj c).mp h2,
end

-- 2ª demostración
-- ===============

example : injective (λ x, x + c) :=
begin
  intros x1 x2 h,
  change x1 + c = x2 + c at h,
  apply add_right_cancel h,
end

-- 3ª demostración
-- ===============

example : injective (λ x, x + c) :=
begin
  intros x1 x2 h,
  apply (add_left_inj c).mp,
  exact h,
end

-- 4ª demostración
-- ===============

example : injective (λ x, x + c) :=
λ x1 x2 h, (add_left_inj c).mp h
