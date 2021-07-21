-- Si_f(x)_leq_f(y)_to_x_leq_y,_entonces_f_es_inyectiva.lean
-- Si `f x ≤ f y → x ≤ y`, entonces f es inyectiva
-- José A. Alonso Jiménez
-- Sevilla, 22 de julio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sea f una función de ℝ en ℝ tal que
--    ∀ x y, f(x) ≤ f(y) → x ≤ y
-- Demostrar que f es inyectiva.
-- ---------------------------------------------------------------------

import data.real.basic
open function

variable (f : ℝ → ℝ)

-- 1ª demostración
example
  (h : ∀ {x y}, f x ≤ f y → x ≤ y)
  : injective f :=
begin
  intros x y hxy,
  apply le_antisymm,
  { apply h,
    exact le_of_eq hxy, },
  { apply h,
    exact ge_of_eq hxy, },
end

-- 2ª demostración
example
  (h : ∀ {x y}, f x ≤ f y → x ≤ y)
  : injective f :=
begin
  intros x y hxy,
  apply le_antisymm,
  { exact h (le_of_eq hxy), },
  { exact h (ge_of_eq hxy), },
end

-- 3ª demostración
example
  (h : ∀ {x y}, f x ≤ f y → x ≤ y)
  : injective f :=
λ x y hxy, le_antisymm (h hxy.le) (h hxy.ge)
