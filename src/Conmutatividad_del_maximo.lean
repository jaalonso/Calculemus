-- Conmutatividad_del_maximo.lean
-- Si a, b ∈ ℝ, entonces max(a,b) = max(b,a)
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 30-septiembre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si a, b ∈ ℝ, entonces max(a,b) = max(b,a)
-- ---------------------------------------------------------------------

import data.real.basic

variables a b : ℝ

-- 1ª demostración
-- ===============

example : max a b = max b a :=
begin
  apply le_antisymm,
  { show max a b ≤ max b a,
    apply max_le,
    { apply le_max_right },
    { apply le_max_left }},
  { show max b a ≤ max a b,
    apply max_le,
    { apply le_max_right },
    { apply le_max_left }},
end

-- 2ª demostración
-- ===============

example : max a b = max b a :=
begin
  have h : ∀ x y : ℝ, max x y ≤ max y x,
  { intros x y,
    apply max_le,
    { apply le_max_right },
    { apply le_max_left }},
  apply le_antisymm,
  apply h,
  apply h,
end

-- 3ª demostración
-- ===============

example : max a b = max b a :=
begin
  have h : ∀ {x y : ℝ}, max x y ≤ max y x,
  { intros x y,
    exact max_le (le_max_right y x) (le_max_left y x),},
  exact le_antisymm h h,
end

-- 4ª demostración
-- ===============

example : max a b = max b a :=
begin
  apply le_antisymm,
  repeat {
    apply max_le,
    apply le_max_right,
    apply le_max_left },
end
