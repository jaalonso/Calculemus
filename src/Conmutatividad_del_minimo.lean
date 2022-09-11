-- Conmutatividad_del_minimo.lean
-- Si a, b ∈ ℝ, entonces min(a,b) = min(b,a)
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 29-septiembre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si a, b ∈ ℝ, entonces min(a,b) = min(b,a)
-- ---------------------------------------------------------------------

import data.real.basic

variables a b : ℝ

-- 1ª demostración
-- ===============

example : min a b = min b a :=
begin
  apply le_antisymm,
  { show min a b ≤ min b a,
    apply le_min,
    { apply min_le_right },
    { apply min_le_left }},
  { show min b a ≤ min a b,
    apply le_min,
    { apply min_le_right },
    { apply min_le_left }},
end

-- 2ª demostración
-- ===============

example : min a b = min b a :=
begin
  have h : ∀ x y : ℝ, min x y ≤ min y x,
  { intros x y,
    apply le_min,
    { apply min_le_right },
    { apply min_le_left }},
  apply le_antisymm,
  apply h,
  apply h,
end

-- 3ª demostración
-- ===============

example : min a b = min b a :=
begin
  have h : ∀ {x y : ℝ}, min x y ≤ min y x,
  { intros x y,
    exact le_min (min_le_right x y) (min_le_left x y) },
  exact le_antisymm h h,
end

-- 4ª demostración
-- ===============

example : min a b = min b a :=
begin
  apply le_antisymm,
  repeat {
    apply le_min,
    apply min_le_right,
    apply min_le_left },
end
