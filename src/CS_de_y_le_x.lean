-- CS_de_y_le_x.lean
-- Pruebas de "(∀ ε > 0, y ≤ x + ε) →  y ≤ x"
-- José A. Alonso Jiménez
-- Sevilla, 15 de septiembre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sean x, y ∈ ℝ. Demostrar que
--    (∀ ε > 0, y ≤ x + ε) →  y ≤ x
-- ----------------------------------------------------------------------

import data.real.basic

variables {x y : ℝ}

-- 1ª demostración
example :
  (∀ ε > 0, y ≤ x + ε) → y ≤ x :=
begin
  contrapose!,
  intro h,
  use (y-x)/2,
  split,
  { apply half_pos,
    exact sub_pos.mpr h, },
  { calc x + (y - x) / 2
         = (x + y) / 2   : by ring_nf
     ... < (y + y) / 2   : div_lt_div_of_lt zero_lt_two (add_lt_add_right h y)
     ... = (2 * y) / 2   : congr_arg2 (/) (two_mul y).symm rfl
     ... = y             : by ring_nf, },
end

-- 2ª demostración
example :
  (∀ ε > 0, y ≤ x + ε) → y ≤ x :=
begin
  contrapose!,
  intro h,
  use (y-x)/2,
  split,
  { exact half_pos (sub_pos.mpr h), },
  { calc x + (y - x) / 2
         = (x + y) / 2   : by ring_nf
     ... < (y + y) / 2   : by linarith
     ... = (2 * y) / 2   : by ring_nf
     ... = y             : by ring_nf, },
end

-- 3ª demostración
example :
  (∀ ε > 0, y ≤ x + ε) → y ≤ x :=
begin
  contrapose!,
  intro h,
  use (y-x)/2,
  split,
  { linarith },
  { linarith },
end

-- 4ª demostración
example :
  (∀ ε > 0, y ≤ x + ε) → y ≤ x :=
begin
  contrapose!,
  intro h,
  use (y-x)/2,
  split ; linarith,
end

-- 5ª demostración
example :
  (∀ ε > 0, y ≤ x + ε) → y ≤ x :=
begin
  intro h1,
  by_contradiction h2,
  replace h2 : x < y := not_le.mp h2,
  rcases (exists_between h2) with ⟨z, h3, h4⟩,
  replace h3 : 0 < z - x := sub_pos.mpr h3,
  replace h1 : y ≤ x + (z - x) := h1 (z - x) h3,
  replace h1 : y ≤ z := by finish,
  have h4 : y < y := gt_of_gt_of_ge h4 h1,
  exact absurd h4 (irrefl y),
end

-- 6ª demostración
example :
  (∀ ε > 0, y ≤ x + ε) → y ≤ x :=
begin
  intro h1,
  by_contradiction h2,
  replace h2 : x < y := not_le.mp h2,
  rcases (exists_between h2) with ⟨z, hxz, hzy⟩,
  apply lt_irrefl y,
  calc y ≤ x + (z - x) : h1 (z - x) (sub_pos.mpr hxz)
     ... = z           : by ring
     ... < y           : hzy,
end
