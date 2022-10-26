-- Distancia_no_negativa.lean
-- Si X es un espacio métrico y x, y ∈ X, entonces dist(x,y) ≥ 0
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 31-octubre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si X es un espacio métrico y x, y ∈ X, entonces
--    0 ≤ dist x y
-- ----------------------------------------------------------------------

import topology.metric_space.basic

variables {X : Type*} [metric_space X]
variables x y : X

-- 1ª demostración
example : 0 ≤ dist x y :=
  have h1 : 2 * dist x y ≥ 0, by calc
    2 * dist x y = dist x y + dist x y : two_mul (dist x y)
             ... = dist x y + dist y x : by rw [dist_comm x y]
             ... ≥ dist x x            : dist_triangle x y x
             ... = 0                   : dist_self x,
  show 0 ≤ dist x y,
    by exact nonneg_of_mul_nonneg_left h1 zero_lt_two

-- 2ª demostración
example : 0 ≤ dist x y :=
-- by library_search
dist_nonneg
