-- Caracterizacion_de_producto_igual_al_primer_factor.lean
-- Caracterización de producto igual al primer factor
-- José A. Alonso Jiménez
-- Sevilla, 3 de julio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Un monoide cancelativo por la izquierda es un monoide
-- https://bit.ly/3h4notA M que cumple la propiedad cancelativa por la
-- izquierda; es decir, para todo a, b ∈ M
--    a * b = a * c ↔ b = c.
--
-- En Lean la clase de los monoides cancelativos por la izquierda es
-- left_cancel_monoid y la propiedad cancelativa por la izquierda es
--    mul_left_cancel_iff : a * b = a * c ↔ b = c
--
-- Demostrar que si M es un monoide cancelativo por la izquierda y
-- a, b ∈ M, entonces
--    a * b = a ↔ b = 1
-- ---------------------------------------------------------------------

import algebra.group.basic

universe  u
variables {M : Type u} [left_cancel_monoid M]
variables {a b : M}

-- ?ª demostración
-- ===============

example : a * b = a ↔ b = 1 :=
begin
  split,
  { intro h,
    rw ← @mul_left_cancel_iff _ _ a b 1,
    rw mul_one,
    exact h, },
  { intro h,
    rw h,
    exact mul_one a, },
end

-- ?ª demostración
-- ===============

example : a * b = a ↔ b = 1 :=
calc a * b = a ↔ a * b = a * 1 : by rw mul_one
           ... ↔ b = 1         : mul_left_cancel_iff

-- ?ª demostración
-- ===============

example : a * b = a ↔ b = 1 :=
mul_right_eq_self

-- ?ª demostración
-- ===============

example : a * b = a ↔ b = 1 :=
by finish
