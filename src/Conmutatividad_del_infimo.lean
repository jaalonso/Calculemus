-- Conmutatividad_del_infimo.lean
-- Si R es un retículo y x, y ∈ R, entonces x ⊓ y = y ⊓ x.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 12-octubre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sea R un retículo. Demostrar que si x, y ∈ R, entonces
--     x ⊓ y = y ⊓ x
-- ----------------------------------------------------------------------

import order.lattice

variables {R : Type*} [lattice R]
variables x y z : R

-- 1ª demostración
-- ===============

lemma aux1 : x ⊓ y ≤ y ⊓ x :=
begin
  have h1 : x ⊓ y ≤ y,
    by exact inf_le_right,
  have h2 : x ⊓ y ≤ x,
    by exact inf_le_left,
  show x ⊓ y ≤ y ⊓ x,
    by exact le_inf h1 h2,
end

example : x ⊓ y = y ⊓ x :=
begin
  have h1 : x ⊓ y ≤ y ⊓ x,
    by exact aux1 x y,
  have h2 : y ⊓ x ≤ x ⊓ y,
    by exact aux1 y x,
  show x ⊓ y = y ⊓ x,
    by exact le_antisymm h1 h2,
end

-- 2ª demostración
-- ===============

lemma aux2 : x ⊓ y ≤ y ⊓ x :=
le_inf inf_le_right inf_le_left

example : x ⊓ y = y ⊓ x :=
le_antisymm (aux2 x y) (aux2 y x)

-- 3ª demostración
-- ===============

lemma aux3 : x ⊓ y ≤ y ⊓ x :=
begin
  apply le_inf,
  apply inf_le_right,
  apply inf_le_left,
end

example : x ⊓ y = y ⊓ x :=
begin
  apply le_antisymm,
  apply aux3,
  apply aux3,
end

-- 4ª demostración
-- ===============

example : x ⊓ y = y ⊓ x :=
by apply le_antisymm; simp

-- 5ª demostración
-- ===============

example : x ⊓ y = y ⊓ x :=
inf_comm
