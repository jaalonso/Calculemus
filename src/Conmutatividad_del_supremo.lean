-- Conmutatividad_del_supremo.lean
-- Si R es un retículo y x, y ∈ R, entonces x ⊔ y = y ⊔ x.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 17-octubre-2022
-- ---------------------------------------------------------------------

import order.lattice

variables {R : Type*} [lattice R]
variables x y : R

-- 1ª demostración
-- ===============

lemma aux1 : x ⊔ y ≤ y ⊔ x :=
begin
  have h1 : x ≤ y ⊔ x,
    by exact le_sup_right,
  have h2 : y ≤ y ⊔ x,
    by exact le_sup_left,
  show x ⊔ y ≤ y ⊔ x,
    by exact sup_le h1 h2,
end

example : x ⊔ y = y ⊔ x :=
begin
  have h1 : x ⊔ y ≤ y ⊔ x,
    by exact aux1 x y,
  have h2 : y ⊔ x ≤ x ⊔ y,
    by exact aux1 y x,
  show x ⊔ y = y ⊔ x,
    by exact le_antisymm h1 h2,
end

-- 2ª demostración
-- ===============

lemma aux2 : x ⊔ y ≤ y ⊔ x :=
sup_le le_sup_right le_sup_left

example : x ⊔ y = y ⊔ x :=
le_antisymm (aux2 x y) (aux2 y x)

-- 3ª demostración
-- ===============

lemma aux : x ⊔ y ≤ y ⊔ x :=
begin
  apply sup_le,
  apply le_sup_right,
  apply le_sup_left,
end

example : x ⊔ y = y ⊔ x :=
begin
  apply le_antisymm,
  apply aux,
  apply aux,
end

-- 4ª demostración
-- ===============

example : x ⊔ y = y ⊔ x :=
by apply le_antisymm; simp

-- 5ª demostración
-- ===============

example : x ⊔ y = y ⊔ x :=
-- by library_search
sup_comm

-- 6ª demostración
-- ===============

example : x ⊔ y = y ⊔ x :=
-- by hint
by finish
