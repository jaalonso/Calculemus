-- Ley_de_absorcion_2.lean
-- Si R es un retículo y x, y ∈ R, entonces x ⊔ (x ⊓ y) = x
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 21-octubre-2022
-- ---------------------------------------------------------------------

import order.lattice
variables {R : Type*} [lattice R]
variables x y : R

-- 1ª demostración
-- ===============

example : x ⊔ (x ⊓ y) = x :=
begin
  have h1 : x ⊔ (x ⊓ y) ≤ x, finish,
  have h2 : x ≤ x ⊔ (x ⊓ y), finish,
  show x ⊔ (x ⊓ y) = x,
    by exact le_antisymm h1 h2,
end

-- 2ª demostración
-- ===============

example : x ⊔ (x ⊓ y) = x :=
begin
  have h1 : x ⊔ (x ⊓ y) ≤ x,
  { have h1a : x ≤ x := le_rfl,
    have h1b : x ⊓ y ≤ x := inf_le_left,
    show x ⊔ (x ⊓ y) ≤ x,
      by exact sup_le h1a h1b,
  },
  have h2 : x ≤ x ⊔ (x ⊓ y) := le_sup_left,
  show x ⊔ (x ⊓ y) = x,
    by exact le_antisymm h1 h2,
end

-- 3ª demostración
-- ===============

example : x ⊔ (x ⊓ y) = x :=
begin
  apply le_antisymm,
  { apply sup_le,
    { apply le_refl },
    { apply inf_le_left }},
  { apply le_sup_left },
end

-- 4ª demostración
-- ===============

example : x ⊔ (x ⊓ y) = x :=
-- by library_search
sup_inf_self

-- 4ª demostración
-- ===============

example : x ⊔ (x ⊓ y) = x :=
-- by hint
by simp
