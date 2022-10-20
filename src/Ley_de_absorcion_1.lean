-- Ley_de_absorcion_1.lean
-- Si R es un retículo y x, y ∈ R, entonces x ⊓ (x ⊔ y) = x
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 20-octubre-2022
-- ---------------------------------------------------------------------

import order.lattice
variables {R : Type*} [lattice R]
variables x y : R

-- 1ª demostración
-- ===============

example : x ⊓ (x ⊔ y) = x :=
begin
  have h1 : x ⊓ (x ⊔ y) ≤ x, finish,
  have h2 : x ≤ x ⊓ (x ⊔ y), finish,
  show x ⊓ (x ⊔ y) = x,
    by exact le_antisymm h1 h2,
end

-- 2ª demostración
-- ===============

example : x ⊓ (x ⊔ y) = x :=
begin
  have h1 : x ⊓ (x ⊔ y) ≤ x := inf_le_left,
  have h2 : x ≤ x ⊓ (x ⊔ y),
  { have h2a : x ≤ x := rfl.ge,
    have h2b : x ≤ x ⊔ y := le_sup_left,
    show x ≤ x ⊓ (x ⊔ y),
      by exact le_inf h2a h2b, },
  show x ⊓ (x ⊔ y) = x,
    by exact le_antisymm h1 h2,
end

-- 3ª demostración
-- ===============

example : x ⊓ (x ⊔ y) = x :=
begin
  apply le_antisymm,
  { apply inf_le_left },
  { apply le_inf,
    { apply le_refl },
    { apply le_sup_left }},
end

-- 4ª demostración
example : x ⊓ (x ⊔ y) = x :=
-- by library_search
inf_sup_self

-- 5ª demostración
-- ===============

example : x ⊓ (x ⊔ y) = x :=
-- by hint
by simp
