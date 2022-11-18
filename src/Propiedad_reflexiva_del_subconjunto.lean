-- Propiedad_reflexiva_del_subconjunto.lean
-- Para cualquier conjunto s, s ⊆ s.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 18-noviembre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que para cualquier conjunto s, s ⊆ s.
-- ----------------------------------------------------------------------

import tactic
variables {α : Type*} (s : set α)

-- 1ª demostración
-- ===============

example : s ⊆ s :=
begin
  assume x,
  assume xs: x ∈ s,
  show x ∈ s,
    by exact xs,
end

-- 2ª demostración
-- ===============

example : s ⊆ s :=
begin
  intros x xs,
  exact xs,
end

-- 3ª demostración
-- ===============

example : s ⊆ s :=
λ x (xs : x ∈ s), xs

-- 4ª demostración
-- ===============

example : s ⊆ s :=
-- by library_search
rfl.subset

-- 5ª demostración
-- ===============

example : s ⊆ s :=
-- by hint
by refl
