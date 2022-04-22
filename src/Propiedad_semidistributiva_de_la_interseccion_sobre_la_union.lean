-- Propiedad semidistributiva de la intersección sobre la unión
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 21-abril-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u)
-- ----------------------------------------------------------------------

import data.set.basic
import tactic

open set

variable {α : Type}
variables s t u : set α

-- 1ª demostración
-- ===============

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
begin
  intros x hx,
  cases hx with hxs hxtu,
  cases hxtu with hxt hxu,
  { left,
    split,
    { exact hxs, },
    { exact hxt, }},
  { right,
    split,
    { exact hxs, },
    { exact hxu, }},
end

-- 2ª demostración
-- ===============

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
begin
  rintros x ⟨hxs, hxt | hxu⟩,
  { left,
    exact ⟨hxs, hxt⟩, },
  { right,
    exact ⟨hxs, hxu⟩, },
end

-- 3ª demostración
-- ===============

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
begin
  rintros x ⟨hxs, hxt | hxu⟩,
  { exact or.inl ⟨hxs, hxt⟩, },
  { exact or.inr ⟨hxs, hxu⟩, },
end

-- 4ª demostración
-- ===============

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
begin
  intros x hx,
  by finish,
end

-- 5ª demostración
-- ===============

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
by rw inter_union_distrib_left
