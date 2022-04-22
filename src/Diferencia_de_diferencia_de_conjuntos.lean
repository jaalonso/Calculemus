-- Diferencia_de_diferencia_de_conjuntos.lean
-- Diferencia de diferencia de conjuntos
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 23-abril-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    (s \ t) \ u ⊆ s \ (t ∪ u)
-- ----------------------------------------------------------------------

import data.set.basic
open set

variable {α : Type}
variables s t u : set α

-- 1ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
begin
  intros x hx,
  cases hx with hxst hxnu,
  cases hxst with hxs hxnt,
  split,
  { exact hxs },
  { dsimp,
    by_contradiction hxtu,
    cases hxtu with hxt hxu,
    { apply hxnt,
      exact hxt, },
    { apply hxnu,
      exact hxu, }},
end
  
-- 2ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
begin
  rintros x ⟨⟨hxs, hxnt⟩, hxnu⟩,
  split,
  { exact hxs },
  { by_contradiction hxtu,
    cases hxtu with hxt hxu,
    { exact hxnt hxt, },
    { exact hxnu hxu, }},
end
  
-- 3ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
begin
  rintros x ⟨⟨xs, xnt⟩, xnu⟩,
  use xs,
  rintros (xt | xu),
  { contradiction, },
  { contradiction, },
end

-- 4ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
begin
  rintros x ⟨⟨xs, xnt⟩, xnu⟩,
  use xs,
  rintros (xt | xu); contradiction, 
end

-- 5ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
begin
  intros x xstu,
  simp at *,
  finish,
end

-- 6ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
begin
  intros x xstu,
  finish,
end

-- 7ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
by rw diff_diff

-- 8ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
by tidy 
