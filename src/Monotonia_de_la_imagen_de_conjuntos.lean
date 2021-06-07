-- Monotonia_de_la_imagen_de_conjuntos.lean
-- Monotonía de la imagen de conjuntos
-- José A. Alonso Jiménez
-- Sevilla, 12 de junio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si s ⊆ t, entonces
--    f '' s ⊆ f '' t
-- ----------------------------------------------------------------------

import data.set.basic
import tactic

open set

variables {α : Type*} {β : Type*}
variable  f : α → β
variables s t : set α

-- 1ª demostración
-- ===============

example
  (h : s ⊆ t)
  : f '' s ⊆ f '' t :=
begin
  intros y hy,
  rw mem_image at hy,
  cases hy with x hx,
  cases hx with xs fxy,
  use x,
  split,
  { exact h xs, },
  { exact fxy, },
end

-- 2ª demostración
-- ===============

example
  (h : s ⊆ t)
  : f '' s ⊆ f '' t :=
begin
  intros y hy,
  rcases hy with ⟨x, xs, fxy⟩,
  use x,
  exact ⟨h xs, fxy⟩,
end

-- 3ª demostración
-- ===============

example
  (h : s ⊆ t)
  : f '' s ⊆ f '' t :=
begin
  rintros y ⟨x, xs, fxy ⟩,
  use [x, h xs, fxy],
end

-- 4ª demostración
-- ===============

example
  (h : s ⊆ t)
  : f '' s ⊆ f '' t :=
by finish [subset_def, mem_image_eq]

-- 5ª demostración
-- ===============

example
  (h : s ⊆ t)
  : f '' s ⊆ f '' t :=
image_subset f h
