-- Imagen_de_la_diferencia_de_conjuntos.lean
-- Imagen de la diferencia de conjuntos
-- José A. Alonso Jiménez
-- Sevilla, 17 de junio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    f '' s \ f '' t ⊆ f '' (s \ t)
-- ----------------------------------------------------------------------

import data.set.basic
import tactic

open set

variables {α : Type*} {β : Type*}
variable  f : α → β
variables s t : set α

-- 1ª demostración
-- ===============

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
begin
  intros y hy,
  cases hy with yfs ynft,
  cases yfs with x hx,
  cases hx with xs fxy,
  use x,
  split,
  { split,
    { exact xs, },
    { dsimp,
      intro xt,
      apply ynft,
      rw ← fxy,
      apply mem_image_of_mem,
      exact xt, }},
  { exact fxy, },
end

-- 2ª demostración
-- ===============

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
begin
  rintros y ⟨⟨x, xs, fxy⟩, ynft⟩,
  use x,
  split,
  { split,
    { exact xs, },
    { intro xt,
      apply ynft,
      use [x, xt, fxy], }},
  { exact fxy, },
end

-- 3ª demostración
-- ===============

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
begin
  rintros y ⟨⟨x, xs, fxy⟩, ynft⟩,
  use x,
  finish,
end

-- 4ª demostración
-- ===============

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
subset_image_diff f s t
