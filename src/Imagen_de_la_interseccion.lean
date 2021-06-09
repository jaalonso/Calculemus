-- Imagen_de_la_interseccion.lean
-- Imagen de la intersección
-- José A. Alonso Jiménez
-- Sevilla, 15 de junio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    f '' (s ∩ t) ⊆ f '' s ∩ f '' t
-- ----------------------------------------------------------------------

import data.set.basic
import tactic

open set

variables {α : Type*} {β : Type*}
variable  f : α → β
variables s t : set α

-- 1ª demostración
-- ===============

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
begin
  intros y hy,
  cases hy with x hx,
  cases hx with xst fxy,
  split,
  { use x,
    split,
    { exact xst.1, },
    { exact fxy, }},
  { use x,
    split,
    { exact xst.2, },
    { exact fxy, }},
end

-- 2ª demostración
-- ===============

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
begin
  intros y hy,
  rcases hy with ⟨x, ⟨xs, xt⟩, fxy⟩,
  split,
  { use x,
    exact ⟨xs, fxy⟩, },
  { use x,
    exact ⟨xt, fxy⟩, },
end

-- 3ª demostración
-- ===============

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
begin
  rintros y ⟨x, ⟨xs, xt⟩, fxy⟩,
  split,
  { use [x, xs, fxy], },
  { use [x, xt, fxy], },
end

-- 4ª demostración
-- ===============

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
image_inter_subset f s t

-- 5ª demostración
-- ===============

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
by intro ; finish
