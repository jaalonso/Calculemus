-- Imagen_de_la_union.lean
-- Imagen de la unión.
-- José A. Alonso Jiménez
-- Sevilla, 4 de mayo de 2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean, la imagen de un conjunto s por una función f se representa
-- por `f '' s`; es decir,
--    f '' s = {y | ∃ x, x ∈ s ∧ f x = y}
--
-- Demostrar que
--    f '' (s ∪ t) = f '' s ∪ f '' t
-- ----------------------------------------------------------------------

import data.set.basic
import tactic

open set

variables {α : Type*} {β : Type*}
variable  f : α → β
variables s t : set α

-- 1ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
begin
  ext y,
  split,
  { intro h,
    rw mem_image at h,
    cases h with x hx,
    cases hx with xst fxy,
    rw ← fxy, 
    rw mem_union at xst,
    cases xst with xs xt, 
    { apply mem_union_left,
      apply mem_image_of_mem,
      exact xs, },
    { apply mem_union_right,
      apply mem_image_of_mem,
      exact xt, }},
  { intro h,
    rw mem_union at h,
    cases h with yfs yft,
    { rw mem_image,
      rw mem_image at yfs,
      cases yfs with x hx,
      cases hx with xs fxy,
      use x,
      split,
      { apply mem_union_left,
        exact xs, },
      { exact fxy, }},
    { rw mem_image,
      rw mem_image at yft,
      cases yft with x hx,
      cases hx with xt fxy,
      use x,
      split,
      { apply mem_union_right,
        exact xt, },
      { exact fxy, }}},
end

-- 2ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
begin
  ext y,
  split,
  { rintro ⟨x, xst, rfl⟩,
    cases xst with xs xt, 
    { left,
      exact mem_image_of_mem f xs, },
    { right,
      exact mem_image_of_mem f xt, }},
  { rintro (yfs | yft),
    { rcases yfs with ⟨x, xs, rfl⟩,
      apply mem_image_of_mem,
      left,
      exact xs, },
    { rcases yft with ⟨x, xt, rfl⟩,
      apply mem_image_of_mem,
      right,
      exact xt, }},
end

-- 3ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
begin
  ext y,
  split,
  { rintro ⟨x, xst, rfl⟩,
    cases xst with xs xt, 
    { left,
      use [x, xs], },
    { right,
      use [x, xt], }},
  { rintro (yfs | yft),
    { rcases yfs with ⟨x, xs, rfl⟩,
      use [x, or.inl xs], },
    { rcases yft with ⟨x, xt, rfl⟩,
      use [x, or.inr xt], }},
end

-- 4ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
begin
  ext y,
  split,
  { rintro ⟨x, xs | xt, rfl⟩,
    { left,
      use [x, xs], },
    { right,
      use [x, xt], }},
  { rintros (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩),
    { use [x, or.inl xs], },
    { use [x, or.inr xt], }},
end

-- 5ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
begin
  ext y,
  split,
  { rintros ⟨x, xs | xt, rfl⟩ ; finish, },
  { rintros (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩) ; finish, },
end

-- 6ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
begin
  ext y,
  split,
  { finish, },
  { finish, },
end

-- 7ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
begin
  ext y,
  rw iff_def,
  finish, 
end

-- 8ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
by finish [ext_iff, iff_def]

-- 9ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
image_union f s t