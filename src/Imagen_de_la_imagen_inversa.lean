-- Imagen_de_la_imagen_inversa.lean
-- Imagen de la imagen inversa
-- José A. Alonso Jiménez
-- Sevilla, 10 de junio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    f '' (f⁻¹' u) ⊆ u
-- ----------------------------------------------------------------------

import data.set.basic
open set

variables {α : Type*} {β : Type*}
variable  f : α → β
variable  u : set β

-- 1ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
begin
  intros y h,
  cases h with x h2,
  cases h2 with hx fxy,
  rw ← fxy,
  exact hx,
end

-- 2ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
begin
  intros y h,
  rcases h with ⟨x, hx, fxy⟩,
  rw ← fxy,
  exact hx,
end

-- 3ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
begin
  rintros y ⟨x, hx, fxy⟩,
  rw ← fxy,
  exact hx,
end

-- 4ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
begin
  rintros y ⟨x, hx, rfl⟩,
  exact hx,
end

-- 5ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
image_preimage_subset f u

-- 6ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
by simp
