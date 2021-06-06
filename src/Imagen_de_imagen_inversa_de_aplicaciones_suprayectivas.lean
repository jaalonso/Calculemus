-- Imagen_de_imagen_inversa_de_aplicaciones_suprayectivas.lean
-- Imagen de imagen inversa de aplicaciones suprayectivas
-- José A. Alonso Jiménez
-- Sevilla, 11 de junio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si f es suprayectiva, entonces
--    u ⊆ f '' (f⁻¹' u)
-- ----------------------------------------------------------------------

import data.set.basic
open set function

variables {α : Type*} {β : Type*}
variable  f : α → β
variable  u : set β

-- 1ª demostración
-- ===============

example
  (h : surjective f)
  : u ⊆ f '' (f⁻¹' u) :=
begin
  intros y yu,
  cases h y with x fxy,
  use x,
  split,
  { apply mem_preimage.mpr,
    rw fxy,
    exact yu },
  { exact fxy },
end

-- 2ª demostración
-- ===============

example
  (h : surjective f)
  : u ⊆ f '' (f⁻¹' u) :=
begin
  intros y yu,
  cases h y with x fxy,
  use x,
  split,
  { show f x ∈ u,
    rw fxy,
    exact yu },
  { exact fxy },
end

-- 3ª demostración
-- ===============

example
  (h : surjective f)
  : u ⊆ f '' (f⁻¹' u) :=
begin
  intros y yu,
  cases h y with x fxy,
  by finish,
end
