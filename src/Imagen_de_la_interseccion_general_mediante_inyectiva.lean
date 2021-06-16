-- Imagen_de_la_interseccion_general_mediante_inyectiva.lean
-- Imagen de la interseccion general mediante inyectiva
-- José A. Alonso Jiménez
-- Sevilla, 25 de junio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si f es inyectiva, entonces
--    (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i)
-- ----------------------------------------------------------------------

import data.set.basic
import tactic

open set function

variables {α : Type*} {β : Type*} {I : Type*}
variable  f : α → β
variables A : I → set α

-- 1ª demostración
-- ===============

example
  (i : I)
  (injf : injective f)
  : (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i) :=
begin
  intros y hy,
  rw mem_Inter at hy,
  rcases hy i with ⟨x, xAi, fxy⟩,
  use x,
  split,
  { apply mem_Inter_of_mem,
    intro j,
    rcases hy j with ⟨z, zAj, fzy⟩,
    convert zAj,
    apply injf,
    rw fxy,
    rw ← fzy, },
  { exact fxy, },
end

-- 2ª demostración
-- ===============

example
  (i : I)
  (injf : injective f)
  : (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i) :=
begin
  intro y,
  simp,
  intro h,
  rcases h i with ⟨x, xAi, fxy⟩,
  use x,
  split,
  { intro j,
    rcases h j with ⟨z, zAi, fzy⟩,
    have : f x = f z, by rw [fxy, fzy],
    have : x = z, from injf this,
    rw this,
    exact zAi, },
  { exact fxy, },
end
