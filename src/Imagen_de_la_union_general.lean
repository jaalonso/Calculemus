-- Imagen_de_la_union_general.lean
-- Imagen de la unión general
-- José A. Alonso Jiménez
-- Sevilla, 23 de junio de 2021
-- ---------------------------------------------------------------------

-- ----------------------------------------------------------------------
-- Demostrar que
--    f '' (⋃ i, A i) = ⋃ i, f '' A i
-- ----------------------------------------------------------------------

import data.set.basic
import tactic

open set

variables {α : Type*} {β : Type*} {I : Type*}
variable  f : α → β
variables A : ℕ → set α

-- 1ª demostración
-- ===============

example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
begin
  ext y,
  split,
  { intro hy,
    rw mem_image at hy,
    cases hy with x hx,
    cases hx with xUA fxy,
    rw mem_Union at xUA,
    cases xUA with i xAi,
    rw mem_Union,
    use i,
    rw ← fxy,
    apply mem_image_of_mem,
    exact xAi, },
  { intro hy,
    rw mem_Union at hy,
    cases hy with i yAi,
    cases yAi with x hx,
    cases hx with xAi fxy,
    rw ← fxy,
    apply mem_image_of_mem,
    rw mem_Union,
    use i,
    exact xAi, },
end

-- 2ª demostración
-- ===============

example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
begin
  ext y,
  simp,
  split,
  { rintros ⟨x, ⟨i, xAi⟩, fxy⟩,
    use [i, x, xAi, fxy] },
  { rintros ⟨i, x, xAi, fxy⟩,
    exact ⟨x, ⟨i, xAi⟩, fxy⟩ },
end

-- 3ª demostración
-- ===============

example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
by tidy

-- 4ª demostración
-- ===============

example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
image_Union
