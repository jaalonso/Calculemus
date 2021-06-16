-- Imagen_inversa_de_la_union_general.lean
-- Imagen inversa de la unión general
-- José A. Alonso Jiménez
-- Sevilla, 26 de junio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i)
-- ----------------------------------------------------------------------

import data.set.basic
import tactic

open set

variables {α : Type*} {β : Type*} {I : Type*}
variable  f : α → β
variables B : I → set β

-- 1ª demostración
-- ===============

example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
begin
  ext x,
  split,
  { intro hx,
    rw mem_preimage at hx,
    rw mem_Union at hx,
    cases hx with i fxBi,
    rw mem_Union,
    use i,
    apply mem_preimage.mpr,
    exact fxBi, },
  { intro hx,
    rw mem_preimage,
    rw mem_Union,
    rw mem_Union at hx,
    cases hx with i xBi,
    use i,
    rw mem_preimage at xBi,
    exact xBi, },
end

-- 2ª demostración
-- ===============

example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
preimage_Union

-- 3ª demostración
-- ===============

example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
by  simp
