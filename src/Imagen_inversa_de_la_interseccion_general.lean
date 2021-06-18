-- Imagen_inversa_de_la_interseccion_general.lean
-- Imagen inversa de la intersección general
-- José A. Alonso Jiménez
-- Sevilla, 27 de junio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i)
-- ----------------------------------------------------------------------

import data.set.basic
import tactic

open set

variables {α : Type*} {β : Type*} {I : Type*}
variable  f : α → β
variables B : I → set β

-- 1ª demostración
-- ===============

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
begin
  ext x,
  split,
  { intro hx,
    apply mem_Inter_of_mem,
    intro i,
    rw mem_preimage,
    rw mem_preimage at hx,
    rw mem_Inter at hx,
    exact hx i, },
  { intro hx,
    rw mem_preimage,
    rw mem_Inter,
    intro i,
    rw ← mem_preimage,
    rw mem_Inter at hx,
    exact hx i, },
end

-- 2ª demostración
-- ===============

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
begin
  ext x,
  calc  (x ∈ f ⁻¹' ⋂ (i : I), B i)
      ↔ f x ∈ ⋂ (i : I), B i       : mem_preimage
  ... ↔ (∀ i : I, f x ∈ B i)       : mem_Inter
  ... ↔ (∀ i : I, x ∈ f ⁻¹' B i)   : iff_of_eq rfl
  ... ↔ x ∈ ⋂ (i : I), f ⁻¹' B i   : mem_Inter.symm,
end

-- 3ª demostración
-- ===============

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
begin
  ext x,
  simp,
end

-- 4ª demostración
-- ===============

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
by { ext, simp }
