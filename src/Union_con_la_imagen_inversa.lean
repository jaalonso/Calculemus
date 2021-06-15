-- Union_con_la_imagen_inversa.lean
-- Unión con la imagen inversa
-- José A. Alonso Jiménez
-- Sevilla, 21 de junio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    s ∩ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∩ v)
-- ----------------------------------------------------------------------

import data.set.basic

open set

variables {α : Type*} {β : Type*}
variable  f : α → β
variable  s : set α
variable  v : set β

-- 1ª demostración
-- ===============

example : s ∩ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∩ v) :=
begin
  intros x hx,
  rw mem_preimage,
  split,
  { apply mem_image_of_mem,
    exact hx.1, },
  { rw ← mem_preimage,
    exact hx.2, },
end

-- 2ª demostración
-- ===============

example : s ∩ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∩ v) :=
begin
  rintros x ⟨xs, xv⟩,
  split,
  { exact mem_image_of_mem f xs, },
  { exact xv, },
end

-- 3ª demostración
-- ===============

example : s ∩ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∩ v) :=
begin
  rintros x ⟨xs, xv⟩,
  exact ⟨mem_image_of_mem f xs, xv⟩,
end

-- 4ª demostración
-- ===============

example : s ∩ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∩ v) :=
begin
  rintros x ⟨xs, xv⟩,
  show f x ∈ f '' s ∩ v,
  split,
  { use [x, xs, rfl] },
  { exact xv },
end

-- 5ª demostración
-- ===============

example : s ∩ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∩ v) :=
inter_preimage_subset s v f
