-- Imagen_inversa_de_la_interseccion.lean
-- Imagen inversa de la intersección
-- José A. Alonso Jiménez
-- Sevilla, 7 de junio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean, la imagen inversa de un conjunto s (de elementos de tipo β)
-- por la función f (de tipo α → β) es el conjunto `f ⁻¹' s` de
-- elementos x (de tipo α) tales que `f x ∈ s`.
--
-- Demostrar que
--    f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v
-- ----------------------------------------------------------------------

import data.set.basic

open set

variables {α : Type*} {β : Type*}
variable  f : α → β
variables u v : set β

-- 1ª demostración
-- ===============

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
begin
  ext x,
  split,
  { intro h,
    split,
    { apply mem_preimage.mpr,
      rw mem_preimage at h,
      exact mem_of_mem_inter_left h, },
    { apply mem_preimage.mpr,
      rw mem_preimage at h,
      exact mem_of_mem_inter_right h, }},
  { intro h,
    apply mem_preimage.mpr,
    split,
    { apply mem_preimage.mp,
      exact mem_of_mem_inter_left h,},
    { apply mem_preimage.mp,
      exact mem_of_mem_inter_right h, }},
end

-- 2ª demostración
-- ===============

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
begin
  ext x,
  exact ⟨λ h, ⟨mem_preimage.mpr (mem_of_mem_inter_left h),
               mem_preimage.mpr (mem_of_mem_inter_right h)⟩,
         λ h, ⟨mem_preimage.mp (mem_of_mem_inter_left h),
               mem_preimage.mp (mem_of_mem_inter_right h)⟩⟩,
end

-- 3ª demostración
-- ===============

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
begin
  ext,
  refl,
end

-- 4ª demostración
-- ===============

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
by {ext, refl}

-- 5ª demostración
-- ===============

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
rfl

-- 6ª demostración
-- ===============

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
preimage_inter
