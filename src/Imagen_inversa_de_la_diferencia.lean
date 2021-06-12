-- Imagen_inversa_de_la_diferencia.lean
-- Imagen inversa de la diferencia
-- José A. Alonso Jiménez
-- Sevilla, 18 de junio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v)
-- ----------------------------------------------------------------------

import data.set.basic

open set

variables {α : Type*} {β : Type*}
variable  f : α → β
variables u v : set β

-- 1ª demostración
-- ===============

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
begin
  intros x hx,
  rw mem_preimage,
  split,
  { rw ← mem_preimage,
    exact hx.1, },
  { dsimp,
    rw ← mem_preimage,
    exact hx.2, },
end

-- 2ª demostración
-- ===============

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
begin
  intros x hx,
  split,
  { exact hx.1, },
  { exact hx.2, },
end

-- 3ª demostración
-- ===============

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
begin
  intros x hx,
  exact ⟨hx.1, hx.2⟩,
end

-- 4ª demostración
-- ===============

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
begin
  rintros x ⟨h1, h2⟩,
  exact ⟨h1, h2⟩,
end

-- 5ª demostración
-- ===============

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
subset.rfl

-- 6ª demostración
-- ===============

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
by finish
