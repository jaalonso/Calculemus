-- Imagen_inversa_de_la_imagen_de_aplicaciones_inyectivas.lean
-- Imagen inversa de la imagen de aplicaciones inyectivas
-- José A. Alonso Jiménez
-- Sevilla, 9 de junio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si f es inyectiva, entonces
--    f⁻¹[f[s]] ⊆ s
-- ----------------------------------------------------------------------

import data.set.basic

open set function

variables {α : Type*} {β : Type*}
variable  f : α → β
variable  s : set α

-- 1ª demostración
-- ===============

example
  (h : injective f)
  : f ⁻¹' (f '' s) ⊆ s :=
begin
  intros x hx,
  rw mem_preimage at hx,
  rw mem_image_eq at hx,
  cases hx with y hy,
  cases hy with ys fyx,
  unfold injective at h,
  have h1 : y = x := h fyx,
  rw ← h1,
  exact ys,
end

-- 2ª demostración
-- ===============

example
  (h : injective f)
  : f ⁻¹' (f '' s) ⊆ s :=
begin
  intros x hx,
  rw mem_preimage at hx,
  rcases hx with ⟨y, ys, fyx⟩,
  rw ← h fyx,
  exact ys,
end

-- 3ª demostración
-- ===============

example
  (h : injective f)
  : f ⁻¹' (f '' s) ⊆ s :=
begin
  rintros x ⟨y, ys, hy⟩,
  rw ← h hy,
  exact ys,
end
