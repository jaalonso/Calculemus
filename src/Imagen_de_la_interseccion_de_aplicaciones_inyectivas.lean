-- Imagen_de_la_interseccion_de_aplicaciones_inyectivas.lean
-- Imagen de la intersección de aplicaciones inyectivas
-- José A. Alonso Jiménez
-- Sevilla, 16 de junio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si f es inyectiva, entonces
--    f '' s ∩ f '' t ⊆ f '' (s ∩ t)
-- ----------------------------------------------------------------------

import data.set.basic

open set function

variables {α : Type*} {β : Type*}
variable  f : α → β
variables s t : set α

-- 1ª demostración
-- ===============

example
  (h : injective f)
  : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
begin
  intros y hy,
  cases hy  with hy1 hy2,
  cases hy1 with x1 hx1,
  cases hx1 with x1s fx1y,
  cases hy2 with x2 hx2,
  cases hx2 with x2t fx2y,
  use x1,
  split,
  { split,
    { exact x1s, },
    { convert x2t,
      apply h,
      rw ← fx2y at fx1y,
      exact fx1y, }},
  { exact fx1y, },
end

-- 2ª demostración
-- ===============

example
  (h : injective f)
  : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
begin
  rintros y ⟨⟨x1, x1s, fx1y⟩, ⟨x2, x2t, fx2y⟩⟩,
  use x1,
  split,
  { split,
    { exact x1s, },
    { convert x2t,
      apply h,
      rw ← fx2y at fx1y,
      exact fx1y, }},
  { exact fx1y, },
end

-- 3ª demostración
-- ===============

example
  (h : injective f)
  : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
begin
  rintros y ⟨⟨x1, x1s, fx1y⟩, ⟨x2, x2t, fx2y⟩⟩,
  unfold injective at h,
  finish,
end

-- 4ª demostración
-- ===============

example
  (h : injective f)
  : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
by intro ; unfold injective at *  ; finish
