-- Union_con_la_imagen_inversa.lean
-- Unión con la imagen inversa
-- José A. Alonso Jiménez
-- Sevilla, 22 de junio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v)
-- ----------------------------------------------------------------------

import data.set.basic

open set

variables {α : Type*} {β : Type*}
variable  f : α → β
variable  s : set α
variable  v : set β

-- 1ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
begin
  intros x hx,
  rw mem_preimage,
  cases hx with xs xv,
  { apply mem_union_left,
    apply mem_image_of_mem,
    exact xs, },
  { apply mem_union_right,
    rw ← mem_preimage,
    exact xv, },
end

-- 2ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
begin
  intros x hx,
  cases hx with xs xv,
  { apply mem_union_left,
    apply mem_image_of_mem,
    exact xs, },
  { apply mem_union_right,
    exact xv, },
end

-- 3ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
begin
  rintros x (xs | xv),
  { left,
    exact mem_image_of_mem f xs, },
  { right,
    exact xv, },
end

-- 4ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
begin
  rintros x (xs | xv),
  { exact or.inl (mem_image_of_mem f xs), },
  { exact or.inr xv, },
end

-- 5ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
begin
  intros x h,
  exact or.elim h (λ xs, or.inl (mem_image_of_mem f xs)) or.inr,
end

-- 6ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
λ x h, or.elim h (λ xs, or.inl (mem_image_of_mem f xs)) or.inr

-- 7ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
begin
  rintros x (xs | xv),
  { show f x ∈ f '' s ∪ v,
    use [x, xs, rfl] },
  { show f x ∈ f '' s ∪ v,
    right,
    apply xv },
end

-- 8ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
union_preimage_subset s v f
