-- Interseccion_con_su_union.lean
-- Intersección con su unión
-- José A. Alonso Jiménez
-- Sevilla, 25 de mayo de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    s ∩ (s ∪ t) = s
-- ----------------------------------------------------------------------

import data.set.basic
open set

variable {α : Type}
variables s t : set α

-- 1ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
begin
  ext x,
  split,
  { intros h,
    dsimp at h,
    exact h.1, },
  { intro xs,
    dsimp,
    split,
    { exact xs, },
    { left,
      exact xs, }},
end

-- 2ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
begin
  ext x,
  split,
  { intros h,
    exact h.1, },
  { intro xs,
    split,
    { exact xs, },
    { left,
      exact xs, }},
end

-- 3ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
begin
  ext x,
  split,
  { intros h,
    exact h.1, },
  { intro xs,
    split,
    { exact xs, },
    { exact (or.inl xs), }},
end

-- 4ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
begin
  ext,
  exact ⟨λ h, h.1,
         λ xs, ⟨xs, or.inl xs⟩⟩,
end

-- 5ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
begin
  ext,
  exact ⟨and.left,
         λ xs, ⟨xs, or.inl xs⟩⟩,
end

-- 6ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
begin
  ext x,
  split,
  { rintros ⟨xs, _⟩,
    exact xs },
  { intro xs,
    use xs,
    left,
    exact xs },
end

-- 7ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
inf_sup_self
