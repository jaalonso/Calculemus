-- Teorema_de_Cantor.lean
-- Teorema de Cantor
-- José A. Alonso Jiménez
-- Sevilla, 28 de junio de 2021
-- ---------------------------------------------------------------------


-- ---------------------------------------------------------------------
-- Demostrar el teorema de Cantor:
--    ∀ f : α → set α, ¬ surjective f
-- ----------------------------------------------------------------------

import data.set.basic
open function

variables {α : Type}

-- 1ª demostración
-- ===============

example : ∀ f : α → set α, ¬ surjective f :=
begin
  intros f surjf,
  let S := {i | i ∉ f i},
  unfold surjective at surjf,
  cases surjf S with j fjS,
  by_cases j ∈ S,
  { apply absurd _ h,
    rw fjS,
    exact h, },
  { apply h,
    rw ← fjS at h,
    exact h, },
end

-- 2ª demostración
-- ===============

example : ∀ f : α → set α, ¬ surjective f :=
begin
  intros f surjf,
  let S := {i | i ∉ f i},
  cases surjf S with j fjS,
  by_cases j ∈ S,
  { apply absurd _ h,
    rwa fjS, },
  { apply h,
    rwa ← fjS at h, },
end

-- 3ª demostración
-- ===============

example : ∀ f : α → set α, ¬ surjective f :=
begin
  intros f surjf,
  let S := {i | i ∉ f i},
  cases surjf S with j fjS,
  have h : (j ∈ S) = (j ∉ S), from
    calc  (j ∈ S)
        = (j ∉ f j) : set.mem_set_of_eq
    ... = (j ∉ S)   : congr_arg not (congr_arg (has_mem.mem j) fjS),
  exact false_of_a_eq_not_a h,
end

-- 4ª demostración
-- ===============

example : ∀ f : α → set α, ¬ surjective f :=
cantor_surjective
