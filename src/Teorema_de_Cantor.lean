-- Teorema_de_Cantor.lean
-- Teorema de Cantor.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 6-mayo-2022
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
  intros f hf,
  let S := {i | i ∉ f i},
  unfold surjective at hf,
  cases hf S with j hj,
  by_cases j ∈ S,
  { dsimp at h,
    apply h,
    rw hj,
    exact h, },
  { apply h,
    rw ← hj at h,
    exact h, },
end

-- 2ª demostración
-- ===============

example : ∀ f : α → set α, ¬ surjective f :=
begin
  intros f hf,
  let S := {i | i ∉ f i},
  cases hf S with j hj,
  by_cases j ∈ S,
  { apply  h,
    rwa hj, },
  { apply h,
    rwa ← hj at h, },
end

-- 3ª demostración
-- ===============

example : ∀ f : α → set α, ¬ surjective f :=
begin
  intros f hf,
  let S := {i | i ∉ f i},
  cases hf S with j hj,
  have h : (j ∈ S) = (j ∉ S), from
    calc  (j ∈ S)
        = (j ∉ f j) : set.mem_set_of_eq
    ... = (j ∉ S)   : congr_arg not (congr_arg (has_mem.mem j) hj),
  exact false_of_a_eq_not_a h,
end

-- 4ª demostración
-- ===============

example : ∀ f : α → set α, ¬ surjective f :=
begin
  intros f hf,
  let S := {i | i ∉ f i},
  cases hf S with j hj,
  have h : (j ∈ S) = (j ∉ S),
  { dsimp,
    exact congr_arg not (congr_arg (has_mem.mem j) hj), },
  { exact false_of_a_eq_not_a (congr_arg not (congr_arg not h)), },
end

-- 5ª demostración
-- ===============

example : ∀ f : α → set α, ¬ surjective f :=
cantor_surjective
