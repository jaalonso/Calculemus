-- Pruebas_de_take_n_xs_++_drop_n_xs_Ig_xs.lean
-- Pruebas de take n xs ++ drop n xs = xs
-- José A. Alonso Jiménez
-- Sevilla, 10 de septiembre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean están definidas las funciones
--    take : nat → list α → nat
--    drop : nat → list α → nat
--    (++) : list α → list α → list α
-- tales que
-- + (take n xs) es la lista formada por los n primeros elementos de
--   xs. Por ejemplo,
--      take 2 [3,5,1,9,7] = [3,5]
-- + (drop n xs) es la lista formada eliminando los n primeros elementos
--   de xs. Por ejemplo,
--      drop 2 [3,5,1,9,7] = [1,9,7]
-- + (xs ++ ys) es la lista obtenida concatenando xs e ys. Por ejemplo.
--      [3,5] ++ [1,9,7] = [3,5,1,9,7]
-- Dichas funciones están caracterizadas por los siguientes lemas:
--    take_zero   : take 0 xs = []
--    take_nil    : take n [] = []
--    take_cons   : take (succ n) (x :: xs) = x :: take n xs
--    drop_zero   : drop 0 xs = xs
--    drop_nil    : drop n [] = []
--    drop_cons   : drop (succ n) (x :: xs) = drop n xs := rfl
--    nil_append  : [] ++ ys = ys
--    cons_append : (x :: xs) ++ y = x :: (xs ++ ys)
--
-- Demostrar que
--    take n xs ++ drop n xs = xs
-- ---------------------------------------------------------------------

import data.list.basic
import tactic
open list
open nat

variable {α : Type}
variable (n : ℕ)
variable (x : α)
variable (xs : list α)

lemma drop_zero : drop 0 xs = xs := rfl
lemma drop_cons : drop (succ n) (x :: xs) = drop n xs := rfl

-- 1ª demostración
example :
  take n xs ++ drop n xs = xs :=
begin
  induction n with m HI1 generalizing xs,
  { rw take_zero,
    rw drop_zero,
    rw nil_append, },
  { induction xs with a as HI2,
    { rw take_nil,
      rw drop_nil,
      rw nil_append, },
    { rw take_cons,
      rw drop_cons,
      rw cons_append,
      rw (HI1 as), }, },
end

-- 2ª demostración
example :
  take n xs ++ drop n xs = xs :=
begin
  induction n with m HI1 generalizing xs,
  { calc take 0 xs ++ drop 0 xs
         = [] ++ drop 0 xs        : by rw take_zero
     ... = [] ++ xs               : by rw drop_zero
     ... = xs                     : by rw nil_append, },
  { induction xs with a as HI2,
    { calc take (succ m) [] ++ drop (succ m) []
           = ([] : list α) ++ drop (succ m) [] : by rw take_nil
       ... = [] ++ []                          : by rw drop_nil
       ... = []                                : by rw nil_append, },
    { calc take (succ m) (a :: as) ++ drop (succ m) (a :: as)
           = (a :: take m as) ++ drop (succ m) (a :: as) : by rw take_cons
       ... = (a :: take m as) ++ drop m as               : by rw drop_cons
       ... = a :: (take m as ++ drop m as)               : by rw cons_append
       ... = a :: as                                     : by rw (HI1 as), }, },
end

-- 3ª demostración
example :
  take n xs ++ drop n xs = xs :=
begin
  induction n with m HI1 generalizing xs,
  { simp, },
  { induction xs with a as HI2,
    { simp, },
    { simp [HI1 as], }, },
end

-- 4ª demostración
lemma conc_take_drop_1 :
  ∀ (n : ℕ) (xs : list α), take n xs ++ drop n xs = xs
| 0 xs := by calc
    take 0 xs ++ drop 0 xs
        = [] ++ drop 0 xs   : by rw take_zero
    ... = [] ++ xs          : by rw drop_zero
    ... = xs                : by rw nil_append
| (succ m) [] := by calc
    take (succ m) [] ++ drop (succ m) []
        = ([] : list α) ++ drop (succ m) [] : by rw take_nil
    ... = [] ++ []                          : by rw drop_nil
    ... = []                                : by rw nil_append
| (succ m) (a :: as) := by calc
    take (succ m) (a :: as) ++ drop (succ m) (a :: as)
        = (a :: take m as) ++ drop (succ m) (a :: as)    : by rw take_cons
    ... = (a :: take m as) ++ drop m as                  : by rw drop_cons
    ... = a :: (take m as ++ drop m as)                  : by rw cons_append
    ... = a :: as                                        : by rw conc_take_drop_1

-- 5ª demostración
lemma conc_take_drop_2 :
  ∀ (n : ℕ) (xs : list α), take n xs ++ drop n xs = xs
| 0        xs        := by simp
| (succ m) []        := by simp
| (succ m) (a :: as) := by simp [conc_take_drop_2]

-- 6ª demostración
lemma conc_take_drop_3 :
  ∀ (n : ℕ) (xs : list α), take n xs ++ drop n xs = xs
| 0        xs        := rfl
| (succ m) []        := rfl
| (succ m) (a :: as) := congr_arg (cons a) (conc_take_drop_3 m as)

-- 7ª demostración
example : take n xs ++ drop n xs = xs :=
-- by library_search
take_append_drop n xs

-- 8ª demostración
example : take n xs ++ drop n xs = xs :=
by simp
