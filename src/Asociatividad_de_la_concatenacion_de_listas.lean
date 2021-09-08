-- Asociatividad_de_la_concatenacion_de_listas.lean
-- Asociatividad de la concatenación de listas
-- José A. Alonso Jiménez
-- Sevilla, 8 de septiembre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean la operación de concatenación de listas se representa por
-- (++) y está caracterizada por los siguientes lemas
--    nil_append  : [] ++ ys = ys
--    cons_append : (x :: xs) ++ y = x :: (xs ++ ys)
--
-- Demostrar que la concatenación es asociativa; es decir,
--    xs ++ (ys ++ zs) = (xs ++ ys) ++ zs
-- ---------------------------------------------------------------------

import data.list.basic
import tactic
open list

variable  {α : Type}
variable  (x : α)
variables (xs ys zs : list α)

-- 1ª demostración
example :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
begin
  induction xs with a as HI,
  { calc [] ++ (ys ++ zs)
         = ys ++ zs                : append.equations._eqn_1 (ys ++ zs)
     ... = ([] ++ ys) ++ zs        : congr_arg2 (++) (append.equations._eqn_1 ys) rfl, },
  { calc (a :: as) ++ (ys ++ zs)
         = a :: (as ++ (ys ++ zs)) : append.equations._eqn_2 a as (ys ++ zs)
     ... = a :: ((as ++ ys) ++ zs) : congr_arg2 (::) rfl HI
     ... = (a :: (as ++ ys)) ++ zs : (append.equations._eqn_2 a (as ++ ys) zs).symm
     ... = ((a :: as) ++ ys) ++ zs : congr_arg2 (++) (append.equations._eqn_2 a as ys).symm rfl, },
end

-- 2ª demostración
example :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
begin
  induction xs with a as HI,
  { calc [] ++ (ys ++ zs)
         = ys ++ zs                : nil_append (ys ++ zs)
     ... = ([] ++ ys) ++ zs        : congr_arg2 (++) (nil_append ys) rfl, },
  { calc (a :: as) ++ (ys ++ zs)
         = a :: (as ++ (ys ++ zs)) : cons_append a as (ys ++ zs)
     ... = a :: ((as ++ ys) ++ zs) : congr_arg2 (::) rfl HI
     ... = (a :: (as ++ ys)) ++ zs : (cons_append a (as ++ ys) zs).symm
     ... = ((a :: as) ++ ys) ++ zs : congr_arg2 (++) (cons_append a as ys).symm rfl, },
end

-- 3ª demostración
example :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
begin
  induction xs with a as HI,
  { calc [] ++ (ys ++ zs)
         = ys ++ zs                : by rw nil_append
     ... = ([] ++ ys) ++ zs        : by rw nil_append, },
  { calc (a :: as) ++ (ys ++ zs)
         = a :: (as ++ (ys ++ zs)) : by rw cons_append
     ... = a :: ((as ++ ys) ++ zs) : by rw HI
     ... = (a :: (as ++ ys)) ++ zs : by rw cons_append
     ... = ((a :: as) ++ ys) ++ zs : by rw ← cons_append, },
end

-- 4ª demostración
example :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
begin
  induction xs with a as HI,
  { calc [] ++ (ys ++ zs)
         = ys ++ zs                : rfl
     ... = ([] ++ ys) ++ zs        : rfl, },
  { calc (a :: as) ++ (ys ++ zs)
         = a :: (as ++ (ys ++ zs)) : rfl
     ... = a :: ((as ++ ys) ++ zs) : by rw HI
     ... = (a :: (as ++ ys)) ++ zs : rfl
     ... = ((a :: as) ++ ys) ++ zs : rfl, },
end

-- 5ª demostración
example :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
begin
  induction xs with a as HI,
  { calc [] ++ (ys ++ zs)
         = ys ++ zs                : by simp
     ... = ([] ++ ys) ++ zs        : by simp, },
  { calc (a :: as) ++ (ys ++ zs)
         = a :: (as ++ (ys ++ zs)) : by simp
     ... = a :: ((as ++ ys) ++ zs) : congr_arg (cons a) HI
     ... = (a :: (as ++ ys)) ++ zs : by simp
     ... = ((a :: as) ++ ys) ++ zs : by simp, },
end

-- 6ª demostración
example :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
begin
  induction xs with a as HI,
  { by simp, },
  { by exact (cons_inj a).mpr HI, },
end

-- 7ª demostración
example :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
begin
  induction xs with a as HI,
  { rw nil_append,
    rw nil_append, },
  { rw cons_append,
    rw HI,
    rw cons_append,
    rw cons_append, },
end

-- 8ª demostración
example :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
list.rec_on xs
  ( show [] ++ (ys ++ zs) = ([] ++ ys) ++ zs,
      from calc
        [] ++ (ys ++ zs)
            = ys ++ zs         : by rw nil_append
        ... = ([] ++ ys) ++ zs : by rw nil_append )
  ( assume a as,
    assume HI : as ++ (ys ++ zs) = (as ++ ys) ++ zs,
    show (a :: as) ++ (ys  ++ zs) = ((a :: as) ++ ys) ++ zs,
      from calc
        (a :: as) ++ (ys ++ zs)
            = a :: (as ++ (ys ++ zs)) : by rw cons_append
        ... = a :: ((as ++ ys) ++ zs) : by rw HI
        ... = (a :: (as ++ ys)) ++ zs : by rw cons_append
        ... = ((a :: as) ++ ys) ++ zs : by rw ← cons_append)

-- 9ª demostración
example :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
list.rec_on xs
  (by simp)
  (by simp [*])

-- 10ª demostración
lemma conc_asoc_1 :
  ∀ xs, xs ++ (ys ++ zs) = (xs ++ ys) ++ zs
| [] := by calc
    [] ++ (ys ++ zs)
        = ys ++ zs         : by rw nil_append
    ... = ([] ++ ys) ++ zs : by rw nil_append
| (a :: as) := by calc
    (a :: as) ++ (ys ++ zs)
        = a :: (as ++ (ys ++ zs)) : by rw cons_append
    ... = a :: ((as ++ ys) ++ zs) : by rw conc_asoc_1
    ... = (a :: (as ++ ys)) ++ zs : by rw cons_append
    ... = ((a :: as) ++ ys) ++ zs : by rw ← cons_append

-- 11ª demostración
example :
  (xs ++ ys) ++ zs = xs ++ (ys ++ zs) :=
-- by library_search
append_assoc xs ys zs

-- 12ª demostración
example :
  (xs ++ ys) ++ zs = xs ++ (ys ++ zs) :=
by induction xs ; simp [*]

-- 13ª demostración
example :
  (xs ++ ys) ++ zs = xs ++ (ys ++ zs) :=
by simp
