-- Pruebas_de_length(xs_++_ys)_Ig_length_xs+length_ys.lean
-- Pruebas de length(xs ++ ys) = length(xs) + length(ys)
-- José A. Alonso Jiménez
-- Sevilla, 9 de septiembre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean están definidas las funciones
--    length : list α → nat
--    (++)   : list α → list α → list α
-- tales que
-- + (length xs) es la longitud de xs. Por ejemplo,
--      length [2,3,5,3] = 4
-- + (xs ++ ys) es la lista obtenida concatenando xs e ys. Por ejemplo.
--      [1,2] ++ [2,3,5,3] = [1,2,2,3,5,3]
-- Dichas funciones están caracterizadas por los siguientes lemas:
--    length_nil  : length [] = 0
--    length_cons : length (x :: xs) = length xs + 1
--    nil_append  : [] ++ ys = ys
--    cons_append : (x :: xs) ++ y = x :: (xs ++ ys)
--
-- Demostrar que
--    length (xs ++ ys) = length xs + length ys
-- ---------------------------------------------------------------------

import tactic
open list

variable  {α : Type}
variable  (x : α)
variables (xs ys zs : list α)

lemma length_nil  : length ([] : list α) = 0 := rfl

-- 1ª demostración
example :
  length (xs ++ ys) = length xs + length ys :=
begin
  induction xs with a as HI,
  { rw nil_append,
    rw length_nil,
    rw zero_add, },
  { rw cons_append,
    rw length_cons,
    rw HI,
    rw length_cons,
    rw add_assoc,
    rw add_comm (length ys),
    rw add_assoc, },
end

-- 2ª demostración
example :
  length (xs ++ ys) = length xs + length ys :=
begin
  induction xs with a as HI,
  { rw nil_append,
    rw length_nil,
    rw zero_add, },
  { rw cons_append,
    rw length_cons,
    rw HI,
    rw length_cons,
    -- library_search,
    exact add_right_comm (length as) (length ys) 1 },
end

-- 3ª demostración
example :
  length (xs ++ ys) = length xs + length ys :=
begin
  induction xs with a as HI,
  { rw nil_append,
    rw length_nil,
    rw zero_add, },
  { rw cons_append,
    rw length_cons,
    rw HI,
    rw length_cons,
    -- by hint,
    linarith, },
end

-- 4ª demostración
example :
  length (xs ++ ys) = length xs + length ys :=
begin
  induction xs with a as HI,
  { simp, },
  { simp [HI],
    linarith, },
end

-- 5ª demostración
example :
  length (xs ++ ys) = length xs + length ys :=
begin
  induction xs with a as HI,
  { simp, },
  { finish [HI],},
end

-- 6ª demostración
example :
  length (xs ++ ys) = length xs + length ys :=
by induction xs ; finish [*]

-- 7ª demostración
example :
  length (xs ++ ys) = length xs + length ys :=
begin
  induction xs with a as HI,
  { calc length ([] ++ ys)
         = length ys                    : congr_arg length (nil_append ys)
     ... = 0 + length ys                : (zero_add (length ys)).symm
     ... = length [] + length ys        : congr_arg2 (+) length_nil.symm rfl, },
  { calc length ((a :: as) ++ ys)
         = length (a :: (as ++ ys))     : congr_arg length (cons_append a as ys)
     ... = length (as ++ ys) + 1        : length_cons a (as ++ ys)
     ... = (length as + length ys) + 1  : congr_arg2 (+) HI rfl
     ... = (length as + 1) + length ys  : add_right_comm (length as) (length ys) 1
     ... = length (a :: as) + length ys : congr_arg2 (+) (length_cons a as).symm rfl, },
end

-- 8ª demostración
example :
  length (xs ++ ys) = length xs + length ys :=
begin
  induction xs with a as HI,
  { calc length ([] ++ ys)
         = length ys                    : by rw nil_append
     ... = 0 + length ys                : (zero_add (length ys)).symm
     ... = length [] + length ys        : by rw length_nil },
  { calc length ((a :: as) ++ ys)
         = length (a :: (as ++ ys))     : by rw cons_append
     ... = length (as ++ ys) + 1        : by rw length_cons
     ... = (length as + length ys) + 1  : by rw HI
     ... = (length as + 1) + length ys  : add_right_comm (length as) (length ys) 1
     ... = length (a :: as) + length ys : by rw length_cons, },
end

-- 9ª demostración
example :
  length (xs ++ ys) = length xs + length ys :=
list.rec_on xs
  ( show length ([] ++ ys) = length [] + length ys, from
      calc length ([] ++ ys)
           = length ys                    : by rw nil_append
       ... = 0 + length ys                : (zero_add (length ys)).symm
       ... = length [] + length ys        : by rw length_nil )
  ( assume a as,
    assume HI : length (as ++ ys) = length as + length ys,
    show length ((a :: as) ++ ys) = length (a :: as) + length ys, from
      calc length ((a :: as) ++ ys)
           = length (a :: (as ++ ys))     : by rw cons_append
       ... = length (as ++ ys) + 1        : by rw length_cons
       ... = (length as + length ys) + 1  : by rw HI
       ... = (length as + 1) + length ys  : add_right_comm (length as) (length ys) 1
       ... = length (a :: as) + length ys : by rw length_cons)

-- 10ª demostración
example :
  length (xs ++ ys) = length xs + length ys :=
list.rec_on xs
  ( by simp)
  ( λ a as HI, by simp [HI, add_right_comm])

-- 11ª demostración
lemma longitud_conc_1 :
  ∀ xs, length (xs ++ ys) = length xs + length ys
| [] := by calc
    length ([] ++ ys)
        = length ys                    : by rw nil_append
    ... = 0 + length ys                : by rw zero_add
    ... = length [] + length ys        : by rw length_nil
| (a :: as) := by calc
    length ((a :: as) ++ ys)
        = length (a :: (as ++ ys))     : by rw cons_append
    ... = length (as ++ ys) + 1        : by rw length_cons
    ... = (length as + length ys) + 1  : by rw longitud_conc_1
    ... = (length as + 1) + length ys  : add_right_comm (length as) (length ys) 1
    ... = length (a :: as) + length ys : by rw length_cons

-- 12ª demostración
lemma longitud_conc_2 :
  ∀ xs, length (xs ++ ys) = length xs + length ys
| []        := by simp
| (a :: as) := by simp [longitud_conc_2 as, add_right_comm]

-- 13ª demostración
example :
  length (xs ++ ys) = length xs + length ys :=
-- by library_search
length_append xs ys

-- 14ª demostración
example :
  length (xs ++ ys) = length xs + length ys :=
by simp
