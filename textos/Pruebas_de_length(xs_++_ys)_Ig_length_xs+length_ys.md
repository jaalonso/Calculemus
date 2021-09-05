---
Título: Pruebas de length (xs ++ ys) = length xs + length ys
Autor:  José A. Alonso
---

En Lean están definidas las funciones
<pre lang="text">
   length : list α → nat
   (++)   : list α → list α → list α
</pre>
tales que

+ (length xs) es la longitud de xs. Por ejemplo,
<pre lang="text">
     length [2,3,5,3] = 4
</pre>
+ (xs ++ ys) es la lista obtenida concatenando xs e ys. Por ejemplo.
<pre lang="text">
     [1,2] ++ [2,3,5,3] = [1,2,2,3,5,3]
</pre>
Dichas funciones están caracterizadas por los siguientes lemas:
<pre lang="text">
   length_nil  : length [] = 0
   length_cons : length (x :: xs) = length xs + 1
   nil_append  : [] ++ ys = ys
   cons_append : (x :: xs) ++ y = x :: (xs ++ ys)
</pre>

Demostrar que
<pre lang="text">
   length (xs ++ ys) = length xs + length ys
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic
open list

variable  {α : Type}
variable  (x : α)
variables (xs ys zs : list α)

lemma length_nil  : length ([] : list α) = 0 := rfl

example :
  length (xs ++ ys) = length xs + length ys :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
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
       ... = 0 + length ys                : by exact (zero_add (length ys)).symm
       ... = length [] + length ys        : by rw length_nil )
  ( assume a as,
    assume HI : length (as ++ ys) = length as + length ys,
    show length ((a :: as) ++ ys) = length (a :: as) + length ys, from
      calc length ((a :: as) ++ ys)
           = length (a :: (as ++ ys))     : by rw cons_append
       ... = length (as ++ ys) + 1        : by rw length_cons
       ... = (length as + length ys) + 1  : by rw HI
       ... = (length as + 1) + length ys  : by exact add_right_comm (length as) (length ys) 1
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
    ... = (length as + 1) + length ys  : by exact add_right_comm (length as) (length ys) 1
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
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Pruebas_de_length(xs_++_ys)_Ig_length_xs+length_ys.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory "Pruebas_de_length(xs_++_ys)_Ig_length_xs+length_ys"
imports Main
begin

(* 1ª demostración *)
lemma "length (xs @ ys) = length xs + length ys"
proof (induct xs)
  have "length ([] @ ys) = length ys"
    by (simp only: append_Nil)
  also have "… = 0 + length ys"
    by (rule add_0 [symmetric])
  also have "… = length [] + length ys"
    by (simp only: list.size(3))
  finally show "length ([] @ ys) = length [] + length ys"
    by this
next
  fix x xs
  assume HI : "length (xs @ ys) = length xs + length ys"
  have "length ((x # xs) @ ys) =
        length (x # (xs @ ys))"
    by (simp only: append_Cons)
  also have "… = length (xs @ ys) + 1"
    by (simp only: list.size(4))
  also have "… = (length xs + length ys) + 1"
    by (simp only: HI)
  also have "… = (length xs + 1) + length ys"
    by (simp only: add.assoc add.commute)
  also have "… = length (x # xs) + length ys"
    by (simp only: list.size(4))
  then show "length ((x # xs) @ ys) = length (x # xs) + length ys"
    by simp
qed

(* 2ª demostración *)
lemma "length (xs @ ys) = length xs + length ys"
proof (induct xs)
  show "length ([] @ ys) = length [] + length ys"
    by simp
next
  fix x xs
  assume "length (xs @ ys) = length xs + length ys"
  then show "length ((x # xs) @ ys) = length (x # xs) + length ys"
    by simp
qed

(* 3ª demostración *)
lemma "length (xs @ ys) = length xs + length ys"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by simp
qed

(* 4ª demostración *)
lemma "length (xs @ ys) = length xs + length ys"
by (induct xs) simp_all

(* 5ª demostración *)
lemma "length (xs @ ys) = length xs + length ys"
by (fact length_append)

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
