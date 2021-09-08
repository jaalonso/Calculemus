---
Título: Asociatividad de la concatenación de listas
Autor:  José A. Alonso
---

En Lean la operación de concatenación de listas se representa por (++) y está caracterizada por los siguientes lemas
<pre lang="text">
   nil_append  : [] ++ ys = ys
   cons_append : (x :: xs) ++ y = x :: (xs ++ ys)
</pre>

Demostrar que la concatenación es asociativa; es decir,
<pre lang="text">
   xs ++ (ys ++ zs) = (xs ++ ys) ++ zs
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.list.basic
import tactic
open list

variable  {α : Type}
variable  (x : α)
variables (xs ys zs : list α)

example :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
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
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Asociatividad_de_la_concatenacion_de_listas.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Asociatividad_de_la_concatenacion_de_listas
imports Main
begin

(* 1ª demostración *)
lemma "xs @ (ys @ zs) = (xs @ ys) @ zs"
proof (induct xs)
  have "[] @ (ys @ zs) = ys @ zs"
    by (simp only: append_Nil)
  also have "… = ([] @ ys) @ zs"
    by (simp only: append_Nil)
  finally show "[] @ (ys @ zs) = ([] @ ys) @ zs"
    by this
next
  fix x xs
  assume HI : "xs @ (ys @ zs) = (xs @ ys) @ zs"
  have "(x # xs) @ (ys @ zs) = x # (xs @ (ys @ zs))"
    by (simp only: append_Cons)
  also have "… = x # ((xs @ ys) @ zs)"
    by (simp only: HI)
  also have "… = (x # (xs @ ys)) @ zs"
    by (simp only: append_Cons)
  also have "… = ((x # xs) @ ys) @ zs"
    by (simp only: append_Cons)
  finally show "(x # xs) @ (ys @ zs) = ((x # xs) @ ys) @ zs"
    by this
qed

(* 2ª demostración *)
lemma "xs @ (ys @ zs) = (xs @ ys) @ zs"
proof (induct xs)
  have "[] @ (ys @ zs) = ys @ zs" by simp
  also have "… = ([] @ ys) @ zs" by simp
  finally show "[] @ (ys @ zs) = ([] @ ys) @ zs" .
next
  fix x xs
  assume HI : "xs @ (ys @ zs) = (xs @ ys) @ zs"
  have "(x # xs) @ (ys @ zs) = x # (xs @ (ys @ zs))" by simp
  also have "… = x # ((xs @ ys) @ zs)" by simp
  also have "… = (x # (xs @ ys)) @ zs" by simp
  also have "… = ((x # xs) @ ys) @ zs" by simp
  finally show "(x # xs) @ (ys @ zs) = ((x # xs) @ ys) @ zs" .
qed

(* 3ª demostración *)
lemma "xs @ (ys @ zs) = (xs @ ys) @ zs"
proof (induct xs)
  show "[] @ (ys @ zs) = ([] @ ys) @ zs" by simp
next
  fix x xs
  assume "xs @ (ys @ zs) = (xs @ ys) @ zs"
  then show "(x # xs) @ (ys @ zs) = ((x # xs) @ ys) @ zs" by simp
qed

(* 4ª demostración *)
lemma "xs @ (ys @ zs) = (xs @ ys) @ zs"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by simp
qed

(* 5ª demostración *)
lemma "xs @ (ys @ zs) = (xs @ ys) @ zs"
  by (rule append_assoc [symmetric])

(* 6ª demostración *)
lemma "xs @ (ys @ zs) = (xs @ ys) @ zs"
  by (induct xs) simp_all

(* 7ª demostración *)
lemma "xs @ (ys @ zs) = (xs @ ys) @ zs"
  by simp

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
