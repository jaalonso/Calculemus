---
Título: Pruebas de take n xs ++ drop n xs = xs
Autor:  José A. Alonso
---

En Lean están definidas las funciones
<pre lang="text">
   take : nat → list α → nat
   drop : nat → list α → nat
   (++) : list α → list α → list α
</pre>
tales que

+ (take n xs) es la lista formada por los n primeros elementos de xs. Por ejemplo,
<pre lang="text">
     take 2 [3,5,1,9,7] = [3,5]
</pre>
+ (drop n xs) es la lista formada eliminando los n primeros elementos de xs. Por ejemplo,
<pre lang="text">
     drop 2 [3,5,1,9,7] = [1,9,7]
</pre>
+ (xs ++ ys) es la lista obtenida concatenando xs e ys. Por ejemplo.
<pre lang="text">
     [3,5] ++ [1,9,7] = [3,5,1,9,7]
</pre>
Dichas funciones están caracterizadas por los siguientes lemas:
<pre lang="text">
   take_zero   : take 0 xs = []
   take_nil    : take n [] = []
   take_cons   : take (succ n) (x :: xs) = x :: take n xs
   drop_zero   : drop 0 xs = xs
   drop_nil    : drop n [] = []
   drop_cons   : drop (succ n) (x :: xs) = drop n xs := rfl
   nil_append  : [] ++ ys = ys
   cons_append : (x :: xs) ++ y = x :: (xs ++ ys)
</pre>

Demostrar que
<pre lang="text">
   take n xs ++ drop n xs = xs
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.list.basic
import tactic
open list nat

variable {α : Type}
variable (x : α)
variable (xs : list α)
variable (n : ℕ)

lemma drop_zero : drop 0 xs = xs := rfl
lemma drop_cons : drop (succ n) (x :: xs) = drop n xs := rfl

example :
  take n xs ++ drop n xs = xs :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
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
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Pruebas_de_take_n_xs_++_drop_n_xs_Ig_xs.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory "Pruebas_de_take_n_xs_++_drop_n_xs_Ig_xs"
imports Main
begin

fun take' :: "nat ⇒ 'a list ⇒ 'a list" where
  "take' n []           = []"
| "take' 0 xs           = []"
| "take' (Suc n) (x#xs) = x # (take' n xs)"

fun drop' :: "nat ⇒ 'a list ⇒ 'a list" where
  "drop' n []           = []"
| "drop' 0 xs           = xs"
| "drop' (Suc n) (x#xs) = drop' n xs"

(* 1ª demostración *)
lemma "take' n xs @ drop' n xs = xs"
proof (induct rule: take'.induct)
  fix n
  have "take' n [] @ drop' n [] = [] @ drop' n []"
    by (simp only: take'.simps(1))
  also have "… = drop' n []"
    by (simp only: append.simps(1))
  also have "… = []"
    by (simp only: drop'.simps(1))
  finally show "take' n [] @ drop' n [] = []"
    by this
next
  fix x :: 'a and xs :: "'a list"
  have "take' 0 (x#xs) @ drop' 0 (x#xs) =
        [] @ drop' 0 (x#xs)"
    by (simp only: take'.simps(2))
  also have "… = drop' 0 (x#xs)"
    by  (simp only: append.simps(1))
  also have "… = x # xs"
    by  (simp only: drop'.simps(2))
  finally show "take' 0 (x#xs) @ drop' 0 (x#xs) = x#xs"
    by this
next
  fix n :: nat and x :: 'a and xs :: "'a list"
  assume HI: "take' n xs @ drop' n xs = xs"
  have "take' (Suc n) (x # xs) @ drop' (Suc n) (x # xs) =
        (x # (take' n xs)) @ drop' n xs"
    by (simp only: take'.simps(3)
                   drop'.simps(3))
  also have "… = x # (take' n xs @ drop' n xs)"
    by (simp only: append.simps(2))
  also have "… = x#xs"
    by (simp only: HI)
  finally show "take' (Suc n) (x#xs) @ drop' (Suc n) (x#xs) =
                x#xs"
    by this
qed

(* 2ª demostración *)
lemma "take' n xs @ drop' n xs = xs"
proof (induct rule: take'.induct)
case (1 n)
  then show ?case by simp
next
  case (2 x xs)
  then show ?case by simp
next
  case (3 n x xs)
  then show ?case by simp
qed

(* 3ª demostración *)
lemma "take' n xs @ drop' n xs = xs"
by (induct rule: take'.induct) simp_all

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
