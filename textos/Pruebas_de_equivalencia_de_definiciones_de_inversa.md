---
Título: Pruebas de equivalencia de definiciones de inversa
Autor:  José A. Alonso
---

En Lean, está definida la función
<pre lang="text">
   reverse : list α → list α
</pre>
tal que (reverse xs) es la lista obtenida invirtiendo el orden de los elementos de xs. Por ejemplo,
<pre lang="text">
   reverse  [3,2,5,1] = [1,5,2,3]
</pre>
Su definición es
<pre lang="text">
   def reverse_core : list α → list α → list α
   | []     r := r
   | (a::l) r := reverse_core l (a::r)

   def reverse : list α → list α :=
   λ l, reverse_core l []
</pre>

Una definición alternativa es
<pre lang="text">
   def inversa : list α → list α
   | []        := []
   | (x :: xs) := inversa xs ++ [x]
</pre>

Demostrar que las dos definiciones son equivalentes; es decir,
<pre lang="text">
   reverse xs = inversa xs
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.list.basic
open list

variable  {α : Type*}
variable  (x : α)
variables (xs ys : list α)

def inversa : list α → list α
| []        := []
| (x :: xs) := inversa xs ++ [x]

example : reverse xs = inversa xs :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.list.basic
open list

variable  {α : Type*}
variable  (x : α)
variables (xs ys : list α)

-- Definición y reglas de simplificación de inversa
-- ================================================

def inversa : list α → list α
| []        := []
| (x :: xs) := inversa xs ++ [x]

@[simp]
lemma inversa_nil :
  inversa ([] : list α) = [] :=
rfl

@[simp]
lemma inversa_cons :
  inversa (x :: xs) = inversa xs ++ [x] :=
rfl

-- Reglas de simplificación de reverse_core
-- ========================================

@[simp]
lemma reverse_core_nil :
  reverse_core [] ys = ys :=
rfl

@[simp]
lemma reverse_core_cons :
  reverse_core (x :: xs) ys = reverse_core xs (x :: ys) :=
rfl

-- Lema auxiliar: reverse_core xs ys = (inversa xs) ++ ys
-- ======================================================

-- 1ª demostración del lema auxiliar
example :
  reverse_core xs ys = (inversa xs) ++ ys :=
begin
  induction xs with a as HI generalizing ys,
  { calc reverse_core [] ys
         = ys                        : reverse_core_nil ys
     ... = [] ++ ys                  : (nil_append ys).symm
     ... = inversa [] ++ ys          : congr_arg2 (++) inversa_nil.symm rfl, },
  { calc reverse_core (a :: as) ys
         = reverse_core as (a :: ys) : reverse_core_cons a as ys
     ... = inversa as ++ (a :: ys)   : (HI (a :: ys))
     ... = inversa as ++ ([a] ++ ys) : congr_arg2 (++) rfl singleton_append
     ... = (inversa as ++ [a]) ++ ys : (append_assoc (inversa as) [a] ys).symm
     ... = inversa (a :: as) ++ ys   : congr_arg2 (++) (inversa_cons a as).symm rfl},
end

-- 2ª demostración del lema auxiliar
example :
  reverse_core xs ys = (inversa xs) ++ ys :=
begin
  induction xs with a as HI generalizing ys,
  { calc reverse_core [] ys
         = ys                        : by rw reverse_core_nil
     ... = [] ++ ys                  : by rw nil_append
     ... = inversa [] ++ ys          : by rw inversa_nil },
  { calc reverse_core (a :: as) ys
         = reverse_core as (a :: ys) : by rw reverse_core_cons
     ... = inversa as ++ (a :: ys)   : by rw (HI (a :: ys))
     ... = inversa as ++ ([a] ++ ys) : by rw singleton_append
     ... = (inversa as ++ [a]) ++ ys : by rw append_assoc
     ... = inversa (a :: as) ++ ys   : by rw inversa_cons },
end

-- 3ª demostración del lema auxiliar
example :
  reverse_core xs ys = (inversa xs) ++ ys :=
begin
  induction xs with a as HI generalizing ys,
  { calc reverse_core [] ys
         = ys                        : rfl
     ... = [] ++ ys                  : rfl
     ... = inversa [] ++ ys          : rfl },
  { calc reverse_core (a :: as) ys
         = reverse_core as (a :: ys) : rfl
     ... = inversa as ++ (a :: ys)   : (HI (a :: ys))
     ... = inversa as ++ ([a] ++ ys) : rfl
     ... = (inversa as ++ [a]) ++ ys : by rw append_assoc
     ... = inversa (a :: as) ++ ys   : rfl },
end

-- 3ª demostración del lema auxiliar
example :
  reverse_core xs ys = (inversa xs) ++ ys :=
begin
  induction xs with a as HI generalizing ys,
  { calc reverse_core [] ys
         = ys                        : by simp
     ... = [] ++ ys                  : by simp
     ... = inversa [] ++ ys          : by simp },
  { calc reverse_core (a :: as) ys
         = reverse_core as (a :: ys) : by simp
     ... = inversa as ++ (a :: ys)   : (HI (a :: ys))
     ... = inversa as ++ ([a] ++ ys) : by simp
     ... = (inversa as ++ [a]) ++ ys : by simp
     ... = inversa (a :: as) ++ ys   : by simp },
end

-- 4ª demostración del lema auxiliar
example :
  reverse_core xs ys = (inversa xs) ++ ys :=
begin
  induction xs with a as HI generalizing ys,
  { by simp, },
  { calc reverse_core (a :: as) ys
         = reverse_core as (a :: ys) : by simp
     ... = inversa as ++ (a :: ys)   : (HI (a :: ys))
     ... = inversa (a :: as) ++ ys   : by simp },
end

-- 5ª demostración del lema auxiliar
example :
  reverse_core xs ys = (inversa xs) ++ ys :=
begin
  induction xs with a as HI generalizing ys,
  { simp, },
  { simp [HI (a :: ys)], },
end

-- 6ª demostración del lema auxiliar
example :
  reverse_core xs ys = (inversa xs) ++ ys :=
by induction xs generalizing ys ; simp [*]

-- 7ª demostración del lema auxiliar
example :
  reverse_core xs ys = (inversa xs) ++ ys :=
begin
  induction xs with a as HI generalizing ys,
  { rw reverse_core_nil,
    rw inversa_nil,
    rw nil_append, },
  { rw reverse_core_cons,
    rw (HI (a :: ys)),
    rw inversa_cons,
    rw append_assoc,
    rw singleton_append, },
end

-- 8ª demostración  del lema auxiliar
@[simp]
lemma inversa_equiv :
  ∀ xs : list α, ∀ ys, reverse_core xs ys = (inversa xs) ++ ys
| []         := by simp
| (a :: as)  := by simp [inversa_equiv as]

-- Demostraciones del lema principal
-- =================================

-- 1ª demostración
example : reverse xs = inversa xs :=
calc reverse xs
     = reverse_core xs [] : rfl
 ... = inversa xs ++ []   : by rw inversa_equiv
 ... = inversa xs         : by rw append_nil

-- 2ª demostración
example : reverse xs = inversa xs :=
by simp [inversa_equiv, reverse]

-- 3ª demostración
example : reverse xs = inversa xs :=
by simp [reverse]
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Pruebas_de_equivalencia_de_definiciones_de_inversa.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Pruebas_de_equivalencia_de_definiciones_de_inversa
imports Main
begin

(* Definición alternativa *)
(* ====================== *)

fun inversa_aux :: "'a list ⇒ 'a list ⇒ 'a list" where
  "inversa_aux [] ys     = ys"
| "inversa_aux (x#xs) ys = inversa_aux xs (x#ys)"

fun inversa :: "'a list ⇒ 'a list" where
  "inversa xs = inversa_aux xs []"

(* Lema auxiliar: inversa_aux xs ys = (rev xs) @ ys *)
(* ================================================ *)

(* 1ª demostración del lema auxiliar *)
lemma
  "inversa_aux xs ys = (rev xs) @ ys"
proof (induct xs arbitrary: ys)
  fix ys :: "'a list"
  have "inversa_aux [] ys = ys"
    by (simp only: inversa_aux.simps(1))
  also have "… = [] @ ys"
    by (simp only: append.simps(1))
  also have "… = rev [] @ ys"
    by (simp only: rev.simps(1))
  finally show "inversa_aux [] ys = rev [] @ ys"
    by this
next
  fix a ::'a and xs :: "'a list"
  assume HI: "⋀ys. inversa_aux xs ys = rev xs@ys"
  show "⋀ys. inversa_aux (a#xs) ys = rev (a#xs)@ys"
  proof -
    fix ys
    have "inversa_aux (a#xs) ys = inversa_aux xs (a#ys)"
      by (simp only: inversa_aux.simps(2))
    also have "… = rev xs@(a#ys)"
      by (simp only: HI)
    also have "… = rev xs @ ([a] @ ys)"
      by (simp only: append.simps)
    also have "… = (rev xs @ [a]) @ ys"
      by (simp only: append_assoc)
    also have "… = rev (a # xs) @ ys"
      by (simp only: rev.simps(2))
    finally show "inversa_aux (a#xs) ys = rev (a#xs)@ys"
      by this
  qed
qed

(* 2ª demostración del lema auxiliar *)
lemma
  "inversa_aux xs ys = (rev xs) @ ys"
proof (induct xs arbitrary: ys)
  fix ys :: "'a list"
  have "inversa_aux [] ys = ys" by simp
  also have "… = [] @ ys" by simp
  also have "… = rev [] @ ys" by simp
  finally show "inversa_aux [] ys = rev [] @ ys" .
next
  fix a ::'a and xs :: "'a list"
  assume HI: "⋀ys. inversa_aux xs ys = rev xs@ys"
  show "⋀ys. inversa_aux (a#xs) ys = rev (a#xs)@ys"
  proof -
    fix ys
    have "inversa_aux (a#xs) ys = inversa_aux xs (a#ys)" by simp
    also have "… = rev xs@(a#ys)" using HI by simp
    also have "… = rev xs @ ([a] @ ys)" by simp
    also have "… = (rev xs @ [a]) @ ys" by simp
    also have "… = rev (a # xs) @ ys" by simp
    finally show "inversa_aux (a#xs) ys = rev (a#xs)@ys" .
  qed
qed

(* 3ª demostración del lema auxiliar *)
lemma
  "inversa_aux xs ys = (rev xs) @ ys"
proof (induct xs arbitrary: ys)
  fix ys :: "'a list"
  show "inversa_aux [] ys = rev [] @ ys" by simp
next
  fix a ::'a and xs :: "'a list"
  assume HI: "⋀ys. inversa_aux xs ys = rev xs@ys"
  show "⋀ys. inversa_aux (a#xs) ys = rev (a#xs)@ys"
  proof -
    fix ys
    have "inversa_aux (a#xs) ys = rev xs@(a#ys)" using HI by simp
    also have "… = rev (a # xs) @ ys" by simp
    finally show "inversa_aux (a#xs) ys = rev (a#xs)@ys" .
  qed
qed

(* 4ª demostración del lema auxiliar *)
lemma
  "inversa_aux xs ys = (rev xs) @ ys"
proof (induct xs arbitrary: ys)
  show "⋀ys. inversa_aux [] ys = rev [] @ ys" by simp
next
  fix a ::'a and xs :: "'a list"
  assume "⋀ys. inversa_aux xs ys = rev xs@ys"
  then show "⋀ys. inversa_aux (a#xs) ys = rev (a#xs)@ys" by simp
qed

(* 5ª demostración del lema auxiliar *)
lemma
  "inversa_aux xs ys = (rev xs) @ ys"
proof (induct xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by simp
qed

(* 6ª demostración del lema auxiliar *)
lemma inversa_equiv:
  "inversa_aux xs ys = (rev xs) @ ys"
by (induct xs arbitrary: ys) simp_all

(* Demostraciones del lema principal *)
(* ================================= *)

(* 1ª demostración *)
lemma "inversa xs = rev xs"
proof -
  have "inversa xs = inversa_aux xs []"
    by (rule inversa.simps)
  also have "… = (rev xs) @ []"
    by (rule inversa_equiv)
  also have "… = rev xs"
    by (rule append.right_neutral)
  finally show "inversa xs = rev xs"
    by this
qed

(* 2ª demostración *)
lemma "inversa xs = rev xs"
proof -
  have "inversa xs = inversa_aux xs []"  by simp
  also have "… = (rev xs) @ []" by (rule inversa_equiv)
  also have "… = rev xs" by simp
  finally show "inversa xs = rev xs" .
qed

(* 3ª demostración *)
lemma "inversa xs = rev xs"
by (simp add: inversa_equiv)

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
