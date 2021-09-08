---
Título: Razonamiento sobre árboles binarios: Aplanamiento e imagen especular
Autor:  José A. Alonso
---

El árbol correspondiente a
<pre lang="text">
       3
      / \
     2   4
    / \
   1   5
</pre>
se puede representar por el término
<pre lang="text">
   nodo 3 (nodo 2 (hoja 1) (hoja 5)) (hoja 4)
</pre>
usando el tipo de dato arbol definido por
<pre lang="text">
   inductive arbol (α : Type) : Type
   | hoja : α → arbol
   | nodo : α → arbol → arbol → arbol
</pre>

La imagen especular del árbol anterior es
<pre lang="text">
     3
    / \
   4   2
      / \
     5   1
</pre>
y la lista obtenida aplanándolo (recorriéndolo en orden infijo) es
<pre lang="text">
   [4, 3, 5, 2, 1]
</pre>

La definición de la función que calcula la imagen especular es
<pre lang="text">
   def espejo : arbol α → arbol α
   | (hoja x)     := hoja x
   | (nodo x i d) := nodo x (espejo d) (espejo i)
</pre>
y la que aplana el árbol es
<pre lang="text">
   def aplana : arbol α → list α
   | (hoja x)     := [x]
   | (nodo x i d) := (aplana i) ++ [x] ++ (aplana d)
</pre>

Demostrar que
<pre lang="text">
   aplana (espejo a) = rev (aplana a)
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic
open list

variable {α : Type}

inductive arbol (α : Type) : Type
| hoja : α → arbol
| nodo : α → arbol → arbol → arbol

namespace arbol

variables (a i d : arbol α)
variable  (x : α)

def espejo : arbol α → arbol α
| (hoja x)     := hoja x
| (nodo x i d) := nodo x (espejo d) (espejo i)

def aplana : arbol α → list α
| (hoja x)     := [x]
| (nodo x i d) := (aplana i) ++ [x] ++ (aplana d)

example :
  aplana (espejo a) = reverse (aplana a) :=
sorry

end arbol
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import tactic
open list

variable {α : Type}

-- Para que no use la notación con puntos
set_option pp.structure_projections false

inductive arbol (α : Type) : Type
| hoja : α → arbol
| nodo : α → arbol → arbol → arbol

namespace arbol

variables (a i d : arbol α)
variable  (x : α)

def espejo : arbol α → arbol α
| (hoja x)     := hoja x
| (nodo x i d) := nodo x (espejo d) (espejo i)

@[simp]
lemma espejo_1 :
  espejo (hoja x) = hoja x :=
rfl

@[simp]
lemma espejo_2 :
  espejo (nodo x i d) = nodo x (espejo d) (espejo i) :=
rfl

def aplana : arbol α → list α
| (hoja x)     := [x]
| (nodo x i d) := (aplana i) ++ [x] ++ (aplana d)

@[simp]
lemma aplana_1 :
  aplana (hoja x) = [x] :=
rfl

@[simp]
lemma aplana_2 :
  aplana (nodo x i d) = (aplana i) ++ [x] ++ (aplana d) :=
rfl

-- 1ª demostración
example :
  aplana (espejo a) = reverse (aplana a) :=
begin
  induction a with x x i d Hi Hd,
  { rw espejo_1,
    rw aplana_1,
    rw reverse_singleton, },
  { rw espejo_2,
    rw aplana_2,
    rw [Hi, Hd],
    rw aplana_2,
    rw reverse_append,
    rw reverse_append,
    rw reverse_singleton,
    rw append_assoc, },
end

-- 2ª demostración
example :
  aplana (espejo a) = reverse (aplana a) :=
begin
  induction a with x x i d Hi Hd,
  { calc aplana (espejo (hoja x))
         = aplana (hoja x)
             : congr_arg aplana (espejo_1 x)
     ... = [x]
             : aplana_1 x
     ... = reverse [x]
             : reverse_singleton x
     ... = reverse (aplana (hoja x))
             : congr_arg reverse (aplana_1 x).symm, },
  { calc aplana (espejo (nodo x i d))
         = aplana (nodo x (espejo d) (espejo i))
             : congr_arg aplana (espejo_2 i d x)
     ... = (aplana (espejo d) ++ [x]) ++ aplana (espejo i)
             : aplana_2 (espejo d) (espejo i) x
     ... = (reverse (aplana d) ++ [x]) ++ aplana (espejo i)
             : congr_arg2 (++) (congr_arg2 (++) Hd rfl) rfl
     ... = (reverse (aplana d) ++ [x]) ++ reverse (aplana i)
             : congr_arg2 (++) rfl Hi
     ... = (reverse (aplana d) ++ reverse [x]) ++ reverse (aplana i)
             : congr_arg2 (++) (congr_arg2 (++) rfl (reverse_singleton x).symm) rfl
     ... = reverse ([x] ++ aplana d) ++ reverse (aplana i)
             : congr_arg2 (++) (reverse_append [x] (aplana d)).symm rfl
     ... = reverse (aplana i ++ ([x] ++ aplana d))
             : (reverse_append (aplana i) ([x] ++ aplana d)).symm
     ... = reverse ((aplana i ++ [x]) ++ aplana d)
             : congr_arg reverse (append_assoc (aplana i) [x] (aplana d)).symm
     ... = reverse (aplana (nodo x i d))
             : congr_arg reverse (aplana_2 i d x), },
end

-- 3ª demostración
example :
  aplana (espejo a) = reverse (aplana a) :=
begin
  induction a with x x i d Hi Hd,
  { calc aplana (espejo (hoja x))
         = aplana (hoja x)
             : by simp only [espejo_1]
     ... = [x]
             : by rw aplana_1
     ... = reverse [x]
             : by rw reverse_singleton
     ... = reverse (aplana (hoja x))
             : by simp only [aplana_1], },
  { calc aplana (espejo (nodo x i d))
         = aplana (nodo x (espejo d) (espejo i))
             : by simp only [espejo_2]
     ... = aplana (espejo d) ++ [x] ++ aplana (espejo i)
             : by rw aplana_2
     ... = reverse (aplana d) ++ [x] ++ reverse (aplana i)
             : by rw [Hi, Hd]
     ... = reverse (aplana d) ++ reverse [x] ++ reverse (aplana i)
             : by simp only [reverse_singleton]
     ... = reverse ([x] ++ aplana d) ++ reverse (aplana i)
             : by simp only [reverse_append]
     ... = reverse (aplana i ++ ([x] ++ aplana d))
             : by simp only [reverse_append]
     ... = reverse (aplana i ++ [x] ++ aplana d)
             : by simp only [append_assoc]
     ... = reverse (aplana (nodo x i d))
             : by simp only [aplana_2], },
end

-- 3ª demostración
example :
  aplana (espejo a) = reverse (aplana a) :=
begin
  induction a with x x i d Hi Hd,
  { calc aplana (espejo (hoja x))
         = aplana (hoja x)           : by simp
     ... = [x]                       : by simp
     ... = reverse [x]               : by simp
     ... = reverse (aplana (hoja x)) : by simp, },
  { calc aplana (espejo (nodo x i d))
         = aplana (nodo x (espejo d) (espejo i))
             : by simp
     ... = aplana (espejo d) ++ [x] ++ aplana (espejo i)
             : by simp
     ... = reverse (aplana d) ++ [x] ++ reverse (aplana i)
             : by simp [Hi, Hd]
     ... = reverse (aplana d) ++ reverse [x] ++ reverse (aplana i)
             : by simp
     ... = reverse ([x] ++ aplana d) ++ reverse (aplana i)
             : by simp
     ... = reverse (aplana i ++ ([x] ++ aplana d))
             : by simp
     ... = reverse (aplana i ++ [x] ++ aplana d)
             : by simp
     ... = reverse (aplana (nodo x i d))
             : by simp },
end

-- 5ª demostración
example :
  aplana (espejo a) = reverse (aplana a) :=
begin
  induction a with x x i d Hi Hd,
  { simp, },
  { calc aplana (espejo (nodo x i d))
         = reverse (aplana d) ++ [x] ++ reverse (aplana i)
             : by simp [Hi, Hd]
     ... = reverse (aplana (nodo x i d))
             : by simp },
end

-- 6ª demostración
example :
  aplana (espejo a) = reverse (aplana a) :=
begin
  induction a with x x i d Hi Hd,
  { simp, },
  { simp [Hi, Hd], },
end

-- 7ª demostración
example :
  aplana (espejo a) = reverse (aplana a) :=
by induction a ; simp [*]

-- 8ª demostración
example :
  aplana (espejo a) = reverse (aplana a) :=
arbol.rec_on a
  ( assume x,
    calc aplana (espejo (hoja x))
         = aplana (hoja x)
             : by simp only [espejo_1]
     ... = [x]
             : by rw aplana_1
     ... = reverse [x]
             : by rw reverse_singleton
     ... = reverse (aplana (hoja x))
             : by simp only [aplana_1])
  ( assume x i d,
    assume Hi : aplana (espejo i) = reverse (aplana i),
    assume Hd : aplana (espejo d) = reverse (aplana d),
    calc aplana (espejo (nodo x i d))
         = aplana (nodo x (espejo d) (espejo i))
             : by simp only [espejo_2]
     ... = aplana (espejo d) ++ [x] ++ aplana (espejo i)
             : by rw aplana_2
     ... = reverse (aplana d) ++ [x] ++ reverse (aplana i)
             : by rw [Hi, Hd]
     ... = reverse (aplana d) ++ reverse [x] ++ reverse (aplana i)
             : by simp only [reverse_singleton]
     ... = reverse ([x] ++ aplana d) ++ reverse (aplana i)
             : by simp only [reverse_append]
     ... = reverse (aplana i ++ ([x] ++ aplana d))
             : by simp only [reverse_append]
     ... = reverse (aplana i ++ [x] ++ aplana d)
             : by simp only [append_assoc]
     ... = reverse (aplana (nodo x i d))
             : by simp only [aplana_2])

-- 9ª demostración
example :
  aplana (espejo a) = reverse (aplana a) :=
arbol.rec_on a
  (λ x, by simp)
  (λ x i d Hi Hd, by simp [Hi, Hd])

-- 10ª demostración
lemma aplana_espejo :
  ∀ a : arbol α, aplana (espejo a) = reverse (aplana a)
| (hoja x)     := by simp
| (nodo x i d) := by simp [aplana_espejo i,
                           aplana_espejo d]

end arbol
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Razonamiento_sobre_arboles_binarios_Aplanamiento_e_imagen_especular.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Razonamiento_sobre_arboles_binarios_Aplanamiento_e_imagen_especular
imports Main
begin

datatype 'a arbol = hoja "'a"
                  | nodo "'a" "'a arbol" "'a arbol"

fun espejo :: "'a arbol ⇒ 'a arbol" where
  "espejo (hoja x)     = (hoja x)"
| "espejo (nodo x i d) = (nodo x (espejo d) (espejo i))"

fun aplana :: "'a arbol ⇒ 'a list" where
  "aplana (hoja x)     = [x]"
| "aplana (nodo x i d) = (aplana i) @ [x] @ (aplana d)"

(* Lema auxiliar *)
(* ============= *)

(* 1ª demostración del lema auxiliar *)
lemma "rev [x] = [x]"
proof -
  have "rev [x] = rev [] @ [x]"
    by (simp only: rev.simps(2))
  also have "… = [] @ [x]"
    by (simp only: rev.simps(1))
  also have "… = [x]"
    by (simp only: append.simps(1))
  finally show ?thesis
    by this
qed

(* 2ª demostración del lema auxiliar *)
lemma rev_unit: "rev [x] = [x]"
by simp

(* Lema principal *)
(* ============== *)

(* ?ª demostración *)
lemma
  fixes a :: "'b arbol"
  shows "aplana (espejo a) = rev (aplana a)" (is "?P a")
proof (induct a)
  fix x :: 'b
  have "aplana (espejo (hoja x)) = aplana (hoja x)"
    by (simp only: espejo.simps(1))
  also have "… = [x]"
    by (simp only: aplana.simps(1))
  also have "… = rev [x]"
    by (rule rev_unit [symmetric])
  also have "… = rev (aplana (hoja x))"
    by (simp only: aplana.simps(1))
  finally show "?P (hoja x)"
    by this
next
  fix x :: 'b
  fix i assume h1: "?P i"
  fix d assume h2: "?P d"
  show "?P (nodo x i d)"
  proof -
    have "aplana (espejo (nodo x i d)) =
          aplana (nodo x (espejo d) (espejo i))"
      by (simp only: espejo.simps(2))
    also have "… = (aplana (espejo d)) @ [x] @ (aplana (espejo i))"
      by (simp only: aplana.simps(2))
    also have "… = (rev (aplana d)) @ [x] @ (rev (aplana i))"
      by (simp only: h1 h2)
    also have "… = rev ((aplana i) @ [x] @ (aplana d))"
      by (simp only: rev_append rev_unit append_assoc)
    also have "… = rev (aplana (nodo x i d))"
      by (simp only: aplana.simps(2))
    finally show ?thesis
      by this
 qed
qed

(* 2ª demostración *)
lemma
  fixes a :: "'b arbol"
  shows "aplana (espejo a) = rev (aplana a)" (is "?P a")
proof (induct a)
  fix x
  show "?P (hoja x)" by simp
next
  fix x
  fix i assume h1: "?P i"
  fix d assume h2: "?P d"
  show "?P (nodo x i d)"
  proof -
    have "aplana (espejo (nodo x i d)) =
          aplana (nodo x (espejo d) (espejo i))" by simp
    also have "… = (aplana (espejo d)) @ [x] @ (aplana (espejo i))"
      by simp
    also have "… = (rev (aplana d)) @ [x] @ (rev (aplana i))"
      using h1 h2 by simp
    also have "… = rev ((aplana i) @ [x] @ (aplana d))" by simp
    also have "… = rev (aplana (nodo x i d))" by simp
    finally show ?thesis .
 qed
qed

(* 3ª demostración *)
lemma "aplana (espejo a) = rev (aplana a)"
proof (induct a)
case (hoja x)
then show ?case by simp
next
  case (nodo x i d)
  then show ?case by simp
qed

(* 4ª demostración *)
lemma "aplana (espejo a) = rev (aplana a)"
  by (induct a) simp_all

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
