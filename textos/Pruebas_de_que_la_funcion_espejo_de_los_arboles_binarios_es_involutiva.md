---
Título: Pruebas de que la función espejo de los árboles binarios es involutiva
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
usado el tipo de dato arbol definido por
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
cuyo término es
<pre lang="text">
   nodo 3 (hoja 4) (nodo 2 (hoja 5) (hoja 1))
</pre>

La definición de la función que calcula la imagen especular es
<pre lang="text">
   def espejo : arbol α → arbol α
   | (hoja x)     := hoja x
   | (nodo x i d) := nodo x (espejo d) (espejo i)
</pre>

Demostrar que la función espejo es involutiva; es decir,
<pre lang="text">
   espejo (espejo a) = a
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic

variable  {α : Type}

inductive arbol (α : Type) : Type
| hoja : α → arbol
| nodo : α → arbol → arbol → arbol

namespace arbol

variables (a i d : arbol α)
variable  (x : α)

def espejo : arbol α → arbol α
| (hoja x)     := hoja x
| (nodo x i d) := nodo x (espejo d) (espejo i)

example :
  espejo (espejo a) = a :=
sorry

end arbol
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import tactic

variable  {α : Type}

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
espejo.equations._eqn_1 x

@[simp]
lemma espejo_2 :
  espejo (nodo x i d) = nodo x (espejo d) (espejo i) :=
espejo.equations._eqn_2 x i d

-- 1ª demostración
example :
  espejo (espejo a) = a :=
begin
  induction a with x x i d Hi Hd,
  { rw espejo_1,
    rw espejo_1, },
  { rw espejo_2,
    rw espejo_2,
    rw Hi,
    rw Hd, },
end

-- 2ª demostración
example :
  espejo (espejo a) = a :=
begin
  induction a with x x i d Hi Hd,
  { calc espejo (espejo (hoja x))
         = espejo (hoja x)
             : congr_arg espejo (espejo_1 x)
     ... = hoja x
             : espejo_1 x, },
  { calc espejo (espejo (nodo x i d))
         = espejo (nodo x (espejo d) (espejo i))
             : congr_arg espejo (espejo_2 i d x)
     ... = nodo x (espejo (espejo i)) (espejo (espejo d))
             : espejo_2 (espejo d) (espejo i) x
     ... = nodo x i (espejo (espejo d))
             : congr_arg2 (nodo x) Hi rfl
     ... = nodo x i d
             : congr_arg2 (nodo x) rfl Hd, },
end

-- 3ª demostración
example :
  espejo (espejo a) = a :=
begin
  induction a with x x i d Hi Hd,
  { calc espejo (espejo (hoja x))
         = espejo (hoja x)
             : congr_arg espejo (espejo_1 x)
     ... = hoja x
             : by rw espejo_1, },
  { calc espejo (espejo (nodo x i d))
         = espejo (nodo x (espejo d) (espejo i))
             : congr_arg espejo (espejo_2 i d x)
     ... = nodo x (espejo (espejo i)) (espejo (espejo d))
             : by rw espejo_2
     ... = nodo x i (espejo (espejo d))
             : by rw Hi
     ... = nodo x i d
             : by rw Hd, },
end

-- 4ª demostración
example :
  espejo (espejo a) = a :=
begin
  induction a with x x i d Hi Hd,
  { calc espejo (espejo (hoja x))
         = espejo (hoja x)
             : by simp
     ... = hoja x
             : by simp },
  { calc espejo (espejo (nodo x i d))
         = espejo (nodo x (espejo d) (espejo i))
             : by simp
     ... = nodo x (espejo (espejo i)) (espejo (espejo d))
             : by simp
     ... = nodo x i (espejo (espejo d))
             : by simp [Hi]
     ... = nodo x i d
             : by simp [Hd], },
end

-- 5ª demostración
example :
  espejo (espejo a) = a :=
begin
  induction a with _ x i d Hi Hd,
  { simp, },
  { simp [Hi, Hd], },
end

-- 6ª demostración
example :
  espejo (espejo a) = a :=
by induction a ; simp [*]

-- 7ª demostración
example :
  espejo (espejo a) = a :=
arbol.rec_on a
  ( assume x,
    calc espejo (espejo (hoja x))
         = espejo (hoja x)
             : congr_arg espejo (espejo_1 x)
     ... = hoja x
             : espejo_1 x)
  ( assume x i d,
    assume Hi : espejo (espejo i) = i,
    assume Hd : espejo (espejo d) = d,
    calc espejo (espejo (nodo x i d))
         = espejo (nodo x (espejo d) (espejo i))
             : congr_arg espejo (espejo_2 i d x)
     ... = nodo x (espejo (espejo i)) (espejo (espejo d))
             : by rw espejo_2
     ... = nodo x i (espejo (espejo d))
             : by rw Hi
     ... = nodo x i d
             : by rw Hd )

-- 8ª demostración
example :
  espejo (espejo a) = a :=
arbol.rec_on a
  (λ x, by simp )
  (λ x i d Hi Hd, by simp [Hi,Hd])

-- 9ª demostración
lemma espejo_espejo :
  ∀ a : arbol α, espejo (espejo a) = a
| (hoja x)     := by simp
| (nodo x i d) := by simp [espejo_espejo i, espejo_espejo d]

end arbol
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Pruebas_de_que_la_funcion_espejo_de_los_arboles_binarios_es_involutiva.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Pruebas_de_que_la_funcion_espejo_de_los_arboles_binarios_es_involutiva
imports Main
begin

datatype 'a arbol = hoja "'a"
                  | nodo "'a" "'a arbol" "'a arbol"

fun espejo :: "'a arbol ⇒ 'a arbol" where
  "espejo (hoja x)     = (hoja x)"
| "espejo (nodo x i d) = (nodo x (espejo d) (espejo i))"

(* 1ª demostración *)
lemma
  fixes a :: "'b arbol"
  shows "espejo (espejo a) = a" (is "?P a")
proof (induct a)
  fix x
  show "?P (hoja x)"
    by (simp only: espejo.simps(1))
next
  fix x
  fix i assume h1: "?P i"
  fix d assume h2: "?P d"
  show "?P (nodo x i d)"
  proof -
    have "espejo (espejo (nodo x i d)) =
          espejo (nodo x (espejo d) (espejo i))"
      by (simp only: espejo.simps(2))
    also have "… = nodo x (espejo (espejo i)) (espejo (espejo d))"
      by (simp only: espejo.simps(2))
    also have "… = nodo x i d"
      by (simp only: h1 h2)
    finally show ?thesis
      by this
 qed
qed

(* 2ª demostración *)
lemma
  fixes a :: "'b arbol"
  shows "espejo (espejo a) = a" (is "?P a")
proof (induct a)
  fix x
  show "?P (hoja x)"  by simp
next
  fix x
  fix i assume h1: "?P i"
  fix d assume h2: "?P d"
  show "?P (nodo x i d)"
  proof -
    have "espejo (espejo (nodo x i d)) =
          espejo (nodo x (espejo d) (espejo i))" by simp
    also have "… = nodo x (espejo (espejo i)) (espejo (espejo d))"
      by simp
    also have "… = nodo x i d" using h1 h2 by simp
    finally show ?thesis .
 qed
qed

(* 3ª demostración *)
lemma
  "espejo (espejo a ) = a"
by (induct a) simp_all

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
