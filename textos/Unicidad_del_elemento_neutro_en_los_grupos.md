---
Título: Unicidad del elemento neutro en los grupos
Autor:  José A. Alonso
---

Demostrar que un grupo sólo posee un elemento neutro.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import algebra.group.basic

universe  u
variables {G : Type u} [group G]

example
  (e : G)
  (h : ∀ x, x * e = x)
  : e = 1 :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import algebra.group.basic

universe  u
variables {G : Type u} [group G]

-- 1ª demostración
-- ===============

example
  (e : G)
  (h : ∀ x, x * e = x)
  : e = 1 :=
calc e = 1 * e : (one_mul e).symm
   ... = 1     : h 1

-- 2ª demostración
-- ===============

example
  (e : G)
  (h : ∀ x, x * e = x)
  : e = 1 :=
by finish
</pre>

Se puede interactuar con la prueba anterior en <a href="https://www.cs.us.es/~jalonso/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Unicidad_del_elemento_neutro_en_los_grupos.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Unicidad_del_elemento_neutro_en_los_grupos
imports Main
begin

context group
begin

(* 1ª demostración *)

lemma
  assumes "∀ x. x * e = x"
  shows   "e = 1"
proof -
  have "e = 1 * e"     by (simp only: left_neutral)
  also have "… = 1"    using assms by (rule allE)
  finally show "e = 1" by this
qed

(* 2ª demostración *)

lemma
  assumes "∀ x. x * e = x"
  shows   "e = 1"
proof -
  have "e = 1 * e"     by simp
  also have "… = 1"    using assms by simp
  finally show "e = 1" .
qed

(* 3ª demostración *)

lemma
  assumes "∀ x. x * e = x"
  shows   "e = 1"
  using assms
  by (metis left_neutral)

end

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

<h4> Referencia</h4>

Propiedad 3.17 del libro [Abstract algebra: Theory and applications](http://abstract.ups.edu/download/aata-20200730.pdf#page=49) de Thomas W. Judson.
