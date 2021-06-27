---
Título: Unicidad de los inversos en los grupos
Autor:  José A. Alonso
---

Demostrar que si a es un elemento de un grupo G, entonces a tiene un único inverso; es decir, si b es un elemento de G tal que a * b = 1, entonces a⁻¹ = b.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import algebra.group.basic

universe  u
variables {G : Type u} [group G]
variables {a b : G}

example
  (h : a * b = 1)
  : a⁻¹ = b :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import algebra.group.basic

universe  u
variables {G : Type u} [group G]
variables {a b : G}

-- 1ª demostración
-- ===============

example
  (h : a * b = 1)
  : a⁻¹ = b :=
calc a⁻¹ = a⁻¹ * 1       : (mul_one a⁻¹).symm
     ... = a⁻¹ * (a * b) : congr_arg ((*) a⁻¹) h.symm
     ... = (a⁻¹ * a) * b : (mul_assoc a⁻¹ a b).symm
     ... = 1 * b         : congr_arg (* b) (inv_mul_self a)
     ... = b             : one_mul b

-- 2ª demostración
-- ===============

example
  (h : a * b = 1)
  : a⁻¹ = b :=
calc a⁻¹ = a⁻¹ * 1       : by simp only [mul_one]
     ... = a⁻¹ * (a * b) : by simp only [h]
     ... = (a⁻¹ * a) * b : by simp only [mul_assoc]
     ... = 1 * b         : by simp only [inv_mul_self]
     ... = b             : by simp only [one_mul]

-- 3ª demostración
-- ===============

example
  (h : a * b = 1)
  : a⁻¹ = b :=
calc a⁻¹ = a⁻¹ * 1       : by simp
     ... = a⁻¹ * (a * b) : by simp [h]
     ... = (a⁻¹ * a) * b : by simp
     ... = 1 * b         : by simp
     ... = b             : by simp

-- 4ª demostración
-- ===============

example
  (h : a * b = 1)
  : a⁻¹ = b :=
calc a⁻¹ = a⁻¹ * (a * b) : by simp [h]
     ... = b             : by simp

-- 5ª demostración
-- ===============

example
  (h : b * a = 1)
  : b = a⁻¹ :=
eq_inv_of_mul_eq_one h
</pre>

Se puede interactuar con la prueba anterior en <a href="https://www.cs.us.es/~jalonso/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Unicidad_de_los_inversos_en_los_grupos.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Unicidad_de_los_inversos_en_los_grupos
imports Main
begin

context group
begin

(* 1ª demostración *)

lemma
  assumes "a * b = 1"
  shows "inverse a = b"
proof -
  have "inverse a = inverse a * 1"    by (simp only: right_neutral)
  also have "… = inverse a * (a * b)" by (simp only: assms(1))
  also have "… = (inverse a * a) * b" by (simp only: assoc [symmetric])
  also have "… = 1 * b"               by (simp only: left_inverse)
  also have "… = b"                   by (simp only: left_neutral)
  finally show "inverse a = b"        by this
qed

(* 2ª demostración *)

lemma
  assumes "a * b = 1"
  shows "inverse a = b"
proof -
  have "inverse a = inverse a * 1"    by simp
  also have "… = inverse a * (a * b)" using assms by simp
  also have "… = (inverse a * a) * b" by (simp add: assoc [symmetric])
  also have "… = 1 * b"               by simp
  also have "… = b"                   by simp
  finally show "inverse a = b"        .
qed

(* 3ª demostración *)

lemma
  assumes "a * b = 1"
  shows "inverse a = b"
proof -
  from assms have "inverse a * (a * b) = inverse a"
    by simp
  then show "inverse a = b"
    by (simp add: assoc [symmetric])
qed

(* 4ª demostración *)

lemma
  assumes "a * b = 1"
  shows "inverse a = b"
  using assms
  by (simp only: inverse_unique)

end

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

<h4>Referencia</h4>

Propiedad 3.18 del libro [Abstract algebra: Theory and applications](http://abstract.ups.edu/download/aata-20200730.pdf#page=49) de Thomas W. Judson.
