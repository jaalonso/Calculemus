---
Título: Inverso del inverso en grupos
Autor:  José A. Alonso
---

Sea G un grupo y a ∈ G. Demostrar que
<pre lang="text">
    (a⁻¹)⁻¹ = a
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import algebra.group.basic

universe  u
variables {G : Type u} [group G]
variables {a b : G}

example : (a⁻¹)⁻¹ = a :=
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

example : (a⁻¹)⁻¹ = a :=
calc (a⁻¹)⁻¹
     = (a⁻¹)⁻¹ * 1         : (mul_one (a⁻¹)⁻¹).symm
 ... = (a⁻¹)⁻¹ * (a⁻¹ * a) : congr_arg ((*) (a⁻¹)⁻¹) (inv_mul_self a).symm
 ... = ((a⁻¹)⁻¹ * a⁻¹) * a : (mul_assoc _ _ _).symm
 ... = 1 * a               : congr_arg (* a) (inv_mul_self a⁻¹)
 ... = a                   : one_mul a

-- 2ª demostración
-- ===============

example : (a⁻¹)⁻¹ = a :=
calc (a⁻¹)⁻¹
     = (a⁻¹)⁻¹ * 1         : by simp only [mul_one]
 ... = (a⁻¹)⁻¹ * (a⁻¹ * a) : by simp only [inv_mul_self]
 ... = ((a⁻¹)⁻¹ * a⁻¹) * a : by simp only [mul_assoc]
 ... = 1 * a               : by simp only [inv_mul_self]
 ... = a                   : by simp only [one_mul]

-- 3ª demostración
-- ===============

example : (a⁻¹)⁻¹ = a :=
calc (a⁻¹)⁻¹
     = (a⁻¹)⁻¹ * 1         : by simp
 ... = (a⁻¹)⁻¹ * (a⁻¹ * a) : by simp
 ... = ((a⁻¹)⁻¹ * a⁻¹) * a : by simp
 ... = 1 * a               : by simp
 ... = a                   : by simp

-- 4ª demostración
-- ===============

example : (a⁻¹)⁻¹ = a :=
begin
  apply inv_eq_of_mul_eq_one,
  exact mul_left_inv a,
end

-- 5ª demostración
-- ===============

example : (a⁻¹)⁻¹ = a :=
inv_eq_of_mul_eq_one (mul_left_inv a)

-- 6ª demostración
-- ===============

example : (a⁻¹)⁻¹ = a:=
inv_inv a

-- 7ª demostración
-- ===============

example : (a⁻¹)⁻¹ = a:=
by simp
</pre>

Se puede interactuar con la prueba anterior en <a href="https://www.cs.us.es/~jalonso/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Inverso_del_inverso_en_grupos.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Inverso_del_inverso_en_grupos
imports Main
begin

context group
begin

(* 1ª demostración *)

lemma "inverse (inverse a) = a"
proof -
  have "inverse (inverse a) =
        (inverse (inverse a)) * 1"
    by (simp only: right_neutral)
  also have "… = inverse (inverse a) * (inverse a * a)"
    by (simp only: left_inverse)
  also have "… = (inverse (inverse a) * inverse a) * a"
    by (simp only: assoc)
  also have "… = 1 * a"
    by (simp only: left_inverse)
  also have "… = a"
    by (simp only: left_neutral)
  finally show "inverse (inverse a) = a"
    by this
qed

(* 2ª demostración *)

lemma "inverse (inverse a) = a"
proof -
  have "inverse (inverse a) =
        (inverse (inverse a)) * 1"                      by simp
  also have "… = inverse (inverse a) * (inverse a * a)" by simp
  also have "… = (inverse (inverse a) * inverse a) * a" by simp
  also have "… = 1 * a"                                 by simp
  finally show "inverse (inverse a) = a"                by simp
qed

(* 3ª demostración *)

lemma "inverse (inverse a) = a"
proof (rule inverse_unique)
  show "inverse a * a = 1"
    by (simp only: left_inverse)
qed

(* 4ª demostración *)

lemma "inverse (inverse a) = a"
proof (rule inverse_unique)
  show "inverse a * a = 1" by simp
qed

(* 5ª demostración *)

lemma "inverse (inverse a) = a"
  by (rule inverse_unique) simp

(* 6ª demostración *)

lemma "inverse (inverse a) = a"
  by (simp only: inverse_inverse)

(* 7ª demostración *)

lemma "inverse (inverse a) = a"
  by simp

end

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

<h4>Referencia</h4>

Propiedad 3.20 del libro [Abstract algebra: Theory and applications](http://abstract.ups.edu/download/aata-20200730.pdf#page=49) de Thomas W. Judson.
