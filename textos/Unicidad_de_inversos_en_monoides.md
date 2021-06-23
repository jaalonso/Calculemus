---
Título: Unicidad de inversos en monoides conmutativos
Autor:  José A. Alonso
---

Demostrar que en los monoides conmutativos, si un elemento tiene un inverso por la derecha, dicho inverso es único.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import algebra.group.basic

variables {M : Type} [comm_monoid M]
variables {x y z : M}

example
  (hy : x * y = 1)
  (hz : x * z = 1)
  : y = z :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import algebra.group.basic

variables {M : Type} [comm_monoid M]
variables {x y z : M}

-- 1ª demostración
-- ===============

example
  (hy : x * y = 1)
  (hz : x * z = 1)
  : y = z :=
calc y = 1 * y       : (one_mul y).symm
   ... = (x * z) * y : congr_arg (* y) hz.symm
   ... = (z * x) * y : congr_arg (* y) (mul_comm x z)
   ... = z * (x * y) : mul_assoc z x y
   ... = z * 1       : congr_arg ((*) z) hy
   ... = z           : mul_one z

-- 2ª demostración
-- ===============

example
  (hy : x * y = 1)
  (hz : x * z = 1)
  : y = z :=
calc y = 1 * y       : by simp only [one_mul]
   ... = (x * z) * y : by simp only [hz]
   ... = (z * x) * y : by simp only [mul_comm]
   ... = z * (x * y) : by simp only [mul_assoc]
   ... = z * 1       : by simp only [hy]
   ... = z           : by simp only [mul_one]

-- 3ª demostración
-- ===============

example
  (hy : x * y = 1)
  (hz : x * z = 1)
  : y = z :=
calc y = 1 * y       : by simp
   ... = (x * z) * y : by simp [hz]
   ... = (z * x) * y : by simp [mul_comm]
   ... = z * (x * y) : by simp [mul_assoc]
   ... = z * 1       : by simp [hy]
   ... = z           : by simp

-- 4ª demostración
-- ===============

example
  (hy : x * y = 1)
  (hz : x * z = 1)
  : y = z :=
begin
  apply left_inv_eq_right_inv _ hz,
  rw mul_comm,
  exact hy,
end

-- 5ª demostración
-- ===============

example
  (hy : x * y = 1)
  (hz : x * z = 1)
  : y = z :=
left_inv_eq_right_inv (trans (mul_comm _ _) hy) hz

-- 6ª demostración
-- ===============

example
  (hy : x * y = 1)
  (hz : x * z = 1)
  : y = z :=
inv_unique hy hz
</pre>

Se puede interactuar con la prueba anterior en <a href="https://www.cs.us.es/~jalonso/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Unicidad_de_inversos_en_monoides.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>,

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Unicidad_de_inversos_en_monoides
imports Main
begin

context comm_monoid
begin

(* 1ª demostración *)

lemma
  assumes "x * y = 1"
          "x * z = 1"
  shows "y = z"
proof -
  have "y = 1 * y"             by (simp only: left_neutral)
  also have "… = (x * z) * y" by (simp only: ‹x * z = 1›)
  also have "… = (z * x) * y" by (simp only: commute)
  also have "… = z * (x * y)" by (simp only: assoc)
  also have "… = z * 1"       by (simp only: ‹x * y = 1›)
  also have "… = z"           by (simp only: right_neutral)
  finally show "y = z"         by this
qed

(* 2ª demostración *)

lemma
  assumes "x * y = 1"
          "x * z = 1"
  shows "y = z"
proof -
  have "y = 1 * y"             by simp
  also have "… = (x * z) * y" using assms(2) by simp
  also have "… = (z * x) * y" by simp
  also have "… = z * (x * y)" by simp
  also have "… = z * 1"       using assms(1) by simp
  also have "… = z"           by simp
  finally show "y = z"         by this
qed

(* 3ª demostración *)

lemma
  assumes "x * y = 1"
          "x * z = 1"
  shows "y = z"
  using assms
  by auto

end

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
