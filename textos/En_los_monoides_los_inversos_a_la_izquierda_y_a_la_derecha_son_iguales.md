---
Título: En los monoides, los inversos a la izquierda y a la derecha son iguales
Autor:  José A. Alonso
---

Un [monoide](https://en.wikipedia.org/wiki/Monoid) es un conjunto junto con una operación binaria que es asociativa y tiene elemento neutro.

En Lean, está definida la clase de los monoides (como `monoid`) y sus propiedades características son
<pre lang="text">
   mul_assoc : (a * b) * c = a * (b * c)
   one_mul :   1 * a = a
   mul_one :   a * 1 = a
</pre>

Demostrar que si M es un monide, a ∈ M, b es un inverso de a por la izquierda y c es un inverso de a por la derecha, entonce b = c.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import algebra.group.defs

variables {M : Type} [monoid M]
variables {a b c : M}

example
  (hba : b * a = 1)
  (hac : a * c = 1)
  : b = c :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import algebra.group.defs

variables {M : Type} [monoid M]
variables {a b c : M}

-- 1ª demostración
-- ===============

example
  (hba : b * a = 1)
  (hac : a * c = 1)
  : b = c :=
begin
 rw ←one_mul c,
 rw ←hba,
 rw mul_assoc,
 rw hac,
 rw mul_one b,
end

-- 2ª demostración
-- ===============

example
  (hba : b * a = 1)
  (hac : a * c = 1)
  : b = c :=
by rw [←one_mul c, ←hba, mul_assoc, hac, mul_one b]

-- 3ª demostración
-- ===============

example
  (hba : b * a = 1)
  (hac : a * c = 1)
  : b = c :=
calc b   = b * 1       : (mul_one b).symm
     ... = b * (a * c) : congr_arg (λ x, b * x) hac.symm
     ... = (b * a) * c : (mul_assoc b a c).symm
     ... = 1 * c       : congr_arg (λ x, x * c) hba
     ... = c           : one_mul c

-- 4ª demostración
-- ===============

example
  (hba : b * a = 1)
  (hac : a * c = 1)
  : b = c :=
calc b   = b * 1       : by finish
     ... = b * (a * c) : by finish
     ... = (b * a) * c : (mul_assoc b a c).symm
     ... = 1 * c       : by finish
     ... = c           : by finish

-- 5ª demostración
-- ===============

example
  (hba : b * a = 1)
  (hac : a * c = 1)
  : b = c :=
left_inv_eq_right_inv hba hac
</pre>

Se puede interactuar con la prueba anterior en <a href="https://www.cs.us.es/~jalonso/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/En_los_monoides_los_inversos_a_la_izquierda_y_a_la_derecha_son_iguales.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>,

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory En_los_monoides_los_inversos_a_la_izquierda_y_a_la_derecha_son_iguales
imports Main
begin

context monoid
begin

(* 1ª demostración *)

lemma
  assumes "b ❙* a = ❙1"
          "a ❙* c = ❙1"
  shows   "b = c"
proof -
  have      "b  = b ❙* ❙1"       by (simp only: right_neutral)
  also have "… = b ❙* (a ❙* c)" by (simp only: ‹a ❙* c = ❙1›)
  also have "… = (b ❙* a) ❙* c" by (simp only: assoc)
  also have "… = ❙1 ❙* c"       by (simp only: ‹b ❙* a = ❙1›)
  also have "… = c"           by (simp only: left_neutral)
  finally show "b = c"         by this
qed

(* 2ª demostración *)

lemma
  assumes "b ❙* a = ❙1"
          "a ❙* c = ❙1"
  shows   "b = c"
proof -
  have      "b  = b ❙* ❙1"       by simp
  also have "… = b ❙* (a ❙* c)" using ‹a ❙* c = ❙1› by simp
  also have "… = (b ❙* a) ❙* c" by (simp add: assoc)
  also have "… = ❙1 ❙* c"       using ‹b ❙* a = ❙1› by simp
  also have "… = c"           by simp
  finally show "b = c"         by this
qed

(* 3ª demostración *)

lemma
  assumes "b ❙* a = ❙1"
          "a ❙* c = ❙1"
  shows   "b = c"
  using assms
  by (metis assoc left_neutral right_neutral)

end

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
