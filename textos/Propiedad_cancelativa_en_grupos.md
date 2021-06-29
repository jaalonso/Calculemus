---
Título: Propiedad cancelativa en grupos
Autor:  José A. Alonso
---

Sea G un grupo y a,b,c ∈ G. Demostrar que si a * b = a* c, entonces b = c.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import algebra.group.basic

universe  u
variables {G : Type u} [group G]
variables {a b c : G}

example
  (h: a * b = a  * c)
  : b = c :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import algebra.group.basic

universe  u
variables {G : Type u} [group G]
variables {a b c : G}

-- 1ª demostración
-- ===============

example
  (h: a * b = a  * c)
  : b = c :=
calc b = 1 * b         : (one_mul b).symm
   ... = (a⁻¹ * a) * b : congr_arg (* b) (inv_mul_self a).symm
   ... = a⁻¹ * (a * b) : mul_assoc a⁻¹ a b
   ... = a⁻¹ * (a * c) : congr_arg ((*) a⁻¹) h
   ... = (a⁻¹ * a) * c : (mul_assoc a⁻¹ a c).symm
   ... = 1 * c         : congr_arg (* c) (inv_mul_self a)
   ... = c             : one_mul c

-- 2ª demostración
-- ===============

example
  (h: a * b = a  * c)
  : b = c :=
calc b = 1 * b         : by rw one_mul
   ... = (a⁻¹ * a) * b : by rw inv_mul_self
   ... = a⁻¹ * (a * b) : by rw mul_assoc
   ... = a⁻¹ * (a * c) : by rw h
   ... = (a⁻¹ * a) * c : by rw mul_assoc
   ... = 1 * c         : by rw inv_mul_self
   ... = c             : by rw one_mul

-- 3ª demostración
-- ===============

example
  (h: a * b = a  * c)
  : b = c :=
calc b = 1 * b         : by simp
   ... = (a⁻¹ * a) * b : by simp
   ... = a⁻¹ * (a * b) : by simp
   ... = a⁻¹ * (a * c) : by simp [h]
   ... = (a⁻¹ * a) * c : by simp
   ... = 1 * c         : by simp
   ... = c             : by simp

-- 4ª demostración
-- ===============

example
  (h: a * b = a  * c)
  : b = c :=
calc b = a⁻¹ * (a * b) : by simp
   ... = a⁻¹ * (a * c) : by simp [h]
   ... = c             : by simp

-- 4ª demostración
-- ===============

example
  (h: a * b = a  * c)
  : b = c :=
begin
  have h1 : a⁻¹ * (a * b) = a⁻¹ * (a  * c),
    { by finish [h] },
  have h2 : (a⁻¹ * a) * b = (a⁻¹ * a)  * c,
    { by finish },
  have h3 : 1 * b = 1  * c,
    { by finish },
  have h3 : b = c,
    { by finish },
  exact h3,
end

-- 4ª demostración
-- ===============

example
  (h: a * b = a  * c)
  : b = c :=
begin
  have : a⁻¹ * (a * b) = a⁻¹ * (a  * c),
    { by finish [h] },
  have h2 : (a⁻¹ * a) * b = (a⁻¹ * a)  * c,
    { by finish },
  have h3 : 1 * b = 1  * c,
    { by finish },
  have h3 : b = c,
    { by finish },
  exact h3,
end

-- 4ª demostración
-- ===============

example
  (h: a * b = a  * c)
  : b = c :=
begin
  have h1 : a⁻¹ * (a * b) = a⁻¹ * (a  * c),
    { congr, exact h, },
  have h2 : (a⁻¹ * a) * b = (a⁻¹ * a)  * c,
    { simp only [h1, mul_assoc], },
  have h3 : 1 * b = 1  * c,
    { simp only [h2, (inv_mul_self a).symm], },
  rw one_mul at h3,
  rw one_mul at h3,
  exact h3,
end

-- 5ª demostración
-- ===============

example
  (h: a * b = a  * c)
  : b = c :=
mul_left_cancel h

-- 6ª demostración
-- ===============

example
  (h: a * b = a  * c)
  : b = c :=
by finish
</pre>

Se puede interactuar con la prueba anterior en <a href="https://www.cs.us.es/~jalonso/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Propiedad_cancelativa_en_grupos.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Propiedad_cancelativa_en_grupos
imports Main
begin

context group
begin

(* 1ª demostración *)

lemma
  assumes "a * b = a * c"
  shows   "b = c"
proof -
  have "b = 1 * b"                     by (simp only: left_neutral)
  also have "… = (inverse a * a) * b" by (simp only: left_inverse)
  also have "… = inverse a * (a * b)" by (simp only: assoc)
  also have "… = inverse a * (a * c)" by (simp only: ‹a * b = a * c›)
  also have "… = (inverse a * a) * c" by (simp only: assoc)
  also have "… = 1 * c"               by (simp only: left_inverse)
  also have "… = c"                   by (simp only: left_neutral)
  finally show "b = c"                 by this
qed

(* 2ª demostración *)

lemma
  assumes "a * b = a * c"
  shows   "b = c"
proof -
  have "b = 1 * b"                     by simp
  also have "… = (inverse a * a) * b" by simp
  also have "… = inverse a * (a * b)" by (simp only: assoc)
  also have "… = inverse a * (a * c)" using ‹a * b = a * c› by simp
  also have "… = (inverse a * a) * c" by (simp only: assoc)
  also have "… = 1 * c"               by simp
  finally show "b = c"                 by simp
qed

(* 3ª demostración *)

lemma
  assumes "a * b = a * c"
  shows   "b = c"
proof -
  have "b = (inverse a * a) * b"      by simp
  also have "… = inverse a * (a * b)" by (simp only: assoc)
  also have "… = inverse a * (a * c)" using ‹a * b = a * c› by simp
  also have "… = (inverse a * a) * c" by (simp only: assoc)
  finally show "b = c"                by simp
qed

(* 4ª demostración *)

lemma
  assumes "a * b = a * c"
  shows   "b = c"
proof -
  have "inverse a * (a * b) = inverse a * (a * c)"
    by (simp only: ‹a * b = a * c›)
  then have "(inverse a * a) * b = (inverse a * a) * c"
    by (simp only: assoc)
  then have "1 * b = 1 * c"
    by (simp only: left_inverse)
  then show "b = c"
    by (simp only: left_neutral)
qed

(* 5ª demostración *)

lemma
  assumes "a * b = a * c"
  shows   "b = c"
proof -
  have "inverse a * (a * b) = inverse a * (a * c)"
    by (simp only: ‹a * b = a * c›)
  then have "(inverse a * a) * b = (inverse a * a) * c"
    by (simp only: assoc)
  then have "1 * b = 1 * c"
    by (simp only: left_inverse)
  then show "b = c"
    by (simp only: left_neutral)
qed

(* 6ª demostración *)

lemma
  assumes "a * b = a * c"
  shows   "b = c"
proof -
  have "inverse a * (a * b) = inverse a * (a * c)"
    using ‹a * b = a * c› by simp
  then have "(inverse a * a) * b = (inverse a * a) * c"
    by (simp only: assoc)
  then have "1 * b = 1 * c"
    by simp
  then show "b = c"
    by simp
qed

(* 7ª demostración *)

lemma
  assumes "a * b = a * c"
  shows   "b = c"
  using assms
  by (simp only: left_cancel)

end

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
