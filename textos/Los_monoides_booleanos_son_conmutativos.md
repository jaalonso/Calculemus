---
Título: Los monoides booleanos son conmutativos
Autor:  José A. Alonso
---

Un [monoide](https://en.wikipedia.org/wiki/Monoid) es un conjunto junto con una operación binaria que es asociativa y tiene elemento neutro.

Un monoide M es booleano si
<pre lang="text">
   ∀ x ∈ M, x * x = 1
</pre>
y es conmutativo si
<pre lang="text">
   ∀ x y ∈ M, x * y = y * x
</pre>

En Lean, está definida la clase de los monoides (como `monoid`) y sus propiedades características son
<pre lang="text">
   mul_assoc : (a * b) * c = a * (b * c)
   one_mul :   1 * a = a
   mul_one :   a * 1 = a
</pre>

Demostrar que los monoides booleanos son conmutativos.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import algebra.group.basic

universe  u
variables {M : Type u} [monoid M]

example
  (h : ∀ x : M, x * x = 1)
  : ∀ x y : M, x * y = y * x :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import algebra.group.basic

universe  u
variables {M : Type u} [monoid M]

-- 1ª demostración
-- ===============

example
  (h : ∀ x : M, x * x = 1)
  : ∀ x y : M, x * y = y * x :=
begin
  intros a b,
  calc a * b
       = (a * b) * 1                   : (mul_one (a * b)).symm
   ... = (a * b) * (a * a)             : congr_arg ((*) (a*b)) (h a).symm
   ... = ((a * b) * a) * a             : (mul_assoc (a*b) a a).symm
   ... = (a * (b * a)) * a             : congr_arg (* a) (mul_assoc a b a)
   ... = (1 * (a * (b * a))) * a       : congr_arg (* a) (one_mul (a*(b*a))).symm
   ... = ((b * b) * (a * (b * a))) * a : congr_arg (* a) (congr_arg (* (a*(b*a))) (h b).symm)
   ... = (b * (b * (a * (b * a)))) * a : congr_arg (* a) (mul_assoc b b (a*(b*a)))
   ... = (b * ((b * a) * (b * a))) * a : congr_arg (* a) (congr_arg ((*) b) (mul_assoc b a (b*a)).symm)
   ... = (b * 1) * a                   : congr_arg (* a) (congr_arg ((*) b) (h (b*a)))
   ... = b * a                         : congr_arg (* a) (mul_one b),
end

-- 2ª demostración
-- ===============

example
  (h : ∀ x : M, x * x = 1)
  : ∀ x y : M, x * y = y * x :=
begin
  intros a b,
  calc a * b
       = (a * b) * 1                   : by simp only [mul_one]
   ... = (a * b) * (a * a)             : by simp only [h]
   ... = ((a * b) * a) * a             : by simp only [mul_assoc]
   ... = (a * (b * a)) * a             : by simp only [mul_assoc]
   ... = (1 * (a * (b * a))) * a       : by simp only [one_mul]
   ... = ((b * b) * (a * (b * a))) * a : by simp only [h]
   ... = (b * (b * (a * (b * a)))) * a : by simp only [mul_assoc]
   ... = (b * ((b * a) * (b * a))) * a : by simp only [mul_assoc]
   ... = (b * 1) * a                   : by simp only [h]
   ... = b * a                         : by simp only [mul_one]
end

-- 3ª demostración
-- ===============

example
  (h : ∀ x : M, x * x = 1)
  : ∀ x y : M, x * y = y * x :=
begin
  intros a b,
  calc a * b
       = (a * b) * 1                   : by simp
   ... = (a * b) * (a * a)             : by simp [h]
   ... = ((a * b) * a) * a             : by simp [mul_assoc]
   ... = (a * (b * a)) * a             : by simp [mul_assoc]
   ... = (1 * (a * (b * a))) * a       : by simp
   ... = ((b * b) * (a * (b * a))) * a : by simp [h]
   ... = (b * (b * (a * (b * a)))) * a : by simp [mul_assoc]
   ... = (b * ((b * a) * (b * a))) * a : by simp [mul_assoc]
   ... = (b * 1) * a                   : by simp [h]
   ... = b * a                         : by simp,
end

-- 4ª demostración
-- ===============

example
  (h : ∀ x : M, x * x = 1)
  : ∀ x y : M, x * y = y * x :=
begin
  intros a b,
  calc a * b
       = (a * b) * (a * a)             : by simp [h]
   ... = (1 * (a * (b * a))) * a       : by simp [mul_assoc]
   ... = ((b * b) * (a * (b * a))) * a : by simp [h]
   ... = (b * ((b * a) * (b * a))) * a : by simp [mul_assoc]
   ... = b * a                         : by simp [h],
end

-- 5ª demostración
-- ===============

example
  (h : ∀ x : M, x * x = 1)
  : ∀ x y : M, x * y = y * x :=
begin
  intros a b,
  calc a * b
       = ((b * b) * (a * (b * a))) * a : by simp [h, mul_assoc]
   ... = (b * ((b * a) * (b * a))) * a : by simp [mul_assoc]
   ... = b * a                         : by simp [h],
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://www.cs.us.es/~jalonso/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Los_monoides_booleanos_son_conmutativos.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Los_monoides_booleanos_son_conmutativos
imports Main
begin

context monoid
begin

(* 1ª demostración *)

lemma
  assumes "∀ x. x * x = 1"
  shows   "∀ x y. x * y = y * x"
proof (rule allI)+
  fix a b
  have "a * b = (a * b) * 1"
    by (simp only: right_neutral)
  also have "… = (a * b) * (a * a)"
    by (simp only: assms)
  also have "… = ((a * b) * a) * a"
    by (simp only: assoc)
  also have "… = (a * (b * a)) * a"
    by (simp only: assoc)
  also have "… = (1 * (a * (b * a))) * a"
    by (simp only: left_neutral)
  also have "… = ((b * b) * (a * (b * a))) * a"
    by (simp only: assms)
  also have "… = (b * (b * (a * (b * a)))) * a"
    by (simp only: assoc)
  also have "… = (b * ((b * a) * (b * a))) * a"
    by (simp only: assoc)
  also have "… = (b * 1) * a"
    by (simp only: assms)
  also have "… = b * a"
    by (simp only: right_neutral)
  finally show "a * b = b * a"
    by this
qed

(* 2ª demostración *)

lemma
  assumes "∀ x. x * x = 1"
  shows   "∀ x y. x * y = y * x"
proof (rule allI)+
  fix a b
  have "a * b = (a * b) * 1"                    by simp
  also have "… = (a * b) * (a * a)"             by (simp add: assms)
  also have "… = ((a * b) * a) * a"             by (simp add: assoc)
  also have "… = (a * (b * a)) * a"             by (simp add: assoc)
  also have "… = (1 * (a * (b * a))) * a"       by simp
  also have "… = ((b * b) * (a * (b * a))) * a" by (simp add: assms)
  also have "… = (b * (b * (a * (b * a)))) * a" by (simp add: assoc)
  also have "… = (b * ((b * a) * (b * a))) * a" by (simp add: assoc)
  also have "… = (b * 1) * a"                   by (simp add: assms)
  also have "… = b * a"                         by simp
  finally show "a * b = b * a"                  by this
qed

(* 3ª demostración *)

lemma
  assumes "∀ x. x * x = 1"
  shows   "∀ x y. x * y = y * x"
proof (rule allI)+
  fix a b
  have "a * b = (a * b) * (a * a)"              by (simp add: assms)
  also have "… = (a * (b * a)) * a"             by (simp add: assoc)
  also have "… = ((b * b) * (a * (b * a))) * a" by (simp add: assms)
  also have "… = (b * ((b * a) * (b * a))) * a" by (simp add: assoc)
  also have "… = (b * 1) * a"                   by (simp add: assms)
  finally show "a * b = b * a"                  by simp
qed

(* 4ª demostración *)

lemma
  assumes "∀ x. x * x = 1"
  shows   "∀ x y. x * y = y * x"
  by (metis assms assoc right_neutral)

end

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
