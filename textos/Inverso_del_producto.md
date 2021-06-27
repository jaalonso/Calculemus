---
Título: Inverso del producto
Autor:  José A. Alonso
---

Sea G un grupo y a, b ∈ G. Entonces,
<pre lang="text">
   (a * b)⁻¹ = b⁻¹ * a⁻¹
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import algebra.group.basic

universe  u
variables {G : Type u} [group G]
variables {a b : G}

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
begin
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

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
begin
  apply inv_eq_of_mul_eq_one,
  calc a * b * (b⁻¹ * a⁻¹)
       = ((a * b) * b⁻¹) * a⁻¹ : (mul_assoc _ _ _).symm
   ... = (a * (b * b⁻¹)) * a⁻¹ : congr_arg (* a⁻¹) (mul_assoc a _ _)
   ... = (a * 1) * a⁻¹         : congr_arg2 _ (congr_arg _ (mul_inv_self b)) rfl
   ... = a * a⁻¹               : congr_arg (* a⁻¹) (mul_one a)
   ... = 1                     : mul_inv_self a
end

-- 2ª demostración
-- ===============

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
begin
  apply inv_eq_of_mul_eq_one,
  calc a * b * (b⁻¹ * a⁻¹)
       = ((a * b) * b⁻¹) * a⁻¹ : by simp only [mul_assoc]
   ... = (a * (b * b⁻¹)) * a⁻¹ : by simp only [mul_assoc]
   ... = (a * 1) * a⁻¹         : by simp only [mul_inv_self]
   ... = a * a⁻¹               : by simp only [mul_one]
   ... = 1                     : by simp only [mul_inv_self]
end

-- 3ª demostración
-- ===============

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
begin
  apply inv_eq_of_mul_eq_one,
  calc a * b * (b⁻¹ * a⁻¹)
       = ((a * b) * b⁻¹) * a⁻¹ : by simp [mul_assoc]
   ... = (a * (b * b⁻¹)) * a⁻¹ : by simp
   ... = (a * 1) * a⁻¹         : by simp
   ... = a * a⁻¹               : by simp
   ... = 1                     : by simp,
end

-- 4ª demostración
-- ===============

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
mul_inv_rev a b

-- 5ª demostración
-- ===============

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
by simp
</pre>

Se puede interactuar con la prueba anterior en <a href="https://www.cs.us.es/~jalonso/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Inverso_del_producto.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Inverso_del_producto
imports Main
begin

context group
begin

(* 1ª demostración *)

lemma "inverse (a * b) = inverse b * inverse a"
proof (rule inverse_unique)
  have "(a * b) * (inverse b * inverse a) =
        ((a * b) * inverse b) * inverse a"
    by (simp only: assoc)
  also have "… = (a * (b * inverse b)) * inverse a"
    by (simp only: assoc)
  also have "… = (a * 1) * inverse a"
    by (simp only: right_inverse)
  also have "… = a * inverse a"
    by (simp only: right_neutral)
  also have "… = 1"
    by (simp only: right_inverse)
  finally show "a * b * (inverse b * inverse a) = 1"
    by this
qed

(* 2ª demostración *)

lemma "inverse (a * b) = inverse b * inverse a"
proof (rule inverse_unique)
  have "(a * b) * (inverse b * inverse a) =
        ((a * b) * inverse b) * inverse a"
    by (simp only: assoc)
  also have "… = (a * (b * inverse b)) * inverse a"
    by (simp only: assoc)
  also have "… = (a * 1) * inverse a"
    by simp
  also have "… = a * inverse a"
    by simp
  also have "… = 1"
    by simp
  finally show "a * b * (inverse b * inverse a) = 1"
    .
qed

(* 3ª demostración *)

lemma "inverse (a * b) = inverse b * inverse a"
proof (rule inverse_unique)
  have "a * b * (inverse b * inverse a) =
        a * (b * inverse b) * inverse a"
    by (simp only: assoc)
  also have "… = 1"
    by simp
  finally show "a * b * (inverse b * inverse a) = 1" .
qed

(* 4ª demostración *)

lemma "inverse (a * b) = inverse b * inverse a"
  by (simp only: inverse_distrib_swap)

(* ?ª demostración *)

end

end

</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

<h4>Referencia</h4>

Propiedad 3.19 del libro [Abstract algebra: Theory and applications](http://abstract.ups.edu/download/aata-20200730.pdf#page=49) de Thomas W. Judson.
