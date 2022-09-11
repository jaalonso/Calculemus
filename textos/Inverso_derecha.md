---
Título: Si G es un grupo y a ∈ G, entonces a * a⁻¹ = 1
Autor:  José A. Alonso
---

En Lean, se declara que G es un grupo mediante la expresión
<pre lang="text">
   variables {G : Type*} [group G]
</pre>
y, como consecuencia, se tiene los siguientes axiomas
<pre lang="text">
   mul_assoc    : ∀ a b c : G, a * b * c = a * (b * c)
   one_mul      : ∀ a : G,     1 * a = a
   mul_left_inv : ∀ a : G,     a⁻¹ * a = 1
</pre>

Demostrar que si G es un grupo y a ∈ G, entonces
<pre lang="text">
a * a⁻¹ = 1
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import algebra.group
variables {G : Type*} [group G]
variables (a b : G)

example : a * a⁻¹ = 1 :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import algebra.group
variables {G : Type*} [group G]
variables (a b : G)

-- 1ª demostración
-- ===============

example : a * a⁻¹ = 1 :=
calc a * a⁻¹
     = 1 * (a * a⁻¹)
       : (one_mul (a * a⁻¹)).symm
 ... = (1 * a) * a⁻¹
       : (mul_assoc 1 a  a⁻¹).symm
 ... = (((a⁻¹)⁻¹ * a⁻¹)  * a) * a⁻¹
       : congr_arg (λ x, (x * a) * a⁻¹) (mul_left_inv a⁻¹).symm
 ... = ((a⁻¹)⁻¹ * (a⁻¹  * a)) * a⁻¹
       : congr_fun (congr_arg has_mul.mul (mul_assoc a⁻¹⁻¹ a⁻¹ a)) a⁻¹
 ... = ((a⁻¹)⁻¹ * 1) * a⁻¹
       : congr_arg (λ x, (a⁻¹⁻¹ * x) * a⁻¹) (mul_left_inv a)
 ... = (a⁻¹)⁻¹ * (1 * a⁻¹)
       : mul_assoc (a⁻¹)⁻¹ 1 a⁻¹
 ... = (a⁻¹)⁻¹ * a⁻¹
       : congr_arg (λ x, (a⁻¹)⁻¹ * x) (one_mul a⁻¹)
 ... = 1
       : mul_left_inv a⁻¹

-- 2ª demostración
-- ===============

example : a * a⁻¹ = 1 :=
calc
  a * a⁻¹ = 1 * (a * a⁻¹)                : by rw one_mul
      ... = (1 * a) * a⁻¹                : by rw mul_assoc
      ... = (((a⁻¹)⁻¹ * a⁻¹)  * a) * a⁻¹ : by rw mul_left_inv
      ... = ((a⁻¹)⁻¹ * (a⁻¹  * a)) * a⁻¹ : by rw ← mul_assoc
      ... = ((a⁻¹)⁻¹ * 1) * a⁻¹          : by rw mul_left_inv
      ... = (a⁻¹)⁻¹ * (1 * a⁻¹)          : by rw mul_assoc
      ... = (a⁻¹)⁻¹ * a⁻¹                : by rw one_mul
      ... = 1                            : by rw mul_left_inv

-- 3ª demostración
-- ===============

example : a * a⁻¹ = 1 :=
calc
  a * a⁻¹ = 1 * (a * a⁻¹)                : by simp
      ... = (1 * a) * a⁻¹                : by simp
      ... = (((a⁻¹)⁻¹ * a⁻¹)  * a) * a⁻¹ : by simp
      ... = ((a⁻¹)⁻¹ * (a⁻¹  * a)) * a⁻¹ : by simp
      ... = ((a⁻¹)⁻¹ * 1) * a⁻¹          : by simp
      ... = (a⁻¹)⁻¹ * (1 * a⁻¹)          : by simp
      ... = (a⁻¹)⁻¹ * a⁻¹                : by simp
      ... = 1                            : by simp

-- 4ª demostración
-- ===============

example : a * a⁻¹ = 1 :=
by simp

-- 5ª demostración
-- ===============

example : a * a⁻¹ = 1 :=
-- by library_search
mul_inv_self a
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Inverso_derecha.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 14.
