---
Título: Si G es un grupo y a ∈ G, entonces a * 1 = a.
Autor:  José A. Alonso
---

Demostrar que si G es un grupo y a ∈ G, entonces
<pre lang="text">
a * 1 = a
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import algebra.group
variables {G : Type*} [group G]
variables a : G

example : a * 1 = a :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import algebra.group
variables {G : Type*} [group G]
variables a : G

-- 1ª demostración
-- ===============

example : a * 1 = a :=
calc
  a * 1 = a * (a⁻¹ * a) : congr_arg (λ x, a * x) (mul_left_inv a).symm
    ... = (a * a⁻¹) * a : (mul_assoc a a⁻¹ a).symm
    ... = 1 * a         : congr_arg (λ x, x* a) (mul_right_inv a)
    ... = a             : one_mul a

-- 2ª demostración
-- ===============

example : a * 1 = a :=
calc
  a * 1 = a * (a⁻¹ * a) : by rw mul_left_inv
    ... = (a * a⁻¹) * a : by rw mul_assoc
    ... = 1 * a         : by rw mul_right_inv
    ... = a             : by rw one_mul

-- 3ª demostración
-- ===============

example : a * 1 = a :=
calc
  a * 1 = a * (a⁻¹ * a) : by simp
    ... = (a * a⁻¹) * a : by simp
    ... = 1 * a         : by simp
    ... = a             : by simp

-- 3ª demostración
-- ===============

example : a * 1 = a :=
by simp

-- 4ª demostración
-- ===============

example : a * 1 = a :=
-- by library_search
mul_one a
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Neutro_derecha.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.
