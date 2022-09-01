---
Título: Si G es un grupo y a, b ∈ G tales que b * a = 1, entonces a⁻¹ = b
Autor:  José A. Alonso
---

Demostrar que si G es un grupo y a, b ∈ G tales que
<pre lang="text">
b * a = 1
</pre>
entonces
<pre lang="text">
a⁻¹ = b
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import algebra.group
variables {G : Type*} [group G]
variables a b : G

example
  (h : b * a = 1)
  : a⁻¹ = b :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import algebra.group
variables {G : Type*} [group G]
variables a b : G

-- 1ª demostración
-- ===============

example
  (h : b * a = 1)
  : a⁻¹ = b :=
calc
  a⁻¹ =  1 * a⁻¹       : (one_mul a⁻¹).symm
  ... =  (b * a) * a⁻¹ : congr_arg (λ x, x * a⁻¹) h.symm
  ... =  b * (a * a⁻¹) : mul_assoc b a a⁻¹
  ... =  b * 1         : congr_arg (λ x, b * x) (mul_right_inv a)
  ... =  b             : mul_one b

-- 2ª demostración
-- ===============

example
  (h : b * a = 1)
  : a⁻¹ = b :=
calc
  a⁻¹ =  1 * a⁻¹       : by rw one_mul
  ... =  (b * a) * a⁻¹ : by rw h
  ... =  b * (a * a⁻¹) : by rw mul_assoc
  ... =  b * 1         : by rw mul_right_inv
  ... =  b             : by rw mul_one

-- 3ª demostración
-- ===============

example
  (h : b * a = 1)
  : a⁻¹ = b :=
calc
  a⁻¹ =  1 * a⁻¹       : by simp
  ... =  (b * a) * a⁻¹ : by simp [h]
  ... =  b * (a * a⁻¹) : by simp
  ... =  b * 1         : by simp
  ... =  b             : by simp

-- 4ª demostración
-- ===============

example
  (h : b * a = 1)
  : a⁻¹ = b :=
-- by library_search
inv_eq_of_mul_eq_one_left h
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/CS_inverso_izquierda.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.
