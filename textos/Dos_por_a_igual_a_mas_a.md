---
Título: Si R es un anillo y a ∈ R, entonces 2 * a = a + a.
Autor:  José A. Alonso
---

Demostrar que si R es un anillo y a ∈ R, entonces
<pre lang="text">
2 * a = a + a.
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import algebra.ring

variables {R : Type*} [ring R]
variables a : R

example : 2 * a = a + a :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import algebra.ring

variables {R : Type*} [ring R]
variables a : R

-- 1ª demostración
-- ===============

example : 2 * a = a + a :=
calc
  2 * a = (1 + 1) * a   : congr_fun (congr_arg has_mul.mul one_add_one_eq_two.symm) a
  ...   = 1 * a + 1 * a : add_mul 1 1 a
  ...   = a + 1 * a     : congr_arg (λ x, x + 1 * a) (one_mul a)
  ...   = a + a         : congr_arg (λ x, a + x) (one_mul a)

-- 2ª demostración
-- ===============

example : 2 * a = a + a :=
calc
  2 * a = (1 + 1) * a   : by rw one_add_one_eq_two
  ...   = 1 * a + 1 * a : by rw add_mul
  ...   = a + a         : by rw one_mul

-- 3ª demostración
-- ===============

example : 2 * a = a + a :=
by rw [one_add_one_eq_two.symm, add_mul, one_mul]

-- 4ª demostración
-- ===============

example : 2 * a = a + a :=
calc
  2 * a = (1 + 1)  * a  : rfl
  ...   = 1 * a + 1 * a : by simp [add_mul]
  ...   = a + a         : by simp

-- 5ª demostración
-- ===============

example : 2 * a = a + a :=
-- by library_search
two_mul a
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Dos_por_a_igual_a_mas_a.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.
