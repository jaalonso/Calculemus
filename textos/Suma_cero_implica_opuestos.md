---
Título: Si R es un anillo y a,b∈R tales que a+b=0, entonces -a=b.
Autor:  José A. Alonso
---

Demostrar que Si R es un anillo y a, b ∈ R tales que
<pre lang="text">
a + b = 0
</pre>
entonces
<pre lang="text">
-a = b
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import algebra.ring

variables {R : Type*} [ring R]
variables {a b : R}

example
  (h : a + b = 0)
  : -a = b :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import algebra.ring

variables {R : Type*} [ring R]
variables {a b : R}

-- 1ª demostración
-- ===============

example
  (h : a + b = 0)
  : -a = b :=
calc
  -a  = -a + 0       : (add_zero (-a)).symm
  ... = -a + (a + b) : congr_arg (λ x, -a +x) h.symm
  ... = b            : neg_add_cancel_left a b

-- 2ª demostración
-- ===============

example
  (h : a + b = 0)
  : -a = b :=
calc
  -a  = -a + 0       : by rw add_zero
  ... = -a + (a + b) : by rw h
  ... = b            : by rw neg_add_cancel_left

-- 3ª demostración
-- ===============

example
  (h : a + b = 0)
  : -a = b :=
calc
  -a  = -a + 0       : by simp
  ... = -a + (a + b) : by simp [h]
  ... = b            : by simp

-- 4ª demostración
-- ===============

example
  (h : a + b = 0)
  : -a = b :=
-- by library_search
add_eq_zero_iff_neg_eq.mp h
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Suma_cero_implica_opuestos.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 16.
