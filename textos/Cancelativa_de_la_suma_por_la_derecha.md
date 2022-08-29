---
Título: Si R es un anillo y a, b, c ∈ R tales que a + b = c + b, entonces a = c.
Autor:  José A. Alonso
---

Demostrar que si R es un anillo y a, b, c ∈ R tales que
<pre lang="text">
   a + b = c + b
</pre>
entonces
<pre lang="text">
   a = c
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import algebra.ring
import tactic

variables {R : Type*} [ring R]
variables {a b c : R}

example
  (h : a + b = c + b)
  : a = c :=
sorry
</pre>

<b>Soluciones con Lean</b>

<pre lang="lean">
import algebra.ring
import tactic

variables {R : Type*} [ring R]
variables {a b c : R}

-- 1ª demostración
-- ===============

example
  (h : a + b = c + b)
  : a = c :=
calc a
     = a + 0        : by rw add_zero
 ... = a + (b + -b) : by rw add_right_neg
 ... = (a + b) + -b : by rw add_assoc
 ... = (c + b) + -b : by rw h
 ... = c + (b + -b) : by rw ← add_assoc
 ... = c + 0        : by rw ← add_right_neg
 ... = c            : by rw add_zero

-- 2ª demostración
-- ===============

example
  (h : a + b = c + b)
  : a = c :=
calc a
     = a + 0        : by simp
 ... = a + (b + -b) : by simp
 ... = (a + b) + -b : by simp
 ... = (c + b) + -b : by rw h
 ... = c + (b + -b) : by simp
 ... = c + 0        : by simp
 ... = c            : by simp

-- 3ª demostración
-- ===============

lemma aux : (a + b) + -b = a :=
by finish

example
  (h : a + b = c + b)
  : a = c :=
calc a
     = (a + b) + -b : aux.symm
 ... = (c + b) + -b : congr_arg (λ x, x + -b) h
 ... = c            : aux

-- 4ª demostración
-- ===============

example
  (h : a + b = c + b)
  : a = c :=
by finish
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Cancelativa_de_la_suma_por_la_derecha.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.
