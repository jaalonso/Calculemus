---
Título: Si R es un anillo, entonces -0 = 0
Autor:  José A. Alonso
---

Demostrar que si R es un anillo, entonces
<pre lang="text">
-0 = 0
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import algebra.ring

variables {R : Type*} [ring R]

example : (-0 : R) = 0 :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import algebra.ring

variables {R : Type*} [ring R]

-- 1ª demostración
-- ===============

example : (-0 : R) = 0 :=
begin
  have h : 0 - 0 = (-0 : R) := zero_sub 0,
  calc (-0 : R)
       = 0 - 0    : h.symm
   ... = -(0 - 0) : (neg_sub (0 : R) 0).symm
   ... = -(-0)    : congr_arg (λ x, -x) h
   ... = 0        : neg_neg 0
end

-- 2ª demostración
-- ===============

example : (-0 : R) = 0 :=
begin
  have h : 0 - 0 = (-0 : R) := by rw zero_sub,
  calc (-0 : R)
       = 0 - 0    : by rw h
   ... = -(0 - 0) : by rw neg_sub
   ... = -(-0)    : by {congr; rw h}
   ... = 0        : by rw neg_neg
end

-- 3ª demostración
-- ===============

example : (-0 : R) = 0 :=
by simpa only [zero_sub, neg_neg] using (neg_sub (0 : R) 0).symm

-- 4ª demostración
-- ===============

example : (-0 : R) = 0 :=
neg_zero

-- 5ª demostración
-- ===============

example : (-0 : R) = 0 :=
by simp

-- 6ª demostración
-- ===============

example : (-0 : R) = 0 :=
begin
  apply neg_eq_of_add_eq_zero_right,
  rw add_zero,
end

-- 7ª demostración
-- ===============

example : (-0 : R) = 0 :=
neg_eq_of_add_eq_zero_right (add_zero 0)
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Opuesto_de_cero.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 12.
