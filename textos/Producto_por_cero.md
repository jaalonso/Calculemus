---
Título: Si R es un anillo y a ∈ R, entonces a * 0 = 0
Autor:  José A. Alonso
---

Demostrar que Si R es un anillo y a ∈ R, entonces
<pre lang="text">
a * 0 = 0
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import algebra.ring

variables {R : Type*} [ring R]
variable  a : R

example : a * 0 = 0 :=
sorry
</pre>

<b>Soluciones con Lean</b>

<pre lang="lean">
import algebra.ring

variables {R : Type*} [ring R]
variable  a : R

-- 1ª demostración
-- ===============

example : a * 0 = 0 :=
begin
  have h : a * 0 + a * 0 = a * 0 + 0,
    calc a * 0 + a * 0
         = a * (0 + 0) : (mul_add a 0 0).symm
     ... = a * 0       : congr_arg (λ x, a * x) (add_zero 0)
     ... = a * 0 + 0   : (add_zero (a * 0)).symm,
  rw add_left_cancel h
end

-- 2ª demostración
-- ===============

example : a * 0 = 0 :=
begin
  have h : a * 0 + a * 0 = a * 0 + 0,
    calc a * 0 + a * 0
         = a * (0 + 0) : by rw ←mul_add
     ... = a * 0       : by rw add_zero
     ... = a * 0 + 0   : by rw add_zero,
  rw add_left_cancel h
end

-- 3ª demostración
-- ===============

example : a * 0 = 0 :=
begin
  have h : a * 0 + a * 0 = a * 0 + 0,
  { rw [←mul_add, add_zero, add_zero] },
  rw add_left_cancel h
end

-- 4ª demostración
-- ===============

example : a * 0 = 0 :=
begin
  have h : a * 0 + a * 0 = a * 0 + 0,
    calc a * 0 + a * 0
         = a * (0 + 0) : by simp
     ... = a * 0       : by simp
     ... = a * 0 + 0   : by simp,
  simp,
end

-- 5ª demostración
-- ===============

example : a * 0 = 0 :=
by simp

-- 6ª demostración
-- ===============

example : a * 0 = 0 :=
-- by library_search
mul_zero a
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Producto_por_cero.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 16.
