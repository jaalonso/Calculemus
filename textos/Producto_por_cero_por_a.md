---
Título: Si R es un anillo y a ∈ R, entonces 0 * a = 0.
Autor:  José A. Alonso
---

Demostrar que si R es un anillo y a ∈ R, entonces
<pre lang="text">
0 * a = 0.
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import algebra.ring

variables {R : Type*} [ring R]
variable (a : R)

example : 0 * a = 0 :=
sorry
</pre>

<!-- more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import algebra.ring

variables {R : Type*} [ring R]
variable (a : R)

-- 1ª demostración
-- ===============

example : 0 * a = 0 :=
begin
  have h : 0 * a + 0 * a = 0 * a + 0,
    calc 0 * a + 0 * a
         = (0 + 0) * a : (add_mul 0 0 a).symm
     ... = 0 * a       : congr_arg (λ x, x * a) (add_zero 0)
     ... = 0 * a + 0   : self_eq_add_right.mpr rfl,
  rw add_left_cancel h
end

-- 2ª demostración
-- ===============

example : 0 * a = 0 :=
begin
  have h : 0 * a + 0 * a = 0 * a + 0,
    calc 0 * a + 0 * a
         = (0 + 0) * a : by rw add_mul
     ... = 0 * a       : by rw add_zero
     ... = 0 * a + 0   : by rw add_zero,
  rw add_left_cancel h
end

-- 3ª demostración
-- ===============

example : 0 * a = 0 :=
begin
  have h : 0 * a + 0 * a = 0 * a + 0,
  { rw [←add_mul, add_zero, add_zero] },
  rw add_left_cancel h
end

-- 4ª demostración
-- ===============

example : 0 * a = 0 :=
begin
  have h : 0 * a + 0 * a = 0 * a + 0,
    calc 0 * a + 0 * a
         = (0 + 0) * a : by simp
     ... = 0 * a       : by simp
     ... = 0 * a + 0   : by simp,
  simp,
end

-- 5ª demostración
-- ===============

example : 0 * a = 0 :=
by simp
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Producto_por_cero_por_a.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.
