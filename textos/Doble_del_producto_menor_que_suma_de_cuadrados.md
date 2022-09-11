---
Título: Si a, b ∈ ℝ, entonces 2ab ≤ a² + b²
Autor:  José A. Alonso
---

Demostrar que si a, b ∈ ℝ, entonces 2ab ≤ a² + b²

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic
import tactic

variables a b : ℝ

example : 2*a*b ≤ a^2 + b^2 :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import data.real.basic
import tactic

variables a b : ℝ

-- 1ª demostración
example : 2*a*b ≤ a^2 + b^2 :=
begin
  have : 0 ≤ (a - b)^2 := sq_nonneg (a - b),
  have : 0 ≤ a^2 - 2*a*b + b^2, by linarith,
  show 2*a*b ≤ a^2 + b^2, by linarith,
end

-- 2ª demostración
example : 2*a*b ≤ a^2 + b^2 :=
begin
  have h : 0 ≤ a^2 - 2*a*b + b^2,
  { calc a^2 - 2*a*b + b^2
        = (a - b)^2                   : by ring
    ... ≥ 0                           : by apply pow_two_nonneg },
  calc 2*a*b
       = 2*a*b + 0                   : by ring
   ... ≤ 2*a*b + (a^2 - 2*a*b + b^2) : add_le_add (le_refl _) h
   ... = a^2 + b^2                   : by ring
end

-- 3ª demostración
example : 2*a*b ≤ a^2 + b^2 :=
begin
  have : 0 ≤ a^2 - 2*a*b + b^2,
  { calc a^2 - 2*a*b + b^2
         = (a - b)^2       : by ring
     ... ≥ 0               : by apply pow_two_nonneg },
  linarith,
end

-- 4ª demostración
example : 2*a*b ≤ a^2 + b^2 :=
-- by library_search
two_mul_le_add_sq a b
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Doble_del_producto_menor_que_suma_de_cuadrados.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.
