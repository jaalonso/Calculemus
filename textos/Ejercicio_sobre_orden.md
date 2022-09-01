---
Título: Si a, b, c, d, e ∈ ℝ tales que a ≤ b, b < c, c ≤ d, d < e, entonces a < e
Autor:  José A. Alonso
---

Demostrar que si a, b, c, d, e ∈ ℝ tales que
<pre lang="text">
a ≤ b
b < c
c ≤ d
d < e
</pre>
entonces
<pre lang="text">
a < e
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic

variables a b c d e : ℝ

example
  (h₀ : a ≤ b)
  (h₁ : b < c)
  (h₂ : c ≤ d)
  (h₃ : d < e) :
  a < e :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import data.real.basic

variables a b c d e : ℝ

-- 1ª demostración
-- ===============

example
  (h₀ : a ≤ b)
  (h₁ : b < c)
  (h₂ : c ≤ d)
  (h₃ : d < e) :
  a < e :=
calc a ≤ b : h₀
   ... < c : h₁
   ... ≤ d : h₂
   ... < e : h₃

-- 2ª demostración
-- ===============

example
  (h₀ : a ≤ b)
  (h₁ : b < c)
  (h₂ : c ≤ d)
  (h₃ : d < e) :
  a < e :=
begin
  apply lt_of_le_of_lt h₀,
  apply lt_trans h₁,
  apply lt_of_le_of_lt h₂,
  exact h₃,
end

-- 3ª demostración
-- ===============

example
  (h₀ : a ≤ b)
  (h₁ : b < c)
  (h₂ : c ≤ d)
  (h₃ : d < e) :
  a < e :=
by finish
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Ejercicio_sobre_orden.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.
