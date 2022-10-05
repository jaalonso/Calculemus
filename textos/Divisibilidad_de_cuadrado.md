---
Título: Si x ∈ ℕ, entonces x ∣ x²
Autor:  José A. Alonso
---

Demostrar que si x ∈ ℕ, entonces
<pre lang="text">
x ∣ x^2
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.nat.pow
variable x : ℕ

example : x ∣ x^2 :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import data.nat.pow
variable x : ℕ

-- 1ª demostración
-- ===============

example : x ∣ x^2 :=
begin
  rw pow_two,
  apply dvd_mul_right,
end

-- 2ª demostración
-- ===============

example : x ∣ x^2 :=
by apply dvd_mul_right
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Divisibilidad_de_cuadrado.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 20.
