---
Título: Si x, y, z ∈ ℕ, entonces x ∣ y * x * z
Autor:  José A. Alonso
---

Demostrar que si x, y, z ∈ N, entonces
<pre lang="text">
   x ∣ y * x * z
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.nat.basic
variables x y z : ℕ

example : x ∣ y * x * z :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import data.nat.basic
variables x y z : ℕ

-- 1ª demostración
-- ===============

example : x ∣ y * x * z :=
begin
  have h1 : x ∣ y * x,
    { exact dvd_mul_left x y },
  have h2 : (y * x) ∣ (y * x * z),
    { exact dvd.intro z rfl},
  show x ∣ y * x * z,
    { exact dvd_trans h1 h2},
end

-- 2ª demostración
-- ===============

example : x ∣ y * x * z :=
dvd_trans (dvd_mul_left x y) (dvd.intro z rfl)

-- 3ª demostración
-- ===============

example : x ∣ y * x * z :=
begin
  apply dvd_mul_of_dvd_left,
  apply dvd_mul_left
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Divisivilidad_productos.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 20.
