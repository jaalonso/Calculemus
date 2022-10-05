---
Título: Si w, x, y, z ∈ ℕ tales que x ∣ w, entonces x ∣ yxz + x² + w²
Autor:  José A. Alonso
---

Demostrar que Si w, x, y, z ∈ ℕ tales que x ∣ w, entonces x ∣ yxz + x² + w²

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.nat.gcd

variables w x y z : ℕ

example
  (h : x ∣ w)
  : x ∣ y * (x * z) + x^2 + w^2 :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import data.nat.gcd

variables w x y z : ℕ

-- 1ª demostración
-- ===============

example
  (h : x ∣ w)
  : x ∣ y * (x * z) + x^2 + w^2 :=
begin
  have h1 : x ∣ x * z,
    by exact dvd.intro z rfl,
  have h2 : x ∣ y * (x * z),
    by exact dvd_mul_of_dvd_right h1 y,
  have h3 : x ∣ x^2,
    by apply dvd_mul_right,
  have h4 : x ∣ w * w,
    by exact dvd_mul_of_dvd_left h w,
  have h5 : x ∣ w^2,
    by rwa ← pow_two w at h4,
  have h6 : x ∣ y * (x * z) + x^2,
    by exact dvd_add h2 h3,
  show x ∣ y * (x * z) + x^2 + w^2,
    by exact dvd_add h6 h5,
end

-- 2ª demostración
-- ===============

example
  (h : x ∣ w)
  : x ∣ y * (x * z) + x^2 + w^2 :=
begin
  apply dvd_add,
  { apply dvd_add,
    { apply dvd_mul_of_dvd_right,
      apply dvd_mul_right, },
    { rw pow_two,
      apply dvd_mul_right, }},
  { rw pow_two,
    apply dvd_mul_of_dvd_left h, },
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Expresion_divisible.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 20.
