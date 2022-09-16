---
Título: Si a, b ∈ ℝ, entonces max(a,b) = max(b,a)
Autor:  José A. Alonso
---

Demostrar que si a, b ∈ ℝ, entonces max(a,b) = max(b,a)

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic

variables a b : ℝ

example : max a b = max b a :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import data.real.basic

variables a b : ℝ

-- 1ª demostración
-- ===============

example : max a b = max b a :=
begin
  apply le_antisymm,
  { show max a b ≤ max b a,
    apply max_le,
    { apply le_max_right },
    { apply le_max_left }},
  { show max b a ≤ max a b,
    apply max_le,
    { apply le_max_right },
    { apply le_max_left }},
end

-- 2ª demostración
-- ===============

example : max a b = max b a :=
begin
  have h : ∀ x y : ℝ, max x y ≤ max y x,
  { intros x y,
    apply max_le,
    { apply le_max_right },
    { apply le_max_left }},
  apply le_antisymm,
  apply h,
  apply h,
end

-- 3ª demostración
-- ===============

example : max a b = max b a :=
begin
  have h : ∀ {x y : ℝ}, max x y ≤ max y x,
  { intros x y,
    exact max_le (le_max_right y x) (le_max_left y x),},
  exact le_antisymm h h,
end

-- 4ª demostración
-- ===============

example : max a b = max b a :=
begin
  apply le_antisymm,
  repeat {
    apply max_le,
    apply le_max_right,
    apply le_max_left },
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Conmutatividad_del_maximo.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 19.
