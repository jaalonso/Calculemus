---
Título: La suma de dos funciones monótonas es monótona
Autor:  José A. Alonso
---

Demostrar que la suma de dos funciones monótonas es monótona.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic

variables (f g : ℝ → ℝ)

example
  (mf : monotone f)
  (mg : monotone g)
  : monotone (f + g) :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import data.real.basic

variables (f g : ℝ → ℝ)

-- 1ª demostración
-- ===============

example
  (mf : monotone f)
  (mg : monotone g)
  : monotone (f + g) :=
begin
  have h1 : ∀ a b, a ≤ b → (f + g) a ≤ (f + g ) b,
    { intros a b hab,
      have h2 : f a ≤ f b := mf hab,
      have h3 : g a ≤ g b := mg hab,
      calc (f + g) a
           = f a + g a : rfl
       ... ≤ f b + g b : add_le_add h2 h3
       ... = (f + g) b : rfl, },
  show monotone (f + g),
    by exact h1,
end

-- 2ª demostración
-- ===============

example
  (mf : monotone f)
  (mg : monotone g)
  : monotone (f + g) :=
begin
  intros a b hab,
  apply add_le_add,
  apply mf hab,
  apply mg hab
end

-- 3ª demostración
-- ===============

example
  (mf : monotone f)
  (mg : monotone g)
  : monotone (f + g) :=
λ a b hab, add_le_add (mf hab) (mg hab)
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Suma_de_funciones_monotonas.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 28.
