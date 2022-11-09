---
Título: Si f es monótona y c ≥ 0, entonces c·f es monótona.
Autor:  José A. Alonso
---

Demostrar que si f es monótona y c ≥ 0, entonces c·f es monótona.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic

variables (f : ℝ → ℝ)
variable  {c : ℝ}

example
  (mf : monotone f)
  (nnc : 0 ≤ c)
  : monotone (λ x, c * f x) :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import data.real.basic

variables (f : ℝ → ℝ)
variable  {c : ℝ}

-- 1ª demostración
-- ===============

example
  (mf : monotone f)
  (nnc : 0 ≤ c)
  : monotone (λ x, c * f x) :=
begin
  have h1 : ∀ a b, a ≤ b → (λ x, c * f x) a ≤ (λ x, c * f x) b,
    { intros a b hab,
      have h2 : f a ≤ f b := mf hab,
      have h3 : c * f a ≤ c * f b := mul_le_mul_of_nonneg_left h2 nnc,
      show (λ x, c * f x) a ≤ (λ x, c * f x) b,
        by exact h3, },
  show monotone (λ x, c * f x),
    by exact h1,
end

-- 2ª demostración
-- ===============

example
  (mf : monotone f)
  (nnc : 0 ≤ c)
  : monotone (λ x, c * f x) :=
begin
  intros a b hab,
  apply mul_le_mul_of_nonneg_left,
  apply mf hab,
  apply nnc
end

-- 3ª demostración
-- ===============

example (mf : monotone f) (nnc : 0 ≤ c) :
  monotone (λ x, c * f x) :=
λ a b hab, mul_le_mul_of_nonneg_left (mf hab) nnc
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Producto_de_un_positivo_por_una_funcion_monotona.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 28.
