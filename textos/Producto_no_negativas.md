---
Título: El producto de dos funciones no negativas es no negativa
Autor:  José A. Alonso
---

Demostrar que el producto de dos funciones no negativas es no negativa.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic
variables (f g : ℝ → ℝ)

def no_negativa (f : ℝ → ℝ) : Prop := ∀ x, 0 ≤ f x

example
  (nnf : no_negativa f)
  (nng : no_negativa g)
  : no_negativa (f * g) :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import data.real.basic
variables (f g : ℝ → ℝ)

def no_negativa (f : ℝ → ℝ) : Prop := ∀ x, 0 ≤ f x

-- 1ª demostración
-- ===============

example
  (nnf : no_negativa f)
  (nng : no_negativa g)
  : no_negativa (f * g) :=
begin
  have h1 : ∀x, 0 ≤ f x * g x,
  { intro x,
    have h2: 0 ≤ f x := nnf x,
    have h3: 0 ≤ g x := nng x,
    show 0 ≤ f x * g x,
      by exact mul_nonneg (nnf x) (nng x), },
  show no_negativa (f * g),
    by exact h1,
end

-- 2ª demostración
-- ===============

example
  (nnf : no_negativa f)
  (nng : no_negativa g)
  : no_negativa (f * g) :=
begin
  intro x,
  change 0 ≤ f x * g x,
  apply mul_nonneg,
  apply nnf,
  apply nng
end

-- 3ª demostración
-- ===============

example
  (nnf : no_negativa f)
  (nng : no_negativa g)
  : no_negativa (f * g) :=
λ x, mul_nonneg (nnf x) (nng x)
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Producto_no_negativas.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 27.
