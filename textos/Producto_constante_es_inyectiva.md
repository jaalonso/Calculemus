---
Título: Para todo c ∈ ℝ-{0}, la función f(x) = x * c es inyectiva
Autor:  José A. Alonso
---

Demostrar que para todo c ∈ ℝ-{0}, la función f(x) = x * c es inyectiva

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic

open function

variable {c : ℝ}

example
  (h : c ≠ 0)
  : injective (λ x, c * x) :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import data.real.basic

open function

variable {c : ℝ}

-- 1ª demostración
-- ===============

example
  (h : c ≠ 0)
  : injective (λ x, c * x) :=
begin
  assume x1 : ℝ,
  assume x2 : ℝ,
  assume h1 : (λ x, c * x) x1 = (λ x, c * x) x2,
  have h2 : c * x1 = c * x2 := h1,
  show x1 = x2,
    by exact (mul_right_inj' h).mp h1,
end

-- 2ª demostración
-- ===============

example
  (h : c ≠ 0)
  : injective (λ x, c * x) :=
begin
  intros x1 x2 h',
  dsimp at h',
  apply mul_left_cancel₀ h,
  exact h',
end

-- 3ª demostración
-- ===============

example
  (h : c ≠ 0)
  : injective (λ x, c * x) :=
begin
  intros x1 x2 h',
  dsimp at h',
  exact (mul_right_inj' h).mp h'
end

-- 3ª demostración
-- ===============

example
  {c : ℝ}
  (h : c ≠ 0)
  : injective (λ x, c * x) :=
λ x1 x2 h', mul_left_cancel₀ h h'
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Producto_constante_es_inyectiva.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 29.
