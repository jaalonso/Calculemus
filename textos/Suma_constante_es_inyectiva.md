---
Título: Para todo c ∈ ℝ, la función f(x) = x+c es inyectiva.
Autor:  José A. Alonso
---

Demostrar que para todo c ∈ ℝ, la función f(x) = x+c es inyectiva.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic                                               -- 1

open function                                                        -- 2

variable {c : ℝ}

example : injective (λ x, x + c) :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import data.real.basic                                               -- 1

open function                                                        -- 2

variable {c : ℝ}

-- 1ª demostración
-- ===============

example : injective (λ x, x + c) :=
begin
  assume x1 : ℝ,
  assume x2 : ℝ,
  assume h1 : (λ x, x + c) x1 = (λ x, x + c) x2,
  have h2 : x1 + c = x2 + c := h1,
  show x1 = x2,
    by exact (add_left_inj c).mp h2,
end

-- 2ª demostración
-- ===============

example : injective (λ x, x + c) :=
begin
  intros x1 x2 h,
  change x1 + c = x2 + c at h,
  apply add_right_cancel h,
end

-- 3ª demostración
-- ===============

example : injective (λ x, x + c) :=
begin
  intros x1 x2 h,
  apply (add_left_inj c).mp,
  exact h,
end

-- 4ª demostración
-- ===============

example : injective (λ x, x + c) :=
λ x1 x2 h, (add_left_inj c).mp h
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Suma_constante_es_inyectiva.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 29.
