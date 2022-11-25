---
Título: ∃ x ∈ ℝ, 2 < x < 3
Autor:  José A. Alonso
---

Demostrar que ∃ x ∈ ℝ, 2 < x < 3

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import data.real.basic

-- 1ª demostración
-- ===============

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
begin
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3,
    by norm_num,
  show ∃ x : ℝ, 2 < x ∧ x < 3,
    by exact Exists.intro (5 / 2) h,
end

-- 2ª demostración
-- ===============

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
begin
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3,
    by norm_num,
  show ∃ x : ℝ, 2 < x ∧ x < 3,
    by exact ⟨5 / 2, h⟩,
end

-- 3ª demostración
-- ===============

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
begin
  use 5 / 2,
  norm_num
end

-- 4ª demostración
-- ===============

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
⟨5 / 2, by norm_num⟩
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Existencia_de_valor_intermedio.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 30.
