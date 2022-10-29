---
Título: La suma de una cota superior de f y una cota superior de g es una cota superior de f+g
Autor:  José A. Alonso
---

Demostrar que la suma de una cota superior de f y una cota superior de g es una cota superior de f+g.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic

-- (cota_superior f a) se verifica si a es una cota superior de f.
def cota_superior (f : ℝ → ℝ) (a : ℝ) : Prop :=
∀ x, f x ≤ a

variables (f g : ℝ → ℝ)
variables (a b : ℝ)

example
  (hfa : cota_superior f a)
  (hgb : cota_superior g b)
  : cota_superior (λ x, f x + g x) (a + b) :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import data.real.basic

-- (cota_superior f a) se verifica si a es una cota superior de f.
def cota_superior (f : ℝ → ℝ) (a : ℝ) : Prop :=
∀ x, f x ≤ a

variables (f g : ℝ → ℝ)
variables (a b : ℝ)

-- 1ª demostración
-- ===============

example
  (hfa : cota_superior f a)
  (hgb : cota_superior g b)
  : cota_superior (λ x, f x + g x) (a + b) :=
begin
  have h1 : ∀ x, f x + g x ≤ a + b,
  { intro x,
    have h1a : f x ≤ a := hfa x,
    have h1b : g x ≤ b := hgb x,
    show f x + g x ≤ a + b,
      by exact add_le_add (hfa x) (hgb x), },
  show cota_superior (λ x, f x + g x) (a + b),
    by exact h1,
end

-- 2ª demostración
-- ===============

example
  (hfa : cota_superior f a)
  (hgb : cota_superior g b)
  : cota_superior (λ x, f x + g x) (a + b) :=
begin
  intro x,
  dsimp,
  change f x + g x ≤ a + b,
  apply add_le_add,
  apply hfa,
  apply hgb
end

-- 3ª demostración
-- ===============

example
  (hfa : cota_superior f a)
  (hgb : cota_superior g b)
  : cota_superior (λ x, f x + g x) (a + b) :=
λ x, add_le_add (hfa x) (hgb x)
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Suma_de_cotas_superiores.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 27.
