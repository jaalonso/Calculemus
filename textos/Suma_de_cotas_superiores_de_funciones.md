---
Título: Si a es una cota superior de f y b lo es de g, entonces a + b lo es de f + g.
Autor:  José A. Alonso
---

Demostrar que si a es una cota superior de f y b lo es de g, entonces a + b lo es de f + g.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic

-- (es_cota_superior f a) se verifica si a es una cota superior de f.
def es_cota_superior (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a

variables {f g : ℝ → ℝ}
variables {a b : ℝ}

example
  (hfa : es_cota_superior f a)
  (hgb : es_cota_superior g b)
  : es_cota_superior (f + g) (a + b) :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import data.real.basic

-- (es_cota_superior f a) se verifica si a es una cota superior de f.
def es_cota_superior (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a

variables {f g : ℝ → ℝ}
variables {a b : ℝ}

-- 1ª demostración
-- ===============

example
  (hfa : es_cota_superior f a)
  (hgb : es_cota_superior g b)
  : es_cota_superior (f + g) (a + b) :=
begin
  assume x : ℝ,
  have h1 : f x ≤ a := hfa x,
  have h2 : g x ≤ b := hgb x,
  calc (f + g) x
       = f x + g x : rfl
   ... ≤ a + b     : add_le_add h1 h2
end

-- 2ª demostración
-- ===============

example
  (hfa : es_cota_superior f a)
  (hgb : es_cota_superior g b)
  : es_cota_superior (f + g) (a + b) :=
begin
  intro x,
  change f x + g x ≤ a + b,
  apply add_le_add,
  apply hfa,
  apply hgb
end

-- 3ª demostración
-- ===============

example
  (hfa : es_cota_superior f a)
  (hgb : es_cota_superior g b)
  : es_cota_superior (f + g) (a + b) :=
λ x, add_le_add (hfa x) (hgb x)
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Suma_de_cotas_superiores_de_funciones.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. ???.
