---
Título: Si c ≥ 0 y f está acotada superiormente, entonces c * f también lo está.
Autor:  José A. Alonso
---

Demostrar que si c ≥ 0 y f está acotada superiormente, entonces c * f también lo está.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic

variables {f : ℝ → ℝ}                    -- 2
variables {a c : ℝ}                      -- 3

-- (cota_superior f a) se verifica si a es una cota superior de f.
def cota_superior (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a

-- (acotada_sup f) se verifica si f tiene cota superior.
def acotada_sup (f : ℝ → ℝ) := ∃ a, cota_superior f a

example
  (hf : acotada_sup f)
  (h : c ≥ 0)
  : acotada_sup (λ x, c * f x) :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import data.real.basic

variables {f : ℝ → ℝ}
variables {a c : ℝ}

-- (cota_superior f a) se verifica si a es una cota superior de f.
def cota_superior (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a

-- (acotada_sup f) se verifica si f tiene cota superior.
def acotada_sup (f : ℝ → ℝ) := ∃ a, cota_superior f a

-- Lema auxiliar
-- ============

lemma cota_superior_mul
  (hfa : cota_superior f a)
  (h : c ≥ 0)
  : cota_superior (λ x, c * f x) (c * a) :=
λ x, mul_le_mul_of_nonneg_left (hfa x) h

-- 1ª demostración
-- ===============

example
  (hf : acotada_sup f)
  (h : c ≥ 0)
  : acotada_sup (λ x, c * f x) :=
begin
  cases hf with a ha,
  have h1 : cota_superior (λ x, c * f x) (c * a) := cota_superior_mul ha h,
  have h2 : ∃ z, ∀ x, (λ x, c * f x) x ≤ z,
    by exact Exists.intro (c * a) h1,
  show acotada_sup (λ x, c * f x),
    by exact h2,
end

-- 2ª demostración
-- ===============

example
  (hf : acotada_sup f)
  (h : c ≥ 0)
  : acotada_sup (λ x, c * f x) :=
begin
  cases hf with a ha,
  use c * a,
  apply cota_superior_mul ha h,
end

-- 3ª demostración
-- ===============

example
  (hf : acotada_sup f)
  (h : c ≥ 0)
  : acotada_sup (λ x, c * f x) :=
begin
  rcases hf with ⟨a, ha⟩,
  exact ⟨c * a, cota_superior_mul ha h⟩,
end

-- 4ª demostración
-- ===============

example
  (h : c ≥ 0)
  : acotada_sup f → acotada_sup (λ x, c * f x) :=
begin
  rintro ⟨a, ha⟩,
  exact ⟨c * a, cota_superior_mul ha h⟩,
end

-- 5ª demostración
-- ===============

example
  (h : c ≥ 0)
  : acotada_sup f → acotada_sup (λ x, c * f x) :=
λ ⟨a, ha⟩, ⟨c * a, cota_superior_mul ha h⟩
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Producto_por_funcion_acotada_superiormente.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 31.
