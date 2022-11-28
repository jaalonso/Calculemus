---
Título: La suma de dos funciones acotadas superiormente también lo está.
Autor:  José A. Alonso
---

Demostrar que la suma de dos funciones acotadas superiormente también lo está.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic

variables {f g : ℝ → ℝ}
variables {a b : ℝ}

-- (cota_superior f a) se verifica si a es una cota superior de f.
def cota_superior (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a

-- (acotada_sup f) afirma que f tiene cota superior.
def acotada_sup (f : ℝ → ℝ) := ∃ a, cota_superior f a

example
  (hf : acotada_sup f)
  (hg : acotada_sup g)
  : acotada_sup (f + g) :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import data.real.basic

variables {f g : ℝ → ℝ}
variables {a b : ℝ}

-- (cota_superior f a) se verifica si a es una cota superior de f.
def cota_superior (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a

-- (acotada_sup f) afirma que f tiene cota superior.
def acotada_sup (f : ℝ → ℝ) := ∃ a, cota_superior f a

-- Lema auxiliar
-- =============

lemma cota_superior_suma
  (hfa : cota_superior f a)
  (hgb : cota_superior g b)
  : cota_superior (f + g) (a + b) :=
λ x, add_le_add (hfa x) (hgb x)

-- 1ª demostración
-- ===============

example
  (hf : acotada_sup f)
  (hg : acotada_sup g)
  : acotada_sup (f + g) :=
begin
  cases hf with a hfa,
  cases hg with b hgb,
  have h3 : cota_superior (f + g) (a + b) :=
    cota_superior_suma hfa hgb,
  have h4 : ∃ z, ∀ x, (f + g) x ≤ z,
    by exact Exists.intro (a + b) h3,
  show acotada_sup (f + g),
    by exact h4,
end

-- 2ª demostración
-- ===============

example
  (hf : acotada_sup f)
  (hg : acotada_sup g)
  : acotada_sup (f + g) :=
begin
  cases hf with a hfa,
  cases hg with b hfb,
  use a + b,
  apply cota_superior_suma hfa hfb,
end

-- 3ª demostración
-- ===============

example
  (hf : acotada_sup f)
  (hg : acotada_sup g)
  : acotada_sup (f + g) :=
begin
  rcases hf with ⟨a, hfa⟩,
  rcases hg with ⟨b, hfb⟩,
  exact ⟨a + b, cota_superior_suma hfa hfb⟩
end

-- 4ª demostración
-- ===============

example :
  acotada_sup f → acotada_sup g → acotada_sup (f + g) :=
begin
  rintros ⟨a, hfa⟩ ⟨b, hfb⟩,
  exact ⟨a + b, cota_superior_suma hfa hfb⟩,
end

-- 5ª demostración
-- ===============

example :
  acotada_sup f → acotada_sup g → acotada_sup (f + g) :=
λ ⟨a, hfa⟩ ⟨b, hfb⟩, ⟨a + b, cota_superior_suma hfa hfb⟩
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Suma_de_funciones_acotadas_superiormente.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 31.
