---
Título: La suma de dos funciones acotadas inferiormente también lo está
Autor:  José A. Alonso
---

Demostrar que la suma de dos funciones acotadas inferiormente también lo está.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic

variables {f g : ℝ → ℝ}
variables {a b : ℝ}

-- (cota_inferior f a) se verifica si a es una cota inferior de f.
def cota_inferior (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

-- (acotada_inf f) se verifica si f tiene cota inferior.
def acotada_inf (f : ℝ → ℝ) := ∃ a, cota_inferior f a

example
  (hf : acotada_inf f)
  (hg : acotada_inf g)
  : acotada_inf (f + g) :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import data.real.basic

variables {f g : ℝ → ℝ}
variables {a b : ℝ}

-- (cota_inferior f a) se verifica si a es una cota inferior de f.
def cota_inferior (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

-- (acotada_inf f) se verifica si f tiene cota inferior.
def acotada_inf (f : ℝ → ℝ) := ∃ a, cota_inferior f a

-- Lema auxiliar
-- =============

lemma cota_inferior_add
  (hfa : cota_inferior f a)
  (hgb : cota_inferior g b)
  : cota_inferior (f + g) (a + b) :=
λ x, add_le_add (hfa x) (hgb x)

-- 1ª demostración
-- ===============

example
  (hf : acotada_inf f)
  (hg : acotada_inf g)
  : acotada_inf (f + g) :=
begin
  cases hf with a ha,
  cases hg with b hb,
  have h1 : cota_inferior (f + g) (a + b) := cota_inferior_add ha hb,
  have h2 : ∃ z, ∀ x, z ≤ (f + g) x :=
    by exact Exists.intro (a + b) h1,
  show acotada_inf (f + g),
    by exact h2,
end

-- 2ª demostración
-- ===============

example
  (hf : acotada_inf f)
  (hg : acotada_inf g)
  : acotada_inf (f + g) :=
begin
  cases hf with a hfa,
  cases hg with b hgb,
  use a + b,
  apply cota_inferior_add hfa hgb,
end

-- 3ª demostración
-- ===============

example
  (hf : acotada_inf f)
  (hg : acotada_inf g)
  : acotada_inf (f + g) :=
begin
  rcases hf with ⟨a, hfa⟩,
  rcases hg with ⟨b, hfb⟩,
  exact ⟨a + b, cota_inferior_add hfa hfb⟩,
end

-- 4ª demostración
-- ===============

example :
  acotada_inf f → acotada_inf g → acotada_inf (f + g) :=
begin
  rintros ⟨a, hfa⟩ ⟨b, hfb⟩,
  exact ⟨a + b, cota_inferior_add hfa hfb⟩,
end

-- 5ª demostración
-- ===============

example :
  acotada_inf f → acotada_inf g → acotada_inf (f + g) :=
λ ⟨a, hfa⟩ ⟨b, hfb⟩, ⟨a + b, cota_inferior_add hfa hfb⟩
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Suma_de_funciones_acotadas_inferiormente.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 31.
