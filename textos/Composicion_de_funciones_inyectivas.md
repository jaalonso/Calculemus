---
Título: Si f: A → B y g: B → C son inyectiva, entonces g ∘ f es inyectiva
Autor:  José A. Alonso
---

Demostrar que si f: A → B y g: B → C son inyectiva, entonces g ∘ f es inyectiva.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic

open function

variables {A : Type*} {B : Type*} {C : Type*}
variables {f : A → B} {g : B → C}

example
  (hg : injective g)
  (hf : injective f) :
  injective (g ∘ f) :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import tactic

open function

variables {A : Type*} {B : Type*} {C : Type*}
variables {f : A → B} {g : B → C}

-- 1ª demostración
-- ===============

example
  (hg : injective g)
  (hf : injective f) :
  injective (g ∘ f) :=
begin
  assume x : A,
  assume y : A,
  assume h1: (g ∘ f) x = (g ∘ f) y,
  have h2: g (f x) = g (f y) := h1,
  have h3: f x = f y := hg h2,
  show x = y,
    by exact hf h3,
end

-- 2ª demostración
-- ===============

example
  (hg : injective g)
  (hf : injective f) :
  injective (g ∘ f) :=
begin
  intros x y h,
  apply hf,
  apply hg,
  apply h,
end

-- 3ª demostración
-- ===============

example
  (hg : injective g)
  (hf : injective f) :
  injective (g ∘ f) :=
λ x y h, hf (hg h)

-- 4ª demostración
-- ===============

example
  (hg : injective g)
  (hf : injective f) :
  injective (g ∘ f) :=
-- by library_search
injective.comp hg hf

-- 5ª demostración
-- ===============

example
  (hg : injective g)
  (hf : injective f) :
  injective (g ∘ f) :=
-- by hint
by tauto
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Composicion_de_funciones_inyectivas.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 29.
