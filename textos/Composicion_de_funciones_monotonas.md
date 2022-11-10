---
Título: La composición de dos funciones monótonas es monótona.
Autor:  José A. Alonso
---

Demostrar que la composición de dos funciones monótonas es monótona.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic

variables (f g : ℝ → ℝ)

example
  (mf : monotone f)
  (mg : monotone g)
  : monotone (f ∘ g) :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import data.real.basic

variables (f g : ℝ → ℝ)

-- 1ª demostración
-- ===============

example
  (mf : monotone f)
  (mg : monotone g)
  : monotone (f ∘ g) :=
begin
  have h1 : ∀ a b, a ≤ b → (f ∘ g) a ≤ (f ∘ g) b,
    { intros a b hab,
      have h1 : g a ≤ g b := mg hab,
      have h2 : f (g a) ≤ f (g b) := mf h1,
      show (f ∘ g) a ≤ (f ∘ g) b,
        by exact h2, },
  show monotone (f ∘ g),
    by exact h1,
end

-- 2ª demostración
-- ===============

example
  (mf : monotone f)
  (mg : monotone g)
  : monotone (f ∘ g) :=
begin
  intros a b hab,
  apply mf,
  apply mg,
  apply hab
end

-- 3ª demostración
-- ===============

example
  (mf : monotone f)
  (mg : monotone g)
  : monotone (f ∘ g) :=
λ a b hab, mf (mg hab)

-- 4ª demostración
-- ===============

example
  (mf : monotone f)
  (mg : monotone g)
  : monotone (f ∘ g) :=
-- by library_search
monotone.comp mf mg

-- 5ª demostración
-- ===============

example
  (mf : monotone f)
  (mg : monotone g)
  : monotone (f ∘ g) :=
-- by hint
by tauto
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Composicion_de_funciones_monotonas.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 28.
