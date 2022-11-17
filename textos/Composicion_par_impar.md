---
Título: Si f es par y g es impar, entonces f ∘ g es par.
Autor:  José A. Alonso
---

La función f de ℝ en ℝ es par si, para todo x, f(-x) = f(x) y es impar si, para todo x, f(-x) -f(x).

Demostrar que si f es par y g es impar, entonces f ∘ g es par.


Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic
variables (f g : ℝ → ℝ)

def par (f : ℝ → ℝ) : Prop    := ∀ x, f x = f (-x)
def impar  (f : ℝ → ℝ) : Prop := ∀ x, f x = -f (-x)

example
  (hf : par f)
  (hg : impar g)
  : par (f ∘ g) :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import data.real.basic
variables (f g : ℝ → ℝ)

def par (f : ℝ → ℝ) : Prop    := ∀ x, f x = f (-x)
def impar  (f : ℝ → ℝ) : Prop := ∀ x, f x = -f (-x)

-- 1ª demostración
-- ===============

example
  (hf : par f)
  (hg : impar g)
  : par (f ∘ g) :=
begin
  intro x,
  have h1 : f x = f (-x) := hf x,
  have h2 : g x = -g (-x) := hg x,
  calc (f ∘ g) x
       = f (g x)      : rfl
   ... = f (-g (-x))  : congr_arg f (hg x)
   ... = f (g (-x))   : eq.symm (hf (g (-x)))
   ... = (f ∘ g) (-x) : rfl
end

-- 2ª demostración
-- ===============

example
  (hf : par f)
  (hg : impar g)
  : par (f ∘ g) :=
begin
  intro x,
  calc (f ∘ g) x
       = f (g x)      : rfl
   ... = f (-g (-x))  : by rw hg
   ... = f (g (-x))   : by rw ←hf
   ... = (f ∘ g) (-x) : rfl
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Composicion_par_impar.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 29.
