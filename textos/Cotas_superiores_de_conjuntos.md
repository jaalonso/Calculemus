---
Título: Si a es una cota superior de s y a ≤ b, entonces b es una cota superior de s
Autor:  José A. Alonso
---

Demostrar que si a es una cota superior de s y a ≤ b, entonces b es una cota superior de s

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic

variables {α : Type*} [partial_order α]
variables s : set α
variables a b : α

-- (cota_superior s a) expresa que a es una cota superior de s.
def cota_superior (s : set α) (a : α) := ∀ {x}, x ∈ s → x ≤ a

example
  (h1 : cota_superior s a)
  (h2 : a ≤ b)
  : cota_superior s b :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import tactic

variables {α : Type*} [partial_order α]
variables s : set α
variables a b : α

-- (cota_superior s a) expresa que a es una cota superior de s.
def cota_superior (s : set α) (a : α) := ∀ {x}, x ∈ s → x ≤ a

-- 1ª demostración
-- ===============

example
  (h1 : cota_superior s a)
  (h2 : a ≤ b)
  : cota_superior s b :=
begin
  intro x,
  assume xs : x ∈ s,
  have h3 : x ≤ a := h1 xs,
  show x ≤ b,
    by exact le_trans h3 h2,
end

-- 2ª demostración
-- ===============

example
  (h1 : cota_superior s a)
  (h2 : a ≤ b)
  : cota_superior s b :=
begin
  intros x xs,
  calc x ≤ a : h1 xs
     ... ≤ b : h2
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Cotas_superiores_de_conjuntos.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 29.
