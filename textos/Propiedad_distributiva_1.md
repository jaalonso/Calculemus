---
Título: Si R es un retículo tal que (∀ x y z ∈ R, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z))), entonces (∀ a b c ∈ R, (a ⊔ b) ⊓ c = (a ⊓ c) ⊔ (b ⊓ c))
Autor:  José A. Alonso
---

Demostrar que si R es un retículo tal que
<pre lang="text">
   (∀ x y z ∈ R, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z))),
</pre>
entonces
<pre lang="text">
   (∀ a b c ∈ R, (a ⊔ b) ⊓ c = (a ⊓ c) ⊔ (b ⊓ c))
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import order.lattice
variables {R : Type*} [lattice R]

example
  (h : ∀ x y z : R, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z))
  : ∀ a b c : R, (a ⊔ b) ⊓ c = (a ⊓ c) ⊔ (b ⊓ c) :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import order.lattice
variables {R : Type*} [lattice R]

example
  (h : ∀ x y z : R, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z))
  : ∀ a b c : R, (a ⊔ b) ⊓ c = (a ⊓ c) ⊔ (b ⊓ c) :=
begin
  intros a b c,
  calc (a ⊔ b) ⊓ c
       = c ⊓ (a ⊔ b)       : by rw inf_comm
   ... = (c ⊓ a) ⊔ (c ⊓ b) : by rw h
   ... = (a ⊓ c) ⊔ (c ⊓ b) : by rw [@inf_comm _ _ c a]
   ... = (a ⊓ c) ⊔ (b ⊓ c) : by rw [@inf_comm _ _ c b]
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Propiedad_distributiva_1.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 23.
