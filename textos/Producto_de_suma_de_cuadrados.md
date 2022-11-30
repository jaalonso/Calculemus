---
Título: Si x e y son sumas de dos cuadrados, entonces xy también lo es
Autor:  José A. Alonso
---

Demostrar que si x e y son sumas de dos cuadrados, entonces xy también lo es.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic
variables {α : Type*} [comm_ring α]
variables {x y : α}

-- (es_suma_de_cuadrados x) se verifica si x se puede escribir como la
-- suma de dos cuadrados.
def es_suma_de_cuadrados (x : α) := ∃ a b, x = a^2 + b^2

example
  (hx : es_suma_de_cuadrados x)
  (hy : es_suma_de_cuadrados y)
  : es_suma_de_cuadrados (x * y) :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import tactic
variables {α : Type*} [comm_ring α]
variables {x y : α}

-- (es_suma_de_cuadrados x) se verifica si x se puede escribir como la
-- suma de dos cuadrados.
def es_suma_de_cuadrados (x : α) := ∃ a b, x = a^2 + b^2

-- 1ª demostración
-- ===============

example
  (hx : es_suma_de_cuadrados x)
  (hy : es_suma_de_cuadrados y)
  : es_suma_de_cuadrados (x * y) :=
begin
  rcases hx with ⟨a, b, hab : x = a^2 + b^2⟩,
  rcases hy with ⟨c, d, hcd : y = c^2 + d^2⟩,
  have h1: x * y = (a*c - b*d)^2 + (a*d + b*c)^2,
    calc x * y
         = (a^2 + b^2) * (c^2 + d^2)     : by rw [hab, hcd]
     ... = (a*c - b*d)^2 + (a*d + b*c)^2 : by ring,
  have h2 : ∃ f, x * y = (a*c - b*d)^2 + f^2,
    by exact Exists.intro (a*d + b*c) h1,
  have h3 : ∃ e f, x * y = e^2 + f^2,
    by exact Exists.intro (a*c - b*d) h2,
  show es_suma_de_cuadrados (x * y),
    by exact h3,
end

-- 2ª demostración
-- ===============

example
  (hx : es_suma_de_cuadrados x)
  (hy : es_suma_de_cuadrados y)
  : es_suma_de_cuadrados (x * y) :=
begin
  rcases hx with ⟨a, b, hab : x = a^2 + b^2⟩,
  rcases hy with ⟨c, d, hcd : y = c^2 + d^2⟩,
  have h1: x * y = (a*c - b*d)^2 + (a*d + b*c)^2,
    calc x * y
         = (a^2 + b^2) * (c^2 + d^2)     : by rw [hab, hcd]
     ... = (a*c - b*d)^2 + (a*d + b*c)^2 : by ring,
  have h2 : ∃ e f, x * y = e^2 + f^2,
    by tauto,
  show es_suma_de_cuadrados (x * y),
    by exact h2,
end

-- 3ª demostración
-- ===============

example
  (hx : es_suma_de_cuadrados x)
  (hy : es_suma_de_cuadrados y)
  : es_suma_de_cuadrados (x * y) :=
begin
  rcases hx with ⟨a, b, hab⟩,
  rcases hy with ⟨c, d, hcd⟩,
  rw [hab, hcd],
  use [a*c - b*d, a*d + b*c],
  ring,
end

-- 3ª demostración
-- ===============

example
  (hx : es_suma_de_cuadrados x)
  (hy : es_suma_de_cuadrados y)
  : es_suma_de_cuadrados (x * y) :=
begin
  rcases hx with ⟨a, b, rfl⟩,
  rcases hy with ⟨c, d, rfl⟩,
  use [a*c - b*d, a*d + b*c],
  ring
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Producto_de_suma_de_cuadrados.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 32.
