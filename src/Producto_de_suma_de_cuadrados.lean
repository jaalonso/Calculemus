-- Producto_de_suma_de_cuadrados.lean
-- Si x e y son sumas de dos cuadrados, entonces xy también lo es.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 01-diciembre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si x e y se pueden escribir como la suma
-- de dos cuadrados, entonces también se puede escribir x * y.
-- ----------------------------------------------------------------------

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
