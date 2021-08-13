-- Las_clases_de_equivalencia_de_elementos_relacionados_son_iguales.lean
-- Las clases de equivalencia de elementos relacionados son iguales
-- José A. Alonso Jiménez
-- Sevilla, 22 de agosto de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que las clases de equivalencia de elementos relacionados
-- son iguales.
-- ---------------------------------------------------------------------

import tactic

variable  {X : Type}
variables {x y: X}
variable  {R : X → X → Prop}

def clase (R : X → X → Prop) (x : X) :=
  {y : X | R x y}

-- En la demostración se usará el siguiente lema del que se presentan
-- varias demostraciones.

-- 1ª demostración del lema auxiliar
example
  (h : equivalence R)
  (hxy : R x y)
  : clase R y ⊆ clase R x :=
begin
  intros z hz,
  have hyz : R y z := hz,
  have htrans : transitive R := h.2.2,
  have hxz : R x z := htrans hxy hyz,
  exact hxz,
end

-- 2ª demostración del lema auxiliar
example
  (h : equivalence R)
  (hxy : R x y)
  : clase R y ⊆ clase R x :=
begin
  intros z hz,
  exact h.2.2 hxy hz,
end

-- 3ª demostración del lema auxiliar
lemma aux
  (h : equivalence R)
  (hxy : R x y)
  : clase R y ⊆ clase R x :=
λ z hz, h.2.2 hxy hz

-- A continuación se presentan varias demostraciones del ejercicio
-- usando el lema auxiliar

-- 1ª demostración
example
  (h : equivalence R)
  (hxy : R x y)
  : clase R x = clase R y :=
begin
  apply le_antisymm,
  { have hs : symmetric R := h.2.1,
    have hyx : R y x := hs hxy,
    exact aux h hyx, },
  { exact aux h hxy, },
end

-- 2ª demostración
example
  (h : equivalence R)
  (hxy : R x y)
  : clase R x = clase R y :=
begin
  apply le_antisymm,
  { exact aux h (h.2.1 hxy), },
  { exact aux h hxy, },
end

-- 3ª demostración
example
  (h : equivalence R)
  (hxy : R x y)
  : clase R x = clase R y :=
le_antisymm (aux h (h.2.1 hxy)) (aux h hxy)
