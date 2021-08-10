-- La_igualdad_de_valores_es_una_relacion_de_equivalencia.lean
-- La igualdad de valores es una relación de equivalencia
-- José A. Alonso Jiménez
-- Sevilla, 19 de agosto de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sean X e Y dos conjuntos y f una función de X en Y. Se define la
-- relación R en X de forma que x está relacionado con y si f(x) = f(y).
--
-- Demostrar que R es una relación de equivalencia.
-- ---------------------------------------------------------------------

import tactic

universe u
variables {X Y : Type u}
variable  (f : X → Y)

def R (x y : X) := f x = f y

-- 1ª demostración
example : equivalence (R f) :=
begin
  unfold equivalence,
  repeat { split },
  { unfold reflexive,
    intro x,
    unfold R, },
  { unfold symmetric,
    intros x y hxy,
    unfold R,
    exact symm hxy, },
  { unfold transitive,
    unfold R,
    intros x y z hxy hyz,
    exact eq.trans hxy hyz, },
end

-- 2ª demostración
example : equivalence (R f) :=
begin
  repeat { split },
  { intro x,
    exact rfl, },
  { intros x y hxy,
    exact eq.symm hxy, },
  { intros x y z hxy hyz,
    exact eq.trans hxy hyz, },
end

-- 3ª demostración
example : equivalence (R f) :=
begin
  repeat { split },
  { exact λ x, rfl, },
  { exact λ x y hxy, eq.symm hxy, },
  { exact λ x y z hxy hyz, eq.trans hxy hyz, },
end

-- 4ª demostración
example : equivalence (R f) :=
⟨λ x, rfl,
 λ x y hxy, eq.symm hxy,
 λ x y z hxy hyz, eq.trans hxy hyz⟩
