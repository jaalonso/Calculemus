-- La_equipotencia_es_una_relacion_de_equivalencia.lean
-- La equipotencia es una relación de equivalencia
-- José A. Alonso Jiménez
-- Sevilla, 2 de agosto de 2021
-- ---------------------------------------------------------------------

import tactic
open function

def es_equipotente (A B : Type*) := ∃ g : A → B, bijective g
infix ` ⋍ `: 50 := es_equipotente

example : equivalence (⋍) :=
begin
  repeat {split},
  { intro X,
    let f : X → X := id,
    use f,
    exact bijective_id, },
  { intros X Y hXY,
    cases hXY with f hf,
    -- have hg : ∃ g : Y → X, two_sided_inverse f g,
    --    { rwa exist_two_sided_inverse, },
    --
    -- {cases hg with g hg,
    --
    -- existsi g,
sorry },
  { sorry },
end
