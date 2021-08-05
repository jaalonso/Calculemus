-- La_equipotencia_es_una_relacion_reflexiva.lean
-- La equipotencia es una relación reflexiva
-- José A. Alonso Jiménez
-- Sevilla, 11 de agosto de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Dos conjuntos A y B son equipotentes (y se denota por A ≃ B) si
-- existe una aplicación biyectiva entre ellos. La equipotencia se puede
-- definir en Lean por
--    def es_equipotente (A B : Type*) :=
--      ∃ g : A → B, bijective g
--
--    infix ` ⋍ `: 50 := es_equipotente
--
-- Demostrar que la relación de equipotencia es reflexiva.
-- ---------------------------------------------------------------------

import tactic
open function

def es_equipotente (A B : Type*) :=
  ∃ g : A → B, bijective g

infix ` ⋍ `: 50 := es_equipotente

-- 1ª demostración
example : reflexive (⋍) :=
begin
  intro X,
  use id,
  exact bijective_id,
end

-- 2ª demostración
example : reflexive (⋍) :=
begin
  intro X,
  use [id, bijective_id],
end

-- 3ª demostración
example : reflexive (⋍) :=
λ X, ⟨id, bijective_id⟩

-- 4ª demostración
example : reflexive (⋍) :=
by tidy
