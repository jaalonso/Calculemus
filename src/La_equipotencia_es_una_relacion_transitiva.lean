-- La_equipotencia_es_una_relacion_transitiva.lean
-- La equipotencia es una relación transitiva
-- José A. Alonso Jiménez
-- Sevilla, 17 de agosto de 2021
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
-- Demostrar que la relación de equipotencia es transitiva.
-- ---------------------------------------------------------------------

import tactic
open function

def es_equipotente (A B : Type*) :=
  ∃ g : A → B, bijective g

infix ` ⋍ `: 50 := es_equipotente

-- 1ª demostración
example : transitive (⋍) :=
begin
  intros X Y Z hXY hYZ,
  unfold es_equipotente at *,
  cases hXY with f hf,
  cases hYZ with g hg,
  use (g ∘ f),
  exact bijective.comp hg hf,
end

-- 2ª demostración
example : transitive (⋍) :=
begin
  rintros X Y Z ⟨f, hf⟩ ⟨g, hg⟩,
  use [g ∘ f, bijective.comp hg hf],
end

-- 3ª demostración
example : transitive (⋍) :=
λ X Y Z ⟨f, hf⟩ ⟨g, hg⟩, by use [g ∘ f, bijective.comp hg hf]

-- 4ª demostración
example : transitive (⋍) :=
λ X Y Z ⟨f, hf⟩ ⟨g, hg⟩, exists.intro (g ∘ f) (bijective.comp hg hf)

-- 4ª demostración
example : transitive (⋍) :=
λ X Y Z ⟨f, hf⟩ ⟨g, hg⟩, ⟨g ∘ f, bijective.comp hg hf⟩
