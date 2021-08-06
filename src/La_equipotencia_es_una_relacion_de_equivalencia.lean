-- La_equipotencia_es_una_relacion_de_equivalencia.lean
-- La equipotencia es una relación de equivalencia
-- José A. Alonso Jiménez
-- Sevilla, 18 de agosto de 2021
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
-- Demostrar que la relación de equipotencia es simétrica.
-- ---------------------------------------------------------------------

import tactic
open function

def es_equipotente (A B : Type*) :=
  ∃ g : A → B, bijective g

infix ` ⋍ `: 50 := es_equipotente

variables {X Y : Type*}
variable  {f : X → Y}
variable  {g : Y → X}

def inversa (f : X → Y) (g : Y → X) :=
  (∀ x, (g ∘ f) x = x) ∧ (∀ y, (f ∘ g) y = y)

def tiene_inversa (f : X → Y) :=
  ∃ g, inversa g f

lemma aux1
  (hf : bijective f)
  : tiene_inversa f :=
begin
  cases (bijective_iff_has_inverse.mp hf) with g hg,
  by tidy,
end

lemma aux2
  (hf : bijective f)
  (hg : inversa g f)
  : bijective g :=
bijective_iff_has_inverse.mpr (by use [f, hg])

example : equivalence (⋍) :=
begin
  repeat {split},
  { exact λ X, ⟨id, bijective_id⟩ },
  { rintros X Y ⟨f, hf⟩,
    cases (aux1 hf) with g hg,
    use [g, aux2 hf hg], },
  { rintros X Y Z ⟨f, hf⟩ ⟨g, hg⟩,
    exact ⟨g ∘ f, bijective.comp hg hf⟩, },
end
