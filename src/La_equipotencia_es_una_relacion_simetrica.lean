-- La_equipotencia_es_una_relacion_simetrica.lean
-- La equipotencia es una relación simétrica
-- José A. Alonso Jiménez
-- Sevilla, 13 de agosto de 2021
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

-- 1ª demostración
example : symmetric (⋍) :=
begin
  unfold symmetric,
  intros x y hxy,
  unfold es_equipotente at *,
  cases hxy with f hf,
  have h1 : tiene_inversa f := aux1 hf,
  cases h1 with g hg,
  use g,
  exact aux2 hf hg,
end

-- 2ª demostración
example : symmetric (⋍) :=
begin
  intros x y hxy,
  cases hxy with f hf,
  cases (aux1 hf) with g hg,
  use [g, aux2 hf hg],
end

-- 3ª demostración
example : symmetric (⋍) :=
begin
  rintros x y ⟨f, hf⟩,
  cases (aux1 hf) with g hg,
  use [g, aux2 hf hg],
end
