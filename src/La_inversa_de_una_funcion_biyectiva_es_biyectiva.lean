-- La_inversa_de_una_funcion_biyectiva_es_biyectiva.lean
-- La inversa de una función biyectiva es biyectiva
-- José A. Alonso Jiménez
-- Sevilla, 12 de agosto de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean se puede definir que g es una inversa de f por
--    def inversa (f : X → Y) (g : Y → X) :=
--      (∀ x, (g ∘ f) x = x) ∧ (∀ y, (f ∘ g) y = y)
--
-- Demostrar que si la función f es biyectiva y g es una inversa de f,
-- entonces g es biyectiva.
-- ---------------------------------------------------------------------

import tactic
open function

variables {X Y : Type*}
variable (f : X → Y)
variable (g : Y → X)

def inversa (f : X → Y) (g : Y → X) :=
  (∀ x, (g ∘ f) x = x) ∧ (∀ y, (f ∘ g) y = y)

-- 1ª demostración
example
  (hf : bijective f)
  (hg : inversa g f)
  : bijective g :=
begin
  rcases hg with ⟨h1, h2⟩,
  rw bijective_iff_has_inverse,
  use f,
  split,
  { exact h1, },
  { exact h2, },
end

-- 2ª demostración
example
  (hf : bijective f)
  (hg : inversa g f)
  : bijective g :=
begin
  rcases hg with ⟨h1, h2⟩,
  rw bijective_iff_has_inverse,
  use f,
  exact ⟨h1, h2⟩,
end

-- 3ª demostración
example
  (hf : bijective f)
  (hg : inversa g f)
  : bijective g :=
begin
  rcases hg with ⟨h1, h2⟩,
  rw bijective_iff_has_inverse,
  use [f, ⟨h1, h2⟩],
end

-- 4ª demostración
example
  (hf : bijective f)
  (hg : inversa g f)
  : bijective g :=
begin
  rw bijective_iff_has_inverse,
  use f,
  exact hg,
end

-- 5ª demostración
example
  (hf : bijective f)
  (hg : inversa g f)
  : bijective g :=
begin
  rw bijective_iff_has_inverse,
  use [f, hg],
end

-- 6ª demostración
example
  (hf : bijective f)
  (hg : inversa g f)
  : bijective g :=
begin
  apply bijective_iff_has_inverse.mpr,
  use [f, hg],
end

-- 7ª demostración
example
  (hf : bijective f)
  (hg : inversa g f)
  : bijective g :=
bijective_iff_has_inverse.mpr (by use [f, hg])
