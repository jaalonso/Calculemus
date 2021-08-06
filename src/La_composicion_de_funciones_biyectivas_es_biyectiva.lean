-- La_composicion_de_funciones_biyectivas_es_biyectiva.lean
-- La composición de funciones biyectivas es biyectiva
-- José A. Alonso Jiménez
-- Sevilla, 16 de agosto de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que la composición de dos funciones biyectivas es una
-- función biyectiva.
-- ---------------------------------------------------------------------

import tactic
open function

variables {X Y Z : Type}
variable  {f : X → Y}
variable  {g : Y → Z}

-- 1ª demostración
example
  (Hf : bijective f)
  (Hg : bijective g)
  : bijective (g ∘ f) :=
begin
  cases Hf with Hfi Hfs,
  cases Hg with Hgi Hgs,
  split,
  { apply injective.comp,
    { exact Hgi, },
    { exact Hfi, }},
  { apply surjective.comp,
    { exact Hgs, },
    { exact Hfs, }},
end

-- 2ª demostración
example
  (Hf : bijective f)
  (Hg : bijective g)
  : bijective (g ∘ f) :=
begin
  cases Hf with Hfi Hfs,
  cases Hg with Hgi Hgs,
  split,
  { exact injective.comp Hgi Hfi, },
  { exact surjective.comp Hgs Hfs, },
end

-- 3ª demostración
example
  (Hf : bijective f)
  (Hg : bijective g)
  : bijective (g ∘ f) :=
begin
  cases Hf with Hfi Hfs,
  cases Hg with Hgi Hgs,
  exact ⟨injective.comp Hgi Hfi,
         surjective.comp Hgs Hfs⟩,
end

-- 4ª demostración
example :
  bijective f → bijective g → bijective (g ∘ f) :=
begin
  rintros ⟨Hfi, Hfs⟩ ⟨Hgi, Hgs⟩,
  exact ⟨injective.comp Hgi Hfi,
         surjective.comp Hgs Hfs⟩,
end

-- 5ª demostración
example :
  bijective f → bijective g → bijective (g ∘ f) :=
λ ⟨Hfi, Hfs⟩ ⟨Hgi, Hgs⟩, ⟨injective.comp Hgi Hfi,
                          surjective.comp Hgs Hfs⟩

-- 6ª demostración
example
  (Hf : bijective f)
  (Hg : bijective g)
  : bijective (g ∘ f) :=
-- by library_search
bijective.comp Hg Hf
