-- Composicion_de_funciones_inyectivas.lean
-- Si f: A → B y g: B → C son inyectiva, entonces g ∘ f es inyectiva.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 24-noviembre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si f: A → B y g: B → C son inyectiva, entonces g ∘ f es
-- inyectiva.
-- ----------------------------------------------------------------------

import tactic

open function

variables {A : Type*} {B : Type*} {C : Type*}
variables {f : A → B} {g : B → C}

-- 1ª demostración
-- ===============

example
  (hg : injective g)
  (hf : injective f) :
  injective (g ∘ f) :=
begin
  assume x : A,
  assume y : A,
  assume h1: (g ∘ f) x = (g ∘ f) y,
  have h2: g (f x) = g (f y) := h1,
  have h3: f x = f y := hg h2,
  show x = y,
    by exact hf h3,
end

-- 2ª demostración
-- ===============

example
  (hg : injective g)
  (hf : injective f) :
  injective (g ∘ f) :=
begin
  intros x y h,
  apply hf,
  apply hg,
  apply h,
end

-- 3ª demostración
-- ===============

example
  (hg : injective g)
  (hf : injective f) :
  injective (g ∘ f) :=
λ x y h, hf (hg h)

-- 4ª demostración
-- ===============

example
  (hg : injective g)
  (hf : injective f) :
  injective (g ∘ f) :=
-- by library_search
injective.comp hg hf

-- 5ª demostración
-- ===============

example
  (hg : injective g)
  (hf : injective f) :
  injective (g ∘ f) :=
-- by hint
by tauto
