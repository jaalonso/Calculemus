-- Las_funciones_biyectivas_tienen_inversa.lean
-- Las funciones biyectivas tienen inversa
-- José A. Alonso Jiménez
-- Sevilla, 9 de agosto de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean se puede definir que g es una inversa de f por
--    def inversa (f : X → Y) (g : Y → X) :=
--      (∀ x, (g ∘ f) x = x) ∧ (∀ y, (f ∘ g) y = y)
-- y que f tiene inversa por
--    def tiene_inversa (f : X → Y) :=
--      ∃ g, inversa f g
--
-- Demostrar que si la función f es biyectiva, entonces f tiene inversa.
-- ---------------------------------------------------------------------

import tactic
open function

variables {X Y : Type*}
variable  (f : X → Y)

def inversa (f : X → Y) (g : Y → X) :=
  (∀ x, (g ∘ f) x = x) ∧ (∀ y, (f ∘ g) y = y)

def tiene_inversa (f : X → Y) :=
  ∃ g, inversa f g

-- 1ª demostración
example
  (hf : bijective f)
  : tiene_inversa f :=
begin
  rcases hf with ⟨hfiny, hfsup⟩,
  choose g hg using hfsup,
  use g,
  split,
  { intro a,
    apply hfiny,
    rw hg (f a), },
  { exact hg, },
end

-- 2ª demostración
example
  (hf : bijective f)
  : tiene_inversa f :=
begin
  rcases hf with ⟨hfiny, hfsup⟩,
  choose g hg using hfsup,
  use g,
  split,
  { intro a,
    exact @hfiny (g (f a)) a (hg (f a)), },
  { exact hg, },
end

-- 3ª demostración
example
  (hf : bijective f)
  : tiene_inversa f :=
begin
  rcases hf with ⟨hfiny, hfsup⟩,
  choose g hg using hfsup,
  use g,
  exact ⟨λ a, @hfiny (g (f a)) a (hg (f a)), hg⟩,
end

-- 4ª demostración
example
  (hf : bijective f)
  : tiene_inversa f :=
begin
  rcases hf with ⟨hfiny, hfsup⟩,
  choose g hg using hfsup,
  use [g, ⟨λ a, @hfiny (g (f a)) a (hg (f a)), hg⟩],
end
