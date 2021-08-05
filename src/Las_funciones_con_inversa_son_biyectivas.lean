-- Las_funciones_con_inversa_son_biyectivas.lean
-- Las funciones con inversa son biyectivas
-- José A. Alonso Jiménez
-- Sevilla, 8 de agosto de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean se puede definir que g es una inversa de f por
--    def inversa (f : X → Y) (g : Y → X) :=
--      (∀ x, (g ∘ f) x = x) ∧ (∀ y, (f ∘ g) y = y)
-- y que f tiene inversa por
--    def tiene_inversa (f : X → Y) :=
--      ∃ g, inversa g f
--
-- Demostrar que si la función f tiene inversa, entonces f es biyectiva.
-- ---------------------------------------------------------------------

import tactic
open function

variables {X Y : Type*}
variable  (f : X → Y)

def inversa (f : X → Y) (g : Y → X) :=
  (∀ x, (g ∘ f) x = x) ∧ (∀ y, (f ∘ g) y = y)

def tiene_inversa (f : X → Y) :=
  ∃ g, inversa g f

-- 1ª demostración
example
  (hf : tiene_inversa f)
  : bijective f :=
begin
  rcases hf with ⟨g, ⟨h1, h2⟩⟩,
  split,
  { intros a b hab,
    calc a = g (f a) : (h2 a).symm
       ... = g (f b) : congr_arg g hab
       ... = b       : h2 b, },
  { intro y,
    use g y,
    exact h1 y, },
end

-- 2ª demostración
example
  (hf : tiene_inversa f)
  : bijective f :=
begin
  rcases hf with ⟨g, ⟨h1, h2⟩⟩,
  split,
  { intros a b hab,
    calc a = g (f a) : (h2 a).symm
       ... = g (f b) : congr_arg g hab
       ... = b       : h2 b, },
  { intro y,
    use [g y, h1 y], },
end

-- 3ª demostración
example
  (hf : tiene_inversa f)
  : bijective f :=
begin
  rcases hf with ⟨g, ⟨h1, h2⟩⟩,
  split,
  { exact left_inverse.injective h2, },
  { exact right_inverse.surjective h1, },
end

-- 4ª demostración
example
  (hf : tiene_inversa f)
  : bijective f :=
begin
  rcases hf with ⟨g, ⟨h1, h2⟩⟩,
  exact ⟨left_inverse.injective h2,
         right_inverse.surjective h1⟩,
end

-- 5ª demostración
example :
  tiene_inversa f → bijective f :=
begin
  rintros ⟨g, ⟨h1, h2⟩⟩,
  exact ⟨left_inverse.injective h2,
         right_inverse.surjective h1⟩,
end

-- 6ª demostración
example :
  tiene_inversa f → bijective f :=
λ ⟨g, ⟨h1, h2⟩⟩, ⟨left_inverse.injective h2,
                  right_inverse.surjective h1⟩
