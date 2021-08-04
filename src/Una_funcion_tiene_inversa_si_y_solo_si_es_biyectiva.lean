-- Una_funcion_tiene_inversa_si_y_solo_si_es_biyectiva.lean
-- Una función tiene inversa si y solo si es biyectiva
-- José A. Alonso Jiménez
-- Sevilla, 2 de agosto de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean se puede definir que g es una inversa de f por
--    def inversa (f : X → Y) (g : Y → X) :=
--      (∀ x, (g ∘ f) x = x) ∧ (∀ y, (f ∘ g) y = y)
-- y que f tiene inversa por
--    def tiene_inversa (f : X → Y) :=
--      ∃ g, inversa f g
--
-- Demostrar que la función f tiene inversa si y solo si f es biyectiva.
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
example : tiene_inversa f ↔ bijective f :=
begin
  split,
  { rintro ⟨g, ⟨h1, h2⟩⟩,
    split,
    { intros p q hf,
      calc p = g (f p) : (h1 p).symm
         ... = g (f q) : congr_arg g hf
         ... = q       : h1 q, },
    { intro y,
      use g y,
      exact h2 y, }},
  { rintro ⟨hfinj, hfsur⟩,
    choose g hg using hfsur,
    use g,
    split,
    { intro a,
      apply hfinj,
      rw hg (f a), },
    { exact hg, }},
end

-- 2ª demostración
example : tiene_inversa f ↔ bijective f :=
begin
  split,
  { rintro ⟨g, ⟨h1, h2⟩⟩,
    split,
    { intros p q hf,
      calc p = g (f p) : (h1 p).symm
         ... = g (f q) : congr_arg g hf
         ... = q       : h1 q, },
    { intro y,
      use [g y, h2 y], }},
  { rintro ⟨hfinj, hfsur⟩,
    choose g hg using hfsur,
    use g,
    split,
    { intro a,
      exact @hfinj (g (f a)) a (hg (f a)), },
    { exact hg, }},
end

-- 3ª demostración
example : tiene_inversa f ↔ bijective f :=
begin
  split,
  { rintro ⟨g, ⟨h1, h2⟩⟩,
    split,
    { intros p q hf,
      calc p = g (f p) : (h1 p).symm
         ... = g (f q) : congr_arg g hf
         ... = q       : h1 q, },
    { intro y,
      use [g y, h2 y], }},
  { rintro ⟨hfinj, hfsur⟩,
    choose g hg using hfsur,
    use g,
    exact ⟨λ a, @hfinj (g (f a)) a (hg (f a)), hg⟩, },
end

-- 4ª demostración
example
  : tiene_inversa f ↔ bijective f :=
begin
  split,
  { rintro ⟨g, ⟨h1, h2⟩⟩,
    split,
    { intros p q hf,
      calc p = g (f p) : (h1 p).symm
         ... = g (f q) : congr_arg g hf
         ... = q       : h1 q, },
    { intro y,
      use [g y, h2 y], }},
  { rintro ⟨hfinj, hfsur⟩,
    choose g hg using hfsur,
    use [g, ⟨λ a, @hfinj (g (f a)) a (hg (f a)), hg⟩], },
end
