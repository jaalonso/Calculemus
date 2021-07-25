-- La_paradoja_del_barbero.lean
-- La paradoja del barbero.
-- José A. Alonso Jiménez
-- Sevilla, 26 de julio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar la paradoja del barbero https://bit.ly/3eWyvVw es decir,
-- que no existe un hombre que afeite a todos los que no se afeitan a sí
-- mismo y sólo a los que no se afeitan a sí mismo.
-- ---------------------------------------------------------------------

import tactic

variable (Hombre : Type)
variable (afeita : Hombre → Hombre → Prop)

-- 1ª demostración
example :
  ¬(∃ x : Hombre, ∀ y : Hombre, afeita x y ↔ ¬ afeita y y) :=
begin
  intro h,
  cases h with b hb,
  specialize hb b,
  by_cases (afeita b b),
  { apply absurd h,
    exact hb.mp h, },
  { apply h,
    exact hb.mpr h, },
end

-- 2ª demostración
example :
  ¬(∃ x : Hombre, ∀ y : Hombre, afeita x y ↔ ¬ afeita y y) :=
begin
  intro h,
  cases h with b hb,
  specialize hb b,
  by_cases (afeita b b),
  { exact (hb.mp h) h, },
  { exact h (hb.mpr h), },
end

-- 3ª demostración
example :
  ¬(∃ x : Hombre, ∀ y : Hombre, afeita x y ↔ ¬ afeita y y) :=
begin
  intro h,
  cases h with b hb,
  specialize hb b,
  by itauto,
end

-- 4ª demostración
example :
  ¬ (∃ x : Hombre,  ∀ y : Hombre, afeita x y ↔ ¬ afeita y y ) :=
begin
  rintro ⟨b, hb⟩,
  exact (iff_not_self (afeita b b)).mp (hb b),
end

-- 5ª demostración
example :
  ¬ (∃ x : Hombre,  ∀ y : Hombre, afeita x y ↔ ¬ afeita y y ) :=
λ ⟨b, hb⟩, (iff_not_self (afeita b b)).mp (hb b)
