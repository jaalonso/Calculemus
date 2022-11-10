-- Composicion_de_funciones_monotonas.lean
-- Si f y g son monótonas, entonces f ∘ g es monótona.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 10-noviembre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que la composición de dos funciones monótonas es monótona.
-- ----------------------------------------------------------------------

import data.real.basic

variables (f g : ℝ → ℝ)

-- 1ª demostración
-- ===============

example
  (mf : monotone f)
  (mg : monotone g)
  : monotone (f ∘ g) :=
begin
  have h1 : ∀ a b, a ≤ b → (f ∘ g) a ≤ (f ∘ g) b,
    { intros a b hab,
      have h1 : g a ≤ g b := mg hab,
      have h2 : f (g a) ≤ f (g b) := mf h1,
      show (f ∘ g) a ≤ (f ∘ g) b,
        by exact h2, },
  show monotone (f ∘ g),
    by exact h1,
end

-- 2ª demostración
-- ===============

example
  (mf : monotone f)
  (mg : monotone g)
  : monotone (f ∘ g) :=
begin
  intros a b hab,
  apply mf,
  apply mg,
  apply hab
end

-- 3ª demostración
-- ===============

example
  (mf : monotone f)
  (mg : monotone g)
  : monotone (f ∘ g) :=
λ a b hab, mf (mg hab)

-- 4ª demostración
-- ===============

example
  (mf : monotone f)
  (mg : monotone g)
  : monotone (f ∘ g) :=
-- by library_search
monotone.comp mf mg

-- 5ª demostración
-- ===============

example
  (mf : monotone f)
  (mg : monotone g)
  : monotone (f ∘ g) :=
-- by hint
by tauto
