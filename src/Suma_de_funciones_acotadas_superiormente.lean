-- Suma_de_funciones_acotadas_superiormente.lean
-- La suma de dos funciones acotadas superiormente también lo está.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 28-noviembre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que la suma de dos funciones acotadas superiormente también
-- lo está.
-- ----------------------------------------------------------------------

import data.real.basic

variables {f g : ℝ → ℝ}
variables {a b : ℝ}

-- (cota_superior f a) se verifica si a es una cota superior de f.
def cota_superior (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a

-- (acotada_sup f) afirma que f tiene cota superior.
def acotada_sup (f : ℝ → ℝ) := ∃ a, cota_superior f a

-- Lema auxiliar
-- =============

lemma cota_superior_suma
  (hfa : cota_superior f a)
  (hgb : cota_superior g b)
  : cota_superior (f + g) (a + b) :=
λ x, add_le_add (hfa x) (hgb x)

-- 1ª demostración
-- ===============

example
  (hf : acotada_sup f)
  (hg : acotada_sup g)
  : acotada_sup (f + g) :=
begin
  cases hf with a hfa,
  cases hg with b hgb,
  have h3 : cota_superior (f + g) (a + b) :=
    cota_superior_suma hfa hgb,
  have h4 : ∃ z, ∀ x, (f + g) x ≤ z,
    by exact Exists.intro (a + b) h3,
  show acotada_sup (f + g),
    by exact h4,
end

-- 2ª demostración
-- ===============

example
  (hf : acotada_sup f)
  (hg : acotada_sup g)
  : acotada_sup (f + g) :=
begin
  cases hf with a hfa,
  cases hg with b hfb,
  use a + b,
  apply cota_superior_suma hfa hfb,
end

-- 3ª demostración
-- ===============

example
  (hf : acotada_sup f)
  (hg : acotada_sup g)
  : acotada_sup (f + g) :=
begin
  rcases hf with ⟨a, hfa⟩,
  rcases hg with ⟨b, hfb⟩,
  exact ⟨a + b, cota_superior_suma hfa hfb⟩
end

-- 4ª demostración
-- ===============

example :
  acotada_sup f → acotada_sup g → acotada_sup (f + g) :=
begin
  rintros ⟨a, hfa⟩ ⟨b, hfb⟩,
  exact ⟨a + b, cota_superior_suma hfa hfb⟩,
end

-- 5ª demostración
-- ===============

example :
  acotada_sup f → acotada_sup g → acotada_sup (f + g) :=
λ ⟨a, hfa⟩ ⟨b, hfb⟩, ⟨a + b, cota_superior_suma hfa hfb⟩
