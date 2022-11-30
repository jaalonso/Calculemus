-- Producto_por_funcion_acotada_superiormente.lean
-- Si c ≥ 0 y f está acotada superiormente, entonces c * f también lo está.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 30-noviembre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si c ≥ 0 y f está acotada superiormente, entonces c * f
-- también lo está.
-- ----------------------------------------------------------------------

import data.real.basic

variables {f : ℝ → ℝ}
variables {a c : ℝ}

-- (cota_superior f a) se verifica si a es una cota superior de f.
def cota_superior (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a

-- (acotada_sup f) se verifica si f tiene cota superior.
def acotada_sup (f : ℝ → ℝ) := ∃ a, cota_superior f a

-- Lema auxiliar
-- ============

lemma cota_superior_mul
  (hfa : cota_superior f a)
  (h : c ≥ 0)
  : cota_superior (λ x, c * f x) (c * a) :=
λ x, mul_le_mul_of_nonneg_left (hfa x) h

-- 1ª demostración
-- ===============

example
  (hf : acotada_sup f)
  (h : c ≥ 0)
  : acotada_sup (λ x, c * f x) :=
begin
  cases hf with a ha,
  have h1 : cota_superior (λ x, c * f x) (c * a) := cota_superior_mul ha h,
  have h2 : ∃ z, ∀ x, (λ x, c * f x) x ≤ z,
    by exact Exists.intro (c * a) h1,
  show acotada_sup (λ x, c * f x),
    by exact h2,
end

-- 2ª demostración
-- ===============

example
  (hf : acotada_sup f)
  (h : c ≥ 0)
  : acotada_sup (λ x, c * f x) :=
begin
  cases hf with a ha,
  use c * a,
  apply cota_superior_mul ha h,
end

-- 3ª demostración
-- ===============

example
  (hf : acotada_sup f)
  (h : c ≥ 0)
  : acotada_sup (λ x, c * f x) :=
begin
  rcases hf with ⟨a, ha⟩,
  exact ⟨c * a, cota_superior_mul ha h⟩,
end

-- 4ª demostración
-- ===============

example
  (h : c ≥ 0)
  : acotada_sup f → acotada_sup (λ x, c * f x) :=
begin
  rintro ⟨a, ha⟩,
  exact ⟨c * a, cota_superior_mul ha h⟩,
end

-- 5ª demostración
-- ===============

example
  (h : c ≥ 0)
  : acotada_sup f → acotada_sup (λ x, c * f x) :=
λ ⟨a, ha⟩, ⟨c * a, cota_superior_mul ha h⟩
