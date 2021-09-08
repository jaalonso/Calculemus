-- Si_x_es_el_supremo_de_A,_entonces_forall__y,_y_lt_x_to_exists_a_in_A,_y_lt_a.lean
-- Si x es el supremo de A, entonces ∀ y, y < x → ∃ a ∈ A, y < a
-- José A. Alonso Jiménez
-- Sevilla, 14 de septiembre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean se puede definir que x es una cota superior de A por
--    def cota_superior (A : set ℝ) (x : ℝ) :=
--      ∀ a ∈ A, a ≤ x
-- y x es el supremo de A por
--    def es_supremo (A : set ℝ) (x : ℝ) :=
--      cota_superior A x ∧ ∀ y, cota_superior A y → x ≤ y
--
-- Demostrar que si x es el supremo de A, entonces
--    ∀ y, y < x → ∃ a ∈ A, y < a
-- ---------------------------------------------------------------------

import data.real.basic
variable {A : set ℝ}
variable {x : ℝ}

def cota_superior (A : set ℝ) (x : ℝ) :=
  ∀ a ∈ A, a ≤ x

def es_supremo (A : set ℝ) (x : ℝ) :=
  cota_superior A x ∧ ∀ y, cota_superior A y → x ≤ y

-- 1ª demostración
example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
begin
  intros y hy,
  by_contradiction,
  push_neg at h,
  have h1 : x ≤ y := hx.2 y h,
  replace h1 : ¬(y < x) := not_lt_of_le h1,
  exact h1 hy,
end

-- 2ª demostración
example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
begin
  intros y hy,
  by_contradiction,
  push_neg at h,
  apply absurd hy,
  apply not_lt_of_le,
  apply hx.2 y,
  exact h,
end

-- 3ª demostración
example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
begin
  intros y hy,
  by_contradiction,
  push_neg at h,
  exact absurd hy (not_lt_of_le (hx.2 y h)),
end

-- 4ª demostración
example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
begin
  intros y hy,
  contrapose hy,
  push_neg at hy,
  push_neg,
  unfold es_supremo at hx,
  cases hx with h1 h2,
  apply h2 y,
  unfold cota_superior,
  exact hy,
end

-- 5ª demostración
example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
begin
  intros y hy,
  contrapose hy,
  push_neg at hy,
  push_neg,
  cases hx with h1 h2,
  exact h2 y hy,
end

-- 6ª demostración
example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
begin
  intros y hy,
  contrapose hy,
  push_neg at hy,
  push_neg,
  exact hx.right y hy,
end

-- 7ª demostración
example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
begin
  intro y,
  contrapose!,
  exact hx.right y,
end
