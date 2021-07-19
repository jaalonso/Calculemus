-- La_composicion_de_una_funcion_creciente_y_una_decreciente_es_decreciente.lean
-- La composición de una función creciente y una decreciente es decreciente
-- José A. Alonso Jiménez
-- Sevilla, 20 de julio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sea una función f de ℝ en ℝ. Se dice que f es creciente
-- https://bit.ly/2UShggL si para todo x e y tales que x ≤ y se tiene
-- que f(x) ≤ f(y). Se dice que f es decreciente si para todo x e y
-- tales que x ≤ y se tiene que f(x) ≥ f(y).
--
-- Demostrar que si f es creciente y g es decreciente, entonces (g ∘ f)
-- es decreciente.
-- ---------------------------------------------------------------------

import data.real.basic

variables (f g : ℝ → ℝ)

def creciente (f : ℝ → ℝ) : Prop :=
∀ {x y}, x ≤ y → f x ≤ f y

def decreciente (f : ℝ → ℝ) : Prop :=
∀ {x y}, x ≤ y → f x ≥ f y

-- 1ª demostración
example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
begin
  intros x y hxy,
  calc (g ∘ f) x
       = g (f x)   : rfl
   ... ≥ g (f y)   : hg (hf hxy)
   ... = (g ∘ f) y : rfl,
end

-- 2ª demostración
example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
begin
  unfold creciente decreciente at *,
  intros x y h,
  unfold function.comp,
  apply hg,
  apply hf,
  exact h,
end

-- 3ª demostración
example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
begin
  intros x y h,
  apply hg,
  apply hf,
  exact h,
end

-- 4ª demostración
example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
begin
  intros x y h,
  apply hg,
  exact hf h,
end

-- 5ª demostración
example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
begin
  intros x y h,
  exact hg (hf h),
end

-- 6ª demostración
example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
λ x y h, hg (hf h)

-- 7ª demostración
example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
assume x y,
assume h : x ≤ y,
have h1 : f x ≤ f y,
  from hf h,
show (g ∘ f) x ≥ (g ∘ f) y,
  from hg h1

-- 8ª demostración
example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
assume x y,
assume h : x ≤ y,
show (g ∘ f) x ≥ (g ∘ f) y,
  from hg (hf h)

-- 9ª demostración
example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
λ x y h, hg (hf h)

-- 10ª demostración
example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
-- by hint
by tauto
