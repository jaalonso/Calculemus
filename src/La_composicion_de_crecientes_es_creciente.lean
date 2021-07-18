-- La_composicion_de_crecientes_es_creciente.lean
-- La composición de crecientes es creciente
-- José A. Alonso Jiménez
-- Sevilla, 19 de julio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Se dice que una función f de ℝ en ℝ es creciente https://bit.ly/2UShggL
-- si para todo x e y tales que x ≤ y se tiene que f(x) ≤ f(y).
--
-- En Lean que f sea creciente se representa por `monotone f`.
--
-- Demostrar que la composición de dos funciones crecientes es una
-- función creciente.
-- ---------------------------------------------------------------------

import data.real.basic

variables (f g : ℝ → ℝ)

-- 1ª demostración
example
  (hf : monotone f)
  (hg : monotone g)
  : monotone (g ∘ f) :=
begin
  intros x y hxy,
  calc (g ∘ f) x
       = g (f x)   : rfl
   ... ≤ g (f y)   : hg (hf hxy)
   ... = (g ∘ f) y : rfl,
end

-- 2ª demostración
example
  (hf : monotone f)
  (hg : monotone g)
  : monotone (g ∘ f) :=
begin
  unfold monotone at *,
  intros x y h,
  unfold function.comp,
  apply hg,
  apply hf,
  exact h,
end

-- 3ª demostración
example
  (hf : monotone f)
  (hg : monotone g)
  : monotone (g ∘ f) :=
begin
  intros x y h,
  apply hg,
  apply hf,
  exact h,
end

-- 4ª demostración
example
  (hf : monotone f)
  (hg : monotone g)
  : monotone (g ∘ f) :=
begin
  intros x xy h,
  apply hg,
  exact hf h,
end

-- 5ª demostración
example
  (hf : monotone f)
  (hg : monotone g)
  : monotone (g ∘ f) :=
begin
  intros x y h,
  exact hg (hf h),
end

-- 6ª demostración
example
  (hf : monotone f)
  (hg : monotone g)
  : monotone (g ∘ f) :=
λ x y h, hg (hf h)

-- 7ª demostración
example
  (hf : monotone f)
  (hg : monotone g)
  : monotone (g ∘ f) :=
begin
  intros x y h,
  specialize hf h,
  exact hg hf,
end

-- 8ª demostración
example
  (hf : monotone f)
  (hg : monotone g)
  : monotone (g ∘ f) :=
assume x y,
assume h1 : x ≤ y,
have h2 : f x ≤ f y,
  from hf h1,
show (g ∘ f) x ≤ (g ∘ f) y, from
  calc (g ∘ f) x
       = g (f x)   : rfl
   ... ≤ g (f y)   : hg h2
   ... = (g ∘ f) y : by refl

-- 9ª demostración
example
  (hf : monotone f)
  (hg : monotone g)
  : monotone (g ∘ f) :=
-- by hint
by tauto

-- 10ª demostración
example
  (hf : monotone f)
  (hg : monotone g)
  : monotone (g ∘ f) :=
-- by library_search
monotone.comp hg hf
