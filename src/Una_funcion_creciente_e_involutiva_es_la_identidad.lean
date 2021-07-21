-- Una_funcion_creciente_e_involutiva_es_la_identidad.lean
-- Una función creciente e involutiva es la identidad
-- José A. Alonso Jiménez
-- Sevilla, 21 de julio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sea una función f de ℝ en ℝ.
-- + Se dice que f es creciente si para todo x e y tales que x ≤ y se
--   tiene que f(x) ≤ f(y).
-- + Se dice que f es involutiva si para todo x se tiene que f(f(x)) = x.
--
-- En Lean que f sea creciente se representa por `monotone f` y que sea
-- involutiva por `involutive f`
--
-- Demostrar que si f es creciente e involutiva, entonces f es la
-- identidad.
-- ---------------------------------------------------------------------

import data.real.basic
open function

variable (f : ℝ → ℝ)

-- 1ª demostración
example
  (hc : monotone f)
  (hi : involutive f)
  : f = id :=
begin
  unfold monotone involutive at *,
  funext,
  unfold id,
  cases (le_total (f x) x) with h1 h2,
  { apply antisymm h1,
    have h3 : f (f x) ≤ f x,
      { apply hc,
        exact h1, },
    rwa hi at h3, },
  { apply antisymm _ h2,
    have h4 : f x ≤ f (f x),
      { apply hc,
        exact h2, },
    rwa hi at h4, },
end

-- 2ª demostración
example
  (hc : monotone f)
  (hi : involutive f)
  : f = id :=
begin
  funext,
  cases (le_total (f x) x) with h1 h2,
  { apply antisymm h1,
    have h3 : f (f x) ≤ f x := hc h1,
    rwa hi at h3, },
  { apply antisymm _ h2,
    have h4 : f x ≤ f (f x) := hc h2,
    rwa hi at h4, },
end

-- 3ª demostración
example
  (hc : monotone f)
  (hi : involutive f)
  : f = id :=
begin
  funext,
  cases (le_total (f x) x) with h1 h2,
  { apply antisymm h1,
    calc x
         = f (f x) : (hi x).symm
     ... ≤ f x     : hc h1 },
  { apply antisymm _ h2,
    calc f x
         ≤ f (f x) : hc h2
     ... = x       : hi x },
end
