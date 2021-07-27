-- Propiedad_de_la_densidad_de_los_reales.lean
-- Propiedad de la densidad de los reales
-- José A. Alonso Jiménez
-- Sevilla, 27 de julio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sean x, y números reales tales que
--    ∀ z, y < z → x ≤ z
-- Demostrar que x ≤ y.
-- ---------------------------------------------------------------------

import data.real.basic

variables {x y : ℝ}

-- 1ª demostración
example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
begin
  apply le_of_not_gt,
  intro hxy,
  cases (exists_between hxy) with a ha,
  apply (lt_irrefl a),
  calc a
       < x : ha.2
   ... ≤ a : h a ha.1,
end

-- 2ª demostración
example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
begin
  apply le_of_not_gt,
  intro hxy,
  cases (exists_between hxy) with a ha,
  apply (lt_irrefl a),
  exact lt_of_lt_of_le ha.2 (h a ha.1),
end

-- 3ª demostración
example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
begin
  apply le_of_not_gt,
  intro hxy,
  cases (exists_between hxy) with a ha,
  exact (lt_irrefl a) (lt_of_lt_of_le ha.2 (h a ha.1)),
end

-- 3ª demostración
example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
begin
  apply le_of_not_gt,
  intro hxy,
  rcases (exists_between hxy) with ⟨a, ha⟩,
  exact (lt_irrefl a) (lt_of_lt_of_le ha.2 (h a ha.1)),
end

-- 4ª demostración
example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
begin
  apply le_of_not_gt,
  intro hxy,
  rcases (exists_between hxy) with ⟨a, hya, hax⟩,
  exact (lt_irrefl a) (lt_of_lt_of_le hax (h a hya)),
end

-- 5ª demostración
example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
le_of_not_gt (λ hxy,
  let ⟨a, hya, hax⟩ := exists_between hxy in
  lt_irrefl a (lt_of_lt_of_le hax (h a hya)))

-- 6ª demostración
example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
le_of_forall_le_of_dense h
