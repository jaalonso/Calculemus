-- Pertenencia_a_su_propia_clase_de_equivalencia.lean
-- Pertenencia a su propia clase de equivalencia
-- José A. Alonso Jiménez
-- Sevilla, 2 de octubre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Este ejercicio es el 3º de una serie, que comenzó con el [ejercicio
-- del 30 de septiembre](https://bit.ly/2YfsvBZ), cuyo objetivo es
-- demostrar que el tipo de las particiones de un conjunto `X` es
-- isomorfo al tipo de las relaciones de equivalencia sobre `X`.
--
-- Los anteriores fueron sobre particiones y con este empezamos con las
-- relaciones de equivalencia que están definidas en Lean por:
--    reflexive R := ∀ (x : A), R x x
--    symmetric R := ∀ ⦃x y : A⦄, R x y → R y x
--    transitive R := ∀ ⦃x y z : A⦄, R x y → R y z → R x z
--    equivalence R := reflexive R ∧ symmetric R ∧ transitive R
-- donde `A` un tipo y `R: A → A → Prop` es una relación binaria en `A`.
--
-- Además, en Lean se puede definir la clase de equivalencia de un
-- elemento `a` respecto de una relación de equivalencia `R` por
--    def clase (a : A) :=
--      {b : A | R b a}
--
-- Demostrar que cada elemento pertenece a su clase de equivalencia.
-- ---------------------------------------------------------------------

import tactic

variable {A : Type}
variable (R : A → A → Prop)

def clase (a : A) :=
  {b : A | R b a}

-- Se usará el siguiente lema auxiliar
lemma pertenece_clase_syss
  {a b : A}
  : b ∈ clase R a ↔ R b a :=
by refl

-- 1ª demostración
example
  {hR : equivalence R}
  (a : A)
  : a ∈ clase R a :=
begin
  rw pertenece_clase_syss,
  suffices h : reflexive R,
  { exact h a, },
  { rcases hR with ⟨h2, -, -⟩,
    exact h2, },
end

-- 2ª demostración
example
  {hR : equivalence R}
  (a : A)
  : a ∈ clase R a :=
begin
  rw pertenece_clase_syss,
  suffices h : reflexive R,
  { exact h a, },
  { exact hR.1, },
end

-- 3ª demostración
example
  {hR : equivalence R}
  (a : A)
  : a ∈ clase R a :=
begin
  rw pertenece_clase_syss,
  rcases hR with ⟨hrefl, -, -⟩,
  exact hrefl a,
end

-- 4ª demostración
example
  {hR : equivalence R}
  (a : A)
  : a ∈ clase R a :=
begin
  obtain ⟨hrefl, -, -⟩ := hR,
  rw pertenece_clase_syss,
  apply hrefl,
end

-- 5ª demostración
example
  {hR : equivalence R}
  (a : A)
  : a ∈ clase R a :=
begin
  rw pertenece_clase_syss,
  apply hR.1,
end

-- 6ª demostración
lemma pertenece_clase_propia
  {hR : equivalence R}
  (a : A)
  : a ∈ clase R a :=
(pertenece_clase_syss R).mpr (hR.1 a)