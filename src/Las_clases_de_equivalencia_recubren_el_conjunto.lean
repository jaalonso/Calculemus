-- Las_clases_de_equivalencia_recubren_el_conjunto.lean
-- Las clases de equivalencia recubren el conjunto
-- José A. Alonso Jiménez
-- Sevilla, 6 de octubre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Este ejercicio es el 7º de una serie, que comenzó con el [ejercicio
-- del 30 de septiembre](https://bit.ly/2YfsvBZ), cuyo objetivo es
-- demostrar que el tipo de las particiones de un conjunto `X` es
-- isomorfo al tipo de las relaciones de equivalencia sobre `X`.
--
-- El ejercicio consiste en demostrar que si R es una relación de
-- equivalencia en A, entonces las clases de equivalencia de R recubren
-- a A.
-- ---------------------------------------------------------------------

import tactic

variable {A : Type}
variable (R : A → A → Prop)

def clase (a : A) :=
  {b : A | R b a}

def clases : (A → A → Prop) → set (set A) :=
  λ R, {B : set A | ∃ x : A, B = clase R x}

-- Se usarán los dos siguientes lemas auxiliares
lemma pertenece_clase_syss
  {a b : A}
  : b ∈ clase R a ↔ R b a :=
by refl

lemma pertenece_clase_propia
  {R : A → A → Prop}
  (hR: equivalence R)
  (a : A)
  : a ∈ clase R a :=
(pertenece_clase_syss R).mpr (hR.1 a)

-- 1ª demostración,
example
  (hR: equivalence R)
  : ∀ a, ∃ X ∈ clases R, a ∈ X :=
begin
  intro a,
  use clase R a,
  split,
  { unfold clases,
    dsimp,
    use a, },
  { exact pertenece_clase_propia hR a, },
end

-- 2ª demostración,
lemma clases_recubren
  (hR: equivalence R)
  : ∀ a, ∃ X ∈ clases R, a ∈ X :=
begin
  intro a,
  use clase R a,
  split,
  { use a, },
  { exact hR.1 a, },
end
