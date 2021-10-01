-- Las_clases_de_equivalencia_son_no_vacias.lean
-- Las clases de equivalencia son no vacías
-- José A. Alonso Jiménez
-- Sevilla, 5 de octubre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Este ejercicio es el 6º de una serie, que comenzó con el [ejercicio
-- del 30 de septiembre](https://bit.ly/2YfsvBZ), cuyo objetivo es
-- demostrar que el tipo de las particiones de un conjunto `X` es
-- isomorfo al tipo de las relaciones de equivalencia sobre `X`.
--
-- El conjuntos de las clases correspondientes a una relación R se
-- define en Lean por
 --    def clases : (A → A → Prop) → set (set A) :=
 --      λ R, {B : set A | ∃ x : A, B = clase R x}
--
-- El ejercicio consiste en demostrar que si C es una clase de
-- equivalencia de R, entonces C es no vacía.
-- ---------------------------------------------------------------------

import tactic

variable {A : Type}
variable (R : A → A → Prop)

def clase (a : A) :=
  {b : A | R b a}

def clases : (A → A → Prop) → set (set A) :=
  λ R, {B : set A | ∃ x : A, B = clase R x}

-- Se usará el siguientes lema auxiliar
lemma pertenece_clase_syss
  {a b : A}
  : b ∈ clase R a ↔ R b a :=
by refl

-- 1ª demostración
example
  (hR: equivalence R)
  : ∀ (X : set A), X ∈ clases R → X.nonempty :=
begin
  intros X hX,
  unfold clases at hX,
  dsimp at hX,
  cases hX with a ha,
  rw ha,
  rw set.nonempty_def,
  use a,
  rw pertenece_clase_syss,
  rcases hR with ⟨hrefl, -, -⟩,
  exact hrefl a,
end

-- 2ª demostración
example
  (hR: equivalence R)
  : ∀ (X : set A), X ∈ clases R → X.nonempty :=
begin
  rintros _ ⟨a, rfl⟩,
  use a,
  rw pertenece_clase_syss,
  exact hR.1 a,
end

-- 3ª demostración
example
  (hR: equivalence R)
  : ∀ (X : set A), X ∈ clases R → X.nonempty :=
begin
  rintros _ ⟨a, rfl⟩,
  use a,
  rw pertenece_clase_syss,
  apply hR.1,
end

-- 4ª demostración
lemma clases_no_vacias
  (hR: equivalence R)
  : ∀ (X : set A), X ∈ clases R → X.nonempty :=
begin
  rintros _ ⟨a, rfl⟩,
  use a,
  exact (pertenece_clase_syss R).mpr (hR.1 a),
end
