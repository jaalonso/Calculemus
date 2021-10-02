-- Las_clases_de_equivalencia_son_disjuntas.lean
-- Las clases de equivalencia son disjuntas
-- José A. Alonso Jiménez
-- Sevilla, 7 de octubre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Este ejercicio es el 8º de una serie, que comenzó con el [ejercicio
-- del 30 de septiembre](https://bit.ly/2YfsvBZ), cuyo objetivo es
-- demostrar que el tipo de las particiones de un conjunto `X` es
-- isomorfo al tipo de las relaciones de equivalencia sobre `X`.
--
-- El ejercicio consiste en demostrar que si R es una relación de
-- equivalencia en A, entonces las clases de equivalencia de R son
-- disjuntas.
-- ---------------------------------------------------------------------

import tactic

variable {A : Type}
variable (R : A → A → Prop)

def clase (a : A) :=
  {b : A | R b a}

def clases : (A → A → Prop) → set (set A) :=
  λ R, {B : set A | ∃ x : A, B = clase R x}

-- Se usarán los dos siguientes lemas auxiliares
lemma subclase_si_pertenece
  {R : A → A → Prop}
  (hR: equivalence R)
  {a b : A}
  : a ∈ clase R b → clase R a ⊆ clase R b :=
λ hab z hza, hR.2.2 hza hab

lemma clases_iguales_si_pertenece
  {R : A → A → Prop}
  (hR: equivalence R)
  {a b : A}
  : a ∈ clase R b → clase R a = clase R b :=
λ hab, set.subset.antisymm
        (subclase_si_pertenece hR hab)
        (subclase_si_pertenece hR (hR.2.1 hab))

-- 1ª demostración
example
  (hR: equivalence R)
  : ∀ X Y ∈ clases R, (X ∩ Y : set A).nonempty → X = Y :=
begin
  intros X Y hX hY hXY,
  unfold clases at hX hY,
  dsimp at hX hY,
  cases hX with a ha,
  cases hY with b hb,
  rw [ha, hb] at *,
  rw set.nonempty_def at hXY,
  cases hXY with c hc,
  cases hc with hca hcb,
  apply clases_iguales_si_pertenece hR,
  apply hR.2.2 _ hcb,
  apply hR.2.1,
  exact hca,
end

-- 2ª demostración
example
  (hR: equivalence R)
  : ∀ X Y ∈ clases R, (X ∩ Y : set A).nonempty → X = Y :=
begin
  intros X Y hX hY hXY,
  cases hX with a ha,
  cases hY with b hb,
  rw [ha, hb] at *,
  rw set.nonempty_def at hXY,
  cases hXY with c hc,
  cases hc with hca hcb,
  apply clases_iguales_si_pertenece hR,
  apply hR.2.2 _ hcb,
  apply hR.2.1,
  exact hca,
end

-- 3ª demostración
example
  (hR: equivalence R)
  : ∀ X Y ∈ clases R, (X ∩ Y : set A).nonempty → X = Y :=
begin
  rintros X Y ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨c, hca, hcb⟩,
  apply clases_iguales_si_pertenece hR,
  apply hR.2.2 _ hcb,
  apply hR.2.1,
  exact hca,
end

-- 4ª demostración
lemma clases_disjuntas
  (hR: equivalence R)
  : ∀ X Y ∈ clases R, (X ∩ Y : set A).nonempty → X = Y :=
begin
  rintros X Y ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨c, hca, hcb⟩,
  exact clases_iguales_si_pertenece hR (hR.2.2 (hR.2.1 hca) hcb),
end
