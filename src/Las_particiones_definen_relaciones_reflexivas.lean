-- Las_particiones_definen_relaciones_reflexivas.lean
-- Las particiones definen relaciones reflexivas
-- José A. Alonso Jiménez
-- Sevilla, 25 de agosto de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Cada familia de conjuntos P define una relación de forma que dos
-- elementos están relacionados si algún conjunto de P contiene a ambos
-- elementos. Se puede definir en Lean por
--    def relacion (P : set (set X)) (x y : X) :=
--      ∃ A ∈ P, x ∈ A ∧ y ∈ A
--
-- Una familia de subconjuntos de X es una partición de X si cada elemento
-- de X pertenece a un único conjunto de P y todos los elementos de P
-- son no vacíos. Se puede definir en Lean por
--    def particion (P : set (set X)) : Prop :=
--      (∀ x, (∃ B ∈ P, x ∈ B ∧ ∀ C ∈ P, x ∈ C → B = C)) ∧ ∅ ∉ P
--
-- Demostrar que si P es una partición de X, entonces la relación
-- definida por P es reflexiva.
-- ---------------------------------------------------------------------

import tactic

variable {X : Type}
variable (P : set (set X))

def relacion (P : set (set X)) (x y : X) :=
  ∃ A ∈ P, x ∈ A ∧ y ∈ A

def particion (P : set (set X)) : Prop :=
  (∀ x, (∃ B ∈ P, x ∈ B ∧ ∀ C ∈ P, x ∈ C → B = C)) ∧ ∅ ∉ P

-- 1ª demostración
example
  (h : particion P)
  : reflexive (relacion P) :=
begin
  unfold reflexive,
  intro x,
  unfold relacion,
  unfold particion at h,
  replace h : ∃ A ∈ P, x ∈ A ∧ ∀ B ∈ P, x ∈ B → A = B := h.1 x,
  rcases h with ⟨A, hAP, hxA, -⟩,
  use A,
  repeat { split },
  { exact hAP, },
  { exact hxA, },
  { exact hxA, },
end

-- 2ª demostración
example
  (h : particion P)
  : reflexive (relacion P) :=
begin
  intro x,
  replace h : ∃ A ∈ P, x ∈ A ∧ ∀ B ∈ P, x ∈ B → A = B := h.1 x,
  rcases h with ⟨A, hAP, hxA, -⟩,
  use A,
  repeat { split } ; assumption,
end

-- 3ª demostración
example
  (h : particion P)
  : reflexive (relacion P) :=
begin
  intro x,
  rcases (h.1 x) with ⟨A, hAP, hxA, -⟩,
  use A,
  repeat { split } ; assumption,
end

-- 4ª demostración
example
  (h : particion P)
  : reflexive (relacion P) :=
begin
  intro x,
  rcases (h.1 x) with ⟨A, hAP, hxA, -⟩,
  use [A, ⟨hAP, hxA, hxA⟩],
end
