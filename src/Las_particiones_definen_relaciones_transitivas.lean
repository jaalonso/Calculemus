-- Las_particiones_definen_relaciones_transitivas.lean
-- Las particiones definen relaciones transitivas
-- José A. Alonso Jiménez
-- Sevilla, 27 de agosto de 2021
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
-- definida por P es transitiva.
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
  : transitive (relacion P) :=
begin
  unfold transitive,
  intros x y z h1 h2,
  unfold relacion at *,
  rcases h1 with ⟨B1, hB1P, hxB1, hyB1⟩,
  rcases h2 with ⟨B2, hB2P, hyB2, hzB2⟩,
  use B1,
  repeat { split },
  { exact hB1P, },
  { exact hxB1, },
  { convert hzB2,
    rcases (h.1 y) with ⟨B, -, -, hB⟩,
    have hBB1 : B = B1 := hB B1 hB1P hyB1,
    have hBB2 : B = B2 := hB B2 hB2P hyB2,
    exact eq.trans hBB1.symm hBB2, },
end

-- 2ª demostración
example
  (h : particion P)
  : transitive (relacion P) :=
begin
  rintros x y z ⟨B1,hB1P,hxB1,hyB1⟩ ⟨B2,hB2P,hyB2,hzB2⟩,
  use B1,
  repeat { split },
  { exact hB1P, },
  { exact hxB1, },
  { convert hzB2,
    rcases (h.1 y) with ⟨B, -, -, hB⟩,
    exact eq.trans (hB B1 hB1P hyB1).symm (hB B2 hB2P hyB2), },
end

-- 3ª demostración
example
  (h : particion P)
  : transitive (relacion P) :=
begin
  rintros x y z ⟨B1,hB1P,hxB1,hyB1⟩ ⟨B2,hB2P,hyB2,hzB2⟩,
  use [B1, ⟨hB1P,
            hxB1,
            by { convert hzB2,
                 rcases (h.1 y) with ⟨B, -, -, hB⟩,
                 exact eq.trans (hB B1 hB1P hyB1).symm
                                (hB B2 hB2P hyB2), }⟩],
end
