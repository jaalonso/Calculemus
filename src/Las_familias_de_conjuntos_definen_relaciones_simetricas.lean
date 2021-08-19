-- Las_familias_de_conjuntos_definen_relaciones_simetricas.lean
-- Las familias de conjuntos definen relaciones simétricas
-- José A. Alonso Jiménez
-- Sevilla, 26 de agosto de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Cada familia de conjuntos P define una relación de forma que dos
-- elementos están relacionados si algún conjunto de P contiene a ambos
-- elementos. Se puede definir en Lean por
--    def relacion (P : set (set X)) (x y : X) :=
--      ∃ A ∈ P, x ∈ A ∧ y ∈ A
--
-- Demostrar que si P es una familia de subconjunt❙os de X, entonces la
-- relación definida por P es simétrica.
-- ---------------------------------------------------------------------

import tactic

variable {X : Type}
variable (P : set (set X))

def relacion (P : set (set X)) (x y : X) :=
  ∃ A ∈ P, x ∈ A ∧ y ∈ A

-- 1ª demostración
example : symmetric (relacion P) :=
begin
  unfold symmetric,
  intros x y hxy,
  unfold relacion at *,
  rcases hxy with ⟨B, hBP, ⟨hxB, hyB⟩⟩,
  use B,
  repeat { split },
  { exact hBP, },
  { exact hyB, },
  { exact hxB, },
end

-- 2ª demostración
example : symmetric (relacion P) :=
begin
  intros x y hxy,
  rcases hxy with ⟨B, hBP, ⟨hxB, hyB⟩⟩,
  use B,
  repeat { split } ;
  assumption,
end

-- 3ª demostración
example : symmetric (relacion P) :=
begin
  intros x y hxy,
  rcases hxy with ⟨B, hBP, ⟨hxB, hyB⟩⟩,
  use [B, ⟨hBP, hyB, hxB⟩],
end
