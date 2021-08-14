-- Las_clases_de_equivalencia_de_elementos_no_relacionados_son_disjuntas.lean
-- Las clases de equivalencia de elementos no relacionados son disjuntas
-- José A. Alonso Jiménez
-- Sevilla, 23 de agosto de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que las clases de equivalencia de elementos no relacionados
-- son disjuntas.
-- ---------------------------------------------------------------------

import tactic

variable  {X : Type}
variables {x y: X}
variable  {R : X → X → Prop}

def clase (R : X → X → Prop) (x : X) :=
  {y : X | R x y}

-- 1ª demostración
example
  (h : equivalence R)
  (hxy : ¬ R x y)
  : clase R x ∩ clase R y = ∅ :=
begin
  rcases h with ⟨hr, hs, ht⟩,
  by_contradiction h1,
  apply hxy,
  have h2 : ∃ z, z ∈ clase R x ∩ clase R y,
    { contrapose h1,
      intro h1a,
      apply h1a,
      push_neg at h1,
      exact set.eq_empty_iff_forall_not_mem.mpr h1, },
  rcases h2 with ⟨z, hxz, hyz⟩,
  replace hxz : R x z := hxz,
  replace hyz : R y z := hyz,
  have hzy : R z y := hs hyz,
  exact ht hxz hzy,
end

-- 2ª demostración
example
  (h : equivalence R)
  (hxy : ¬ R x y)
  : clase R x ∩ clase R y = ∅ :=
begin
  rcases h with ⟨hr, hs, ht⟩,
  by_contradiction h1,
  have h2 : ∃ z, z ∈ clase R x ∩ clase R y,
    { by finish [set.eq_empty_iff_forall_not_mem]},
  apply hxy,
  rcases h2 with ⟨z, hxz, hyz⟩,
  exact ht hxz (hs hyz),
end
