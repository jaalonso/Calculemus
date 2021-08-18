-- El_conjunto_de_las_clases_de_equivalencia_es_una_particion.lean
-- El conjunto de las clases de equivalencia es una partición.
-- José A. Alonso Jiménez
-- Sevilla, 24 de agosto de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si R es una relación de equivalencia en X, entonces las
-- clases de equivalencia de R es una partición de X.
-- ---------------------------------------------------------------------

import tactic

variable  {X : Type}
variables {x y: X}
variable  {R : X → X → Prop}

def clase (R : X → X → Prop) (x : X) :=
  {y : X | R x y}

def particion (A : set (set X)) : Prop :=
  (∀ x, (∃ B ∈ A, x ∈ B ∧ ∀ C ∈ A, x ∈ C → B = C)) ∧ ∅ ∉ A

lemma aux
  (h : equivalence R)
  (hxy : R x y)
  : clase R y ⊆ clase R x :=
λ z hz, h.2.2 hxy hz

-- 1ª demostración
example
  (h : equivalence R)
  : particion {a : set X | ∃ s : X, a = clase R s} :=
begin
  split,
  { simp,
    intro y,
    use (clase R y),
    split,
    { use y, },
    { split,
      { exact h.1 y, },
      { intros x hx,
        apply le_antisymm,
        { exact aux h hx, },
        { exact aux h (h.2.1 hx), }}}},
  { simp,
    intros x hx,
    have h1 : x ∈ clase R x := h.1 x,
    rw ← hx at h1,
    exact set.not_mem_empty x h1, },
end

-- 2ª demostración
example
  (h : equivalence R)
  : particion {a : set X | ∃ s : X, a = clase R s} :=
begin
  split,
  { simp,
    intro y,
    use (clase R y),
    split,
    { use y, },
    { split,
      { exact h.1 y, },
      { intros x hx,
        exact le_antisymm (aux h hx) (aux h (h.2.1 hx)), }}},
  { simp,
    intros x hx,
    have h1 : x ∈ clase R x := h.1 x,
    rw ← hx at h1,
    exact set.not_mem_empty x h1, },
end

-- 3ª demostración
example
  (h : equivalence R)
  : particion {a : set X | ∃ s : X, a = clase R s} :=
begin
  split,
  { simp,
    intro y,
    use [clase R y,
         ⟨by use y,
          ⟨h.1 y, λ x hx, le_antisymm (aux h hx) (aux h (h.2.1 hx))⟩⟩], },
  { simp,
    intros x hx,
    have h1 : x ∈ clase R x := h.1 x,
    rw ← hx at h1,
    exact set.not_mem_empty x h1, },
end
