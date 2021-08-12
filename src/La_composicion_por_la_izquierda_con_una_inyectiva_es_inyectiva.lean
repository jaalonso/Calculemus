-- La_composicion_por_la_izquierda_con_una_inyectiva_es_inyectiva.lean
-- La composición por la izquierda con una inyectiva es una operación inyectiva
-- José A. Alonso Jiménez
-- Sevilla, 11 de agosto de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sean f₁ y f₂ funciones de X en Y y g una función de X en Y. Demostrar
-- que si g es inyectiva y g ∘ f₁ = g ∘ f₂, entonces f₁ = f₂.
-- ---------------------------------------------------------------------

import tactic
open function

variables {X Y Z : Type*}
variables {f₁ f₂ : X → Y}
variable  {g : Y → Z}

-- 1ª demostración
example
  (hg : injective g)
  (hgf : g ∘ f₁ = g ∘ f₂)
  : f₁ = f₂ :=
begin
  funext,
  apply hg,
  calc g (f₁ x)
       = (g ∘ f₁) x : rfl
   ... = (g ∘ f₂) x : congr_fun hgf x
   ... = g (f₂ x)   : rfl,
end

-- 2ª demostración
example
  (hg : injective g)
  (hgf : g ∘ f₁ = g ∘ f₂)
  : f₁ = f₂ :=
begin
  funext,
  apply hg,
  exact congr_fun hgf x,
end

-- 3ª demostración
example
  (hg : injective g)
  (hgf : g ∘ f₁ = g ∘ f₂)
  : f₁ = f₂ :=
begin
  refine funext (λ i, hg _),
  exact congr_fun hgf i,
end

-- 4ª demostración
example
  (hg : injective g)
  : injective ((∘) g : (X → Y) → (X → Z)) :=
λ f₁ f₂ hgf, funext (λ i, hg (congr_fun hgf i : _))

-- 5ª demostración
example
  [hY : nonempty Y]
  (hg : injective g)
  (hgf : g ∘ f₁ = g ∘ f₂)
  : f₁ = f₂ :=
calc f₁ = id ∘ f₁              : (left_id f₁).symm
    ... = (inv_fun g ∘ g) ∘ f₁ : congr_arg2 (∘) (inv_fun_comp hg).symm rfl
    ... = inv_fun g ∘ (g ∘ f₁) : comp.assoc _ _ _
    ... = inv_fun g ∘ (g ∘ f₂) : congr_arg2 (∘) rfl hgf
    ... = (inv_fun g ∘ g) ∘ f₂ : comp.assoc _ _ _
    ... = id ∘ f₂              : congr_arg2 (∘) (inv_fun_comp hg) rfl
    ... = f₂                   : left_id f₂

-- 6ª demostración
example
  [hY : nonempty Y]
  (hg : injective g)
  (hgf : g ∘ f₁ = g ∘ f₂)
  : f₁ = f₂ :=
calc f₁ = id ∘ f₁              : by finish
    ... = (inv_fun g ∘ g) ∘ f₁ : by finish [inv_fun_comp]
    ... = inv_fun g ∘ (g ∘ f₁) : by refl
    ... = inv_fun g ∘ (g ∘ f₂) : by finish [hgf]
    ... = (inv_fun g ∘ g) ∘ f₂ : by refl
    ... = id ∘ f₂              : by finish [inv_fun_comp]
    ... = f₂                   : by finish
