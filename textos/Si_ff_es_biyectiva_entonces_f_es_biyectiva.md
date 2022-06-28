---
Título: Si f·f es biyectiva, entonces f es biyectiva.
Autor:  José A. Alonso
---

Demostrar que si f·f es biyectiva, entonces f es biyectiva.

Para ello, completar la siguiente teoría de Lean:
<pre lang="lean">
import tactic
open function

variable {X: Type}

example
  (f : X → X)
  (Hff : bijective (f ∘ f))
  : bijective f :=
sorry
</pre>

<!--more-->

**Soluciones con Lean**

<pre lang="lean">
import tactic
open function

variables {X Y Z : Type}
variable  {f : X → Y}
variable  {g : Y → Z}

-- 1ª demostración
-- ===============

lemma iny_comp_iny_primera
  (Hgf : injective (g ∘ f))
  : injective f :=
begin
  intros x x' f_xx',
  apply Hgf,
  finish,
end

lemma supr_comp_supr_segunda
  (Hgf : surjective (g ∘ f))
  : surjective g :=
begin
  intros z,
  rcases Hgf z with ⟨x, hx⟩,
  use f x,
  calc g (f x) = (g ∘ f) x : rfl
           ... = z         : hx,
end

example
  (f : X → X)
  (Hff : bijective (f ∘ f))
  : bijective f :=
begin
  split,
  { have h1 : injective (f ∘ f) := bijective.injective Hff,
    exact iny_comp_iny_primera h1, },
  { have h2 : surjective (f ∘ f) := bijective.surjective Hff,
    exact supr_comp_supr_segunda h2, },
end
</pre>

El código de las demostraciones se encuentra en [GitHub](https://github.com/jaalonso/Calculemus/blob/main/src/Si_ff_es_biyectiva_entonces_f_es_biyectiva.lean) y puede ejecutarse con el [Lean Web editor](https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Si_ff_es_biyectiva_entonces_f_es_biyectiva.lean).

**Soluciones con Isabelle/HOL**

<pre lang="isar">
theory Si_ff_es_biyectiva_entonces_f_es_biyectiva
imports Main
begin 

lemma
  assumes "bij (f ∘ f)"
  shows   "bij f"
proof (rule bijI)
  show "inj f" 
  proof -
    have h1 : "inj (f ∘ f)"
      using assms by (simp only: bij_is_inj)
    then show "inj f"
      by (simp only: inj_on_imageI2)
  qed 
next
  show "surj f"
  proof -
    have h2 : "surj (f ∘ f)"
      using assms by (simp only: bij_is_surj)
    then show "surj f"
      by auto
  qed
qed

end
</pre>
