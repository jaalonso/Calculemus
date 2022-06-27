---
Título: Si g·f es suprayectiva, entonces g es suprayectiva.
Autor:  José A. Alonso
---

Demostrar que si g·f es suprayectiva, entonces g es suprayectiva.

Para ello, completar la siguiente teoría de Lean:
<pre lang="lean">
import tactic
open function

variables {X Y Z : Type}
variable  {f : X → Y}
variable  {g : Y → Z}

example
  (Hgf : surjective (g ∘ f))
  : surjective g :=
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
example
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
  (Hgf : surjective (g ∘ f))
  : surjective g  := 
begin
  assume z : Z,
  rcases Hgf z with ⟨x : X, hx : (g ∘ f) x = z⟩,
  let y : Y := f x,
  use y,
  show g y = z, from
    calc g y = g (f x)   : rfl
         ... = (g ∘ f) x : rfl
         ... = z         : hx,
end  
</pre>

El código de las demostraciones se encuentra en [GitHub](https://github.com/jaalonso/Calculemus/blob/main/src/Si_gf_es_suprayectiva_entonces_g_es_suprayectiva.lean) y puede ejecutarse con el [Lean Web editor](https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Si_gf_es_suprayectiva_entonces_g_es_suprayectiva.lean).



**Soluciones con Isabelle/HOL**

<pre lang="isar">
theory Si_gf_es_suprayectiva_entonces_g_es_suprayectiva
imports Main
begin 

lemma
  fixes   f :: "'a ⇒ 'b" and 
          g :: "'b ⇒ 'c"
  assumes "surj (g ∘ f)"
  shows   "surj g"
using assms by fastforce

end
</pre>
