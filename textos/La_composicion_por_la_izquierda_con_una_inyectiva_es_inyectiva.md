---
Título: La composición por la izquierda con una inyectiva es una operación inyectiva
Autor:  José A. Alonso
---

Sean f₁ y f₂ funciones de X en Y y g una función de X en Y. Demostrar que si g es inyectiva y g ∘ f₁ = g ∘ f₂, entonces f₁ = f₂.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic

variables {X Y Z : Type*}
variables {f₁ f₂ : X → Y}
variable  {g : Y → Z}

example
  (hg : function.injective g)
  (hgf : g ∘ f₁ = g ∘ f₂)
  : f₁ = f₂ :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import tactic

variables {X Y Z : Type*}
variables {f₁ f₂ : X → Y}
variable  {g : Y → Z}

-- 1ª demostración
example
  (hg : function.injective g)
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
  (hg : function.injective g)
  (hgf : g ∘ f₁ = g ∘ f₂)
  : f₁ = f₂ :=
begin
  funext,
  apply hg,
  exact congr_fun hgf x,
end

-- 3ª demostración
example
  (hg : function.injective g)
  (hgf : g ∘ f₁ = g ∘ f₂)
  : f₁ = f₂ :=
begin
  refine funext (λ i, hg _),
  exact congr_fun hgf i,
end

-- 4ª demostración
example
  (hg : function.injective g)
  : function.injective ((∘) g : (X → Y) → (X → Z)) :=
λ f₁ f₂ hgf, funext (λ i, hg (congr_fun hgf i : _))
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/La_composicion_por_la_izquierda_con_una_inyectiva_es_inyectiva.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory La_composicion_por_la_izquierda_con_una_inyectiva_es_inyectiva
imports Main
begin

(* 1ª demostración *)
lemma
  assumes "inj g"
          "g ∘ f1 = g ∘ f2"
  shows   "f1 = f2"
proof (rule ext)
  fix x
  have "(g ∘ f1) x = (g ∘ f2) x"
    using ‹g ∘ f1 = g ∘ f2› by (rule fun_cong)
  then have "g (f1 x) = g (f2 x)"
    by (simp only: o_apply)
  then show "f1 x = f2 x"
    using ‹inj g› by (simp only: injD)
qed

(* 2ª demostración *)
lemma
  assumes "inj g"
          "g ∘ f1 = g ∘ f2"
  shows   "f1 = f2"
proof
  fix x
  have "(g ∘ f1) x = (g ∘ f2) x"
    using ‹g ∘ f1 = g ∘ f2› by simp
  then have "g (f1 x) = g (f2 x)"
    by simp
  then show "f1 x = f2 x"
    using ‹inj g› by (simp only: injD)
qed

(* 3ª demostración *)
lemma
  assumes "inj g"
          "g ∘ f1 = g ∘ f2"
  shows   "f1 = f2"
using assms
by (metis fun.inj_map_strong inj_eq)

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
