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

(* 4ª demostración *)
lemma
  assumes "inj g"
          "g ∘ f1 = g ∘ f2"
  shows   "f1 = f2"
proof -
  have "f1 = id ∘ f1"
    by (rule id_o [symmetric])
  also have "… = (inv g ∘ g) ∘ f1"
    by (simp add: assms(1))
  also have "… = inv g ∘ (g ∘ f1)"
    by (simp add: comp_assoc)
  also have "… = inv g ∘ (g ∘ f2)"
    using assms(2) by (rule arg_cong)
  also have "… = (inv g ∘ g) ∘ f2"
    by (simp add: comp_assoc)
  also have "… = id ∘ f2"
    by (simp add: assms(1))
  also have "… = f2"
    by (rule id_o)
  finally show "f1 = f2"
    by this
qed

(* 5ª demostración *)
lemma
  assumes "inj g"
          "g ∘ f1 = g ∘ f2"
  shows   "f1 = f2"
proof -
  have "f1 = (inv g ∘ g) ∘ f1"
    by (simp add: assms(1))
  also have "… = (inv g ∘ g) ∘ f2"
    using assms(2) by (simp add: comp_assoc)
  also have "… = f2"
    using assms(1) by simp
  finally show "f1 = f2" .
qed

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
