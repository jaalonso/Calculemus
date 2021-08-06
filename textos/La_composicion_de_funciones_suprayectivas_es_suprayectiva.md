---
Título: La composición de funciones suprayectivas es suprayectiva
Autor:  José A. Alonso
---

Demostrar que la composición de dos funciones suprayectivas es una función suprayectiva.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic
open function

variables {X Y Z : Type}
variable  {f : X → Y}
variable  {g : Y → Z}

example
  (hf : surjective f)
  (hg : surjective g)
  : surjective (g ∘ f) :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import tactic
open function

variables {X Y Z : Type}
variable  {f : X → Y}
variable  {g : Y → Z}

-- 1ª demostración
example
  (hf : surjective f)
  (hg : surjective g)
  : surjective (g ∘ f) :=
begin
  intro z,
  cases hg z with y hy,
  cases hf y with x hx,
  use x,
  dsimp,
  rw hx,
  exact hy,
end

-- 2ª demostración
example
  (hf : surjective f)
  (hg : surjective g)
  : surjective (g ∘ f) :=
begin
  intro z,
  cases hg z with y hy,
  cases hf y with x hx,
  use x,
  calc (g ∘ f) x = g (f x) : by rw comp_app
             ... = g y     : congr_arg g hx
             ... = z       : hy,
end

-- 3ª demostración
example
  (hf : surjective f)
  (hg : surjective g)
  : surjective (g ∘ f) :=
assume z,
exists.elim (hg z)
  ( assume y (hy : g y = z),
    exists.elim (hf y)
    ( assume x (hx : f x = y),
      have g (f x) = z, from eq.subst (eq.symm hx) hy,
      show ∃ x, g (f x) = z, from exists.intro x this))

-- 4ª demostración
example
  (hf : surjective f)
  (hg : surjective g)
  : surjective (g ∘ f) :=
-- by library_search
surjective.comp hg hf

-- 5ª demostración
example
  (hf : surjective f)
  (hg : surjective g)
  : surjective (g ∘ f) :=
λ z, exists.elim (hg z)
  (λ y hy, exists.elim (hf y)
     (λ x hx, exists.intro x
        (show g (f x) = z,
           from (eq.trans (congr_arg g hx) hy))))
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/La_composicion_de_funciones_suprayectivas_es_suprayectiva.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory La_composicion_de_funciones_suprayectivas_es_suprayectiva
imports Main
begin

(* 1ª demostración *)
lemma
  assumes "surj (f :: 'a ⇒ 'b)"
          "surj (g :: 'b ⇒ 'c)"
  shows   "surj (g ∘ f)"
proof (unfold surj_def; intro allI)
  fix z
  obtain y where hy : "g y = z"
    using ‹surj g› by (metis surjD)
  obtain x where hx : "f x = y"
    using ‹surj f› by (metis surjD)
  have "(g ∘ f) x = g (f x)"
    by (simp only: o_apply)
  also have "… = g y"
    by (simp only: ‹f x = y›)
  also have "… = z"
    by (simp only: ‹g y = z›)
  finally have "(g ∘ f) x = z"
    by this
  then have "z = (g ∘ f) x"
    by (rule sym)
  then show "∃x. z = (g ∘ f) x"
    by (rule exI)
qed

(* 2ª demostración *)
lemma
  assumes "surj f"
          "surj g"
  shows   "surj (g ∘ f)"
using assms image_comp [of g f UNIV]
by (simp only:)

(* 3ª demostración *)
lemma
  assumes "surj f"
          "surj g"
  shows   "surj (g ∘ f)"
using assms
by (rule comp_surj)

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
