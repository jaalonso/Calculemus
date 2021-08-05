---
Título: La inversa de una función biyectiva es biyectiva
Autor:  José A. Alonso
---

En Lean se puede definir que g es una inversa de f por
<pre lang="text">
   def inversa (f : X → Y) (g : Y → X) :=
     (∀ x, (g ∘ f) x = x) ∧ (∀ y, (f ∘ g) y = y)
</pre>

Demostrar que si la función f es biyectiva y g es una inversa de f, entonces g es biyectiva.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic
open function

variables {X Y : Type*}
variable (f : X → Y)
variable (g : Y → X)

def inversa (f : X → Y) (g : Y → X) :=
  (∀ x, (g ∘ f) x = x) ∧ (∀ y, (f ∘ g) y = y)

example
  (hf : bijective f)
  (hg : inversa g f)
  : bijective g :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import tactic
open function

variables {X Y : Type*}
variable (f : X → Y)
variable (g : Y → X)

def inversa (f : X → Y) (g : Y → X) :=
  (∀ x, (g ∘ f) x = x) ∧ (∀ y, (f ∘ g) y = y)

-- 1ª demostración
example
  (hf : bijective f)
  (hg : inversa g f)
  : bijective g :=
begin
  rcases hg with ⟨h1, h2⟩,
  rw bijective_iff_has_inverse,
  use f,
  split,
  { exact h1, },
  { exact h2, },
end

-- 2ª demostración
example
  (hf : bijective f)
  (hg : inversa g f)
  : bijective g :=
begin
  rcases hg with ⟨h1, h2⟩,
  rw bijective_iff_has_inverse,
  use f,
  exact ⟨h1, h2⟩,
end

-- 3ª demostración
example
  (hf : bijective f)
  (hg : inversa g f)
  : bijective g :=
begin
  rcases hg with ⟨h1, h2⟩,
  rw bijective_iff_has_inverse,
  use [f, ⟨h1, h2⟩],
end

-- 4ª demostración
example
  (hf : bijective f)
  (hg : inversa g f)
  : bijective g :=
begin
  rw bijective_iff_has_inverse,
  use f,
  exact hg,
end

-- 5ª demostración
example
  (hf : bijective f)
  (hg : inversa g f)
  : bijective g :=
begin
  rw bijective_iff_has_inverse,
  use [f, hg],
end

-- 6ª demostración
example
  (hf : bijective f)
  (hg : inversa g f)
  : bijective g :=
begin
  apply bijective_iff_has_inverse.mpr,
  use [f, hg],
end

-- 7ª demostración
example
  (hf : bijective f)
  (hg : inversa g f)
  : bijective g :=
bijective_iff_has_inverse.mpr (by use [f, hg])
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/La_inversa_de_una_funcion_biyectiva_es_biyectiva.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory La_inversa_de_una_funcion_biyectiva_es_biyectiva
imports Main
begin

definition inversa :: "('a ⇒ 'b) ⇒ ('b ⇒ 'a) ⇒ bool" where
  "inversa f g ⟷ (∀ x. (g ∘ f) x = x) ∧ (∀ y. (f ∘ g) y = y)"

(* 1ª demostración *)
lemma
  fixes   f :: "'a ⇒ 'b"
  assumes "bij f"
          "inversa g f"
  shows   "bij g"
proof (rule bijI)
  show "inj g"
  proof (rule injI)
    fix x y
    assume "g x = g y"
    have h1 : "∀ y. (f ∘ g) y = y"
      by (meson assms(2) inversa_def)
    then have "x = (f ∘ g) x"
      by (simp only: allE)
    also have "… = f (g x)"
      by (simp only: o_apply)
    also have "… = f (g y)"
      by (simp only: ‹g x = g y›)
    also have "… = (f ∘ g) y"
      by (simp only: o_apply)
    also have "… = y"
      using h1 by (simp only: allE)
    finally show "x = y"
      by this
  qed
next
  show "surj g"
  proof (rule surjI)
    fix x
    have h2 : "∀ x. (g ∘ f) x = x"
      by (meson assms(2) inversa_def)
    then have "(g ∘ f) x = x"
      by (simp only: allE)
    then show "g (f x) = x"
      by (simp only: o_apply)
  qed
qed

(* 2ª demostración *)
lemma
  fixes   f :: "'a ⇒ 'b"
  assumes "bij f"
          "inversa g f"
  shows   "bij g"
proof (rule bijI)
  show "inj g"
  proof (rule injI)
    fix x y
    assume "g x = g y"
    have h1 : "∀ y. (f ∘ g) y = y"
      by (meson assms(2) inversa_def)
    then show "x = y"
      by (metis ‹g x = g y› o_apply)
  qed
next
  show "surj g"
  proof (rule surjI)
    fix x
    have h2 : "∀ x. (g ∘ f) x = x"
      by (meson assms(2) inversa_def)
    then show "g (f x) = x"
      by (simp only: o_apply)
  qed
qed

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
