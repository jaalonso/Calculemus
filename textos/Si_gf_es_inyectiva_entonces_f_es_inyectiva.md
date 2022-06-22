---
Título: Si g·f es inyectiva, entonces f es inyectiva.
Autor:  José A. Alonso
---

Demostrar que si g·f es inyectiva, entonces f es inyectiva.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic
open function

variables {X Y Z : Type}
variable  {f : X → Y}
variable  {g : Y → Z}

example
  (Hgf : injective (g ∘ f))
  : injective f :=
sorry
</pre>

<pre lang="lean">

<--!more-->

**Soluciones con Lean**

<pre lang="lean">
import tactic
open function

variables {X Y Z : Type}
variable  {f : X → Y}
variable  {g : Y → Z}

-- 1ª demostración
example
  (Hgf : injective (g ∘ f))
  : injective f :=
begin
  intros x x' f_xx',
  apply Hgf,
  calc (g ∘ f) x = g (f x)    : rfl
             ... = g (f x')   : congr_arg g f_xx'
             ... = (g ∘ f) x' : rfl
end

-- 2ª demostración
example
  (Hgf : injective (g ∘ f))
  : injective f :=
begin
  intros x x' f_xx',
  apply Hgf,
  simp [f_xx'],
end

-- 3ª demostración
example
  (Hgf : injective (g ∘ f))
  : injective f :=
begin
  intros x x' f_xx',
  apply Hgf,
  finish,
end

-- 4ª demostración
example
  (Hgf : injective (g ∘ f))
  : injective f :=
begin
  assume x  : X, 
  assume x' : X, 
  assume f_xx' : f x = f x',
  have gf_xx' : (g ∘ f) x = (g ∘ f) x', from 
    calc (g ∘ f) x = g (f x)    : rfl
               ... = g (f x')   : congr_arg g f_xx'
               ... = (g ∘ f) x' : rfl,
  show x = x', 
    { exact Hgf gf_xx' },
end
</pre>

El código de las demostraciones se encuentra en [GitHub](https://github.com/jaalonso/Razonando-con-Lean/blob/main/src/Si_gf_es_inyectiva_entonces_f_es_inyectiva.lean) y puede ejecutarse con el [Lean Web editor](https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Razonando-con-Lean/main/src/Si_gf_es_inyectiva_entonces_f_es_inyectiva.lean).

**Soluciones con Isabelle/HOL**

<pre lang="isar">
theory La_composicion_de_funciones_inyectivas_es_inyectiva
imports Main
begin

(* 1ª demostración *)
lemma
  assumes "inj f"
          "inj g"
  shows   "inj (f ∘ g)"
proof (rule injI)
  fix x y
  assume "(f ∘ g) x = (f ∘ g) y"
  then have "f (g x) = f (g y)"
    by (simp only: o_apply)
  then have "g x = g y"
    using ‹inj f› by (simp only: injD)
  then show "x = y" 
    using ‹inj g› by (simp only: injD)
qed

(* 2ª demostración *)
lemma
  assumes "inj f"
          "inj g"
  shows   "inj (f ∘ g)"
using assms
by (simp add: inj_def)

(* 3ª demostración *)
lemma
  assumes "inj f"
          "inj g"
  shows   "inj (f ∘ g)"
using assms
by (rule inj_compose)

end
</pre>
