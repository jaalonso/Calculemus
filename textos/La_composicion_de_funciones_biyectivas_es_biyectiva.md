---
Título: La composición de funciones biyectivas es biyectiva
Autor:  José A. Alonso
---

Demostrar que la composición de dos funciones biyectivas es una función biyectiva.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic
open function

variables {X Y Z : Type}
variable  {f : X → Y}
variable  {g : Y → Z}

example
  (Hf : bijective f)
  (Hg : bijective g)
  : bijective (g ∘ f) :=
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
  (Hf : bijective f)
  (Hg : bijective g)
  : bijective (g ∘ f) :=
begin
  cases Hf with Hfi Hfs,
  cases Hg with Hgi Hgs,
  split,
  { apply injective.comp,
    { exact Hgi, },
    { exact Hfi, }},
  { apply surjective.comp,
    { exact Hgs, },
    { exact Hfs, }},
end

-- 2ª demostración
example
  (Hf : bijective f)
  (Hg : bijective g)
  : bijective (g ∘ f) :=
begin
  cases Hf with Hfi Hfs,
  cases Hg with Hgi Hgs,
  split,
  { exact injective.comp Hgi Hfi, },
  { exact surjective.comp Hgs Hfs, },
end

-- 3ª demostración
example
  (Hf : bijective f)
  (Hg : bijective g)
  : bijective (g ∘ f) :=
begin
  cases Hf with Hfi Hfs,
  cases Hg with Hgi Hgs,
  exact ⟨injective.comp Hgi Hfi,
         surjective.comp Hgs Hfs⟩,
end

-- 4ª demostración
example :
  bijective f → bijective g → bijective (g ∘ f) :=
begin
  rintros ⟨Hfi, Hfs⟩ ⟨Hgi, Hgs⟩,
  exact ⟨injective.comp Hgi Hfi,
         surjective.comp Hgs Hfs⟩,
end

-- 5ª demostración
example :
  bijective f → bijective g → bijective (g ∘ f) :=
λ ⟨Hfi, Hfs⟩ ⟨Hgi, Hgs⟩, ⟨injective.comp Hgi Hfi,
                          surjective.comp Hgs Hfs⟩

-- 6ª demostración
example
  (Hf : bijective f)
  (Hg : bijective g)
  : bijective (g ∘ f) :=
-- by library_search
bijective.comp Hg Hf
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/La_composicion_de_funciones_biyectivas_es_biyectiva.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory La_composicion_de_funciones_biyectivas_es_biyectiva
imports Main
begin

(* 1ª demostración *)
lemma
  assumes "bij f"
          "bij g"
  shows   "bij (g ∘ f)"
proof (rule bijI)
  show "inj (g ∘ f)"
  proof (rule inj_compose)
    show "inj g"
      using ‹bij g› by (rule bij_is_inj)
  next
    show "inj f"
      using ‹bij f› by (rule bij_is_inj)
  qed
next
  show "surj (g ∘ f)"
  proof (rule comp_surj)
    show "surj f"
      using ‹bij f› by (rule bij_is_surj)
  next
    show "surj g"
      using ‹bij g› by (rule bij_is_surj)
  qed
qed

(* 2ª demostración *)
lemma
  assumes "bij f"
          "bij g"
  shows   "bij (g ∘ f)"
proof (rule bijI)
  show "inj (g ∘ f)"
  proof (rule inj_compose)
    show "inj g"
      by (rule bij_is_inj [OF ‹bij g›])
  next
    show "inj f"
      by (rule bij_is_inj [OF ‹bij f›])
  qed
next
  show "surj (g ∘ f)"
  proof (rule comp_surj)
    show "surj f"
      by (rule bij_is_surj [OF ‹bij f›])
  next
    show "surj g"
      by (rule bij_is_surj [OF ‹bij g›])
  qed
qed

(* 3ª demostración *)
lemma
  assumes "bij f"
          "bij g"
  shows   "bij (g ∘ f)"
proof (rule bijI)
  show "inj (g ∘ f)"
    by (rule inj_compose [OF bij_is_inj [OF ‹bij g›]
                             bij_is_inj [OF ‹bij f›]])
next
  show "surj (g ∘ f)"
    by (rule comp_surj [OF bij_is_surj [OF ‹bij f›]
                           bij_is_surj [OF ‹bij g›]])
qed

(* 4ª demostración *)
lemma
  assumes "bij f"
          "bij g"
  shows   "bij (g ∘ f)"
by (rule bijI [OF inj_compose [OF bij_is_inj  [OF ‹bij g›]
                                  bij_is_inj  [OF ‹bij f›]]
                  comp_surj   [OF bij_is_surj [OF ‹bij f›]
                                  bij_is_surj [OF ‹bij g›]]])

(* 5ª demostración *)
lemma
  assumes "bij f"
          "bij g"
  shows   "bij (g ∘ f)"
using assms
by (rule bij_comp)

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
