---
Título: Las clases de equivalencia de elementos relacionados son iguales
Autor:  José A. Alonso
---

Demostrar que las clases de equivalencia de elementos relacionados son iguales.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic

variable  {X : Type}
variables {x y: X}
variable  {R : X → X → Prop}

def clase (R : X → X → Prop) (x : X) :=
  {y : X | R x y}

example
  (h : equivalence R)
  (hxy : R x y)
  : clase R x = clase R y :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import tactic

variable  {X : Type}
variables {x y: X}
variable  {R : X → X → Prop}

def clase (R : X → X → Prop) (x : X) :=
  {y : X | R x y}

-- En la demostración se usará el siguiente lema del que se presentan
-- varias demostraciones.

-- 1ª demostración del lema auxiliar
example
  (h : equivalence R)
  (hxy : R x y)
  : clase R y ⊆ clase R x :=
begin
  intros z hz,
  have hyz : R y z := hz,
  have htrans : transitive R := h.2.2,
  have hxz : R x z := htrans hxy hyz,
  exact hxz,
end

-- 2ª demostración del lema auxiliar
example
  (h : equivalence R)
  (hxy : R x y)
  : clase R y ⊆ clase R x :=
begin
  intros z hz,
  exact h.2.2 hxy hz,
end

-- 3ª demostración del lema auxiliar
lemma aux
  (h : equivalence R)
  (hxy : R x y)
  : clase R y ⊆ clase R x :=
λ z hz, h.2.2 hxy hz

-- A continuación se presentan varias demostraciones del ejercicio
-- usando el lema auxiliar

-- 1ª demostración
example
  (h : equivalence R)
  (hxy : R x y)
  : clase R x = clase R y :=
begin
  apply le_antisymm,
  { have hs : symmetric R := h.2.1,
    have hyx : R y x := hs hxy,
    exact aux h hyx, },
  { exact aux h hxy, },
end

-- 2ª demostración
example
  (h : equivalence R)
  (hxy : R x y)
  : clase R x = clase R y :=
begin
  apply le_antisymm,
  { exact aux h (h.2.1 hxy), },
  { exact aux h hxy, },
end

-- 3ª demostración
example
  (h : equivalence R)
  (hxy : R x y)
  : clase R x = clase R y :=
le_antisymm (aux h (h.2.1 hxy)) (aux h hxy)
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Las_clases_de_equivalencia_de_elementos_relacionados_son_iguales.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Las_clases_de_equivalencia_de_elementos_relacionados_son_iguales
imports Main
begin

definition clase :: "('a ⇒ 'a ⇒ bool) ⇒ 'a ⇒ 'a set"
  where "clase R x = {y. R x y}"

(* En la demostración se usará el siguiente lema del que se presentan
   varias demostraciones. *)

(* 1ª demostración del lema auxiliar *)
lemma
  assumes "equivp R"
          "R x y"
  shows "clase R y ⊆ clase R x"
proof (rule subsetI)
  fix z
  assume "z ∈ clase R y"
  then have "R y z"
    by (simp add: clase_def)
  have "transp R"
    using assms(1) by (rule equivp_imp_transp)
  then have "R x z"
    using ‹R x y› ‹R y z› by (rule transpD)
  then show "z ∈ clase R x"
    by (simp add: clase_def)
qed

(* 2ª demostración del lema auxiliar *)
lemma aux :
  assumes "equivp R"
          "R x y"
  shows "clase R y ⊆ clase R x"
  using assms
  by (metis clase_def eq_refl equivp_def)

(* A continuación se presentan demostraciones del ejercicio *)

(* 1ª demostración *)
lemma
  assumes "equivp R"
          "R x y"
  shows "clase R y = clase R x"
proof (rule equalityI)
  show "clase R y ⊆ clase R x"
    using assms by (rule aux)
next
  show "clase R x ⊆ clase R y"
  proof -
    have "symp R"
      using assms(1) equivpE by blast
    have "R y x"
      using ‹R x y› by (simp add: ‹symp R› sympD)
    with assms(1) show "clase R x ⊆ clase R y"
       by (rule aux)
  qed
qed

(* 2ª demostración *)
lemma
  assumes "equivp R"
          "R x y"
  shows "clase R y = clase R x"
  using assms
  by (metis clase_def equivp_def)

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
