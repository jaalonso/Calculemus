# El problema del barbero

Decidir si es cierto que
<blockquote>
Carlos afeita a todos los habitantes de Las Chinas que no se afeitan a sí mismo y sólo a ellos. Carlos es un habitante de las Chinas. Por consiguiente, Carlos no afeita a nadie.
</blockquote>

Se usará la siguiente simbolización:

+ A(x,y) para x afeita a y
+ C(x)   para x es un habitante de Las Chinas
+ c      para Carlos


El problema consiste en completar la siguiente teoría de Isabelle/HOL:

<pre lang="isar">
theory El_problema_del_barbero
imports Main
begin

lemma
  assumes "∀x. A(c,x) ⟷ C(x) ∧ ¬A(x,x)"
          "C(c)"
  shows   "¬(∃x. A(c,x))"
  oops
end
</pre>

<h4>Soluciones con Isabelle/HOL</h4>

<pre lang="isar">
theory El_problema_del_barbero
imports Main
begin

― ‹La demostración automática es›
lemma
  assumes "∀x. A(c,x) ⟷ C(x) ∧ ¬A(x,x)"
          "C(c)"
  shows   "¬(∃x. A(c,x))"
  using assms
  by auto

― ‹La demostración estructurada es›
lemma
  assumes "∀x. A(c,x) ⟷ C(x) ∧ ¬A(x,x)"
          "C(c)"
  shows   "¬(∃x. A(c,x))"
proof -
  have 1: "A(c,c) ⟷ C(c) ∧ ¬A(c,c)" using assms(1) ..
  have "A(c,c)"
  proof (rule ccontr)
    assume "¬A(c,c)"
    with assms(2) have "C(c) ∧ ¬A(c,c)" ..
    with 1 have "A(c,c)" ..
    with ‹¬A(c,c)› show False ..
  qed
  have "¬A(c,c)"
  proof -
    have "C(c) ∧ ¬A(c,c)" using 1 ‹A(c,c)› ..
    then show "¬A(c,c)" ..
  qed
  then show "¬(∃x. A(c,x))" using ‹A(c,c)› ..
qed

― ‹La demostración detallada es›
lemma
  assumes "∀x. A(c,x) ⟷ C(x) ∧ ¬A(x,x)"
          "C(c)"
  shows   "¬(∃x. A(c,x))"
proof -
  have 1: "A(c,c) ⟷ C(c) ∧ ¬A(c,c)" using assms(1) by (rule allE)
  have "A(c,c)"
  proof (rule ccontr)
    assume "¬A(c,c)"
    with assms(2) have "C(c) ∧ ¬A(c,c)" by (rule conjI)
    with 1 have "A(c,c)" by (rule iffD2)
    with ‹¬A(c,c)› show False by (rule notE)
  qed
  have "¬A(c,c)"
  proof -
    have "C(c) ∧ ¬A(c,c)" using 1 ‹A(c,c)› by (rule iffD1)
    then show "¬A(c,c)" by (rule conjunct2)
  qed
  then show "¬(∃x. A(c,x))" using ‹A(c,c)› by (rule notE)
qed

end
</pre>

<h4>Otras soluciones</h4>
<ul>
<li>Se pueden escribir otras soluciones en los comentarios.
<li>El código se debe escribir entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
</ul>
