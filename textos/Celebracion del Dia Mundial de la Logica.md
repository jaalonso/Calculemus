# Celebración del Día Mundial de la Lógica

Decidir si es cierto que
<blockquote>
Existe una Universidad tal que si en dicha Universidad se celebra el Día Mundial de la Lógica (DML), entonces en todas las Universidades se celebra el DML.
</blockquote>

En la formalización usar C(x) para representar que en la Universidad x
se celebra el DML.

<h2>Soluciones</h2>

<pre lang="isar">
theory Celebracion_del_DML
imports Main

begin

(* 1ª solución (automática) *)
lemma "∃x. (C x ⟶ (∀y. C y))"
  by simp

(* 2ª solución (estructurada) *)
lemma "∃x. (C x ⟶ (∀y. C y))"
proof -
  have "¬ (∀y. C y) ∨ (∀y. C y)" ..
  then show "∃x. (C x ⟶ (∀y. C y))"
  proof 
    assume "¬ (∀y. C y)"
    then have "∃y. ¬(C y)" by simp
    then obtain a where "¬ C a" ..
    then have "C a ⟶ (∀y. C y)" by simp
    then show "∃x. (C x ⟶ (∀y. C y))" ..
  next
    assume "∀y. C y"
    then show "∃x. (C x ⟶ (∀y. C y))" by simp
  qed
qed

(* 3ª solución (detallada con lemas auxiliares) *)

lemma aux1:
  assumes "¬ (∀y. C y)"
  shows "∃y. ¬(C y)"
proof (rule ccontr)
  assume "∄y. ¬ C y"
  have "∀y. C y"
  proof 
    fix a
    show "C a"
    proof (rule ccontr)
      assume "¬ C a"
      then have "∃y. ¬ C y" by (rule exI)
      with ‹∄y. ¬ C y› show False by (rule notE)
    qed 
  qed
  with assms show False by (rule notE)
qed

lemma aux2:
  assumes "¬P"
  shows   "P ⟶ Q"
proof
  assume "P"
  with assms show "Q" by (rule notE)
qed

lemma aux3:
  assumes "∄x. P x"
  shows   "∀x. ¬ P x"
proof
  fix a
  show "¬ P a"
  proof 
    assume "P a"
    then have "∃x. P x" by (rule exI)
    with assms show False by (rule notE)
  qed 
qed

lemma aux4:
  assumes "Q"
  shows   "∃x. (P x ⟶ Q)"
proof (rule ccontr)
  assume "∄x. (P x ⟶ Q)"
  then have "∀x. ¬ (P x ⟶ Q)" by (rule aux3)
  then have "¬ (P a ⟶ Q)" by (rule allE)
  moreover
  have "P a ⟶ Q"
  proof
    assume "P a"
    show "Q" using assms by this
  qed
  ultimately show False by (rule notE)
qed

lemma "∃x. (C x ⟶ (∀y. C y))"
proof -
  have "¬ (∀y. C y) ∨ (∀y. C y)" ..
  then show "∃x. (C x ⟶ (∀y. C y))"
  proof 
    assume "¬ (∀y. C y)"
    then have "∃y. ¬(C y)" by (rule aux1)
    then obtain a where "¬ C a" by (rule exE)
    then have "C a ⟶ (∀y. C y)" by (rule aux2)
    then show "∃x. (C x ⟶ (∀y. C y))" by (rule exI)
  next
    assume "∀y. C y"
    then show "∃x. (C x ⟶ (∀y. C y))" by (rule aux4)
  qed
qed

end
</pre>

<h2>Nota</h2>
<ul>
<li>Se pueden añadir otras soluciones en los comentarios.
<li>El código se debe escribir entre una línea con &#60;pre lang="isar"&#62; y otra con &#60;/pre&#62;
</ul>

<h2>Pensamiento</h2>

<blockquote>
Si así fue, así pudo ser;  si así fuera, así podría ser; pero como no es, no es. Eso es lógica. 

Lewis Carroll
</blockquote>

