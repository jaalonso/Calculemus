# La dama o el tigre

En el libro de Raymond Smullyan *¿La dama o el tigre?* (en inglés, [The lady or the tiger?](http://bit.ly/2W5E4bC) se plantea el siguiente  problema

<blockquote>
Un rey somete a un prisionero a la siguiente prueba: lo enfrenta a dos
puertas, habitación correspondiente. Se informa al prisionero que en  cada una de las habitaciones puede haber un tigre o una dama. Como es  natural, el prisionero debe elegir la puerta que le lleva a la dama (entre otras cosas, para no ser devorado por el tigre). Para ayudarle, en cada puerta hay un letrero. El de la puerta 1 dice "en esta habitación hay una dama y en la otra un tigre" y el de la puerta 2 dice "en una de estas habitaciones hay una dama y en una de estas habitaciones hay un tigre".

Sabiendo que uno de los carteles dice la verdad y el otro no, demostrar que la dama se encuentra en la segunda habitación.
</blockquote>

Para la formalización del problema se usarán los siguientes símbolos

+ c1 que representa *el contenido del cartel de la puerta 1*, 
+ c2 que representa *el contenido del cartel de la puerta 2* , 
+ dp que representa *hay una dama en la primera habitación*,
+ tp que representa *hay un tigre en la primera habitación*,
+ ds que representa *hay una dama en la segunda habitación* y
+ ts que representa *hay un tigre en la segunda habitación*.

<pre lang="isar">
theory La_dama_o_el_tigre
imports Main
begin

lemma
  assumes "c1 ⟷ dp ∧ ts"
          "c2 ⟷ (dp ∧ ts) ∨ (ds ∧ tp)"
          "(c1 ∧ ¬ c2) ∨ (c2 ∧ ¬ c1)"
  shows   "ds"
  oops

end
</pre>

Demostrar con Isabelle/HOL que el argumento anterior es correcto.

<h4>Soluciones</h4>

Puedes escribir tus soluciones en los comentarios (con el código entre  una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con  &#60;/pre&#62;) o ver las soluciones propuestas pulsando [expand  title="aquí"]

<h4>Soluciones con Isabelle/HOL</h4>

<pre lang="isar">
theory La_dama_o_el_tigre
imports Main
begin

(* 1ª demostración *)
lemma
  assumes "c1 ⟷ dp ∧ ts"
          "c2 ⟷ (dp ∧ ts) ∨ (ds ∧ tp)"
          "(c1 ∧ ¬ c2) ∨ (c2 ∧ ¬ c1)"
  shows   "ds"
  oops
  using assms
  by auto

(* 2ª demostración *)
lemma
  assumes "c1 ⟷ dp ∧ ts"
    "c2 ⟷ (dp ∧ ts) ∨ (ds ∧ tp)"
    "(c1 ∧ ¬ c2) ∨ (c2 ∧ ¬ c1)"
  shows "ds"
proof -
  note ‹(c1 ∧ ¬ c2) ∨ (c2 ∧ ¬ c1)›
  then show "ds"
  proof 
    assume "c1 ∧ ¬ c2"
    then have "c1" ..
    with ‹c1 ⟷ dp ∧ ts› have "dp ∧ ts" .. 
    then have "(dp ∧ ts) ∨ (ds ∧ tp)" ..
    with assms(2) have "c2" ..
    have "¬ c2" using ‹c1 ∧ ¬ c2› ..
    then show "ds" using ‹c2› ..
  next
    assume "c2 ∧ ¬ c1"
    then have "c2" ..
    with assms(2) have "(dp ∧ ts) ∨ (ds ∧ tp)" ..
    then show "ds"
    proof
      assume "dp ∧ ts"
      with assms(1) have c1 ..
      have "¬ c1" using ‹c2 ∧ ¬ c1› ..
      then show ds using ‹c1› ..
    next
      assume "ds ∧ tp"
      then show ds ..
    qed
  qed
qed

(* 3ª demostración *)
lemma
  assumes "c1 ⟷ dp ∧ ts"
    "c2 ⟷ (dp ∧ ts) ∨ (ds ∧ tp)"
    "(c1 ∧ ¬ c2) ∨ (c2 ∧ ¬ c1)"
  shows "ds"
proof -
  note ‹(c1 ∧ ¬ c2) ∨ (c2 ∧ ¬ c1)›
  then show "ds"
  proof (rule disjE)
    assume "c1 ∧ ¬ c2"
    then have "c1" by (rule conjunct1)
    with ‹c1 ⟷ dp ∧ ts› have "dp ∧ ts" by (rule iffD1) 
    then have "(dp ∧ ts) ∨ (ds ∧ tp)" by (rule disjI1)
    with assms(2) have "c2" by (rule iffD2)
    have "¬ c2" using ‹c1 ∧ ¬ c2› by (rule conjunct2)
    then show "ds" using ‹c2› by (rule notE)
  next
    assume "c2 ∧ ¬ c1"
    then have "c2" by (rule conjunct1)
    with assms(2) have "(dp ∧ ts) ∨ (ds ∧ tp)" by (rule iffD1)
    then show "ds"
    proof (rule disjE)
      assume "dp ∧ ts"
      with assms(1) have c1 by (rule iffD2)
      have "¬ c1" using ‹c2 ∧ ¬ c1› by (rule conjunct2)
      then show ds using ‹c1› by (rule notE)
    next
      assume "ds ∧ tp"
      then show ds by (rule conjunct1)
    qed
  qed
qed

end
</pre>
[/expand]
