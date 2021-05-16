# El problema lógico del mal

El [problema lógico​ del mal](http://bit.ly/38nY9fN) intenta demostrar la inconsistencia lógica entre la existencia de una entidad omnipotente, omnibenevolente y omnisciente y la existencia del mal. Se ha atribuido al filósofo griego Epicuro la formulación original del problema del mal y este argumento puede esquematizarse como sigue:
<blockquote>
Si Dios fuera capaz de evitar el mal y quisiera hacerlo, lo haría. Si Dios fuera incapaz de evitar el mal, no sería omnipotente; si no quisiera evitar el mal sería malévolo. Dios no evita el mal. Si Dios existe, es omnipotente y no es malévolo. Luego, Dios no existe.
</blockquote>
Demostrar con Isabelle/HOL la corrección del argumento
<pre lang="isar">
theory El_problema_logico_del_mal
imports Main
begin

lemma
  assumes "C ∧ Q ⟶ P" 
          "¬C ⟶ ¬Op" 
          "¬Q ⟶ M" 
          "¬P"  
          "E ⟶ Op ∧ ¬M"
  shows  "¬E"
  oops
end
</pre>
donde se han usado los siguientes símbolos

+ C:  Dios es capaz de evitar el mal.
+ Q:  Dios quiere evitar el mal.
+ Op: Dios es omnipotente.
+ M:  Dios es malévolo.
+ P:  Dios evita el mal.
+ E:  Dios existe.

<h4>Soluciones</h4>

Puedes escribir tus soluciones en los comentarios (con el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;) o ver las soluciones propuestas pulsando [expand title="aquí"]

<h4>Soluciones con Isabelle/HOL</h4>

<pre lang="isar">
theory El_problema_logico_del_mal
imports Main
begin

lemma notnotI: "P ⟹ ¬¬P"
  by simp

lemma mt: "⟦F ⟶ G; ¬G⟧ ⟹ ¬F"
  by simp

lemma
  assumes "C ∧ Q ⟶ P" 
          "¬C ⟶ ¬Op" 
          "¬Q ⟶ M" 
          "¬P"  
          "E ⟶ Op ∧ ¬M"
  shows  "¬E"
proof (rule notI)
  assume "E"
  with ‹E ⟶ Op ∧ ¬M› have "Op ∧ ¬M" by (rule mp)
  then have "Op" by (rule conjunct1)
  then have "¬¬Op" by (rule notnotI)
  with ‹¬C ⟶ ¬Op› have "¬¬C" by (rule mt) 
  then have "C" by (rule notnotD)
  moreover
  have "¬M" using ‹Op ∧ ¬M› by (rule conjunct2)
  with ‹¬Q ⟶ M› have "¬¬Q" by (rule mt)
  then have "Q" by (rule notnotD)
  ultimately have "C ∧ Q" by (rule conjI)
  with ‹C ∧ Q ⟶ P› have "P" by (rule mp)
  with ‹¬P› show False by (rule notE)
qed

end
</pre>
[/expand]
