% Teorema de Nicómaco

Demostrar el [teorema de Nicómaco](http://bit.ly/2OaJI7q) que afirma que la suma de los cubos de los n primeros números naturales es igual que el cuadrado de la suma de los n primeros números naturales; es decir, para todo número natural n se tiene que
<pre lang="text">
1³ + 2³ + ... + n³ = (1 + 2 + ... + n)²
</pre>

<h4>Soluciones</h4>

Puedes escribir tus soluciones en los comentarios (con el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;) o ver las soluciones propuestas pulsando [expand title="aquí"]

<h4>Soluciones con Isabelle/HOL</h4>

<pre lang="isar">
theory Teorema_de_Nicomaco 
imports Main 
begin

(* (suma n) es la suma de los primeros números naturales. *)
fun suma :: "nat ⇒ nat" where
  "suma 0 = 0"
| "suma (Suc n) = suma n + Suc n"

(* (sumaCubos n) es la suma de los cubos primeros números naturales. *)
fun sumaCubos :: "nat ⇒ nat" where
  "sumaCubos 0 = 0"
| "sumaCubos (Suc n) = sumaCubos n + (Suc n)^3"

(* Fórmula para la suma *)
lemma "2 * suma n = n^2 + n"
proof (induct n)
  show "2 * suma 0 = 0^2 + 0" by simp
next
  fix n
  assume "2 * suma n = n^2 + n"
  then have "2 * suma (Suc n) = n^2 + n + 2 + 2 * n"
    by simp
  also have "… = (Suc n)^2 + Suc n"
    by (simp add: power2_eq_square)
  finally show "2 * suma (Suc n) = (Suc n)^2 + Suc n"
    by this
qed 

(* Demostración automática de la propiedad anterior *)
lemma formula_suma: 
  "2 * suma n = n^2 + n"
  by (induct n) (auto simp add: power2_eq_square)

lemma "4 * sumaCubos n = (n^2 + n)^2"
proof (induct n) 
  show "4 * sumaCubos 0 = (0^2 + 0)^2"
    by simp
next
  fix n
  assume "4 * sumaCubos n = (n^2 + n)^2"
  then have "4 * sumaCubos (Suc n) = (n^2 + n)^2 + 4 * (Suc n)^3"
    by simp
  then show "4 * sumaCubos (Suc n) = ((Suc n)^2 + Suc n)^2"
  by (simp add: algebra_simps 
                power2_eq_square 
                power3_eq_cube )
qed

(* Demostración automática de la propiedad anterior *)
lemma formula_sumaCubos: 
  "4 * sumaCubos n = (n^2 + n)^2"
  by (induct n) (auto simp add: algebra_simps 
                                power2_eq_square 
                                power3_eq_cube)

(* Lema auxiliar *)
lemma aux: "4 * (m::nat) = (2 * n)^2 ⟹ m = n^2"
  by (simp add: power2_eq_square)

(* Teorema de Nicómaco *)
theorem teorema_de_Nicomaco: 
  "sumaCubos n = (suma n)^2"
  by (simp only: formula_suma formula_sumaCubos aux)

end
</pre>
[/expand]
