(* Prueba_de_1:(1x2)+1:(2x3)+1:(3x4)+...+1:(nx(n+1))_es_n:(n+1).thy
-- Prueba de 1/(1x2)+1/(2x3)+1/(3x4)+...+1/(nx(n+1)) = n/(n+1)
-- José A. Alonso Jiménez
-- Sevilla, 26 de septiembre de 2021
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que
--    1/(1*2)+1/(2*3)+1/(3*4)+...+1/(n*(n+1)) = n/(n+1)
-- ------------------------------------------------------------------ *)

theory Prueba_de_serie_racional
imports Main HOL.Real
begin

lemma 
  fixes n :: nat
  shows "2 + real n \<noteq> 0"
  by simp

lemma 
  fixes n :: nat
  assumes "n > 0"
  shows "(\<Sum>k=1..n. 1 / (k * (k + 1))) = n / (n + 1)"
proof (induct n)
  case 0
  then show ?case by simp
next
  fix n
  assume HI : "(\<Sum>k = 1..n. 1 / real (k * (k + 1))) = real n / real (n + 1)"
  have "(\<Sum>k=1..Suc n. 1 / real (k * (k + 1))) = 
        (\<Sum>k=1..n. 1 / real (k * (k + 1))) + 1 / real (Suc n * (Suc n + 1))"
    by (smt (verit, best) le_add1 plus_1_eq_Suc sum.nat_ivl_Suc')
  also have "\<dots> = real n / real (n + 1) + 1 / real (Suc n * (Suc n + 1))"
    using HI by simp
  also have "\<dots> = real (Suc n) / real (Suc n + 1)"
    sorry (* by (auto simp add: field_simps) *)
  show "(\<Sum>k=1..Suc n. 1 / real (k * (k + 1))) = real (Suc n) / real (Suc n + 1)" sorry
qed

find_theorems "Suc _ = _ + _"

end

(* Referencia: "El método de la inducción matemática" de I.S. Sominski
   p. 13. *)
