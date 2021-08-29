(* La_suma_de_los_n_primeros_impares_es_n^2.thy
-- La suma de los n primeros impares es n^2.
-- José A. Alonso Jiménez
-- Sevilla, 3 de septiembre de 2021
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- En Isabelle/HOL, se puede definir el n-ésimo número primo por
--    definition impar :: "nat \<Rightarrow> nat" where
--      "impar n \<equiv> 2 * n + 1"
-- Además, está definida la función
--    sum :: (nat \<Rightarrow> nat) => nat set \<Rightarrow> nat
-- tal que (sum f A) es la suma del conjunto obtenido aplicando la 
-- función f a los elementos del conjunto A.
--
-- Demostrar que la suma de los n primeros números impares es n².
-- ------------------------------------------------------------------ *)

theory "La_suma_de_los_n_primeros_impares_es_n^2"
imports Main
begin

definition impar :: "nat \<Rightarrow> nat" where
  "impar n \<equiv> 2 * n + 1"

lemma "sum impar {i::nat. i < n} = n\<^sup>2"
proof (induct n)
  show "sum impar {i. i < 0} = 0\<^sup>2" 
    by simp
next 
  fix n
  assume HI : "sum impar {i. i < n} = n\<^sup>2"
  have "{i. i < Suc n} = {i. i < n} \<union> {n}" 
    by auto 
  then have "sum impar {i. i < Suc n} = 
             sum impar {i. i < n} + impar n"
    by simp
  also have "\<dots> = n\<^sup>2 + (2 * n + 1)"
    using HI impar_def by simp
  also have "\<dots> = (n + 1)\<^sup>2" 
    by algebra
  also have "\<dots> = (Suc n)\<^sup>2"
    by simp
  finally show "sum impar {i. i < Suc n} = (Suc n)\<^sup>2" . 
qed

end