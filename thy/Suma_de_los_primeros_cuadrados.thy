(* Suma_de_los_primeros_cuadrados.thy
-- Suma de los primeros cuadrados
-- José A. Alonso Jiménez
-- Sevilla, 21 de septiembre de 2021
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que la suma de los primeros cuadrados
--    0² + 1² + 2² + 3² + \<sqdot>\<sqdot>\<sqdot> + n²
-- es n(n+1)(2n+1)/6
-- ------------------------------------------------------------------ *)

theory Suma_de_los_primeros_cuadrados
imports Main
begin

fun sumaCuadrados :: "nat \<Rightarrow> nat" where
  "sumaCuadrados 0       = 0"
| "sumaCuadrados (Suc n) = sumaCuadrados n + (Suc n)^2"

(* 1\<ordfeminine> demostración *)
lemma
  "6 * sumaCuadrados n = n* (n + 1) * (2 * n + 1)"
proof (induct n)
  show "6 * sumaCuadrados 0 =  0 * (0 + 1) * (2 * 0 + 1)"
    by simp
next
  fix n
  assume HI : "6 * sumaCuadrados n = n * (n + 1) * (2 * n + 1)"
  have "6 * sumaCuadrados (Suc n) =
        6 * (sumaCuadrados n + (n + 1)^2)"
    by simp
  also have "\<dots> = 6 * sumaCuadrados n + 6 * (n + 1)^2"
    by simp
  also have "\<dots> = n * (n + 1) * (2 * n + 1) + 6 * (n + 1)^2"
    using HI by simp
  also have "\<dots> = (n + 1) * (n * (2 * n + 1) + 6 * (n+1))"
    by algebra
  also have "\<dots> = (n + 1) * (2 * n^2 + 7 * n + 6)"
    by algebra
  also have "\<dots> = (n + 1) * (n + 2) * (2 * n + 3)"
    by algebra
  also have "\<dots> = (n + 1) * ((n + 1) + 1) * (2 * (n + 1) + 1)"
    by algebra
  also have "\<dots> = Suc n * (Suc n + 1) * (2 * Suc n + 1)"
    by (simp only: Suc_eq_plus1)
  finally show "6 * sumaCuadrados (Suc n) =
        Suc n * (Suc n + 1) * (2 * Suc n + 1)"
    by this
qed

(* 2\<ordfeminine> demostración *)
lemma
  "6 * sumaCuadrados n = n* (n + 1) * (2 * n + 1)"
proof (induct n)
  show "6 * sumaCuadrados 0 =  0 * (0 + 1) * (2 * 0 + 1)"
    by simp
next
  fix n
  assume HI : "6 * sumaCuadrados n = n * (n + 1) * (2 * n + 1)"
  have "6 * sumaCuadrados (Suc n) =
        6 * sumaCuadrados n + 6 * (n + 1)^2"
    by simp
  also have "\<dots> = n * (n + 1) * (2 * n + 1) + 6 * (n + 1)^2"
    using HI by simp
  also have "\<dots> = (n + 1) * ((n + 1) + 1) * (2 * (n + 1) + 1)"
    by algebra
  finally show "6 * sumaCuadrados (Suc n) =
        Suc n * (Suc n + 1) * (2 * Suc n + 1)"
    by (simp only: Suc_eq_plus1)
qed

end

(* Referencia:
-- \<questiondown>Qué es la Matemática? https://bit.ly/3lrPKAp de R. Courant y
-- H. Robbins p. 21 *)
