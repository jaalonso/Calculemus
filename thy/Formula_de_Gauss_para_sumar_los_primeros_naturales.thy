theory Formula_de_Gauss_para_sumar_los_primeros_naturales
imports Main 
begin

(* (suma n) es la suma de los primeros números naturales. *)
fun suma :: "nat \<Rightarrow> nat" where
  "suma 0 = 0"
| "suma (Suc n) = suma n + Suc n"

(* Demostración automática *)
lemma gauss: "2 * suma n = n^2 + n"
  by (induct n) (auto simp add: power2_eq_square)

(* Demostración detallada del lema anterior *)
lemma "2 * suma n = n^2 + n"
proof (induct n)
  have "2 * suma 0 = 0" 
    by (simp only: suma.simps(1))
  also have "\<dots> = 0^2 + 0" 
    by (simp only: power2_eq_square)
  finally show "2 * suma 0 = 0^2 + 0" by this
next
  fix n 
  assume HI: "2 * suma n = n^2 + n"
  have "2 * suma (Suc n) = 2 * (suma n + Suc n)"
    by (simp only: suma.simps(2))
  also have "\<dots> = 2 * suma n + 2 * Suc n"
    by (simp only: add_mult_distrib2)
  also have "\<dots> = n^2 + n + 2 * Suc n"
    by (simp only: HI)
  also have "\<dots> = n^2 + n + 2 + 2*n"
    by (simp only: mult_Suc_right)
  also have "\<dots> = n^2 + 1^2 + 2*n*1 + n + 1"
    by (simp only: one_power2)
  also have "\<dots> = (n + 1)^2 + n + 1"
    by (simp only: power2_sum [symmetric])
  also have "\<dots> = (Suc n)^2 + Suc n"
    by (simp only: Suc_eq_plus1)
  finally show "2 * suma (Suc n) = (Suc n)^2 + Suc n"
    by this
qed

end