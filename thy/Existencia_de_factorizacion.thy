theory Existencia_de_factorizacion
imports Main 
begin

(* Referencia: Basado en [Existence-by-example](http://bit.ly/37aaDqJ)
   por Frédéric Boulanger.
*)

lemma "∃ (k::nat) (m::nat) (p::nat) . k*m*p = 12 ∧ k≠m ∧ k≠p ∧ m≠p"
proof (rule+)
  show "1 * (2::nat) * 6 = 12"  by simp
  show "1 ≠ (2::nat) ∧ 1 ≠ (6::nat) ∧ 2 ≠  (6::nat)" by simp
qed

lemma "∃ (k::nat) (m::nat) (p::nat) . k*m*p = 12 ∧ k≠m ∧ k≠p ∧ m≠p"
  by (rule exI[where x=1],
      rule exI[where x=2], 
      rule exI[where x=6], 
      simp+)

lemma exI3: "P x y z ⟹ ∃x y z. P x y z" 
  by auto

lemma ‹∃k m p. k*m*p = (12::nat) ∧ k≠m ∧ k≠p ∧ m≠p›
  by (rule exI3[of _ 1 2 6],
      auto)

lemma ‹∃k m p. k*m*p = (12::nat) ∧ k≠m ∧ k≠p ∧ m≠p›
proof -
  have ‹1*3*4 = (12::nat)› by simp
  moreover have ‹1≠(3::nat)› by simp
  moreover have ‹1≠(4::nat)› by simp
  moreover have ‹3≠(4::nat)› by simp
  ultimately show ?thesis by blast
qed

lemma ‹∃k m p. k*m*p = (12::nat) ∧ k≠m ∧ k≠p ∧ m≠p›
proof -
  have ‹1*3*4 = (12::nat)› by simp
  moreover have ‹1≠(3::nat) ∧ 1≠(4::nat) ∧ 3≠(4::nat)› by simp
  ultimately show ?thesis by blast
qed

lemma ‹∃k m p. k*m*p = (12::nat) ∧ k≠m ∧ k≠p ∧ m≠p›
proof -
  have "1 * 3 * 4 = (12::nat)"
    by simp
  then show ?thesis try
    by fastforce
qed

lemma ‹∃k m p. k*m*p = (12::nat) ∧ k≠m ∧ k≠p ∧ m≠p›
  (* sleadgehammer *)
  using One_nat_def 
        Suc3_eq_add_3 
        add_ac(1) 
        add.commute 
        add_One 
        add_self_div_2 
        dvd_triv_left 
        even_plus_one_iff inc.simps(1) 
        left_add_twice 
        mult.comm_neutral 
        mult.left_neutral 
        nat.simps(3) 
        nat_1_add_1 
        num.distinct(1) 
        numeral_Bit0 numeral_eq_one_iff 
        numeral_nat(3) 
        numeral_plus_numeral 
        numerals(1) 
        numerals(2) 
        plus_nat.simps(2) 
        semiring_normalization_rules(4) 
        semiring_normalization_rules(7) 
        times_div_less_eq_dividend 
        times_nat.simps(2) 
        zero_less_Suc 
        zero_less_diff
  by metis
