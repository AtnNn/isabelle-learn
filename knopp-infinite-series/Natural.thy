theory Natural
  imports Main
begin

-- "Natural numbers, starting from 1"

datatype natural = one | succ natural

fun add_nat where
  "add_nat one n = succ n" |
  "add_nat (succ n) m = succ (add_nat n m)"

fun mul_nat where
  "mul_nat one n = n" |
  "mul_nat (succ n) m = add_nat m (mul_nat n m)"

fun succ_abs_diff_nat where
  "succ_abs_diff_nat one one = one" |
  "succ_abs_diff_nat one (succ b) = succ b" |
  "succ_abs_diff_nat (succ a) one = succ a" |
  "succ_abs_diff_nat (succ a) (succ b) = succ_abs_diff_nat a b"

lemma add_nat_commutative: "add_nat a b = add_nat b a"
proof (induction a b rule: add_nat.induct)
  fix n
  show "add_nat one n = add_nat n one"
  proof (simp, induction n one rule: add_nat.induct)
    show "succ one = add_nat one one" by simp
    fix n
    assume "succ n = add_nat n one"
    then have "succ (succ n) = succ (add_nat n one)" by simp
    then show "succ (succ n) = add_nat (succ n) one"
      by (simp add: \<open>succ (succ n) = succ (add_nat n one)\<close>)
  qed
next
  fix n m
  assume IH: "add_nat n m = add_nat m n"
  have "succ (add_nat m n) = add_nat m (succ n)"
    by (induction m n rule: add_nat.induct, auto)
  then show "add_nat (succ n) m = add_nat m (succ n)" using IH by simp
qed
  
lemma "succ_abs_diff_nat a b = c \<Longrightarrow> add_nat c a = succ b \<or> add_nat c b = succ a"
  apply (induction a b rule: succ_abs_diff_nat.induct)
  apply (auto simp add: add_nat_commutative)
  done

fun less_natural where
  "less_natural one (succ _) = True" |
  "less_natural (succ a) (succ b) = less_natural a b" |
  "less_natural _ _ = False"

fun leftover_nat where
  "leftover_nat one one _ _ = undefined" |
  "leftover_nat (succ a) one _ d = leftover_nat a d a d" |
  "leftover_nat one (succ a) c _ = c" |
  "leftover_nat (succ a) (succ b) c d = leftover_nat a b c d"

fun (sequential) gcd_nat where
  "gcd_nat one b = one" |
  "gcd_nat a one = one" |
  "gcd_nat a b = (case succ_abs_diff_nat a b of
    one \<Rightarrow> a |
    succ c \<Rightarrow> if less_natural a b then a else b)"

end