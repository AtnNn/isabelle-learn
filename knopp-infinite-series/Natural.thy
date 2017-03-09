theory Natural
  imports Main
begin

-- "Natural numbers, starting from 1"

datatype natural = one | succ natural

fun add_nat where
  "add_nat one n = succ n" |
  "add_nat (succ n) m = succ (add_nat n m)"

lemma add_nat_associative: "add_nat (add_nat a b) c = add_nat a (add_nat b c)"
  by (induction a b rule: add_nat.induct, auto)

instantiation natural :: one begin
definition "one_natural = one"
declare one_natural_def [simp]
instance by standard end

instantiation natural :: semigroup_add begin
definition "plus_natural = add_nat"
declare plus_natural_def [simp]
instance 
  apply standard
  apply simp
  using add_nat_associative apply assumption
  done
end

instantiation natural :: numeral begin
instance by standard end

instantiation natural :: ord begin

fun less_natural where
  "less_natural one (succ _) = True" |
  "less_natural (succ a) (succ b) = less_natural a b" |
  "less_natural _ _ = False"

fun less_eq_natural where
  "less_eq_natural one _ = True" |
  "less_eq_natural (succ a) (succ b) = less_eq_natural a b" |
  "less_eq_natural _ _ = False"

instance by standard end

instantiation natural :: linorder begin
instance proof
  fix x y z :: natural
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (induction x y rule: less_natural.induct, auto)
  show "x \<le> x"
    by (induction x, auto)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    apply (induction x y arbitrary: z rule: less_eq_natural.induct, auto)
    apply (metis Natural.natural.distinct(1) Natural.natural.inject less_eq_natural.elims(2) less_eq_natural.elims(3))
    done
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    apply (induction x y arbitrary: z rule: less_eq_natural.induct, auto)
    using less_eq_natural.elims(2) apply blast
    done
  show "x \<le> y \<or> y \<le> x"
    by (induction x y arbitrary: z rule: less_eq_natural.induct, auto)
qed
  
fun mul_nat where
  "mul_nat one n = n" |
  "mul_nat (succ n) m = add_nat m (mul_nat n m)"

fun succ_abs_diff_nat where
  "succ_abs_diff_nat one one = one" |
  "succ_abs_diff_nat one (succ b) = succ b" |
  "succ_abs_diff_nat (succ a) one = succ a" |
  "succ_abs_diff_nat (succ a) (succ b) = succ_abs_diff_nat a b"

lemma diff_commute: "succ_abs_diff_nat a b = succ_abs_diff_nat b a"
  by (induction a b rule: succ_abs_diff_nat.induct, auto)

lemma less_succ_self [simp]: "a < succ a"
  by (induction a "succ a" rule: less_natural.induct, auto)

lemma less_succ: "a < b \<Longrightarrow> a < succ b"
  by (induction a b rule: less_natural.induct, auto)

lemma diff_inc: "succ_abs_diff_nat a b = succ_abs_diff_nat (succ a) (succ b)"
  by simp

lemma le_inc: "a < b \<Longrightarrow> a < succ b"
  by (induction a b rule: less_natural.induct, auto)

lemma "a < b \<Longrightarrow> succ_abs_diff_nat a b = succ c \<Longrightarrow> c < b"
proof (induction a b arbitrary: c rule: succ_abs_diff_nat.induct)
  fix a b c
  assume IH: "\<And>c. a < b \<Longrightarrow> succ_abs_diff_nat a b = succ c \<Longrightarrow> c < b"
  assume "succ a < succ b"
  then have "a < b" by simp
  then have "succ_abs_diff_nat a b = succ c \<Longrightarrow> c < b" using IH by blast
  then show "succ_abs_diff_nat (succ a) (succ b) = succ c \<Longrightarrow> c < succ b"
    using diff_inc le_inc by simp
qed simp+

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
  
lemma diff_res2: "succ_abs_diff_nat a b = c \<Longrightarrow> add_nat c a = succ b \<or> add_nat c b = succ a"
  apply (induction a b rule: succ_abs_diff_nat.induct)
  apply (auto simp add: add_nat_commutative)
  done

fun leftover_nat where
  "leftover_nat one one _ _ = undefined" |
  "leftover_nat (succ a) one _ d = leftover_nat a d a d" |
  "leftover_nat one (succ a) c _ = c" |
  "leftover_nat (succ a) (succ b) c d = leftover_nat a b c d"

definition "uncurry f ab = f (fst ab, snd ab)"
declare uncurry_def [simp]

fun to_builtin_nat where
  "to_builtin_nat one = Suc 0" |
  "to_builtin_nat (succ n) = Suc (to_builtin_nat n)"

lemma max_cod: "max a b = c \<Longrightarrow> a = c \<or> b = c"
  by (metis max_def)

lemma lt_imp_le_nat: "(a :: natural) < b \<Longrightarrow> a \<le> b"
  by (induction a b rule: less_natural.induct, auto)

lemma max_res: "(a :: natural) < b \<Longrightarrow> max a b = b"
  by (simp add: lt_imp_le_nat max_absorb2)

lemma to_builtin_nat_zero [simp]: "0 < to_builtin_nat a"
  by (cases a; auto)

lemma lt_nats: "a < b \<Longrightarrow> to_builtin_nat a < to_builtin_nat b"
  by (induction a b rule: less_natural.induct; auto)

lemma diff_eq [simp]: "succ_abs_diff_nat a a = one"
  by (induction a, auto)

lemma diff_res [simp]:
  "a < b \<Longrightarrow> succ_abs_diff_nat a b = c \<Longrightarrow> add_nat a c = succ b"
  by (induction a b arbitrary: c rule: succ_abs_diff_nat.induct, auto)

lemma diff_one [simp]: "succ_abs_diff_nat one a = a"
  by (induction a, auto)

lemma "or_split": "(C \<Longrightarrow> P) \<Longrightarrow> (\<not>C \<Longrightarrow> Q) \<Longrightarrow> P \<or> Q" by auto
  
lemma lt_eq_gt_complete_nat:
  "((a :: natural) < b \<Longrightarrow> P) \<Longrightarrow> (a = b \<Longrightarrow> P) \<Longrightarrow> (a > b \<Longrightarrow> P) \<Longrightarrow> P"
  using not_less_iff_gr_or_eq by blast
  
lemma add_nat_res_gt: "add_nat a b = c \<Longrightarrow> a < c &&& b < c"
  by (induction a b arbitrary: c rule: add_nat.induct, auto simp add: less_succ)
    
function (sequential) gcd_nat where
  "gcd_nat one b = one" |
  "gcd_nat a one = one" |
  "gcd_nat a b = (case succ_abs_diff_nat a b of
    one \<Rightarrow> a |
    succ c \<Rightarrow> if a < b then gcd_nat a c else gcd_nat b c)"
by (pat_completeness, auto)
termination
proof (relation "measure (\<lambda>(a,b). to_builtin_nat (max a b))", auto)
  fix a b c :: natural
  assume diff: "succ_abs_diff_nat a b = succ c"
  assume alt: "a < b"
  from diff alt have clt: "c < b"
    apply (induction a b arbitrary: c rule: succ_abs_diff_nat.induct)
    apply (auto simp add: less_succ) done
  from alt clt have l: "max (succ a) c < succ b"
    by (metis less_natural.simps(2) less_succ max_cod)
  from alt have "succ a < succ b" by simp
  then have r: "max (succ a) (succ b) = succ b" by (rule max_res)
  show "to_builtin_nat (max (succ a) c) < to_builtin_nat (max (succ a) (succ b))"
    using l r lt_nats by fastforce
next
  fix a b c :: natural
  assume c: "succ_abs_diff_nat a b = succ c"
  assume ge: "\<not>(a < b)"
  have "max (succ b) c < max (succ a) (succ b)"
  proof (rule lt_eq_gt_complete_nat[of a b])
    assume "a < b"
    then have "False" using ge by simp
    then show ?thesis by simp
  next
    assume "a = b"
    then show ?thesis using c by simp
  next
    assume gt: "a > b"
    then have sum: "add_nat b c = a"
      by (metis diff_commute natural.inject add_nat.simps(2) add_nat_commutative c diff_res)
    from gt have nle: "\<not>(a \<le> b)" by simp
    have r: "max (succ a) (succ b) = succ a"
      by (subst max_def, auto simp add: nle) 
    from sum have "c < succ a" using add_nat_res_gt less_succ by blast
    show ?thesis by (subst r, auto simp add: gt \<open>c < succ a\<close>)
  qed
  then show "to_builtin_nat (max (succ b) c)
             < to_builtin_nat (max (succ a) (succ b))"
    using lt_nats by force
qed

value "gcd_nat 3 2"
value "succ_abs_diff_nat 3 2"

fun div_nat div_nat_h where
  "div_nat a b = div_nat_h a b b" |
  "div_nat_h one _ _ = one" |
  "div_nat_h (succ a) (succ b) c = div_nat_h a b c" |
  "div_nat_h (succ a) one c = succ (div_nat_h a c c)"

value "mul_nat 2 1"

lemma "gcd_nat a b = c \<Longrightarrow> mul_nat a (div_nat b c) = mul_nat (div_nat a c) b"

end