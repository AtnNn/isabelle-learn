theory Chapter4
  imports Main
begin

-- "Chapter 4"

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume 0: "surj f"
  from 0 have 1: "\<forall> A. \<exists> a. A = f a" by (simp add: surj_def)
  from 1 have 2: "\<exists> a. {x. x \<notin> f x} = f a" by blast
  from 2 show "False" by blast
qed

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  from this have "\<exists> a. {x. x \<notin> f x} = f a" by auto
  from this show False by blast
qed
  
lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists> a. {x. x \<notin> f x} = f a" by auto
  thus False by blast
qed
  
lemma
  fixes f :: "'a \<Rightarrow> 'a set"
  assumes s: "surj f"
  shows False
proof -
  have "\<exists> a. {x. x \<notin> f x} = f a" using s by auto
  thus False by blast
qed
  
lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists> a. {x. x \<notin> f x} = f a" by auto
  then obtain a where "{x. x \<notin> f x} = f a" by blast
  hence "a \<notin> f a \<longleftrightarrow> a \<in> f a" by blast
  thus False by blast
qed
  
-- "Exercise 4.1"

lemma
  assumes T: "\<forall> x y. T x y \<or> T y x"
  and A: "\<forall> x y. A x y \<and> A y x \<longrightarrow> x = y"
  and TA: "\<forall> x y. T x y \<longrightarrow> A x y" and "A x y"
  shows "T x y"
proof (rule ccontr)
  assume "\<not> T x y"
  from this T have "T y x" by blast
  from this TA have "A y x" by blast
  from A this `A x y` have "x = y" by blast
  from this `T y x` have "T x y" by blast
  from this `\<not> T x y` show False by blast
qed

find_theorems "(EX x . _) \<or> (EX y . _)"
find_theorems "(_ = _) \<Longrightarrow> (_ = _)"
find_theorems "?a \<Longrightarrow> ?a \<or> ?b"
thm even_two_times_div_two
thm length_drop
  
lemma
  "  (\<exists> ys zs. xs = ys @ zs \<and> length ys = length zs)
   \<or> (\<exists> ys zs. xs = ys @ zs \<and> length ys = length zs + 1)"
proof -
  obtain zs where zs: "zs = drop (length xs - length xs div 2) xs" by simp
  obtain ys where ys: "ys = take (length xs - length xs div 2) xs" by simp
  show ?thesis proof cases
    assume even: "even (length xs)"
    from zs ys have concat: "xs = ys @ zs" by simp
    from concat have sum: "length xs = length ys + length zs" by simp
    from zs even sum have length: "length ys = length zs"
      by (metis add_diff_cancel_right' even_two_times_div_two length_drop mult_2)
    from concat length show ?thesis by auto
  next
    assume odd: "odd (length xs)"
    from zs ys have concat: "xs = ys @ zs" by simp
    from concat have sum: "length xs = length ys + length zs" by simp
    from zs odd sum have length: "length ys = length zs + 1"
      using odd_ex_decrement by fastforce
    from concat length show ?thesis by auto
  qed
qed
  
inductive ev where
  ev0: "ev 0" |
  evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"
  
lemma "~ ev (Suc (Suc (Suc 0)))" (is "\<not> ?P")
proof
  assume P: "?P"
  hence "ev (Suc 0)" by cases
  thus False by cases
qed

lemma assumes a: "ev (Suc (Suc n))" shows "ev n"
proof -
  from a show "ev n" by cases
qed

lemma "\<not> ev (Suc (Suc (Suc 0)))"
proof
  assume "ev (Suc (Suc (Suc 0)))"
  thus False proof cases
    case evSS
    thus False proof cases qed
  qed
qed

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  star_refl: "star r x x" |
  star_step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  iter_refl: "iter r 0 x x" |
  iter_step: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"

lemma "iter r n x y \<Longrightarrow> star r x y"
proof (induction rule: iter.induct)
  case (iter_refl r x)
  show "star r x x" by (rule star_refl)
next
  case (iter_step r x y n z)
  assume xy: "r x y"
  assume yz: "star r y z"
  show "star r x z" by (rule star_step[OF xy yz])
qed
  
fun elems where
  "elems [] = {}" |
  "elems (x # xs) = insert x (elems xs)"

lemma "\<exists> x. x = 1" proof - show "\<exists> x. x = 1" proof show "1 = 1" by rule qed qed
thm exI

lemma "\<exists> x. x = 1" by (simp add: exI[of _ 1])

lemma "x \<in> elems xs \<Longrightarrow> \<exists> ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys"
proof (induction xs)
  case Nil
  assume "x \<in> elems []"
  then have False by simp
  then show ?case by safe
next
  case (Cons a xs)
  assume ind: "x \<in> elems xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys"
  assume elem: "x \<in> elems (a # xs)"
  show ?case proof cases
    assume eq: "x = a"
    obtain ys :: "'a list" where ys: "ys = []" by simp
    obtain zs where zs: "zs = xs" by simp
    have "a # xs = ys @ x # zs \<and> x \<notin> elems ys" by (simp add: ys zs eq)
    thus ?case by auto
  next
    assume neq: "x \<noteq> a"
    with elem have "x \<in> elems xs" by simp
    with ind have "\<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys" (is "\<exists> ys. ?P ys") by simp
    then obtain ys where "?P ys" by blast
    with neq show "\<exists>ys zs. a # xs = ys @ x # zs \<and> x \<notin> elems ys"
      using Cons_eq_appendI by force
  qed
qed

datatype alpha = a | b

fun balanced where
  balanced_nil: "balanced 0 [] = True" |
  balanced_a: "balanced n (a # xs) = balanced (Suc n) xs" |
  balanced_b: "balanced (Suc n) (b # xs) = balanced n xs" |
  unbalanced_a: "balanced (Suc _) [] = False" |
  unbalanced_b: "balanced 0 (b # _) = False"

inductive S where
  S_empty: "S []" |
  S_match: "S x \<Longrightarrow> S (a # x @ [b])" |
  S_concat: "S x \<Longrightarrow> S y \<Longrightarrow> S (x @ y)"

(*
inductive T where
  T_empty: "T []" |
  T_match: "T x \<Longrightarrow> T y \<Longrightarrow> T (x @ [a] @ y @ [b])"
*)

lemma S_remove:
  "S x \<Longrightarrow> (x = []) \<or> (\<exists> y z . (x = y @ [a] @ z @ [b]) \<and> S y \<and> S z)"
proof (induction rule: S.induct)
  case S_empty
  then show ?case by fast
next
  case (S_match z)
  then have "(a # z @ [b] = [] @ [a] @ z @ [b]) \<and> S [] \<and> S z"
    using S_empty by simp
  then show ?case by fast
next
  case (S_concat y p)
  note IH = this
  then show ?case proof (cases p)
    case Nil
    then show ?thesis using IH by simp
  next
    case (Cons h list)
    note p_cons = this
    then have "\<exists>yy z. p = yy @ [a] @ z @ [b] \<and> S yy \<and> S z" using IH(4) by fast
    then obtain yy z where "p = yy @ [a] @ z @ [b] \<and> S yy \<and> S z" by fast
    then have "y @ p = y @ yy @ [a] @ z @ [b] \<and> S (y @ yy) \<and> S z"
      using IH S.S_concat by presburger
    then show ?thesis by force
  qed
qed

lemma append_split: "length cs < length as \<Longrightarrow> as @ bs = cs @ ds \<Longrightarrow> \<exists>es. as = cs @ es"
  by (metis add_diff_inverse_nat append_Nil2 append_eq_append_conv_if
            drop_all length_drop less_imp_not_less)

lemma S_insert: "S (x @ y) \<Longrightarrow> S (x @ [a, b] @ y)"
proof -
  {
    fix z
    assume "S z"
    then have "\<And> x y. z = x @ y \<Longrightarrow> S (x @ [a, b] @ y)"
    proof (induction rule: S.induct)
      fix x y :: "alpha list"
      assume "[] = x @ y"
      then have "x = [] \<and> y = []" by simp
      then show "S (x @ [a, b] @ y)" using S_empty S_match by force
    next
      fix z x y
      assume IH: "S z" "\<And>x y. z = x @ y \<Longrightarrow> S (x @ [a, b] @ y)"
      assume as: "a # z @ [b] = x @ y"
      show "S (x @ [a, b] @ y)" proof (cases; cases)
        assume "x = []" "y = []"
        then show ?thesis using as by simp
      next
        assume "x = []" "y \<noteq> []"
        then show ?thesis using as IH by (metis S_concat S_empty S_match append_Nil)
      next
        assume "x \<noteq> []" "y = []"
        then show ?thesis using as IH by (metis S_concat S_empty S_match append_Nil append_Nil2)
      next
        assume not_empty: "x \<noteq> []" "y \<noteq> []"
        obtain xx where xx: "x = a # xx" using not_empty as by (metis append_eq_Cons_conv)
        obtain yy where yy: "y = yy @ [b]" using not_empty as
          by (metis last.simps last_appendR snoc_eq_iff_butlast)
        have "S (xx @ [a, b] @ yy)" using xx yy IH as by simp
        then show ?thesis using xx yy by (metis S.simps append.assoc append_Cons)
      qed
    next
      fix u v x y
      assume IHu: "S u" "\<And>x y. u = x @ y \<Longrightarrow> S (x @ [a, b] @ y)"
      assume IHv: "S v" "\<And>x y. v = x @ y \<Longrightarrow> S (x @ [a, b] @ y)"
      assume as: "u @ v = x @ y"
      show "S (x @ [a, b] @ y)" proof cases
        assume "length x < length u"
        then obtain w where w: "u = x @ w" using append_split as by blast
        then have "S (x @ [a, b] @ w)" using IHu by blast
        then have "S ((x @ [a, b] @ w) @ v)" using IHv S_concat by blast
        then show "S (x @ [a, b] @ y)" using as w by simp
      next
        assume "~ length x < length u"
        then obtain w where w: "v = w @ y" using as
          by (metis append_eq_append_conv_if le_imp_less_Suc less_antisym)
        then have "S (w @ [a, b] @ y)" using IHv by blast
        then have "S (u @ (w @ [a, b] @ y))" using IHu S_concat by blast
        then show "S (x @ [a, b] @ y)" using as w by force
      qed
    qed
  }
  then show "S (x @ y) \<Longrightarrow> S (x @ [a, b] @ y)" by simp
qed

lemma balanced_wrap: "balanced n w \<Longrightarrow> balanced (Suc n) (w @ [b])"
  sorry

lemma balanced_concat: "balanced n x \<Longrightarrow> balanced 0 y \<Longrightarrow> balanced n (x @ y)"
  sorry

lemma replicate_split: "m < n \<Longrightarrow> replicate n x = replicate m x @ replicate (n - m) x"
  by (metis add_diff_inverse_nat less_imp_not_less replicate_add)

theorem "balanced n w = S (replicate n a @ w)" (is "?L = ?R")
proof
  show "?L \<Longrightarrow> ?R" proof (induction arbitrary: n rule: balanced.induct)
    fix n
    assume "balanced n []"
    then have "n = 0" using balanced.elims by blast
    then show "S (replicate n a @ [])" using S_empty by simp
  next
    fix n xs
    assume IH: "\<And>n. balanced n xs \<Longrightarrow> S (replicate n a @ xs)"
    assume "balanced n (a # xs)"
    then show "S (replicate n a @ a # xs)" using IH balanced_a
      by (metis append_Cons replicate_Suc replicate_app_Cons_same)
  next
    fix n xs
    assume IH: "\<And>n. balanced n xs \<Longrightarrow> S (replicate n a @ xs)"
    assume as: "balanced n (b # xs)"
    then obtain m where m: "Suc m = n" using balanced.elims by blast
    then have "balanced m xs" using as by force
    then have "S (replicate m a @ xs)" using IH by simp
    then show "S (replicate n a @ b # xs)" using IH S_insert m
      by (metis append_Cons append_Nil2 append_eq_append_conv append_eq_append_conv2
                replicate_Suc replicate_app_Cons_same)
  next
    fix n
    assume "balanced n []"
    then have "n = 0" using balanced.elims by blast
    then show "S (replicate n a @ [])" using S_empty by simp
  next
    fix n xs
    assume "balanced n (b # xs)"
    show "S (replicate n a @ b # xs)"
      (* Isabelle seems to ignore that n is 0 in this case *)
      sorry
  qed
next
  {
    fix v
    assume "S v"
    then have "\<And>n w. (v = replicate n a @ w) \<Longrightarrow> balanced n w"
    proof (induction v rule: S.induct)
      fix n w
      assume "[] = replicate n a @ w"
      then have "w = [] \<and> n = 0" by simp
      then show "balanced n w" by simp
    next
      fix x n w
      assume IH: "S x" "\<And>n w. x = replicate n a @ w \<Longrightarrow> balanced n w"
      assume as: "a # x @ [b] = replicate n a @ w"
      show "balanced n w" proof (cases n)
        assume "n = 0"
        have "balanced 0 x" using IH by simp
        then show "balanced n w" using \<open>n=0\<close> balanced_wrap as by force
      next
        fix m
        assume m: "n = Suc m"
        then obtain y where y: "y @ [b] = w" using as
          by (metis (mono_tags) alpha.distinct(1) append_butlast_last_id append_is_Nil_conv
                    last_ConsR last_append last_snoc list.discI replicate_append_same)
        then have "x = replicate m a @ y" using m as by force
        then have "balanced m y" using IH by blast
        then show "balanced n w" using m y balanced_wrap by blast
      qed
    next
      fix n w x y
      assume IHx: "S x" "\<And>n w. x = replicate n a @ w \<Longrightarrow> balanced n w"
      assume IHy: "S y" "\<And>n w. y = replicate n a @ w \<Longrightarrow> balanced n w"
      assume as: "x @ y = replicate n a @ w"
      show "balanced n w" proof cases
        assume "x = []"
        then show "balanced n w" using IHy as by simp
      next
        assume x_not_nil: "x \<noteq> []"
        show "balanced n w" proof cases
          assume "n > length x"
          then have "x @ y = replicate (length x) a @ replicate (n - length x) a @ w"
            using as replicate_split by simp
          then have "x = replicate (length x) a" by simp
          then have False using x_not_nil IHx
            by (metis unbalanced_a Nitpick.size_list_simp(2) append_Nil2)
          then show "balanced n w" by fast
        next
          assume small_n: "\<not> length x < n"
          then obtain z where z: "x = replicate n a @ z" using as append_split
            by (metis append_Nil2 append_eq_append_conv_if length_replicate linorder_neqE_nat)
          then have left: "balanced n z" using IHx by blast
          have right: "balanced 0 y" using IHy by simp
          have w: "w = z @ y" using z as by simp
          from left right w show "balanced n w" using balanced_concat by simp
        qed
      qed
    qed
  }
  then show "?R \<Longrightarrow> ?L" by simp
qed