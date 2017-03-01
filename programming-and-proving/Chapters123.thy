theory Chapters123
  imports Main
begin

lemma "[a] = [b] \<Longrightarrow> a = b"
  by simp

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add 0 n = n" |
  "add (Suc n) m = Suc (add n m)"

lemma add_02 [simp]: "add n 0 = n"
  apply (induction n)
  apply (auto)
done

thm add_02

datatype 'a list' = Nil' | Cons' 'a "'a list'"
  
fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "app [] ys = ys" |
  "app (x # xs) ys = x # app xs ys"

fun rev' :: "'a list \<Rightarrow> 'a list" where
  "rev' [] = []" |
  "rev' (x # xs) = app (rev' xs) [x]"

value "rev' (Cons True (Cons False Nil))"
value "rev' [a, b]"

lemma app_Nil2 [simp]: "app xs [] = xs"
  apply (induction xs)
  apply auto
done

lemma app_assoc [simp]:
  "app (app a b) c = app a (app b c)"
  apply (induction a)
  apply auto
done

lemma rev_app [simp]:
  "rev' (app a b) = app (rev' b) (rev' a)"
  apply (induction a)
  apply auto
done
  

theorem rev_rev [simp]: "rev' (rev' xs) = xs"
  apply (induction xs)
  apply auto
done

value "1 + 2 :: nat"
value "1 - 2 :: nat"

theorem add_assoc [simp]:
  "add (add a b) c = add a (add b c)"
  apply (induction a)
  apply auto
done

lemma add_12 [simp]:
  "Suc (add a b) = add a (Suc b)"
  apply (induction a)
  apply auto
done

theorem add_comm [simp]: "add a b = add b a"
  apply (induction a)
  apply auto
done

fun double :: "nat \<Rightarrow> nat" where
  "double 0 = 0" |
  "double (Suc n) = Suc (Suc (double n))"

theorem add_double: "double n = add n n"
  apply (induction n)
  apply auto
done

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count _ [] = 0" |
  "count a (x # xs) = (if a = x
                       then Suc (count a xs)
                       else count a xs)"

theorem count_max: "count a xs \<le> length xs"
  apply (induction xs)
  apply auto
done

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc [] a = [a]" |
  "snoc (x # xs) a = x # snoc xs a"

fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse [] = []" |
  "reverse (x # xs) = snoc (reverse xs) x"

lemma reverse_snoc [simp]:
  "reverse (snoc xs x) = x # reverse xs"
  apply (induction xs)
  apply auto
done

theorem reverse_reverse: "reverse (reverse a) = a"
  apply (induction a)
  apply auto
done

fun sum_upto :: "nat \<Rightarrow> nat" where
  "sum_upto 0 = 0" |
  "sum_upto (Suc n) = Suc n + sum_upto n"

theorem sum_upto: "sum_upto n = n * (n + 1) div 2"
  apply (induction n)
  apply auto
done

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
  "mirror Tip = Tip" |
  "mirror (Node l a r) = Node (mirror r) a (mirror l)"

lemma "mirror (mirror t) = t"
  apply induction apply auto done

fun lookup :: "('a * 'b) list \<Rightarrow> 'a \<Rightarrow> 'b option" where
  "lookup [] _ = None" |
  "lookup ((k,v) # xs) a =
    (if a = k then Some v else lookup xs a)"

definition sq :: "nat \<Rightarrow> nat" where
  "sq n = n * n"

abbreviation sq' :: "nat \<Rightarrow> nat" where
  "sq' n == n * n"

fun contents :: "'a tree \<Rightarrow> 'a list" where
  "contents Tip = []" |
  "contents (Node l a r) =
    app (contents l) (app [a] (contents r))"

fun treesum :: "nat tree \<Rightarrow> nat" where
  "treesum Tip = 0" |
  "treesum (Node l a r) = treesum l + a + treesum r"

fun listsum :: "nat list \<Rightarrow> nat" where
  "listsum [] = 0" |
  "listsum (x # xs) = x + listsum xs"

lemma [simp]:
  "listsum (app a b) = listsum a + listsum b"
  apply (induction a) apply auto done

theorem "treesum t = listsum (contents t)"
  apply induction
  apply auto
done

datatype 'a tree2 =
  Tip2 'a |
  Node2 "'a tree2" 'a "'a tree2"

fun mirror2 :: "'a tree2 \<Rightarrow> 'a tree2" where
  "mirror2 (Tip2 a) = Tip2 a" |
  "mirror2 (Node2 l a r) =
     Node2 (mirror2 r) a (mirror2 l)"

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
  "pre_order (Tip2 a) = [a]" |
  "pre_order (Node2 l a r) =
     a # (pre_order l @ pre_order r)"

fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
  "post_order (Tip2 a) = [a]" |
  "post_order (Node2 l a r) =
     post_order l @ post_order r @ [a]"

lemma rev_snoc: "x # rev xs = rev (snoc xs x)"
  apply (induction xs) apply auto done

lemma app_rev:
  "rev a @ rev b = rev (b @ a)"
  apply (induction a)
  apply auto
done

theorem "pre_order (mirror2 t) = rev (post_order t)"
  apply (induction t)
  apply auto
done

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intersperse _ [] = []" |
  "intersperse _ [x] = [x]" |
  "intersperse a (x # xs) = x # a # intersperse a xs"

lemma "f x # map f xs = map f (x # xs)"
  by simp

theorem
  "map f (intersperse a xs) =
   intersperse (f a) (map f xs)"
  apply (induction xs rule: intersperse.induct)
  apply auto
done

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev [] ys = ys" |
  "itrev (x # xs) ys = itrev xs (x # ys)"

lemma "itrev xs ys = rev xs @ ys"
  apply (induction xs arbitrary: ys)
  apply auto
done

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "itadd 0 b = b" |
  "itadd (Suc a) b = itadd a (Suc b)"

lemma [simp]: "add a (Suc b) = add b (Suc a)"
  apply (induction a)
  apply (induction b)
  apply auto
done

theorem "itadd a b = add a b"
  apply (induction a arbitrary: b)
  apply auto
done

datatype tree0 = Tip0 | Node0 tree0 tree0

fun nodes :: "tree0 \<Rightarrow> nat" where
  "nodes Tip0 = 0" |
  "nodes (Node0 l r) = nodes l + nodes r"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
  "explode 0 t = t" |
  "explode (Suc n) t = explode n (Node0 t t)"

theorem "nodes (explode n t) = 2 ^ n * nodes t"
  apply (induction n arbitrary: t)
  apply simp_all
done

datatype exp =
  Var |
  Const int |
  Add exp exp |
  Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
  "eval Var v = v" |
  "eval (Const n) _ = n" |
  "eval (Add a b) v = eval a v + eval b v" |
  "eval (Mult a b) v = eval a v * eval b v"

value "let f = (\<lambda>x y. x) in f a b"
value "case True of True \<Rightarrow> 1 | False \<Rightarrow> 2"

value "let x = 4;
    go = (\<lambda>poly xn. (case poly of
      [] \<Rightarrow> 0 |
      (c # cs) \<Rightarrow> c * xn + go cs (xn * x)))
   in go [2, 3] 4 :: int"

fun evalp_helper :: "int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "evalp_helper [] _ _ = 0" |
  "evalp_helper (c # cs) x xn =
    c * xn + evalp_helper cs x (xn * x)"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "evalp poly x = evalp_helper poly x 1"

value "eval (Add (Const 1) (Mult (Const 2) Var)) 3"
value "evalp [4, 2, -1, 3] 2"

fun coeffs_add :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "coeffs_add [] b = b" |
  "coeffs_add a [] = a" |
  "coeffs_add (a # as) (b # bs) = (a + b) # coeffs_add as bs"

fun pcons :: "int \<Rightarrow> int list \<Rightarrow> int list" where
  "pcons a [] = (if a = 0 then [] else [a])" |
  "pcons a b = a # b"
  
  
fun coeffs_mult :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "coeffs_mult [] _ = []" |
  "coeffs_mult (a # as) bs =
    coeffs_add
      (map (op * a) bs)
      (pcons 0 (coeffs_mult as bs))"

fun coeffs :: "exp \<Rightarrow> int list" where
  "coeffs Var = [0,1]" |
  "coeffs (Const n) = [n]" |
  "coeffs (Mult a b) = coeffs_mult (coeffs a) (coeffs b)" |
  "coeffs (Add a b) = coeffs_add (coeffs a) (coeffs b)"
  
lemma [simp]: "coeffs_mult a [] = []"
  apply (induction a)
  apply auto
done
  
lemma
  "coeffs_mult as (b # bs) = coeffs_add (map (op * b) as) (pcons 0 (coeffs_mult as bs))"
  apply (induction as arbitrary: b bs)
  apply auto
  apply (simp add: algebra_simps)
oops
  
lemma "coeffs_mult a b = coeffs_mult b a"
  apply (induction a)
  apply simp
  apply auto
  apply (cases b)
  apply simp
  apply simp
oops
    
lemma "coeffs (Add (Const 1) (Mult (Const 2) Var)) = [1, 2]" by simp 
lemma "coeffs_mult [0,1] [0,1] = [0, 0, 1]" by simp
lemma "coeffs_mult [2, 3] [5, 7] = [10, 29, 21]" by simp

fun poly_helper :: "int list \<Rightarrow> exp \<Rightarrow> exp" where
  "poly_helper [] _ = Const 0" |
  "poly_helper (x # xs) v = Add (Mult (Const x) v) (poly_helper xs (Mult Var v))"

fun poly :: "int list \<Rightarrow> exp" where
  "poly p = poly_helper p (Const 1)"

value "poly [1,2,3]"

fun iterate :: "nat \<Rightarrow> ('x \<Rightarrow> 'x) \<Rightarrow> 'x \<Rightarrow> 'x" where
  "iterate 0 _ a = a" |
  "iterate (Suc n) f a = iterate n f (f a)"

value "iterate 5 (\<lambda>x. x + 1) 0 :: int"
value "iterate 5 (Add Var) (Const 0) :: exp"

lemma [simp]: "eval (iterate n (Mult Var) k) x = x ^ n * eval k x"
  apply (induction n arbitrary: x k)
  apply auto
done

lemma iterate_more: "iterate n f (f a) = iterate (Suc n) f a"
  by simp

lemma [simp]: "f (iterate n f a) = iterate (Suc n) f a"
  apply (induction n arbitrary: f a)
  apply auto
done

lemma add_power: "(x ^ n * x :: int) = (x ^ Suc n)"
  by simp
  
lemma evalp_is_eval_poly:
  "(xn :: int) = x ^ n
   \<Longrightarrow> v = iterate n (Mult Var) (Const 1)
   \<Longrightarrow> evalp_helper p x xn = eval (poly_helper p v) x"
  apply (induction p arbitrary: n v x xn)
  apply simp
  apply auto
  apply (subst iterate_more)
  apply (subst add_power)
  apply blast
done
  
thm evalp_helper.induct

lemma [simp]: "evalp_helper (coeffs_add a b) x xn =
       evalp_helper a x xn + evalp_helper b x xn"
  apply (induction arbitrary: xn rule: coeffs_add.induct)
  apply simp
  apply simp
  apply auto
  apply (simp add: algebra_simps)
done

lemma [simp]: "evalp_helper (map (op * a) bs) x xn = a * evalp_helper bs x xn"
  apply (induction bs arbitrary: x xn)
  apply auto
  apply (simp add: algebra_simps)
done

lemma evalp_helper_evacuate_x: "evalp_helper p x (xn * x) = x * evalp_helper p x xn"
  apply (induction arbitrary: x xn rule: evalp_helper.induct)
  apply simp
  apply (simp add: algebra_simps)
done


lemma [simp]: "evalp_helper (coeffs_mult a b) x xn =
       evalp_helper a x xn * evalp_helper b x xn"
  apply (induction arbitrary: xn rule: coeffs_mult.induct)
  apply simp
  apply (simp add: algebra_simps evalp_helper_evacuate_x)
  
oops

  
theorem "evalp (coeffs e) x = eval e x"
  apply (induction e)
  apply auto
oops

fun treeset where
  "treeset Tip = {}" |
  "treeset (Node l a r) = treeset l \<union> {a} \<union> treeset r"

fun option_lt where
  "option_lt _ None = True" |
  "option_lt None _ = True" |
  "option_lt (Some x) (Some y) = (x < y)"

fun ordb :: "int tree \<Rightarrow> int option \<Rightarrow> int option \<Rightarrow> bool" where
  "ordb Tip a b = option_lt a b" |
  "ordb (Node l a r) bl br = (ordb l bl (Some a) \<and> ordb r (Some a) br)"

fun ord where "ord t = ordb t None None"

fun ins where
  "ins x Tip = Node Tip x Tip" |
  "ins x (Node l a r) =
    (if x < a then Node (ins x l) a r
    else if x = a then Node l a r
    else Node l a (ins x r))"

theorem "treeset (ins x t) = {x} \<union> treeset t"
  apply (induction t)
  apply auto
done

fun bounded where
  "bounded a c b =
    (option_lt a (Some b) \<and> option_lt (Some b) c)" 

lemma [simp]:
  "ordb t l r
   \<Longrightarrow> bounded l r a
   \<Longrightarrow> ordb (ins a t) l r"
  apply (induction t arbitrary: l r)
  apply auto
done

theorem "ord t \<Longrightarrow> ord (ins x t)"
  apply (induction t)
  apply auto
done

lemma "\<lbrakk> xs @ ys = ys @ xs; length xs = length ys \<rbrakk> \<Longrightarrow> xs = ys"
  using append_eq_append_conv by blast

inductive palindrome :: "'a list \<Rightarrow> bool" where
  "palindrome []" |
  "palindrome [a]" |
  "palindrome xs \<Longrightarrow> palindrome (a # xs @ [a])"

fun init where
  "init [] = []" |
  "init [_] = []" |
  "init (x # xs) = x # init xs"
  
lemma unsnoc: "(xs = []) \<or> (\<exists>ys x. xs = ys @ [x])"
  apply (cases xs)
  apply simp
  apply (metis append_butlast_last_id)
done
    
theorem "rev xs = xs \<Longrightarrow> palindrome xs"
  apply (induction xs)
  apply (simp add: palindrome.intros)
oops
  
inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  star_refl: "star r x x" |
  star_step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  star'_refl: "star' r x x" |
  star'_step: "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

theorem "star' r x y \<Longrightarrow> star r x y"
  apply (induction rule: star'.induct)
  apply (simp add: star.intros)
oops

theorem "star' r x y \<Longrightarrow> star r x y"
oops

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "iter r 0 x x" |
  "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"
  
theorem "star r x y \<Longrightarrow> iter r n x y"
  nitpick
oops

datatype alpha = a | b
  
inductive S where
  "S []" |
  "S x \<Longrightarrow> S (a # x @ [b])" |
  "S x \<Longrightarrow> S y \<Longrightarrow> S (x @ y)"

inductive T where
  "T []" |
  "T x \<Longrightarrow> T y \<Longrightarrow> T (x @ [a] @ y @ [b])"

theorem "S w \<Longrightarrow> T w"
  apply (induction rule: S.induct)
  apply (simp add: T.intros)
oops

value "(0 - 1 :: nat) = 0"
value "1 div 0 :: int"
