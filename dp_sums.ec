require import Int IntExtra Real RealExtra Ring.
require import Distr List Aprhl StdRing StdOrder StdBigop.
  (*---*) import IntID IntOrder RField RealOrder.

op eps: { real | 0%r <= eps } as ge0_eps.

hint exact : ge0_eps.

(* 
   so far we have assumed that we have only one data point 
   and we know that this is the data that may differ. However, 
   in general we are interested in situations where we have a whole 
   dataset
*)

module M1 = {
  proc sum (ls : int list) : int = {
    var s : int <- 0;
    var z : int;
    var i : int;
    i <- 0;
    while (i < size ls) {
      s <- s + (nth 0 ls i);
      i <- i + 1;
    }
    z <$ lap eps s;
    return z;
  }
}.

(* 
  To reason about this example we need to formulate 
  our notion of adjacency. We will start with some additional notion.
*)


pred eq_in_range (ms ns : int list, i j : int) =
  forall (k : int),
  i <= k <= j => nth 0 ms k = nth 0 ns k.

lemma eq_in_range_succ (ms ns : int list, i j : int) :
  eq_in_range ms ns i j => eq_in_range ms ns (i + 1) j.
proof.
move => eir_i.
rewrite /eq_in_range => k le_iplus1_k_j.
rewrite eir_i /#.
qed.
  

pred adjacent_e (ms ns : int list) (i:int)=
  size ms = size ns /\
   0 <= i < size ms /\
   eq_in_range ms ns 0 (i - 1) /\
   `|nth 0 ms i - nth 0 ns i| <= 1 /\
   eq_in_range ms ns (i + 1) (size ms - 1).

(* 
  here is our definition of adjacency
*)

pred adjacent (ms ns : int list) = exists i, adjacent_e ms ns i. 

(* 
 we can prove some lemma about this. 
*)



lemma size_eq_adjacent (ms ns : int list) :
  adjacent ms ns => size ms = size ns.
proof.
rewrite /adjacent. rewrite /adjacent_e => [#].
smt().
qed.

lemma adjacent_sub_abs_bound (ms ns : int list, i : int) :
  adjacent_e ms ns i => 0 <= i < size ms =>
  `|nth 0 ms i - nth 0 ns i| <= 1.
proof.  
  rewrite /adjacent_e. smt().  
qed.

lemma adjacent_ne_sub_eq_after (ms ns : int list, i : int) :
  adjacent_e ms ns i => 0 <= i < size ms => nth 0 ms i <> nth 0 ns i =>
  eq_in_range ms ns (i + 1) (size ms - 1).
proof.
rewrite /adjacent_e. smt(). 
qed.


(* 
  we can now prove the previous program differentially private
*) 

lemma lem1 :
  aequiv
  [[ eps & 0%r]
   M1.sum ~ M1.sum : adjacent ls{1} ls{2} ==> res{1} = res{2}].
proof.
proc.
seq 2 2: (adjacent ls{1} ls{2} /\ ={i, s} /\ i{1} = 0 /\ s{1} = 0).
auto. toequiv. auto.
seq 1 1 : (`|s{1} - s{2}| <= 1).
toequiv.
while
  (adjacent ls{1} ls{2} /\ ={i} /\ 0 <= i{1} <= size ls{1} /\
   (! ={s} =>
    `|s{1} - s{2}| <= 1 /\
     eq_in_range ls{1} ls{2} i{1} (size ls{1} - 1))).
 wp. skip. progress.
smt().
smt().
smt(adjacent_sub_abs_bound).
smt(adjacent_ne_sub_eq_after).
smt(size_eq_adjacent).
smt(size_eq_adjacent).
auto; progress.
rewrite size_ge0.
smt(size_eq_adjacent).
smt(size_eq_adjacent).
smt(addzN).
     lap (0) 1.
qed.


(* 
  the previous example still adds noise only at the end. 
  What shall we do if we want to add noise in an iterative way?
  Let's consider releasing all the partial sums of a vector:
  e.g. on input [1,2,3,4,5] we want to release [1,3,6,10,15]
*) 

(* Here a first approach where we add noise to each sum *)

module M2 = {
  proc dummy_sum (ls : int list) : int list = {
    var s :int <- 0;
    var output : int list;
    var z : int;
    var i :int <- 0;
    output = [];
    while (i < size ls ) {
      s = s + (nth 0 ls i); 
      i <- i + 1; 
      (* notice that the laplace noise is now added in the loop *)
      z <$ lap eps s;
      output = z :: output;
    }
    return output;
  }
}.


(* helper lemma *)
lemma bigops_help : forall n, 
0<=n => eps * n%r = bigi predT (fun (_ : int) => eps) 0 n.
proof. 
move => n H. rewrite sumr_const count_predT size_range max_ler. 
     smt().
  rewrite intmulr; auto.
qed.
 
(*
  we now want to prove that the budget that we spend depends on the size of the list, that is we want to prove that dummy_sum is n*eps-DP
    *)


lemma dummy_sum n : 0<=n => aequiv [ [  (eps *n%r) & 0%r]
  M2.dummy_sum ~ M2.dummy_sum
 :  (adjacent ls{1} ls{2}  /\ n = size ls{1})
      ==> res{2} = res{1} ].
    proof.
    move => H.
    proc.
    seq 3 3: (adjacent ls{1} ls{2} /\ ={i, s, output} /\ i{1} = 0
              /\ s{1} = 0  /\ 0<= n /\ n = size ls{1} ).
      toequiv; auto.
    (*
      we could try to use the usual while rule but this would not bring us very far.
      Instead, we use the approximate while rule which takes as additional parameters
     two functions describing how the privacy budget change at each iteration, and how 
     the number of iterations decreases.
    *)
    awhile  [ (fun _ => eps) & (fun _ => 0%r) ] n [n-i-1] 
    (adjacent ls{1} ls{2} /\ ={i, output} /\ 0 <= i{1} <= n /\
     (! ={s} => `|s{1} - s{2}| <= 1 /\
     eq_in_range ls{1} ls{2} i{1} (n - 1)) /\
     0<= n /\ n = size ls{1});
     first 3 try (auto; progress;smt(ge0_eps)).
     smt(bigops_help).
     rewrite sumr_const intmulr;auto.
     move => v.
     seq 2 2:
     (adjacent ls{1} ls{2} /\ ={i, output} /\ 0 <= i{1} <= size ls{1} /\
     (! ={s} => `|s{1} - s{2}| <= 1 /\
     eq_in_range ls{1} ls{2} i{1} (size ls{1} - 1)) /\
     0<= n /\ n = size ls{1} /\ v=n-i{1}).
     toequiv; auto; progress.
     smt(). smt().
     smt(adjacent_sub_abs_bound).
     smt(adjacent_ne_sub_eq_after).
     smt().
     seq 1 1:
     (adjacent ls{1} ls{2} /\ ={i, output} /\ 0 <= i{1} <= size ls{1} /\
     (! ={s} => `|s{1} - s{2}| <= 1 /\
     eq_in_range ls{1} ls{2} i{1} (size ls{1} - 1)) /\
     0<= n /\ n = size ls{1} /\ v=n-i{1} /\ z{1}=z{2}) <[ eps & 0%r ]>.
     lap (0) 1.   
     auto; progress.
     smt().
     toequiv; auto; progress.
     smt().
     smt().
qed.



(* Here another approach where we add noise to each element *)

module M3 = {
  proc noisy_sum (ls : int list) : int list = {
    var s :int <- 0;
    var output : int list;
    var z : int;
    var i :int <- 0;
    output = [];
    while (i < size ls ) {
      (* we add noise before summing *)
      z <$ lap eps (nth 0 ls i);
      s <- s + z; 
      output <- z :: output;
      i <- i + 1; 
    }
    return output;
  }
}.

(* other helper lemmas *)

lemma count_iota_0 : forall n,
count (transpose (=) n) (iota_ 0 n) = 0.
    proof.
    move => n.
      apply count_eq0. rewrite hasPn. 
    move => x.
    smt(mem_iota).
qed.

lemma count_iota : forall n j,
n=size(iota_ 0 n) =>  0<=j< n =>  (count (fun (i : int) => j = n-i-1) (iota_ 0 n)) = 1.
    proof.
    elim/natind.
    move => n Hn j Hs Hj. smt(size_iota).
    move => n Hn HI j Hs Hj.
      rewrite iotaSr. assumption. simplify.  rewrite -cats1. rewrite count_cat. 
      rewrite /count. case (j=0) => H. rewrite H.
      simplify.  
      have ? : (n+1-n-1=0). smt().
      rewrite H0. simplify.
      have ? :(fun i => i = n) =(fun i => 0=n+1-i-1).  smt(). 
      rewrite -H1. rewrite count_iota_0. smt(). 
      have ? : (n+1-n-1=0). smt().
      rewrite H0 H. simplify.    
      have ? :(fun i => j-1 = n-i-1) =(fun i => j=n+1-i-1).  smt(). 
      rewrite -H1. rewrite HI. smt(size_iota). smt(). smt(). 
  qed.
  
lemma bigi_eps : forall  n j,
    0<= j < n=>
    eps = bigi (fun (i : int) => j = n - i - 1) (fun (_ : int) => eps) 0 n.
    proof.
    move => ? ? ?. rewrite big_const. rewrite count_iota. smt(size_iota). assumption.
    smt(iter1). 
qed.


(* We can now prove that that noisy_sum is eps-DP *)


lemma noisy_sum n j : 0<= j < n => aequiv [ [ eps & 0%r]
  M3.noisy_sum ~ M3.noisy_sum
    :  adjacent_e ls{1} ls{2} j /\ n=size ls{1}
      ==> res{2} = res{1} ].
    proof. 
    move => H. proc.
    seq 3 3: (adjacent_e ls{1} ls{2} j /\ ={i, s, output} /\ i{1} = 0
              /\ s{1} = 0  /\ n=size ls{1}).
      toequiv; auto.
    (* notice the budget function we are using for epsilon *)
    awhile  [ (fun x => if j=n-x -1 then eps else 0%r ) & (fun _ => 0%r) ] n [n -i-1] 
    (adjacent_e ls{1} ls{2} j /\ ={i, output} /\ 0 <= i{1} <= size ls{1} /\ n=size ls{1} /\
      (i{1}=j =>
    `|(nth 0 ls{1} i{1})  - (nth 0 ls{2} i{2}) | <= 1 /\
     eq_in_range ls{1} ls{2} (i{1}+1) (size ls{1} - 1)) /\
        0<=  size ls{1});  first 4 try (auto; progress;smt(ge0_eps)).
       search pred1. search iota_. rewrite /bigi. 
       rewrite -big_mkcond. apply bigi_eps => //. rewrite sumr_const intmulr; smt().
      move => k.
        have H1: (j = n - k - 1)\/ (j <> n - k - 1). smt().
    elim H1 => [?|?].
        wp. progress.
        lap 0 1. smt(). 
       progress. smt().
       progress. smt(). 
       smt(). smt(). 
       smt(adjacent_sub_abs_bound).
       smt(adjacent_ne_sub_eq_after).
       smt(size_eq_adjacent).
       wp. 
       lap 0 0. smt(). 
       progress.  
       smt(size_eq_adjacent).
       auto; progress. smt().
       smt().    
smt(adjacent_sub_abs_bound).
smt(adjacent_ne_sub_eq_after).
smt(size_eq_adjacent).
smt(size_eq_adjacent).
qed. 
