require import Int IntExtra Real RealExtra Ring.
require import Distr List Aprhl StdRing StdOrder StdBigop.
import IntID IntOrder RField RealOrder.

(* defines epsilon and the query*)
op eps: {real | 0%r <= eps } as ge0_eps.
op evalQ: int -> int list -> int.
hint exact : ge0_eps.

(* the notion of adjacent databases are from lab*)
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

(* formal definition of adjacent databases *)
pred adjacent (ms ns : int list) = exists i, adjacent_e ms ns i. 

(* lemmas of adjacency from lab*)
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

(* assume that the query is one sensitive *)
axiom one_sens d1 d2 q: adjacent d1 d2 => `| evalQ q d1 - evalQ q d2 | <= 1.

lemma bigops_help : forall n, 
0<=n => eps * n%r = bigi predT (fun (_ : int) => eps) 0 n.
proof. 
move => n H. rewrite sumr_const count_predT size_range max_ler. 
     smt().
  rewrite intmulr; auto.
qed.
 

(* the above threshold algorithm *)
module M = {
  proc aboveT (db : int list, n:int, t : int) : int = {
    var i : int;
    var nT : int;
    var r : int;
    var s : int;
    s <- 0;
    i <- 0;
    r <- -1;
    (* noisy threshold*)
    nT <$ lap (eps/4%r) t;
    while (i < n) {
      s <$ lap (eps/2%r) (evalQ i db);
      if (nT < s /\ r = -1){
        r <- i;
      }
      i <- i + 1;
    }
    return r;
  }
}.

lemma dp_composition n : 0<=n => aequiv
 [ [eps & 0%r]
   M.aboveT ~ M.aboveT :  (
     adjacent db{1} db{2}  /\
     ={n, t} /\
     n = size db{1} /\
     forall (i: int), (`|evalQ i db{1} - evalQ i db{2}| <= 1)
   )
     ==> res{2} = res{1} ].
proof.
  move => H.
  proc.
(*
   the lap tactic takes two parameters  k1 and k2 and generate two subgoals 
   1) k2 * local_eps <= global eps
   2) |k1 + (M.x{1} - M.x{2})| <= k2
*)
  seq 4 4 :  (
  adjacent db{1} db{2} /\
  ={s, i, r, t, nT, n} /\
  s{1} = 0 /\
  i{1} = 0 /\
  r{1} = -1 /\
  0<=n /\
  n = size db{1}). 
  toequiv; auto.  
    (*
      we could try to use the usual while rule but this would not bring us very far.
      Instead, we use the approximate while rule which takes as additional parameters
     two functions describing how the privacy budget change at each iteration, and how 
     the number of iterations decreases.
    *)

awhile [ (fun _ => eps) & (fun _ => 0%r)]
(n+1)
[n-i]
(
  adjacent db{1} db{2} /\
  ={t, n, i, r, nT} /\
  0<=n /\
  n = size db{1} /\
  n = size db{2} /\
  0 <= i{1} <= n /\
  (! ={s} => `|s{1} - s{2}| <= 1 /\
  eq_in_range db{1} db{2} i{1} (n - 1))
).
    auto.
progress.
    smt(ge0_eps).
    auto.
progress.
    smt(ge0_eps).

    auto.
progress.
smt(ge0_eps).

    auto.
    progress.
    smt.
    trivial.
    rewrite sumr_const intmulr;auto.
    rewrite count_predT size_range max_ler.
smt.

admit.
    rewrite sumr_const;auto.
     rewrite intmulr; auto.
move => v.
     seq 1 1:
       (adjacent db{1} db{2} /\ ={i, t, r, nT, n} /\ 0 <= i{1} <= size db{1} /\
       `|s{1} - s{2}| <= 1 /\
       0 <= n /\
       n = size db{1} /\ v=n-i{1} /\ s{1}=s{2}) <[ eps & 0%r ]>.
       lap (0) 1.
smt.
auto; progress.
         smt.
progress.
       
toequiv.
if.
progress.
         auto. progress.








         smt().
smt().
admit.
smt().
auto; progress.
smt.
smt.
admit.
smt.

         
