Require Import Qabs.
Require Export ZArith.
Require Export Mylist.
Require Export Pol1sparse_is_ring.
Require Export Utils.


 Module POLY(QOPS:RAT_OPS).
   Import QOPS.
   Module QPROP := RAT_PROP QOPS.
   Import QPROP.
(*coefficient structure for the previous parametric set of rationnal numbers *)
   
   Definition Rat_coef_set :=
     mk_cset Rat R0 R1 RatEq Rat_add Rat_prod Rat_sub Rat_opp Rat_zero_test.


  (* une fois qu'on aura les preuves 

   Definition Rat_coef_eq :=
     mk_ceq Rat Rat_coef_set RatEq_refl RatEq_sym RatEq_trans
     Rat_add_ext Rat_prod_ext Rat_opp_ext.
     

   Definition Rat_coef_th :=
     mk_ct Rat Rat_coef_set Rat_0_l Rat_add_sym Rat_add_assoc Rat_prod_1_l
     Rat_prod_sym Rat_prod_assoc Rat_distr_l Rat_sub_spec Rat_opp_spec.
 *)

  (*univariate polynomials over Q*)
   

   Definition Poly := Pol1 Rat.
   
   Implicit Arguments PX [C].
   Implicit Arguments Pc [C].
   
   Implicit Arguments Pol1Eq.
   Implicit Arguments Padd.
   Implicit Arguments Pmul.
   Implicit Arguments Psub.
   Implicit Arguments Pop.
   Implicit Arguments Ppow.

   Delimit Scope P_scope with Pol1.
   Bind Scope P_scope with Pol1.

   Open Scope P_scope.

   Notation "x != y" := (Pol1Eq Rat_coef_set x y) : P_scope.
   Notation "x ++ y" := (Padd Rat_coef_set x y) : P_scope.
   Notation "x ** y" := (Pmul Rat_coef_set x y) : P_scope.
   Notation "x -- y" := (Psub Rat_coef_set x y) : P_scope.
   Notation "-- x" := (Pop Rat_coef_set x) : P_scope.
   Notation "x ^ y" :=(Ppow Rat_coef_set x y) :P_scope.

   Definition poly_zero_test := (Pol1_zero_test Rat Rat_coef_set).
   Definition  Rat_mkPX := (mkPX Rat Rat_coef_set).
   
  (* division by a (Rational) constante  *)
   Fixpoint div_cst(A:Poly)(q:Rat){struct A}:Poly:=
     match A with
       |Pc a => Pc (a/q)
       |PX P i p => PX (div_cst P q) i (p/q)
     end.
   
    (* product of a polynomial by a constant *)
   Fixpoint mult_cst(A:Poly)(q:Rat){struct A}:Poly:=
     match A with
       |Pc a => Pc (a*q)
       |PX P i p => Rat_mkPX (mult_cst P q) i (p*q)
     end.


  (*derivative*)
   Fixpoint deriv(P:Poly):Poly :=
     match P with
       |Pc c => Pc R0
       |PX A i a => match i with
		      |xH => A ++ (Rat_mkPX (deriv A) xH R0)
		      |_ => (mult_cst (PX A (Ppred i) R0) (Rat_of_pos i)) ++ 
			(Rat_mkPX (deriv A) i R0)
		    end
     end.

   

  (* evaluation of a Poly at a Rat *)
   Fixpoint eval(P:Poly)(x:Rat){struct P} : Rat :=
     match P with
       |Pc c =>  c
       |PX A i a => ((eval A x)*(Rat_pow x (Npos i)) )+a
     end.
   

  (*couple degree * coefdom for a polynomial in normal form *)
   Fixpoint deg_coefdom(A:Poly) : N*Rat :=
     match A with
       |Pc a => (N0,a)
       |PX P i p => let (d,c) := (deg_coefdom P) in (Nplus (Npos i) d, c)
     end.

   Section euclide_aux.

     Variable D : Poly.
     
     (*degee and leading coef of D*)
     Let dd_cd := deg_coefdom D.
     Let dd := fst dd_cd.
     Let cd := snd dd_cd.
     
  (*auxiliary division of RX^i by D.invariant : 
  -- deg R < deg D
  -- R <> 0
  -- D is not constant *)		
   Fixpoint div_aux(R : Poly)(i:positive){struct i}:Poly*Poly :=
     let (dr,cr) := (deg_coefdom R) in
       match (Ncompare (dr + (Npos i)) dd) with
	 |Lt => (Pc R0, PX R i R0)
	 | _  => 
	   match i with
	   | xH => (Pc (cr/cd), (Rat_mkPX R xH R0) -- (mult_cst D (cr/cd)))
	   | xO p =>
	       let (Q1, R1) := (div_aux R p) in
	       let (dR1, cR1):=(deg_coefdom R1) in
	       if (Rat_zero_test cR1) then (Rat_mkPX Q1 p R0, Pc R0)
	       else
		 let (Q2, R2):=(div_aux R1 p) in 
		 ((Rat_mkPX Q1 p R0) ++ Q2, R2)
	  | xI p =>
	       let (Q1, R1):=(div_aux R p) in
	       let (dR1, cR1):=deg_coefdom R1 in
	       if (Rat_zero_test cR1) then 
		 ((Rat_mkPX Q1 (Psucc p) R0), Pc R0)
	       else
		 let (Q2, R2) := (div_aux R1 p) in
		 let (dr2, cr2) := (deg_coefdom R2) in
		 if (Rat_zero_test cr2) then
		   ((Rat_mkPX Q1 (Psucc p) R0)++(Rat_mkPX Q2 xH R0), Pc R0)
		 else
		   match (Ncompare (Nsucc dr2) dd) with
		   | Lt => 
		     ((Rat_mkPX Q1 (Psucc p) R0)++(Rat_mkPX Q2 xH R0), Rat_mkPX R2 xH R0)
		   | _ =>
		     let quo := (Rat_mkPX Q1 (Psucc p) R0)++ (Rat_mkPX Q2 xH R0)++(Pc (cr2/cd)) in
                     let rem := (Rat_mkPX R2 xH R0) -- (mult_cst D (cr2/cd)) in
		     (quo,rem)
		   end
	   end
       end.
 
 End euclide_aux.

(*straightforward division of polynomials with coef in Rat:
  - as usual arguments are supposed to be normalized
  - div_euclide A B = (Q,R) with  A = BQ +R and 
	--either deg(R)< deg(B)
	-- or deg(R)=deg(B)=0 and R != P R0
	-- Q and R are normalized
  ** non trivial case :
  if AX^i +a is to be divided by B, with  A = PQ1 + R1 and deg(R1)<deg(B)
  then AX+a=(BQ1)X^i + R1X^i +a and :
    - either deg (R1X^i +a) < deg (B),it ok : Q = X^i*Q1 and R = R1X^i + a
    - or deg (R1X^i +a) >= deg (B) and  Q = (X^i*Q1+Q2) et R = R2 + a
  where (Q2, R2) = div_aux B db cb R1 i i.e. R1X^i = Q2B +R2
  ** poly returned are normalized as soon as args are normalized
  *)
 
 (*first division by a non constant polynomial*)
 Section euclide_PX.
   Variable B : Poly.
   Let dcb := deg_coefdom B.
   Let db := fst dcb.
   Let cb := snd dcb.

   (*division of A by the non constant polynomial B*)
   Fixpoint euclide_div_PX (A :Poly):Poly*Poly :=
   match A with
     |Pc a => (Pc R0, Pc a)
     |PX P i p =>
       let (Q1, R1):=euclide_div_PX P in
	 let (dr, r) := deg_coefdom R1 in
	   match (poly_zero_test R1),(Ncompare (Nplus (Npos i) dr) db) with
	     |true, _ => (Rat_mkPX Q1 i R0, Pc p)
	     | _ , Lt => (Rat_mkPX Q1 i R0, Rat_mkPX R1 i p)
	     | _ , _ => let (Q2, R2) := (div_aux B R1 i) in
	       ((Rat_mkPX Q1 i R0)++Q2, R2 ++ Pc p)
	   end
   end.

 End euclide_PX.

 (*general division function *)
 Definition euclide_div(A B:Poly):Poly*Poly :=
   match B with
     |Pc q => (div_cst A q, Pc R0)
     |PX _ _ _ => (euclide_div_PX B A)
   end.

(* principal signed subresulants sequence for P and Q*)
(*ie without zeros and repetitions modulo a constant*)
(* P = a_p X^p + ... + a_0 *)
(* Q = b_q X^q + ... + b_0 WARNING : with q < p *)
(* cf agorithm 8.73 in MFR *)




  (*q to the n*(n+1)/2 *)
 Definition sum_pow(q:Rat)(n:N):Rat :=
   match n with
     |N0 => R1
     |Npos p => 
       match p with
	 |xH => q
	 |xO p' => Rat_pow q (Npos (Pmult p' (Psucc p)))
	 |xI p' => Rat_pow q (Npos (Pmult (Psucc p') p))
       end
   end.

(*computation of the kth subresultant coefficient*)
 Definition subres_aux (j k:N)(q q':Rat):Rat:=
   let t := (Npred (Nminus j k)) in
     (sum_pow (- R1) t)*(Rat_pow (q/q') t)*q.


  (*next polynomial in the sequence,after ASRi_1 and SRj_1 and arguments
    for the possible next step of computations. if is nul, then B was
    the last poly of the sequence. SRj_1 is no nul*)
 

 Definition next_subres(SRi_1 SRj_1:Poly)(srj:Rat)(i j:N):
   Poly * Rat * N * N :=
   let (k, dom_srj_1) := (deg_coefdom SRj_1) in
   let (d, dom_sri_1) := (deg_coefdom SRi_1) in
   let next_SR := fun x:Rat =>
     --(div_cst 
       (snd (euclide_div (mult_cst SRi_1 x) SRj_1))
       (srj * dom_sri_1)) in
     match (Ncompare k  (Npred j)) with
       |Eq => 
	 let srj_1 := dom_srj_1 in
	   (next_SR (Rat_pow dom_srj_1 2), dom_srj_1, j, k)
       |_ => 
	 let srk := (subres_aux j k dom_srj_1 srj) in
	   (next_SR (dom_srj_1 * srk), srk, j, k)
     end.



  (* extended version, for extended subresultants 
 Definition next_subres_triple(Ti_1 Tj_1:Poly*(Poly*Poly))(srj:Rat)(i j:N):
   (Poly*(Poly*Poly))* Rat * N * N :=
   let (SRi_1,Di_1) := Ti_1 in
   let (SRj_1,Dj_1) := Tj_1 in
   let (Ui_1,Vi_1) := Di_1 in
   let (Uj_1,Vj_1) := Dj_1 in
   let (k, dom_srj_1) := (deg_coefdom SRj_1) in
   let (d, dom_sri_1) := (deg_coefdom SRi_1) in
   let next_poly := fun (P Q:Poly)(x:Rat) => 
	   -- (div_cst (snd (euclide_div (mult_cst P x) Q))
	     (srj * dom_sri_1))  in
     match (Ncompare k  (Npred j)) with
       |Eq => 
	 let y:= (Rat_pow dom_srj_1 2) in
	   (next_poly SRi_1 SRj_1 y,((next_poly Ui_1 Uj_1 y), next_poly Vi_1 Vj_1 y), dom_srj_1, j, k)
       |_ => 
	 let srk := (subres_aux j k dom_srj_1 srj) in
	 let x:= (dom_srj_1 * srk) in
	 let next_SR := next_poly SRi_1 SRj_1 x in
	 let (_,dom_srk_1) := deg_coefdom next_SR in
	   (next_SR,(next_poly Ui_1 Uj_1 x, next_poly  Vi_1 Vj_1 x),
	     srk, j, k)
     end.
*)

 Definition next_subres_triple(Ti_1 Tj_1:Poly*(Poly*Poly))(srj:Rat)(i j:N):
   (Poly*(Poly*Poly))* Rat * N * N :=
   let (SRi_1,Di_1) := Ti_1 in
   let (SRj_1,Dj_1) := Tj_1 in
   let (Ui_1,Vi_1) := Di_1 in
   let (Uj_1,Vj_1) := Dj_1 in
   let (k, dom_srj_1) := (deg_coefdom SRj_1) in
   let (d, dom_sri_1) := (deg_coefdom SRi_1) in
   let next :=
     (fun x => 
       let (C,R) := (euclide_div (mult_cst SRi_1 x) SRj_1) in
       (C, div_cst R ((- srj)*dom_sri_1)) ) in
   let next_UV :=
     (fun (x:Rat)(Pi_1 Pj_1 C:Poly) =>
       (div_cst
	 ((C ** Pj_1) -- (mult_cst Pi_1 x)) (srj*dom_sri_1))) in
     match (Ncompare k  (Npred j)) with
       |Eq => 
	 let y:= (Rat_pow dom_srj_1 2) in
	 let (C,SR) := next y in
	   (SR, (next_UV y Ui_1 Uj_1 C, next_UV y Vi_1 Vj_1 C), dom_srj_1, j, k)
       |_ => 
	 let srk := (subres_aux j k dom_srj_1 srj) in
	 let y:= (dom_srj_1 * srk) in
	 let (C,SR) := next y in
	   (SR, (next_UV y Ui_1 Uj_1 C, next_UV y Vi_1 Vj_1 C), srk, j, k)
     end.


    (*builds the list, from A B n ensures termination and will be deg P + 1*)

 Fixpoint signed_subres_list(A B:Poly)(q:Rat)(i j:N)(m:nat){struct m}:list Poly :=
   match m with
     |O => nil
     |S n => 
       let (next,l) := (next_subres A B q i j) in
       let (next',k) := next in
       let (SR, sr) := next' in
	 if (poly_zero_test SR) then nil
	   else   SR :: (signed_subres_list B SR sr k l n)
   end.


 (*extended versions,to deal with triples, goes one step further to get the last V*)
 Fixpoint ext_signed_subres_list(T T':Poly*(Poly*Poly))(q:Rat)(i j:N)(m:nat)
   {struct m}:list (Poly*(Poly*Poly)) :=
   let (B,D):= T' in
     if (poly_zero_test B) then nil
       else
	 match m with
	   |O => nil
	   |S n => 
	     let (next,l) := (next_subres_triple T T' q i j) in
             let (next',k) := next in
	     let (next_T, sr) := next' in
	     let (next_SR,_) := next_T in
     	       next_T :: (ext_signed_subres_list T' next_T sr k l n)
	 end.



	 
 Section SUBRES_CHAIN.
   Variable P Q :Poly.
   Let ddp := deg_coefdom P.
   Let ddq := deg_coefdom Q.
   Let deg_p := fst ddp.
   Let deg_q := fst ddq.
   Let dom_p := snd ddp.
   Let dom_q := snd ddq.

  (*first polynomials in the subresultant chain*)
   
   Definition subres_chain_init :=
     match (Rat_sign dom_p) with
       |Z0 => (Pc R0, R0, Pc R0) (*must never happen!*)
       |Zpos _ => (P, R1, Q)
       |Zneg _ => match (Npred (Nminus deg_p deg_q)) with
		    |N0 => (P, - R1, Q) 
		    |Npos p => match p with
				 |xO _ => (P, (- R1), Q) 
				 |_ => (-- P, R1, (-- Q))
			       end
		  end
     end.
   

   Let SRq := snd subres_chain_init.
   Let SRp := fst (fst subres_chain_init).
   Let srp := snd (fst subres_chain_init).

   Let Up := Pc R1.
   Let Uq := Pc R0.
   Let Vp := Pc R0.
   Let Vq := Pc R1.

   Let Tp := (SRp, (Up, Vp)).
   Let Tq := (SRq, (Uq, Vq)).
   
   Definition signed_subres_chain : list Poly :=
     SRp :: (SRq :: 
       (signed_subres_list SRp SRq srp deg_p (Npred deg_p) (S (nat_of_N deg_p)))).

 
   (* extended signed subres chain *)
   Definition ext_signed_subres_chain : list (Poly*(Poly*Poly)) :=
     Tp :: (Tq :: 
    (ext_signed_subres_list
      Tp Tq  srp deg_p (Npred deg_p) (S (nat_of_N deg_p)))).
     
       


 End SUBRES_CHAIN.
 


   (*gcd of P and Q : last subresultant*)
 Definition gcd (P Q:Poly) :=
   let l := (signed_subres_chain P Q) in 
   let SRj := (last_elem l Q) in
   let (_, srj) := deg_coefdom SRj in
   let (_, cP) := deg_coefdom P in
     div_cst (mult_cst SRj cP) srj.
    




  (*gcd of P and Q, and gcd free part of P with respect to Q, pourZ,
ca rajoute des contenus dans les DEUX
 Definition gcd_gcd_free (P Q:Poly) :=
   let (_, cP) := deg_coefdom P in
   let (Tj, Tj_1):= two_last_elems (ext_signed_subres_chain P Q) 
     ((Pc R0, (Pc R0,Pc R0)),(Pc R0, (Pc R0,Pc R0))) in
   let (SRj,Dj) := Tj in
   let (_, srj) := deg_coefdom SRj in
   let (_,Dj_1) := Tj_1 in
   let (_, Vj_1) := Dj_1 in
   let (_, cVj_1) := deg_coefdom Vj_1 in 
     (div_cst (mult_cst SRj cP) srj, (div_cst (mult_cst Vj_1 cP) cVj_1)).
*)    

(*WARNING we have NOT gcd*(gcd_free)=P but up to a constant
returns, gcd, gcd_free of P, gcd_free of Q*)
 Definition gcd_gcd_free_strict (P Q:Poly) :=
   let (Tj, Tj_1):= two_last_elems (ext_signed_subres_chain P Q) 
     ((Pc R0, (Pc R0,Pc R0)),(Pc R0, (Pc R0,Pc R0))) in
   let (SRj,Dj) := Tj in
   let (_,Dj_1) := Tj_1 in
   let (Uj_1, Vj_1) := Dj_1 in
     (SRj, Vj_1, Uj_1).

(*TODO virer les contenus constants?*)


  (*gcd of P and Q : last subresultant, one preliminary step for
 polys of same deg*)
 Definition gcd_gcd_free (P Q:Poly) :=
   let (dQ,cQ):= deg_coefdom Q in
   let (dP,cP):= deg_coefdom P in
     match (Ncompare dP dQ) with
       |Eq => 
	 let Next := (mult_cst Q cP) -- (mult_cst P cQ) in
	 let (GCD_Q',Next'):= gcd_gcd_free_strict Q Next in
	 let (GCD,Q'):= GCD_Q' in
	 let (_,cGCD) := deg_coefdom GCD in
	 let (_,cQ') := deg_coefdom Q' in
	 let (_,cNext') := deg_coefdom Next' in
	 let (_,cNext) := deg_coefdom Next in
	   (GCD,
	     (mult_cst Q' ((cGCD*cNext'*cP)/cNext)) -- 
	     (mult_cst Next' ((cGCD*cQ')/cQ)),
	     Q')
       |_ => gcd_gcd_free_strict P Q
     end.
    

 Definition square_free(P:Poly) := snd (fst (gcd_gcd_free P (deriv P))).


    (*evaluation of the sign of a list of Poly at a rational point x*)
 Fixpoint sign_eval_map(l:list Poly)(x:Rat){struct l} : list Z := 
  match l with
    |nil => nil
    |P :: l' => (Rat_sign (eval P x)) :: (sign_eval_map l' x)
  end.


  (*number of sign changes in a list of binary integers*)
  (*recursion on list lenght*)
  (*mieux?*)

 Fixpoint sign_changes_rec(l: list Z)(n : nat){struct n} : nat :=
   match n with
     |O => O
     |S n => match l with
	      |nil => O
	      |a :: l' => match a with
			   |Z0 => sign_changes_rec l' n
			   |_ => match l' with
				  |nil => O
				  |b :: l'' => match (a*b)%Z with
						|Z0 => sign_changes_rec (a :: l'') n
						|Zpos _ => sign_changes_rec l' n
						|Zneg _ => S (sign_changes_rec l' n)
					       end
				 end
			  end
	     end
   end.

 Definition sign_changes(l : list Z) : nat := sign_changes_rec l (length l).

  (*sturm theorem : computes
  #{x \in ]a,b[| P(x)=0 & Q(x) > 0} - # {x\in ]a,b[ | P(x)=0 & Q(x)<0}
  using the modified sturm sequence ie the subresultant chain
  of P and P'Q *)
(*precondition : a et b are not roots of P*)
 Definition sturm_query(P Q:Poly)(a b:Rat):nat :=
   let sturm_seq := signed_subres_chain P ((deriv P)**Q) in
   let va := sign_eval_map sturm_seq a in
   let vb := sign_eval_map sturm_seq b in
     ((sign_changes va) - (sign_changes vb))%nat.

  (*some transformations over polynomials, useful later fo Bernstein*)


 
(*P(X+c), on pourrait s'embeter plus quand meme*)
 Fixpoint Ptranslate(P:Poly)(c:Rat){struct P}:Poly:=
   match P with
     |Pc p => P
     |PX P' i p' => 
       let Q := Ptranslate P' c in 
	 (Q**((PX (Pc R1) xH c) ^ (Npos i))) ++ (Pc p')
   end.


  (*P(cX)*)
 Fixpoint dilat(P:Poly)(c:Rat){struct P}:Poly:=
   match P with
     |Pc _ => P
     |PX P' i p => PX (mult_cst  (dilat P' c) (Rat_pow c (Npos i))) i p
   end.

   (* X^d * P(1/X) where deg(P)=d, ie "reverse" of the polynomial *) 
 Fixpoint Rev1(Q P:Poly)(i:positive){struct P}:Poly:=
   match P with
     |Pc c => Rat_mkPX Q i c
     |PX P' j p => Rev1 (Rat_mkPX Q i p) P' j
   end.
  
 Definition Rev(P:Poly):=
   match P with
     |Pc c => Pc c
     |PX P' i p' => Rev1 (Pc p') P' i 
   end.





(*transfoms a pol in Horner form into a list of coef*power, and reverses
 Fixpoint Pol_to_list'(l:list (Rat*N))(P:Poly){struct P}:list (Rat*N) :=
   match P with
     |Pc p => (p,N0)::l
     |PX Q i q => Pol_to_list' ((q, Npos i)::l) Q
   end.

 Definition Pol_to_list := Pol_to_list' nil.

  builds a pol in Honer form from a list of coef*power
 Fixpoint list_to_Pol(l:list (Rat*N)):Poly :=
   match l with
     |nil => Pc R0   ********should never happen!
     |h::t => 
       let (coef,deg):= h in
	 match t with
	   |nil => Pc coef
	   |h'::t'=>
	     let (coef',deg'):=h' in
	       match deg' with
		 |N0 => Pc coef  *********should never happen
		 |Npos d' =>
		   let Q := list_to_Pol t in
		     Rat_mkPX Q d' coef
	       end
	 end
   end.


 
 Definition Rec(P:Poly):Poly := list_to_Pol (Pol_to_list P).
 *)


   (*adds i times the rationnal r in head of the Rat list l*)
 Fixpoint repeat_add(r:Rat)(i:positive)(l:list Rat){struct i}:list Rat :=
   match i with
     |xH => r::l
     |xO p => repeat_add r p (repeat_add r p l)
     |xI p => r::(repeat_add r p (repeat_add r p l))
   end.


   (*list of coef of a Poly of degree <= p, over 1, X,..., X^p, with
  all zeros, constant in head, *)
 
 Fixpoint Pol_to_list_dense(P:Poly)(p:N){struct P}:list Rat:=
   match P with
     |Pc c =>
       match p with
	 |N0 => c::nil
	 |Npos p' => c::(repeat_add R0 p' nil)
       end
     |PX Q i q =>
       match i with
	 |xH => q::(Pol_to_list_dense Q (Npred p))
	 |_ => q :: (repeat_add R0 (Ppred i) (Pol_to_list_dense Q
	   (Nminus p (Npos i))))
       end
   end.


(*divides by the proper binomial coefs to get the bern coefs*)
 Fixpoint binomial_div (l:list Rat)(p:N)(i:N){struct l}:list Rat:=
   match l with
     |nil => nil
     |h::t => (h/(binomial p i))::(binomial_div t p (Npred i))
   end.


(*coefs of P in the Bernstein basis over c,d,p form b_p to b_0 if
  p is the degree of P*)
 Definition bernstein_coefs(P:Poly)(c d:Rat)(p:N):list Rat :=
   let (deg, coef) := deg_coefdom P in
   let Q := (Ptranslate (Rev (dilat (Ptranslate P c) (d -c))) ( R1)) in
   let list_coef := Pol_to_list_dense Q p in
     binomial_div list_coef deg deg.

 
  (*input : list of bernstein coefs for P of deg <= p in the bern basis
    p over c,d. and a rational e
  
  output : list of bernstein coefs for P of deg <= p in the bern basis
  p over c,e 
  and
  list of bernstein coefs for P of deg <= p in the bern basis
  p over e,d
  *)

 Section BERN_SPLIT.
   Variables c d e:Rat.
   Definition  alpha := (d-e)/(d-c).
   Definition beta := (e-c)/(d-c).
   
  (* computation of the next diag in the "Pascal triangle" of the
    Bernstein relation *)
   
   Fixpoint next_diag_bern(diag:list Rat)(b:Rat){struct diag}:list Rat:=
     match diag with
       |nil => b::nil
       |hd :: tl => 
	 let l:=next_diag_bern tl b in
	   match l with
	     |nil => nil (*should never happen*)
	     |rhd::rtl => ((alpha*hd)+(beta*rhd))::l
	   end
     end.
    (* computation of the new coef, given the previous from b0 to bp
    WARNING, b'' is in reverse order*)

   Fixpoint bern_split1(bern_coef b' b'':list Rat){struct bern_coef}
     :(list Rat)*(list Rat):=
     match bern_coef with
       |nil  => (b',b'')
       |hd::tl => 
	 let next_b'':= next_diag_bern b'' hd in
	   match next_b'' with
	     |nil => (nil,nil) (*should never happen*)
	     |hd''::tl'' => bern_split1 tl (hd''::b') next_b''
	   end
     end.

 End BERN_SPLIT.

   Definition bern_split(bern_coef:list Rat)(c d e:Rat):=
     let (b',b''):= bern_split1 c d e (rev bern_coef) nil nil in 
       (b', rev b'').


 (*splitting again but without introducing any denominators*)

(*computes 2^p lp :: 2^{p-1} lp-1 :: ... :: l1 P :: l0 :: nil form the list l*)

 Fixpoint list_2_pow_mult(l:list Rat): N * (list Rat) :=
   match l with
     |nil => (N0, nil)
     |lhd::ltl => 
       let (p,l'):=(list_2_pow_mult ltl) in
       (Nsucc p , ((Rat_pow (2#1) p)*lhd)::l')
   end.

 Definition spe_bern_aux(l:list Rat) := snd (list_2_pow_mult l).


 
 Fixpoint next_diag_spe_bern(diag:list Rat)(b:Rat){struct diag}:list Rat:=
   match diag with
     |nil => b::nil
     |hd :: tl => 
       let l:=next_diag_spe_bern tl b in
	 match l with
	   |nil => nil (*should never happen*)
	   |rhd::rtl => (hd+rhd)::l
	 end
   end.
 
      (* computation of the new coef, given the previous from b0 to bp
	WARNING, b'' is in reverse order*)
 
 Fixpoint spe_bern_split1(bern_coef b' b'':list Rat){struct bern_coef}
   :(list Rat)*(list Rat):=
   match bern_coef with
     |nil  => (b',b'')
     |hd::tl => 
       let next_b'':= next_diag_spe_bern b'' hd in
	 match next_b'' with
	   |nil => (nil,nil) (*should never happen*)
	   |hd''::tl'' => spe_bern_split1 tl (hd''::b') next_b''
	 end
     end.


(*coefficients of 2^p P in the bernstein basis of c,(c+d)/2 and in the
  bernstien basis of (c+d)/2,d, given the coef of P  in the bern basis
  of c,d,p*)
 Definition spe_bern_split(bern_coef:list Rat):=
   let (b',b''):= spe_bern_split1 (rev bern_coef) nil nil in 
     ((spe_bern_aux b'),(spe_bern_aux (rev b''))).


 (*rational lower bound for the roots of P*)
 Fixpoint sum_abs_val_coef(P:Poly):Rat:=
   match P with
     |Pc p => Rat_abs_val p
     |PX P' i p => (Rat_abs_val p) + sum_abs_val_coef P' 
   end.

 Definition root_up_bound(P:Poly):=
   let (_,p):= deg_coefdom P in
     (sum_abs_val_coef P)/(Rat_abs_val p).

 Fixpoint root_low_bound1(P:Poly)(res:Rat){struct P}:Rat:=
   match P with
     |Pc p => res / (Rat_abs_val p)
     |PX Q i q => root_low_bound1 Q (res + Rat_abs_val q)
   end.

 Definition root_low_bound(P:Poly):=
   match P with
     |Pc p => R1
     |_ => root_low_bound1 P R0 
   end.


 Inductive Inter : Set :=
   |Singl : Rat -> Inter
   |Pair : Rat -> Rat -> Inter.


 Section ISOL.

   Variable P:Poly.
   Let ubound := root_up_bound P.
   Let lbound := root_low_bound P.
   Let  Pbar := square_free P.
   Let degPbar := fst (deg_coefdom Pbar).

    (*Real root isolation, last arg to decrease, P<>0 *)
   Fixpoint root_isol1(res:list Inter)(todo:list (Rat*Rat))
     (c d:Rat)(blist: list Rat)(n:nat){struct n}:(list Inter)*(list (Rat*Rat)):=
     let Vb := sign_changes (map Rat_sign blist) in
       match Vb  with
	 |O => (res,todo)
	 |S m =>
	   let test := Rat_zero_test ((eval Pbar c)*(eval Pbar d)) in 
	     match m,test with
	     |O, false => ((Pair c d)::res,todo)
	     |_, _ =>
	       match n with
		 |O => (res, (c,d)::todo)
		 |S n' => 
		   let mid := (d-c)/(2#1) in
		   let (b', b''):= bern_split blist c d mid in
		   let (res',todo'):=(root_isol1 res todo c
		     mid  b' n') in
		   if (Rat_zero_test (eval Pbar c)) 
		     then
		       root_isol1 ((Singl c)::res') todo' mid d b'' n'
		     else
		       root_isol1 res' todo' mid d b'' n'
	       end
	     end
       end.

 Definition root_isol:= 
   root_isol1 nil nil (- lbound) ubound (bernstein_coefs Pbar (- lbound)
     ubound degPbar).

 

End ISOL.

End POLY.
