intrinsic JointEigenspaceDecomposition(L::SetIndx) -> Assoc
  {
  Given an indexed set of axes L = \{ a_1, ..., a_n\}, decompose the algebra into joint eigenspaces for these axes.  Returns an associative array where the element A_lm_1(a_1) \cap ... \cap A_lm_n(a_n) has keys give by the set of eigenvalues \{ lm_1, ..., lm_n \}.
  }
  
        require forall{x:x in L|Type(x) eq ParAxlAlgElt} : "The elements are not axial algebra elements.";
	/* should we check that the a_i are axes, i.e., HasMonsterFusion(a_i)? */
	decomps:=AssociativeArray();
	A:=Parent(L[1]); /* why this must be really axial*/ 
	eigs:=[1,0,1/4,1/32];
	n:=#L;
	dims:=[];
	ads:=[AdMat(L[i]):i in [1..n]];
	Lst:=[[Eigenspace(ads[i],1):i in [1..n]],[Eigenspace(ads[i],0):i in [1..n]],[Eigenspace(ads[i],1/4):i in [1..n]],[Eigenspace(ads[i],1/32):i in [1..n]]];
	cart:=CartesianPower([1..4],n);
	for x in cart do 
		joint_space:=&meet[Lst[x[i]][i]:i in [1..n]];
		dim:=Dimension(joint_space);
		if not dim eq 0 then
			Append(~dims,dim);
			decomps[[eigs[x[i]]:i  in [1..n]]]:=joint_space;
		end if; 
	end for; 
	return decomps;
end intrinsic;

/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+                                                                                                             +
+ Given an element a of an axial Algebra A, find the matrix of ad_a. The element a must really be axial.      +
+													      +
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++===+++*/

intrinsic AdMat(a::ParAxlAlgElt) ->AlgMatElt
{
Given an axial algebra element a, find its ad_a matrix.
}

	require Type(a) eq ParAxlAlgElt: "The element a is not an axial algebra element."; 
	A:=Parent(a);
	F:=BaseField(A);
	return Matrix(F,[Eltseq(a*A.i):i in [1..Dimension(A)]]);
end intrinsic;

/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Given an algebra A, determine if it is a unital algebra.                                                                                  +
+                                                                                                                                           +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/ 

intrinsic HasIdentityAlg(A::ParAxlAlg)->BoolElt, ParAxlAlgElt
	{Given an axial algebra A, determine if it has identity. Returns true if and only if it has one.
	If true, the identity is returned as a second element.
	}

	require Type(A) eq ParAxlAlg: "A is not a partial axial algebra";
	
	tens:=[];
	d:=Dimension(A);
	V:=VectorSpace(Rationals(),d);
	for i:=1 to d do 
		for j:=i to d do 
			Append(~tens,V!Eltseq(A.i*A.j));
		end for;
	end for;
	k:=1;
	rows:=[];
	vecs:=[];
	sols:=[];
	for k:=1 to d do
		for l:=1 to d do
		       	row:=[];
			for i:=1 to d do
				ii:=Minimum({i,k});jj:=Maximum({i,k});
				Append(~row,tens[IntegerRing()!((ii-1)/2*(2*d+2-ii))+jj-ii+1][l]); 
			end for;
			Append(~rows,row);	

		end for;
			vec:=Zero(V);
			vec[k]:=1;
		Append(~vecs,vec);
	
		end for;
		
		big_vec:=&cat[Eltseq(x):x in vecs];
		big_vec:=Vector(Rationals(),big_vec);	
		bool,ein:= IsConsistent(Transpose(Matrix(Rationals(),rows)),big_vec);
		if bool eq false then
			return bool; 
		else
			return bool, A!ein; 
		end if;
end intrinsic;

/*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ This function takes an axial algebra A, a subspace V (not necessarily a subalgebra) and attempts to find all the +
+ idempotents in V. This takes optional parameters (length, form,one) so that we can determine idempotents of a    +
+ prescribed length. In such a case it will be advantageous to input a form and identity if A has.                 +
+                                                                                                                  +
+ ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/
intrinsic FindAllIdempotents(A::ParAxlAlg, U::ModTupFld: length:=0, form :=IdentityMatrix(BaseField(A),Dimension(A)), one:=A!0, extra_rels:=[]) -> SetIndx
  {
  Given an algebra A and a subspace (not necessarily a subalgebra) U, find all the idempotents of A contained in U.
  
  Optional arguments:
    length - requires the length of the idempotents to be as given
    form - the Frobenius form
    one- the identity of A. 
    extra_rels - require the idempotent to satisfy extra relation(s).  These are given by multivariate polynomials in dim(U) variables corresponding to the basis of U.
  }
 	
	require Type(form) eq AlgMatElt: "form must be a matrix";
	require Nrows(form) eq Ncols(form): "Form must be a square matrix";
	require Type(one) eq ParAxlAlgElt: " one must be an axial algebra element"; 
	n:=Dimension(A);
	id_mat:=IdentityMatrix(BaseField(A),n);
	m:=Dimension(U);
	F:=BaseField(A);
	require IsCoercible(F,length): "The length must be a field element";
	R:=PolynomialRing(F,m);/*Set up F[x_1,x_2,...,x_m].*/
	FF:=FieldOfFractions(R);
	AF:=ChangeRing(A,FF);
	v:=&+[R.i*AF!U.i:i in [1..m]];/*Set up $\sum_{i=1}^m x_iv_i. where v_1,v_2,...,v_m is a basis. */
	if not length eq 0 then
		if form eq id_mat then
			bool,M:=HasFrobeniusForm(A);
			if bool eq false then
				return "fail, the concept of length is not defined";
			elif bool eq true then
				form:=M;
			end if;
		end if;/*at this stage we either have a form or the function has already returned a fail*/
		M:=form;
		if one eq A!0 then
			bool,one:=HasIdentityAlg(A);
			if bool eq false then
				 len_rest:=FrobFormAtElements(v,v,M)-length;
			elif bool eq true then
				one:=AF!Eltseq(one);
				len_rest:=FrobFormAtElements(one,v,M)-length;/* here we use (v,v)=(v,v*1)=(v*v,1)=(v,1)*/ 
			end if;
		else 
			one:=AF!Eltseq(one);		
			len_rest:=FrobFormAtElements(one,v,M)-length;/* here we use (v,v)=(v,v*1)=(v*v,1)=(v,1)*/ 
		end if;	
		if extra_rels eq [] then  
			I:=ideal<R|Eltseq(v*v-v) cat [len_rest]>;
		elif extra_rels ne [] and Dimension(ideal<R|Eltseq(v*v-v) cat [len_rest]>) gt 0 then  
			I:=ideal<R|Eltseq(v*v-v) cat [len_rest] cat extra_rels>;

		else	
			I:=ideal<R|Eltseq(v*v-v) cat [len_rest] >; 
		end if; 
	elif length eq 0 then
		if extra_rels eq [] then  
			I:=ideal<R|Eltseq(v*v-v)>;
		elif extra_rels ne [] then 
			I:=ideal<R|Eltseq(v*v-v) cat extra_rels>;
		end if;
	end if;
		if Dimension(I) le 0 then
			varsize:=VarietySizeOverAlgebraicClosure(I);
			var:=Variety(I);
			if #var eq varsize then
				idemps:=[];
				for x in var do
					ide:=&+[x[i]*A!U.i:i in [1..m]];
					Append(~idemps,ide);
				end for;
				return IndexedSet(idemps);
			else
				FClos:=AlgebraicClosure(FF);
				varF:=Variety(I,FClos);
				AClos:=ChangeRing(A,FClos);
				idemps:=[];
				for x in varF do
					ide:=&+[x[i]*AClos!U.i:i in [1..m]];
					Append(~idemps,ide);
				end for;
				return IndexedSet(idemps), FClos;
			end if;
		elif Dimension(I) eq 1 then
			print "ideal not zero-dimensional";
			return "fail";
		end if;
end intrinsic;

intrinsic	FrobFormAtElements(u::ParAxlAlgElt, v::ParAxlAlgElt, U::AlgMatElt)->FldRatElt 
{
 
Given an axial  algebra A with a form U, compute the number (u,v) for given elements u,v in A.
}
	require Type(u) eq ParAxlAlgElt and Type(v) eq ParAxlAlgElt: "Elements are not both axial algebra elements";
	require Nrows(U) eq Ncols(U): "Form must be a square matrix";
	A:=Parent(u);
	F:=BaseField(A);
	/*Because we work over function fields sometimes, we may need to change the base ring of U.*/ 
	UQ:=ChangeRing(U,F);
	return (Matrix(F,[Eltseq(u)])*UQ*Transpose(Matrix(F,[Eltseq(v)])))[1][1];
end intrinsic;

intrinsic LengthOfElement(u:: ParAxlAlgElt,form::AlgMatElt)->FldRatElt
{
Given an element u of an axial algebra A which admits a Frobenius form "form", find the length of u wrt to the form, i.e., (u,u).
}

require Type(u) eq ParAxlAlgElt: "The element u is not an axial algebra element.";
require Nrows(form) eq Ncols(form): "The Frobenius form must be a square matrix.";
return FrobFormAtElements(u,u,form);
end intrinsic;

/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Function to check if an idempotent satisfies the Monster M(1/4,1/32) fusion law. We start with some auxiliary routines.                 +
+           	                                                                                                                          +
+ We implement ideas from Hall, Rehren and Shpectorov's 'Universal axial algebras and a theorem of Sakuma.                                +
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/

intrinsic Pow(u::ParAxlAlgElt, n::RngIntElt)-> ParAxlAlgElt
{
Given an axial algebra element u and a non-negative integer n, find u^n=u*u*...*u n times. If the parent algebra of u has an identity, then
u^0 is the identity.
}
 
require n ge 0: " n must be a nonnegative integer.";
	if n eq 0 then 
 		bool,id:=HasIdentityAlg(Parent(u));
		if bool eq true then  
			pow:=id;
			pow:=id;
			return pow;
		else
			print("Error, the given power cannot be computed");
			return "fail";
		end if;
	end if;
	/* we now deal with n gt or equal to 1.*/ 
	if n eq 1 then
		pow:=u;
 	else
		count:=n;
		pow:=u;
		while count gt 1 do
			pow:=pow*u;
			 count:=count-1;/*this can actually deal with n=1.*/
		end while;
	end if;
	return pow;
end intrinsic;

/* Function to evaluate ad_a^n(v), i.e., the nth power of ad_a evaluated at v.*/
intrinsic AdPowerAtElement(a::ParAxlAlgElt,n::RngIntElt,v::ParAxlAlgElt) ->ParAxlAlgElt
{
 Function to evaluate ad_a^n(v), i.e., the nth power of ad_a evaluated at v.
} 
	require n ge 0: "The integer n must be  nonnegative."; 
	if n eq 0 then 
		return v;
	else
		return (Pow(a,n))*v; 
	end if;
end intrinsic;

/*Function to evaluate a polynomial f at ad_a and then applied to an alegbra element v.*/

intrinsic PolynomialAtAdAtElement(f::RngMPolElt, a::ParAxlAlgElt, v::ParAxlAlgElt)->ParAxlAlgElt
{

Function to evaluate a polynomial f at ad_a and then applied to an alegbra element v.
} 
	coefs:=Coefficients(f);
	return &+[coefs[i]*AdPowerAtElement(a,i-1,v):i in [1..#coefs]];
end intrinsic;

/*check if the eigenvalues are in eigens, if so, check if dimensions add up.*/
intrinsic HasMonsterFusion(u::ParAxlAlgElt)-> BoolElt
{
Check if the axial algebra element u satisfies the Monster M(1/4,1/32) fusion law.

} 
 bas:=Basis(Parent(u));
 eigens:=[1,0,1/4,1/32];
 P<s>:=PolynomialRing(Rationals(),1);
 ad:=AdMat(u);
  eigs:=IndexedSet(Eigenvalues(ad));
 if exists(ev){eigs[i][1]:i in [1..#eigs]|not (eigs[i][1]  in eigens)} then
  printf("Eigenvalue %o not in [1,0,1/4,1/32]\n"),ev;
  return false; 
 elif &+[eigs[i][2]:i in [1..#eigs]] ne #bas then 
 print("Dimensions do not add up\n");
  return false;
 else 
  E0:=[Parent(u)!Eltseq(u):u in Basis(Eigenspace(ad,0))];/*one hopes all eigenvalues are involved,
 if not, then a check has to be made.*/
  E1:=[Parent(u)!Eltseq(u):u in Basis(Eigenspace(ad,1))];
  E4:=[Parent(u)!Eltseq(u):u in Basis(Eigenspace(ad,1/4))];
  E32:=[Parent(u)!Eltseq(u):u in Basis(Eigenspace(ad,1/32))];
  /*1* everything else, not necessary, but we do it .*/
  bools:=[];
  bool1:=[
  forall{PolynomialAtAdAtElement(s-1,u,E1[i]*E1[j]) eq Zero(Parent(u)) :i in [1..#E1],j in [1..#E1]},
  forall{u*(E0[i]*E1[j]) eq Zero(Parent(u)) :i in [1..#E0],j in [1..#E1]},
  forall{PolynomialAtAdAtElement(s-1/4,u,E4[i]*E1[j]) eq Zero(Parent(u)) :i in [1..#E4],j in [1..#E1]},
  forall{PolynomialAtAdAtElement(s-1/32,u,E32[i]*E1[j]) eq Zero(Parent(u)) :i in [1..#E32],j in [1..#E1]}];
  Append(~bools,forall{bool:bool in bool1|bool eq true});

  /*we now check multiplication by 0 here.*/
  bool2:=[forall{PolynomialAtAdAtElement(s,u,(E0[i]*E0[j])) eq Zero(Parent(u)) :i in [1..#E0],j in [1..#E0]},
  forall{PolynomialAtAdAtElement(s-1/4,u,(E4[i]*E0[j])) eq Zero(Parent(u)) :i in [1..#E4],j in [1..#E0]},   
  forall{PolynomialAtAdAtElement(s-1/32,u,(E32[i]*E0[j])) eq Zero(Parent(u)) :i in [1..#E32],j in [1..#E0]}];
  Append(~bools,forall{bool:bool in bool2|bool eq true});

 /*we check multiplication by 1/4 now.*/
  bool3:=[
  forall{PolynomialAtAdAtElement((s-1)*s,u,E4[i]*E4[j]) eq Zero(Parent(u)) :i in [1..#E4],j in [1..#E4]},
  forall{PolynomialAtAdAtElement(s-(1/32),u,E32[i]*E4[j]) eq Zero(Parent(u)) :i in [1..#E32],j in [1..#E4]}];
  Append(~bools,forall{bool:bool in bool3|bool eq true});

 /*finally multipliction by 1/32.*/
 bool4:=[
 forall{PolynomialAtAdAtElement((s-1)*(s-1/4)*s,u,(E32[i]*E32[j])) eq
 Zero(Parent(u)) :i in [1..#E32],j in [1..#E32]}];
 Append(~bools,forall{bool:bool in bool4|bool eq true});
 if false in bools then 
  return false;
 else 
  return true;
 end if;
end if;
end intrinsic;
 
/*Routine for checking if a given idempotent is a Jordan axis.*/

/*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Given an axis a of an axial algebra A of Monster type, determine if it is of Jordan type 1/4.            +
+                                                                                                          +
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/

intrinsic IsJordanAxis(a::ParAxlAlgElt)->BoolElt
{
Check if a given idempotent is an axis of Jordan type 1/4.
}
	require Pow(a,2) eq a: "Element is not idempotent"; 
	return HasMonsterFusion(a) and {@x[1]:x in Eigenvalues(AdMat(a)) @} eq {@0,1,1/4 @};
end intrinsic;

/*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Must load MonsterFusionProjection.m . Require that a be an axial vector. (length n, dimension n).                          +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/

intrinsic TauMapMonster(a::ParAxlAlgElt)-> AlgMatElt
{
Find the Tau map of an axis.
} 
	require Pow(a,2) eq a: "The element a is not an idempotent";	
	require HasMonsterFusion(a): "The element does not satisfy the Monster fusion law."; 
	A:=Parent(a);
	Q:=Rationals();
	W:=VectorSpace(Rationals(),Dimension(A));
	P1:=ProjMat(a,Q!1);
	P0:=ProjMat(a,Q!0);
	P4:=ProjMat(a,1/4);
	P32:=ProjMat(a,1/32);
	P:=P1+P0+P4;
	return Matrix(Rationals(),[Eltseq((W!Eltseq(A.i))*P-(W!Eltseq(A.i))*P32): i in [1..Dimension(A)]]);
end intrinsic;

/*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Let A be an n-dim algebra and suppose that a is an axis in A. Asumme Monster fusion. Find the          +
+  projections to the 1,0,1/4 and 1/32 spaces. To avoid too many arguments, make sure that a is in cat   +
+  axial. Take as input the axes and the eigenvalue.                                                     +
+                                                                                                        +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/
intrinsic ProjMat(a::ParAxlAlgElt, ev::FldRatElt)->AlgMatElt
{
Given an axis a and an eigenvalue ev of ad_a, find the projection matrix to A_\{ev\}(a).
}
	require Pow(a,2) eq a: "The element a is not idempotent";
	require ev in [Rationals()!1,Rationals()!0,1/4,1/32]: "The given eigenvalue is not in the Monster Fusion eigenvalues."; 
	A:=Parent(a);
	d:=Dimension(A);
	evals:=[Rationals()!1,Rationals()!0,1/4,1/32]; /*should have defined this before tge erequire.*/
	I:=IdentityMatrix(Rationals(),d);
	ad:=Matrix(Rationals(),[Eltseq(a*A.i): i in [1..d]]);
	return &*[(ad-x*I)/(ev-x):x in evals|x ne ev];
end intrinsic;

/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Given an axis a which is known to be J(1/4), find the sigma map which negates the 1/4-space.            +
+                                                                                                         +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++=+++++*/

intrinsic SigmaMapMonster(a::ParAxlAlgElt)->AlgMatElt
{

Given an axis a which is known to be J(1/4), find the sigma map which negates the 1/4-space. 
}
	require IsJordanAxis(a): "Axis is not of Jordan type 1/4."; 
	Q:=Rationals(); 
	A:=Parent(a);
	W:=VectorSpace(Rationals(),Dimension(A));
	P1:=ProjMat(a,Q!1);
	P0:=ProjMat(a,Q!0);
	P4:=ProjMat(a,1/4);
	P:=P1+P0; 
	return Matrix(Rationals(),[Eltseq((W!Eltseq(A.i))*P-(W!Eltseq(A.i))*P4): i in [1..Dimension(A)]]);
end intrinsic;

/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+This is the nuanced zero subalgebra version. Take A as input, and optional parameters one, for the algebra identity, + 
+ as well as Frobenius form "form". Including these if known speeds up thngs considerably.                            +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/ 

IdentityLength := AssociativeArray();
types := ["2A","2B","3A","3C","4A","4B","5A","6A"];
identities_lengths := [(2^2*3)/5,2,(2^2*29)/(5*7),(2^5/11),4, 19/5,(2^5)/7,(3*17)/(2*5)];

for i in [1..#types] do
  IdentityLength[types[i]] := identities_lengths[i];
end for;

intrinsic FindAllAxesNuanced(A::ParAxlAlg: one:=A!0, form:=IdentityMatrix(BaseField(A), Dimension(A)))->SetIndx 
{
We perform the nuanced algorithm for finding all axes in an axial algebra of modest dimension. (Works for up to ~40 on an old laptop running linux.) 
This version only takes an axial algebra as input and attempts to find all axes in A. 
Additional (optional) inputs are :
-one, the algebra identity if it exists. The program will attempt to find this if the default is left as is, increasing run time,
-form, the Frobenius form of A. Same as above.
 }

	require Type(one) eq ParAxlAlgElt: "The given element is not an axial algebra element";
	if one ne A!0 then 
		require forall{i:i in [1..Dimension(A)]|one*A.i eq A.i}: "The given element is not identity";
	end if; 
	require Parent(one) eq A: "The given vector is not in the algebra";
	F := BaseField(A);
	/*The following conditional statement needs additonal code for the else part in the event A is non-unital. However, for the algebras in our current paper this does not occur, since we proved they are unital.
	 */
	if one eq A!0 then 
		_,one:=HasIdentityAlg(A);
	end if;
	if form eq IdentityMatrix(F,Dimension(A)) then
	_,form:=HasFrobeniusForm(A);
	end if;/* Here again it is conceivable that A does not have a form. Additional things to be done in such a case*/
	axes:=Axes(A);
	reps:=[axes[i][1]:i in [1..#axes]];
	reps:=[A!x:x in reps]; 
	axes:=&join[x:x in axes];
	axes:=[A!x:x in axes];
	found:=[];
	count:=0;
	for x in reps do
		a:=x;
		count+:=1;
		W:=Eigenspace(AdMat(a),0);
		for k in Keys(IdentityLength) do
			l:=(IdentityLength[k])-1;
			if k eq "4A" then
				W32:=Eigenspace(AdMat(a),1/32);
				RR:=PolynomialRing(BaseField(A),Dimension(W));
				FF:=FieldOfFractions(RR); 
				AFF:=ChangeRing(A,FF);
				uu:=&+[RR.i*AFF!W.i:i in [1..Dimension(W)]];
				len_rest:=[FrobFormAtElements(uu,AFF!Eltseq(one),ChangeRing(form,FF))-l];
		/*this operation makes the calculation slow so do only as last resort.*/
				if Dimension(ideal<RR|Eltseq(uu) cat len_rest>) gt 0 then
					t:=Cputime();
					extra:=Determinant(AdMatInSubAlg(AFF,W32,uu)-(31/32)*IdentityMatrix(BaseField(A),Dimension(W32)));
					printf "Extra relations found in %o seconds\n",t;
					idemps:=FindAllIdempotents(A,W:length:=l,one:=one,form:=form,extra_rels:=[extra]);
				end if;
			elif k ne "4A" then 
				idemps:=FindAllIdempotents(A,W:length:=l,one:=one,form:=form);
			end if; 
			printf "orbit %o %o nice idempotents found\n", count,k;
			if not #idemps eq 0 then 
				AA:=ChangeRing(A,BaseField(Parent(idemps[1])));
				aa:=AA!Eltseq(a);
				for u in idemps do
					uu:=AA!Eltseq(u); 
					Z:=Eigenspace(AdMat(aa+uu),1);
					potential_axes:=FindAllIdempotents(AA,Z:length:=1,one:=AA!Eltseq(one),form:=form);
					for y in potential_axes do
						if HasMonsterFusion(y) and not A!Eltseq(y) in found then
							Append(~found, A!Eltseq(y));
						end if;
					end for;
				end for; 
				printf "axes arising from orbit %o, B of type %o found\n",count,k;
			end if; 
		end for; 
	 end for; 
	if #found eq #axes then 
		print "nothing new";
	else
		printf "%o new axes found \n", #found-#axes;
	end if;
	return IndexedSet(found);
end intrinsic;

/* Given an axial algebra A (partial or complete), return the list of orbits of axes that generate A. */
intrinsic Axes(A::ParAxlAlg)-> SetIndx 
{
 Given an axial algebra A (partial or complete), return the list of orbits of axes that generate A. 
}
	orbs:=Orbits(Group(A),A`GSet);
	phi:=A`GSet_to_axes;
	axis_orbits:=[{@A!(i@phi):i in o@}:o in orbs];
	return axis_orbits;
end intrinsic;

/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Suppose that V is a subalgebra of an axial algebra A of known multiplication. Determine the ad_a matrix of a in V.    +
+                                                                                                                       +
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/

intrinsic AdMatInSubAlg(A::ParAxlAlg, V::ModTupFld, a::ParAxlAlgElt)-> AlgMatElt 
{
Suppose that V is a subalgebra of an axial algebra A of known multiplication. Determine the ad_a matrix of a in V. 
}

	//require forall{i:i in [1..Dimension(V)]|V.i in A`W}: "V is not a subspace of A."; 
	n:=Dimension(A);
	d:=Dimension(V);
	basV:=Basis(V);
	basmat:=Matrix(BaseField(A),[Eltseq(basV[i]):i in [1..d]]);
	sols:=[Eltseq(Solution(basmat,Vector(BaseField(A),Eltseq(a*(A!V.i))))):i in [1..d]];
	return Matrix(BaseField(A),sols);
end intrinsic;

 /*The description below has changed somewhat. Inputs are A and a subspace U, more natural than specifying a basis.*/  

/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Given an algebra A, and a subspace U with a prescribed basis as a list of vectors,  determine ann U.                                      +
+ The inputs are A, which must be axial, or a tensor which gives algebra multiplication. The basis, bas, of U, can be ordinary vectors.     +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/ 

intrinsic AnnihilatorOfSpace(A::ParAxlAlg, U::ModTupFld) -> ModTupFld
  {
  Given an algebra A and a subspace U of A, return the subspace (not a subalgebra) of A which annihilates U.
  }
	bas:=Basis(U); 
	tens:=[];
	d:=Dimension(A);
	V:=VectorSpace(Rationals(),d);
	basmat:=Matrix(Rationals(),[Eltseq(A.i):i in [1..d]]);
	for i:=1 to d do 
		for j:=1 to d do 
			if i le j then
				Append(~tens, Solution(basmat,V!Eltseq(A.i*A.j)));
			end if;
		end for;
	end for;
	/*We could use coordinates with a prescribed basis but seems slower.*/
	/*here we can as well just input the tensor.*/
        m:=#bas;	
        M:=ZeroMatrix(Rationals(),m*d,d); 
	for k:=1 to m do
		for l:=1 to d do
		       	row:=[];
			for i:=1 to d do
				for j:=1 to d do 	
					ii:=Minimum({i,j});jj:=Maximum({i,j});
					M[d*(k-1)+l][i]+:=bas[k][j]*tens[IntegerRing()!((ii-1)/2*(2*d+2-ii))+jj-ii+1][l];
				end for; 
			end for;
		end for;
	end for;
	big_vec:=VectorSpace(Rationals(),d*m)!0;	
	_,sol:=Solution(Transpose(M),big_vec);
	return sol; 
end intrinsic; 

/*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Given an axis a in an axial algebra A, find axes b such that t_a=t_b if such exist.                                    + 
+                                                                                                                        +
+
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/

intrinsic FindMultiples(a::ParAxlAlgElt: one:=Parent(a)!0, eigenspace:=sub<Parent(a)`W|Parent(a)`W!0>, form := ZeroMatrix(BaseField(Parent(a)),Dimension(Parent(a)),Dimension(Parent(a)))) -> SetIndx
  {
  Given an axis, find the set of all other axes which have the same Miyamoto automorphism as a. 
  Does the same for a sigma automorphism if Jordan 1/4. We have optional arguments:
   1. one, the algebra identity/unit.
   2. 1/32-eigenspace (repsectively 1/4-eigenspace if Jordan),
   3. form, the Frobenius form of the parent algebra.
  }
 	A:=Parent(a);	 
	require Pow(a,2) eq a and HasMonsterFusion(a): "Error, input not an axis";
	/*when the space is given first.*/
	if not Dimension(eigenspace) eq 0 then
		require Degree(eigenspace) eq Dimension(A): "The degree of the space is different from that of the parent"; 
		space:=eigenspace;
	end if;
	if Dimension(eigenspace) eq 0 then 
		if IsJordanAxis(a) then 
			space:=Eigenspace(AdMat(a),1/4);
		else
			space:=Eigenspace(AdMat(a),1/32);
		end if;
	end if;
	/* now deal with the case of identity being supplied.*/
	if one ne A!0 then
		require Type(one) eq ParAxlAlgElt: "The given element is not an axial algebra element";
		require forall{i:i in [1..Dimension(A)]|one*A.i eq A.i}: "The given element is not the identity.";
	end if;
	/*We proved that all algebras with the Monster M(1/4,1/32) fusion law are unital, but for others one may not exist.*/
	/*Now when the identity is not supplied we find it.*/
	if one eq A!0 then  
		_,one:=HasIdentityAlg(A);
	end if;
	/*now check if the form has been supplied.*/
	if form eq ZeroMatrix(BaseField(A), Dimension(A), Dimension(A)) then
		_,U:=HasFrobeniusForm(A);
	else /*form supplied, need to check if it's a square matrix, no other checks beyond that, we assume the user is sensible.*/
		require Type(form) eq AlgMatElt: "Form must be a matrix";
		require Nrows(form) eq Ncols(form): "Form must be a square matrix";
		require BaseRing(form) eq BaseField(A): "The form must ve over the sane field as A.";
		U:=form; 
	end if;
	ann:=AnnihilatorOfSpace(A,space);
	/*we seek w in 1+ann such that a multiple b is of the form b=a+w.*/
	Space:=sub<A`W|A`W!Eltseq(one)>+ann;
	dim:=Dimension(Space);
	R:=PolynomialRing(Rationals(),dim);
	FR:=FieldOfFractions(R);
	AFR:=ChangeField(A,FR);
	UFR:=ChangeRing(U,FR);
	w:=&+[(AFR!Space.i)*R.i:i in [1..dim]];
	aa:=AFR!Eltseq(a); 
	/* from b^2=b we have a+w=a^2+2aw+w^2=a+2aw+w^2 whence 0=w^2+2aw-w: where a is really aa in this comment.*/ 
	res:=w*w+2*aa*w-w;
	len_res:=(VecToMat(w)*UFR*Transpose(VecToMat(w))+2*VecToMat(aa)*UFR*Transpose(VecToMat(w)))[1][1]; 
	/*we have 1=(aa+b,aa+b)=(aa,aa)+2(aa,w)+(w,w) hence 0=(w,w)+2(aa,w).*/;
	I:=ideal<R|[R!x:x in Eltseq(res) cat [len_res]]>;
	var:=Variety(I);
	if not #var eq VarietySizeOverAlgebraicClosure(I) then 
		print "a check is needed here";
		return {@ @};
	elif #var eq 1 then /*notice here that 0 always satisfies our condition.*/ 
		print "nothing new";
		return {@ @};
	elif #var gt 1 then 
		vars:=[];
		for x in var do
			if not forall{y:y in x|y eq 0} then  
				twin:=&+[AFR!Space.i*x[i]:i in [1..dim]];
				Append(~vars,a+A!Eltseq(twin));
			end if;
		end for;
		return IndexedSet(vars);
	end if;
end intrinsic;

/*Turn a vector to a row matrix.*/

intrinsic VecToMat(v:: ModTupFldElt)-> AlgMatElt
{
Turn a vector to a row matrix.
}
	 return Matrix(BaseField(Parent(v)),[Eltseq(v)]);
end intrinsic;
		
intrinsic VecToMat(v:: ParAxlAlgElt)-> AlgMatElt
{
Turn a vector to a row matrix.
}
	 return Matrix(BaseField(Parent(v)),[Eltseq(v)]);
end 	intrinsic;

/* Here we will use overloading for the Hom version. In the description below, lists will be sequences. This function can be used to find subalgebras generated by certain elements, just take the same input and ouput sequence. As a side effect you will also get m-clossure for your input. */

/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ This function takes an axial algebra A, and two lists, input, and images, of axial vectors which must be of the same length and ouputs    +
+ a boolean value as well as either a map in matrix form or a subalgebra if the map does not extend to the full space.                      +
+                                                                                                                                           +
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/

intrinsic ExtendMapToAlgebra(input::SeqEnum,images::SeqEnum)->BoolElt,AlgMatElt
{
	Given two indexed sets of axial algebra elements, the first with preimages and the second containing the corresponding images, 
	extend the map as far as possible. If the map extends to the whole algebra, return true and a matrix that gives a multiplicative map A->A
	where A is the axial algebra in question. If not, return false and the maximum subalgebra (as a vector space) to which the map extends.	

}
	require #input eq #images: "The lengths of the input and output lists must be  equal.";
	require Type(input[1]) eq ParAxlAlgElt and Type(images[1]) eq ParAxlAlgElt: "The elements of the given lists are not algebra elements.";
	 A:=Parent(input[1]);
	require IsIndependent({A`W!Eltseq(x):x in input}): "The input list must be independent.";
	require IsIndependent({A`W!Eltseq(x):x in images}): "The images list must be independent.";
	dim:=Dimension(A);
	closed:=0;
	F:=BaseField(A);
	lst:=[A`W!Eltseq(input[i]):i in [1..#input]];
	ims:=images;
	sub:=sub<A`W|lst>;
	m:=1;
	if forall{i:i in [1..#lst]|forall{j:j in [i..#lst]|A`W!Eltseq((A!lst[i])*(A!lst[j])) in sub}} then
		closed:=1;
	else
		m+:=1;
	end if;
	/*this deals with the obvious failures and an input list as long as the dimension. At this point independence has been established.*/
	if m eq 2 then
		current_inds:=[];
		current_inds[1]:=1;
		current_inds[2]:=#lst;
		for i:=current_inds[1] to current_inds[2] do
			for j:=i to current_inds[2] do
				w:=input[i]*input[j];
				ww:=A`W!Eltseq(w);
				if ww notin sub then
					Append(~lst,ww);
					Append(~ims,ims[i]*ims[j]);
					sub+:=sub<A`W|ww>;
				end if;
			end for;
		end for;
		if #lst eq dim or forall{i:i in [1..#lst]|forall{j:j in [i..#lst]|A`W!Eltseq((A!lst[i])*(A!lst[j])) in sub}} then
			closed:=1;
		else
			subclosed:=1;
			for i:=current_inds[1] to #lst do
				for j:=current_inds[2] to #lst do
					w:=(A!lst[i])*(A!lst[j]);
					ww:=A`W!Eltseq(w);
					if ww notin sub then
						subclosed:=0;
						m+:=1;
						break i;
					end if;
				end for;
			end for;
		end if;
		current_inds[1]:=current_inds[1]+1;
		current_inds[2]:=#lst;
	end if;
	printf("current dimension is %o \n"),#lst;
	while closed eq 0 do
		for i:=1 to #input do
			for j:=current_inds[1] to current_inds[2] do
				w:=(A!lst[i])*(A!lst[j]);
				ww:=A`W!Eltseq(w);
				if ww notin sub then
					Append(~lst,ww);
					Append(~ims,ims[i]*ims[j]);
					sub+:=sub<A`W|ww>;
				end if;
			end for;
		end for;
		if #lst eq dim then 
			closed:=1;
		else
			subclosed:=1;
			for i:=current_inds[1] to #lst do
				for j:=current_inds[2] to #lst do
					w:=(A!lst[i])*(A!lst[j]);
					ww:=A`W!Eltseq(w);
					if ww notin sub then
						Append(~lst,ww);
						Append(~ims,ims[i]*ims[j]);
						sub+:=sub<A`W|ww>; 
						subclosed:=0;
						m+:=1;
						break i;
					end if;
				end for;
			end for;
			if subclosed eq 1 then
				closed:=1;
			end if;
		end if;
		current_inds[1]:=current_inds[2]+1;
		current_inds[2]:=#lst;
		printf("current dimension is %o \n"),#lst;
	end while;
	printf("multiplication is now closed with minimum %o-closure \n"),m;
	if #lst lt dim then
		return false,sub;
	end if;
	bas_mat:=Matrix(F,[Eltseq(lst[i]):i in [1..#lst]]);
	phi:=Matrix(F,[Eltseq(Solution(bas_mat,A`W!Eltseq(ims[i]))):i in [1..#ims]]);
	std_phi:=bas_mat^(-1)*phi*bas_mat;
	if std_phi eq IdentityMatrix(F,#lst) then
		return true, std_phi;
	else
		return true,std_phi;
	end if;
end intrinsic;

/*The following is a naive approach without any length restriction.*/
/*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+This is the brute force approach to finding all the axes of Monster M(1/4,1/32).                 +
+                                                                                                 +
+												  +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/
intrinsic FindAxesNaive(A::ParAxlAlg)->SetIndx
{
	Given an axial algebra A of modest dimension, \(around 10\-dim and less\), find all axes in A by brute force. 
}
	idemps:=FindAllIdempotents(A,A`W);
	try 
		if idemps eq "fail" then	
			return "fail";
		end if;
		idemps:=idemps;
		print "idempotents found";
	catch e
		axes:=[];
		for x in idemps do
			if Dimension(Eigenspace(AdMat(x),1)) eq 1 then
				if HasMonsterFusion(x) then
					Append(~axes,A!Eltseq(x));
				end if;
			end if;
		end for;
			known_axes:=&join[x:x in Axes(A)];
			new:=[x:x in axes| not x in known_axes];
			if #new eq 0 then
				print "nothing new";
			else
				print "new axes found";
			end if;
				return IndexedSet(axes);
		return "fail";
	end try;
end intrinsic;

/*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+This is the brute force approach to finding all the axes of Monster M(1/4,1/32). We add the      +
+extra condition that the idempotents found be of length 1. We require the algebra identity as    +
+optional input.                                                                                  +												
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/
intrinsic FindAxesNaiveWithLengthRestriction(A::ParAxlAlg: id:=A!0,form:=IdentityMatrix(BaseField(A),Dimension(A)))-> SetIndx
{
	We use the brute force approach with the restriction that found idempotents must be of length 1. If the resultant ideal is not zero dimensional it will return fail.
}
	if id eq A!0 then
       		_,id:=HasIdentityAlg(A);
	else/* user supplied identity.*/
		require Parent(id) eq A: "The elemnt is not in A";
		require forall{i:i in [1..Dimension(A)]|id*A.i eq A.i}: "The given element is not the identity of A.";
	end if;
	if form eq IdentityMatrix(BaseField(A),Dimension(A)) then
		bool,M:=HasFrobeniusForm(A);
		form:=M;/*Here again we assumed the existence of form. Provision needs to be made when it does not exist.*/
	else
		require Nrows(form) eq Ncols(form): "The form must be a sqaure matrix";
		require IsSymmetric(form): "The form must be symmetric";
		require Nrows(form) eq Dimension(A): "The size of the form must be the same as the dimension of A.";
	end if;	
	idemps:=FindAllIdempotents(A,A`W:length:=1,one:=id, form:=form);
	try 
		if idemps eq "fail" then	
		return "fail";
		end if;
			idemps:=idemps;
			print "idempotents found";
	catch e
		axes:=[];
		for x in idemps do
			if Dimension(Eigenspace(AdMat(x),1)) eq 1 then
				if HasMonsterFusion(x) then
					Append(~axes,A!Eltseq(x));
				end if;
			end if;
		end for;
			known_axes:=&join[x:x in Axes(A)];
			known_axes:=[A!x:x in known_axes];
			new:=[x:x in axes| not x in known_axes];
			if #new eq 0 then
				print "nothing new";
			else
				printf "new %o axes found\n",#new;
			end if;
				return IndexedSet(axes);
		return "fail";
	end try;
end intrinsic;

/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ This function determines the fixed subalgebra of a given matrix group for a particular algebra A. For efficiency, give the              +
+ fewest possible number of generators of the group. The function will return the fixed subalgebra in vector space form.                  +
+                                                                                                                                         +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/ 
intrinsic FindFixedSubAlgebra(A::ParAxlAlg, lst::SeqEnum)-> ModTupFld
{
	Given an axial algebra A and a list of Miyamoto involutions that generate the Miyamoto group of A, find the fixed subalgebra, i.e., 
	the set of all vectors which are fixed by all Miyamoto involutions or known automorphisms.
}
	require Type(lst[1]) eq AlgMatElt : "The list must have matrices";
        dim:=Dimension(A);
	require forall{x:x in lst|(Nrows(x) eq Ncols(x)) and Nrows(x) eq dim}: "The elemenets of the sequence must be square matrices of the same dimension as A";
	require forall{x:x in lst| IsInvertible(x)} : "Automorphisms must be invertible";  
	Mat:=ZeroMatrix(BaseField(A),#lst*dim,dim); 		 
	for l:=1 to #lst do
		for i:=1 to dim do
			for j:=1 to dim do
				Mat[(l-1)*dim+i,j]:=lst[l][j,i];
			end for;
		end for;
		for j:=1 to dim  do
			Mat[(l-1)*dim+j,j]-:=1;
		end for;
	end for;
	_,sol:=Solution(Transpose(Mat),Vector(BaseField(A),[0*i:i in [1..#lst*dim]]));
	return sol;
end intrinsic; 
/*I could have included a more stringent test here and required that the matrix group generated by lst be the Miyamoto group but I want to be able to include as much automorphisms known as possible to reduce the dimension. For instance, if we know a new Jordan axis, we can add the sigma automorphism.*/ 

/*The following variant of the above function takes a single input, namely the algebra, and produces the fixed algebra. We start by reducing the number of generators of the Miyamoto group.*/ 

/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ This function determines the fixed subalgebra of a given matrix group for a particular algebra A.                                       +
+ The function will return the fixed subalgebra in vector space form.                                                                     +
+                                                                                                                                         +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/ 
intrinsic FindFixedSubAlgebra(A::ParAxlAlg)-> ModTupFld
{
	Given an axial algebra A, find the fixed subalgebra, i.e., the set of all vectors which are fixed by all Miyamoto involutions or known automorphisms.
}
	lst:=MinimumGeneratorsMiyamotoGroup(A);
	printf "A minimum set of %o generators found \n", #lst;
	dim:=Dimension(A);
	F:=BaseField(A);
	Mat:=ZeroMatrix(F,#lst*dim,dim); 		 
	for l:=1 to #lst do
		for i:=1 to dim do
			for j:=1 to dim do
				Mat[(l-1)*dim+i,j]:=lst[l][j,i];
			end for;
		end for;
		for j:=1 to dim  do
			Mat[(l-1)*dim+j,j]-:=1;
		end for;
	end for;
	print "System of equations set up";
	_,sol:=Solution(Transpose(Mat),Vector(F,[0*i:i in [1..#lst*dim]]));
	return sol;
end intrinsic; 

intrinsic FindPerp(A::ParAxlAlg, V::ModTupFld, M::ModTupFld:bool:=true,form:=IdentityMatrix(BaseField(A),Dimension(A)))->ModTupFld
{
	Given an axial algebra A, a subalgebra V of A, and a subspace M of V, find all the elements of V which are perpendicular to all the elements of M. 
	Optional parameters are form: the Frobenius form, and a boolen which is set to true by default indicating that A has a form. Set to false otherwise.
} 
	basV:=Basis(V);
	basM:=Basis(M);
	if form eq IdentityMatrix(BaseField(A),Dimension(A)) then 
		bool,U:=HasFrobeniusForm(A);
	else
		require Type(form) eq AlgMatElt: "The form must be a matrix";
		require (Nrows(form) eq Ncols(form)) and (Nrows(form) eq Dimension(A)): "The form must be a sqaure matrix if the same size as the dimension of A.";
	end if;
	if bool eq false then 
		return "fail";
	else
	m:=#basV;k:=#basM;
	F:=BaseField(A);
	B:=ZeroMatrix(F,k,m);
	for j:=1 to k do
	       for i:=1 to m do
		      B[j][i]+:=FrobFormAtElements(A!basV[i],A!basM[j],U); 
		end for;
	end for;
		_,sol:=Solution(Transpose(B),Vector(F,[0*tt:tt in [1..k]]));
		if Dimension(sol) ne 0 then 
			bas:=[ToBigVec(A,V,sol.i):i in [1..Dimension(sol)]];
			return sub<A`W|[A`W!Eltseq(bas[i]):i in [1..#bas]]>;
		else 
			return sol;
		end if; 
	end if;
end intrinsic;

/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ This function takes an algebra A (dim n) and a subalgebra V of dimension m<=n and a vector v in V written as an m-long+
+ vector and returns an n-long vector in A. The result will be axial, though of course it can be changed.               +
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/
intrinsic ToBigVec(A::ParAxlAlg, V::ModTupFld,v::ModTupFldElt)->ParAxlAlgElt
{
	Given an n-dimenional algebra, a subspace V of dimension m and an m-long vector representing an element of V relative to some basis, return an n-long vector in A. If you really want a specific basis use VectorSpaceWithBasis for the subspace V.
}
	n:=Dimension(A);
	m:=Dimension(V);
	require Degree(v) eq m: "The degree of the input vector must be equal to the dimension of the subspace.";
	basV:=Basis(V);
	return &+[v[i]*A!basV[i]:i in [1..m]];
end intrinsic;

/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Given an axial algebra A, find the Jordan 1/4 axes in A.                                                                  +
+                                                                                                                           +
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/ 

intrinsic JordanAxes(A::ParAxlAlg :one:=A!0,form:=IdentityMatrix(BaseField(A), Dimension(A)))->SetIndx
{
	Givem an axial algebra, find all the Jordan Axes in A. Optional inputs are :
	1. one- the algebra identity and 
	2. form- the Frobenius form of the algebra if exists.
}
	if one eq A!0 then
		_,one:=HasIdentityAlg(A); /* in our setting algebras are untital.*/
	else 
		require Type(one) eq ParAxlAlgElt: "The identity must be an axial algebra element"; 
		require forall{i:i in [1..Dimension(A)]|one*A.i eq A.i}: "The given element is not the algebra identity";
	end if;
	if form eq IdentityMatrix(BaseField(A),Dimension(A)) then
		bool,form:=HasFrobeniusForm(A);
		if bool eq false then
			idemps:=FindAllIdempotents(A,FindFixedSubAlgebra(A):one:=one);
		else/*user did not supply form and it has been calculated (exists).*/	
			idemps:=FindAllIdempotents(A,FindFixedSubAlgebra(A):length:=1,one:=one, form:=form);
		end if;
	else/*user supplied form.*/
		require Type(form) eq AlgMatElt: "The form must be a matrix";
		require Nrows(form) eq Ncols(form) and Nrows(form) eq Dimension(A): "The form must be a square matrix";
		require IsSymmetric(form): "A Frobenius form is necessarily symmetric";	
		idemps:=FindAllIdempotents(A,FindFixedSubAlgebra(A):length:=1,one:=one, form:=form);
	end if;
	if #idemps eq 0 then 
		return idemps;
	else 
		return{@x:x in idemps| HasMonsterFusion(x) @};
	end if;
end intrinsic;

/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+This function takes an alebra/vector space A and a subspace V and a vector v in A to produce a dimV-long +
+ relative to a basis of V. The opposite of ToBigVec.                                                     +
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/
intrinsic ToSmallVec(A::ParAxlAlg, V::ModTupFld, v::ParAxlAlgElt)-> ModTupFldElt 
{ Given an axial algebra A, a subspace V and a vector v of a which is coercible to V, find a dim(V)-long vector which is an expression of v in terms of some basis of V. 
}

	F:=BaseField(A);
	n:=Dimension(A);
	 m:=Dimension(V);
	AA:=VectorSpace(F,n);
	require Degree(V) eq n: "V must be a subspace of A";
	mat:=Matrix(F,[Eltseq(V.i):i in [1..m]]);
	v,_:= Solution(mat,AA!Eltseq(v));
	return v;
end intrinsic;

/*This version is for when A is a vector space.*/
intrinsic ToSmallVec(A::ModTupFld, V::ModTupFld, v::ModTupFldElt)-> ModTupFldElt 
{ Given a vector space A, a subspace V and a vector v in A\\cap V, find a dim(V)-long vector which is an expression of v in terms of some basis of V. 
}

	F:=BaseField(A);
	n:=Dimension(A);
	 m:=Dimension(V);
	AA:=VectorSpace(F,n);
	require Degree(V) eq n and V subset A: "V must be a subspace of A";
	mat:=Matrix(F,[Eltseq(V.i):i in [1..m]]);
	v,_:= Solution(mat,AA!Eltseq(v));
	return v;
end intrinsic;

/*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Given an element x of the permutation group form of the Miyamoto group of an axial algebra, determine if it is     +
+ induced by tau or sigma map of an axis. Return the axis if it exists.                                             +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/

intrinsic IsRealisableAsAxis(A::ParAxlAlg, elt::GrpPermElt :one:=A!0,form:=IdentityMatrix(BaseField(A),Dimension(A)))->BoolElt, SetIndx /*Input an axial algebra A and a group element elt from the Miyamoto group.*/ 
/*We have an optional input for the identity if it exists, naturally inputting it will speed up things.*/
{
	Given an axial algebra A and an element elt from the Miyamoto group of A given as a permutation matrix, determine if elt can be realised as an axis.
} 
	require Type(one) eq ParAxlAlgElt: "The identity must be an axial algebra element.";
	require Type(form) eq AlgMatElt: "The form must be a matrix "; 
	require Nrows(form) eq Ncols(form) and Nrows(form) eq Dimension(A): "The form must be a square matrix";
	require IsSymmetric(form): "A Frobenius form is necessarily symmetric";
	n:=Dimension(A);
	F:=BaseField(A); 
	if form eq IdentityMatrix(F,n) then
		bool1,form:=HasFrobeniusForm(A);
		if bool1 eq true then
			x:=elt;
			aut:=ZeroMatrix(F,n,n);
			for i:=1 to n do
				v:=(A`Wmod)!((A`W).i);
				aut[i]:=(A`W)!Eltseq(v*x);
			end for;
			eigs:={x[1]:x in Eigenvalues(aut)};
			if not eigs eq  {-1,1} then 
				return false;
			elif eigs eq {-1,1} then  
				ann:=AnnihilatorOfSpace(A,(Eigenspace(aut,-1))); 
				if one eq A!0 then
					bool,one:=HasIdentityAlg(A);
					if bool eq false then
					idemps:=FindAllIdempotents(A, ann:length:=1, form:=form); 
						if #idemps eq 0 then
							return false,_;
                				elif #idemps ne 0 then 
							return true,{@x:x in idemps|HasMonsterFusion(x) @};
						end if;
					elif bool eq true then 
						one:=A!one;
						idemps:=FindAllIdempotents(A,sub<A`W|A`W!Eltseq(one)>+ann:length:=1,form:=form,one:=one);
						if #idemps eq 0 then
							return false,_;
                				elif #idemps ne 0 then 
							return true,{@x:x in idemps|HasMonsterFusion(x)@};
						end if;
					end if;
				elif one ne A!0 then
					require forall{i:i in [1..n]|one*A.i eq A.i}: "The given element is not the algebra identity."; 
					idemps:=FindAllIdempotents(A,sub<A`W|A`W!Eltseq(one)>+ann:length:=1,form:=form,one:=one);
					if #idemps eq 0 then
						return false,_;
                			elif #idemps ne 0 then 
						return true,{@ x :x in idemps|HasMonsterFusion(x) @};
					end if;
				end if;
			end if; 
		else /* form does not exist.*/
			x:=elt;
			aut:=ZeroMatrix(F,n,n);
			for i:=1 to n do
			v:=(A`Wmod)!((A`W).i);
			aut[i]:=(A`W)!Eltseq(v*x);
		end for;
		eigs:={x[1]:x in Eigenvalues(aut)};
		if not eigs eq  {-1,1} then 
			return false;
		elif eigs eq {-1,1} then  
			ann:=AnnihilatorOfSpace(A,(Eigenspace(aut,-1))); 
			if one eq A!0 then
				bool,one:=HasIdentityAlg(A);
				if bool eq false then
				idemps:=FindAllIdempotents(A, ann:one:=one); 
					if #idemps eq 0 then
						return false,_;
                			elif #idemps ne 0 then 
						return true,{@x:x in idemps|HasMonsterFusion(x) @};
					end if;
				elif bool eq true then 
					one:=A!one;
					idemps:=FindAllIdempotents(A,sub<A`W|A`W!Eltseq(one)>+ann:one:=one);
					if #idemps eq 0 then
						return false,_;
                			elif #idemps ne 0 then 
						return true,{@x:x in idemps|HasMonsterFusion(x)@};
					end if;
				end if;
			elif one ne A!0 then
				require forall{i:i in [1..n]|one*A.i eq A.i}: "The given element is not the algebra identity."; 
				idemps:=FindAllIdempotents(A,sub<A`W|A`W!Eltseq(one)>+ann:one:=one);
				if #idemps eq 0 then
					return false,_;
                		elif #idemps ne 0 then 
					return true,{@ x :x in idemps|HasMonsterFusion(x) @};
				end if;
			end if;
		end if; 
		end if;
	else
		x:=elt;
		aut:=ZeroMatrix(F,n,n);
		for i:=1 to n do
			v:=(A`Wmod)!((A`W).i);
			aut[i]:=(A`W)!Eltseq(v*x);
		end for;
		eigs:={x[1]:x in Eigenvalues(aut)};
		if not eigs eq  {-1,1} then 
			return false;
		elif eigs eq {-1,1} then  
			ann:=AnnihilatorOfSpace(A,(Eigenspace(aut,-1))); 
			if one eq A!0 then
				bool,one:=HasIdentityAlg(A);
				if bool eq false then
				idemps:=FindAllIdempotents(A, ann:length:=1, form:=form); 
					if #idemps eq 0 then
						return false,_;
                			elif #idemps ne 0 then 
						return true,{@x:x in idemps|HasMonsterFusion(x) @};
					end if;
				elif bool eq true then 
					one:=A!one;
					idemps:=FindAllIdempotents(A,sub<A`W|A`W!Eltseq(one)>+ann:length:=1,form:=form,one:=one);
					if #idemps eq 0 then
						return false,_;
                			elif #idemps ne 0 then 
						return true,{@x:x in idemps|HasMonsterFusion(x)@};
					end if;
				end if;
			elif one ne A!0 then
				require forall{i:i in [1..n]|one*A.i eq A.i}: "The given element is not the algebra identity."; 
				idemps:=FindAllIdempotents(A,sub<A`W|A`W!Eltseq(one)>+ann:length:=1,form:=form,one:=one);
				if #idemps eq 0 then
					return false,_;
                		elif #idemps ne 0 then 
					return true,{@ x :x in idemps|HasMonsterFusion(x) @};
				end if;
			end if;
		end if; 
	end if;
end intrinsic; 

/*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ AxMat(BaseField(A),Dimension(A))-->boolean, axl alg elment or _ depending +
+ on whether boolean is true or false.                                     +
+                                                                          +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/

intrinsic IsInducedFromAxisMat(A::ParAxlAlg, mat::AlgMatElt:one:=A!0,form:=IdentityMatrix(BaseField(A),Dimension(A))) -> BoolElt, SetIndx
{
	Given an axial algebra A and a matrix mat, over the base field of A, check if mat is induced from an axis. The matrix mat must be invertible. We do not check if it is automorphic. If true, the function will also produce an indexed set of axes in A which induce mat.
}
	/*we assume that the matrix is an automorphism, this will not be checked.*/
	F:=BaseField(A);
	n:=Dimension(A);
	require Nrows(mat) eq Ncols(mat) and Nrows(mat) eq n: "The matrix must be square";
	require Type(form) eq AlgMatElt: "The form must be a matrix";
	require Nrows(form) eq Ncols(form): "The form must be a square matrix";
	require IsSymmetric(form):" The form must be symmetric";
	require Type(one) eq ParAxlAlgElt: "Identity must be an axial algebra element";
	require IsInvertible(mat): "An automorphism is invertible";
	require forall{i:i in [1..n]|forall{j:j in [1..n]| IsCoercible(F,mat[i][j])}}:" A and mat must be over the same field";
	eigs:=[x[1]:x in Eigenvalues(mat)];
	if -1 notin eigs then
		print "-1 is not an eigenvalue";
		return false,_;
	end if;
	Space:=Eigenspace(mat,-1);
	ann:=AnnihilatorOfSpace(A,Space);
	if Dimension(ann) eq 0 then
		print "The dimension of the annhilator is 0";
		return false,_;
	end if;
	if one eq A!0 then
		id_bool,one:=HasIdentityAlg(A);
		if id_bool eq true then
			one:=A!one;
		end if;
	else	
		require forall{i:i in [1..n]|one*A.i eq A.i}: "The given vector is not the algebra element";
	end if;
	if form eq IdentityMatrix(F,n) then 
		form_bool,form:=HasFrobeniusForm(A); 
		if form_bool eq false then 
			ax:=FindAllIdempotents(A,sub<A`W|A`W!Eltseq(one)>+ann:one:=one);
		end if;
	end if;
	ax:=FindAllIdempotents(A,sub<A`W|A`W!Eltseq(one)>+ann:length:=1,one:=one, form :=form);
	if #ax eq 0 then
		return false,_;
	else
		ax:=[x:x in ax|HasMonsterFusion(x)];
		if #ax eq 0 then
			return false,_;
		elif #ax gt 0 then
			return true,IndexedSet(ax);
		end if;
	end if;
end intrinsic;

/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Given two vectors a and b, project a to b. We assume that the axial algebra containing a and b has a definite form U  +
+                                                                                                                       +
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/ 
intrinsic Proj_aTo_b(a::ParAxlAlgElt, b::ParAxlAlgElt, form::AlgMatElt)->ParAxlAlgElt
{
	Given two axial algebra elements a and b where the algebra containing them has a form U, project a to b.
}  
	return (FrobFormAtElements(a,b,form)/FrobFormAtElements(b,b,form))*b;
end intrinsic;
/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Function to othorgonalise a basis of a subspace of an axial algebra with a form                                                   =
+                                                                                                                                   +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/
intrinsic OrthogonaliseBasis(A::ParAxlAlg, basis:: SeqEnum, U::AlgMatElt)-> SeqEnum 
{
	Given an axial algebra A and a sequence basis which is a basis for A or a subspace, orthogonalise the sequence. 
}

	require IsIndependent({A`W!Eltseq(x):x in basis}): "A basis must be linearly independent"; 
	m:=#basis;
	orth_bas:=[basis[1]];
	for i:=2 to m do
		v:=basis[i];
		w:=v-(&+[Proj_aTo_b(A!v,A!orth_bas[j],U):j in [1..i-1]]);
		Append(~orth_bas,w);
	end for;
	return orth_bas;
end intrinsic;

/*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Given an axial vector w and a subspae V of an axial algebra A containing w, project w to V.                                                +
+                                                                                                                                            +
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/
intrinsic ProjectVecToSubspace(w::ParAxlAlgElt, V::ModTupFld, form::AlgMatElt)-> ModTupFldElt
{
Given a subspace V of an axial algebra A, and a vector w in A , together with a Frobenius form, project w to V. 
}
	A:=Parent(w);  
	require Dimension(A) eq Degree(V): "Incompatible spaces"; 
	U:=form;
	require Nrows(U) eq Ncols(U): "The form must be a square matrix";
	require IsSymmetric(U): "The form is necessarily symmetric"; 
	if A`W!Eltseq(w) in V then 
		return A`W!Eltseq(w);
	end if; 
	bas:=Basis(V);
	bas:=[A!x:x in bas];
	orth:=OrthogonaliseBasis(A, bas,U); 
	proj:=&+[Proj_aTo_b(w,orth[i],U):i in [1..#bas]];
	return A`W!Eltseq(proj);
 end intrinsic; 

//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
// This function takes an automorphism phi of a subalgebra V of an axial algebra A and checks whether the         + 
// automorphism extends to an automorphism of  a module M of V under adjoint actions of V. Note here              +
//that V is just an ordinary space but A must be axial. Also, phi must be a dim(V)xdim(V) matrix over the base-   +
//field of A. We assume that it is indeed an automorphism and a check shall not be made.                          +
//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

intrinsic ExtendAutToMod(A::ParAxlAlg, V::ModTupFld, M::ModTupFld, phi::AlgMatElt)-> BoolElt, ModTupFld
{
	Given an axial algebra A, a subalgebra V, a module M for V, together with a map or automorphism phi of V, determine if the automorphism induces a map on M. If true, a vector space with degree dim(M)xdim(M) is returned where each basis vector is a concatenation of rows of a matrix representing the induced map.
} 
	n:=Dimension(A);
	k:=Dimension(V);
	m:=Dimension(M);
	F:=BaseField(A);
	V_onM:=[];
	for i:=1 to k do
	       Append(~V_onM,AdMatInSubAlg(A,M,A!V.i));
	end for;
 	/*we've set up the ad_vi matrices acting on M, where v_i is a basis for V.*/ 
	sols:=[* *]; /*initialise the solution list.*/
	B:=ZeroMatrix(F,k*m^2,m^2);
	count:=1; 
	for i:=1 to k do/*fixing some v_i.*/
		for j:=1 to m do /*fixing m_j.*/
			v_im_j:=V_onM[i][j];/* the entries of v_i*m_j are the values C_1,...,C_m.*/
			Mat_lhs:=ZeroMatrix(F,m,m*m);
			for l:=1 to m do /*this is the row number for the matrix lhs.*/
				for r:=1 to m do
				Mat_lhs[l][(r-1)*m+l]:=v_im_j[r];	
				end for;
			end for;
			//Mat_lhs; 
			Mat_rhs:=ZeroMatrix(F,m,m*m);
			vi_phi:=ToSmallVec(A,V,A!V.i)*phi;/* we get \mu_1,...,\mu_k.*/ 
			for l:=1 to m do /*row number of the mat, corresponding to the cols of (x_ij).*/
				for r:=1 to m do 
					coeff:=&+[vi_phi[t]*V_onM[t][r][l]:t in [1..k]];
					Mat_rhs[l][(j-1)*m+r]:=coeff;
				end for;
			end for;
			//Mat_rhs;
			syst:=Mat_lhs-Mat_rhs;
			for l:=1 to m do
				B[(count-1)*m+l]:=syst[l];
			end for;
			count+:=1; 
		end for;
	end for;
	print "the system of equations has been set up.\n";
	sol,space:=Solution(Transpose(B),Vector(F,[0*t:t in [1..m*m*k]]));
	if Dimension(space) eq 0 then
		return false,_;
	else
		return true, space;
	end if; 
end intrinsic;	

/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Given a vector u, project it into a space V. This will assume that the algebra A containing u has a form  +
+ U.                                                                                                        +
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/
intrinsic ProjectVecToJointSpaces(u::ParAxlAlgElt, lst::SeqEnum, lst1::SeqEnum)-> SeqEnum, ParAxlAlgElt
{
Given an axial algebra element u, project u to joint eigenspace decompositions of the algebra A containing u with respect to a set lst of axes. The sequence lst1 contains the keys.
}
/*this blurb needs fine-tuning. Also think about the return value.*/ 
	A:=Parent(u);
        n:=Dimension(A);	
	F:=BaseField(A);
	eigs:=[1,0,1/4,1/32];
	ads:=[];
	for i:=1 to #lst do
		Append(~ads,AdMat(lst[i]));
	end for; 
	projs:=[];
	Id:=IdentityMatrix(F,n); 
	for i:=1 to #lst do
		ad:=ads[i];
		pj:=[];
		for j:=1 to 4 do
			proj:=&*[(ad-eigs[k]*Id)/(eigs[j]-eigs[k]):k in [1..4]|k ne j];
		 	Append(~pj,proj);
		end for;
		Append(~projs,pj);
	end for; 
	im:=A`W!Eltseq(u); 
	for i:=1 to #lst1 do
       		ind:=Index(eigs,lst1[i]); 
		im:=im*(projs[i][ind]);
	end for;	
	return projs,A!im;
end intrinsic;

/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+Given an axial algebra A over the rationals whose Miyamoto group is A_n, find an automorphism of order 2 coming from the action                            + 
+ of an odd involution. As input, take A and n in that order. We will include a switch which will by default turn off the check at end,                     + 
+ but will run it if the extra optional input is set to true.                                                                                               +
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/
intrinsic OuterAut(A::ParAxlAlg, n::RngIntElt :RunCheck:=false)->AlgMatElt, RngIntElt /*input is the algebra A with Miyamoto group A_n. Specify n also.*/

{
	For an axial algebra a whose Miyamoto group is A_n, find an outside automorphism induced by an odd involution of S_n. As a biproduct we get m-clossure for A.
}  
	require n gt 0: "The integer n must be positive"; 
	require GroupName(MiyamotoGroup(A)) eq Sprintf("A%o",n): "The Miyamoto group of A must be A_n for the given n"; 
	axes:=Axes(A);
	axes:=&join[x:x in axes];
	W:=VectorSpace(Rationals(),Dimension(A));
	SS:=SymmetricGroup({(Dimension(A)-#axes)+1..Dimension(A)});/* Here note that by construction (Justin verified), the generating axes ocuppy the last k 
							       positions of the canonical basis, where k is the number of axes.*/
	/* G is the corresponding alternating group.*/
	G:=Alt(n);
	invs:=[x[3]:x in ConjugacyClasses(G)|x[1] eq 2];
	invs:=[invs[i]^G:i in [1..#invs]]; /*actually we need to iterate over all the conjugacy classes of A_n which are involutions. 
for A_5 providence has it that we have only one.*/
	/*	we can can do invs:=&join[x:x in invs];*/
	invs:=&join[x:x in invs];
	cyc:=Sym(n)!(1,2);
	invols:=invs;
	actions:= {@<i,Index(invols,(invols[i]^cyc))>:i in [1..#invols]@};
	actions:=[x:x in actions|x[1] lt x[2]];/*this gives the conjugation action of cyc on the set  of all axes*/
	start:=Dimension(A)-#axes;
	outsider:=SS!(actions[1][1]+start, actions[1][2]+start);
	outsider*:=&*[SS!(actions[i][1]+start,actions[i][2]+start):i in [2..#actions]];
	axes_inds:=[(Dimension(A)-#axes)+1..Dimension(A)];
	unfilled_inds:=[x:x in [1..Dimension(A)]|not x in [(Dimension(A)-#axes)+1..Dimension(A)]];
	mclos:=1 ;
	if #axes eq Dimension(A) then 
		 print "algebra is 1-closed";
	else 
		 mclos+:=1;
	end if;
	outside_aut:=ZeroMatrix(Rationals(),Dimension(A),Dimension(A));
	found:=[];
	for i in axes_inds do 
		outside_aut[i]:=W!(Eltseq(A.(i^outsider)));
		Append(~found,i);
	end for;
	for i in axes_inds do 
		for j in axes_inds do 
			if i lt j then 
				prod:=(A.i)*(A.j);
				prod_vec:=W!Eltseq(prod);
				sup:=Support(prod_vec);
			       	if #{x:x in sup|x in unfilled_inds} eq 1 then
					l:=[x:x in sup|x in unfilled_inds][1];
					im:=(A.(i^outsider)*(A.(j^outsider)))-&+[prod_vec[m]*(A!((W!Eltseq(A.m))*outside_aut)):m in sup|m ne l];
					outside_aut[l]:=(W!Eltseq(im))/(prod_vec[l]);
					Append(~found,l);
					unfilled_inds:=[x:x in unfilled_inds|x notin found];
				end if;
			 end if;
		end for;
	end for;
	old_found:=found;
	new:=[x:x in found|not x in axes_inds];
	while #unfilled_inds gt 0 do
	       new_found:=[];
	       for i:=new[1] to new[#new] do 
		      for j in axes_inds do
			      prod:=(A.i)*(A.j);
			      prod_vec:=W!Eltseq(prod);
			      sup:=Support(prod_vec);
			      if #{x:x in sup|x in unfilled_inds} eq 1 then 
				      l:=[x:x in sup|x in unfilled_inds][1]; 
				      im:=(A!(W!(Eltseq(A.i))*outside_aut))*(A!((W!(Eltseq(A.j)))*outside_aut))-A!(&+[prod_vec[m]*(W!(Eltseq(A.m))*outside_aut):m in sup|m ne l]);
				      outside_aut[l]:=(W!Eltseq(im))/(prod_vec[l]);
				      Append(~found,l);
				      unfilled_inds:=[x:x in unfilled_inds|x ne l];
			      end if;
		   end for;
	    end for;
	    mclos+:=1;
		    new:=[x:x in found|not x in old_found];
		    old_found:=found;
	end while;
 	//outside_aut^2 eq Identity(Parent(outside_aut));
	if not RunCheck eq false then 
		forall{x:x in [y:y in CartesianPower( [1..Dimension(A)] ,2)| y[1] le y[2] ]|A!((W!Eltseq((A.(x[1]))*(A.(x[2]))))*outside_aut) eq A!((W!Eltseq(A.(x[1])))*outside_aut)*(A!((W!Eltseq(A.(x[2])))*outside_aut))};/**/
	end if;
	return outside_aut,mclos;
end intrinsic;

/* NOTE: the function above is actually redundant, we can achieve what it does by creating a map which maps the axes to axes in such a way that the action is equivalent to an odd permutation then apply the map in ExtendMapToAut. */

intrinsic MultTensor(t::SeqEnum, u::ModTupFldElt, v::ModTupFldElt)-> ModTupFldElt
{
	Given a tensor consisting of products v_iv_j for j greater or equal to i, where the v_ks are a basis for a subalgebra of an axial algebra, find the product of the given vectors u and v. Here u and v as well as the vectors in the tensor must have degree equal to the dimension of the subalagebra. 
}
	require Parent(t[1]) eq Parent(u): "The vector u must be in the same universe as the vectors in the tensor";
	require Parent(u) eq Parent(v): "The vectors u and v are not compatible"; 
	sols:=Roots(Polynomial(IntegerRing(),[-2*#t,1,1]));
	d:=[x[1]:x in sols|Sign(x[1]) eq 1][1];
	if Degree(u) ne d then
		return Sprintf("error, the vector must be %o long\n",d);
	else
		sq:=&+[u[i]*v[i]*t[IntegerRing()!((i-1)/2*(2*d+2-i))+1]:i in [1..d]];
		rest:=&+[&+[(u[i]*v[j]+u[j]*v[i])*t[IntegerRing()!((i-1)/2*(2*d-i+2))+j-i+1]:i in [1..(d-1)],j in [1..d]|j gt i]];
		return sq+rest;
	end if;
end intrinsic;

/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Given an algebra A, a subalgebra V, and a subspace W of V with a prescribed basis as a list of vectors,  determine ann W.                 +
+ The inputs are A, which must be axial, or a tensor which gives algebra multiplication. The basis, bas, of W, can be ordinary vectors.     +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/ 

intrinsic AnnInSubspace(A::ParAxlAlg, V::ModTupFld, W::ModTupFld)-> ModTupFld
{
	Given an algebra A, a subalgebra V, and a subspace W of V,  determine ann W. 
}
	require Degree(V) eq Dimension(A): "V must be a subspace of A as a vector space.";
	require Degree(W) eq Dimension(A): "W must be a subspace of A as a vector space.";
	require W subset V: "W must be a subspace of V";
	tens:=[];
	bas:=Basis(W);
	d:=Dimension(V);
	W:=VectorSpace(Rationals(),Dimension(A));
	basmat:=Matrix(Rationals(),[Eltseq(V.i):i in [1..d]]);
	for i:=1 to d do 
		for j:=1 to d do 
			if i le j then
				Append(~tens, Solution(basmat,Vector(BaseField(A),Eltseq(A!Eltseq(V.i)*A!Eltseq(V.j)))));
			end if;
		end for;
	end for;
/*here we can as well just input the tensor.*/
	bas:=[Solution(basmat,Vector(BaseField(A),Eltseq(x))):x in bas];	
        m:=#bas;	
        M:=ZeroMatrix(Rationals(),m*d,d); 
	for k:=1 to m do
		for l:=1 to d do
		       	row:=[];
			for i:=1 to d do
				for j:=1 to d do 	
					ii:=Minimum({i,j});jj:=Maximum({i,j});
					M[d*(k-1)+l][i]+:=bas[k][j]*tens[IntegerRing()!((ii-1)/2*(2*d+2-ii))+jj-ii+1][l];
				end for; 
			end for;
		end for;
	end for;
		big_vec:=VectorSpace(Rationals(),d*m)!0;	
		_,sols:=Solution(Transpose(M),big_vec);
		bas_sols:=Basis(sols);
		sub_ann:=[&+[Eltseq(bas_sols[i])[j]*V.j:j in [1..d]]:i in [1..Dimension(sols)]];
		return sub<W|sub_ann>;
end intrinsic;

/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Given an algebra A, determine if a subalgebra V is a unital algebra.                                                                      +
+                                                                                                                                           +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/ 
intrinsic HasIdentitySubAlg(A::ParAxlAlg, V::ModTupFld)-> BoolElt, ParAxlAlgElt
{
	Given an axial algebra A, and a vector space V which is a subalgebra of A, determine if V has a one as an algebra. It returns true if an identity exists in V, as well the identity, false is returned otherwise.
}
	require Degree(V) eq Dimension(A): "V must be  a subspace of A.";
	require forall{i:i in [1..Dimension(V)]|forall{j:j in [i..Dimension(V)]|A`W!Eltseq((A!V.i)*(A!V.j)) in V}}: "V is not closed under multiplication"; 
	tens:=[];
	d:=Dimension(V);
	W:=VectorSpace(Rationals(),Dimension(A));
	basmat:=Matrix(Rationals(),[Eltseq(V.i):i in [1..d]]);
	for i:=1 to d do 
		for j:=1 to d do 
			if i le j then
				Append(~tens, Solution(basmat,W!Eltseq(A!V.i*A!V.j)));
			end if;
		end for;
	end for;
	k:=1;
	rows:=[];
	vecs:=[];
	sols:=[];
	for k:=1 to d do
		for l:=1 to d do
		       	row:=[];
			for i:=1 to d do
				ii:=Minimum({i,k});jj:=Maximum({i,k});
				Append(~row,tens[IntegerRing()!((ii-1)/2*(2*d+2-ii))+jj-ii+1][l]); 
			end for;
			Append(~rows,row);	
		end for;
		vec:=Vector(BaseField(A),[0*i:i in [1..d]]);
		vec[k]:=1;
		Append(~vecs,vec);
	end for;
	big_vec:=&cat[Eltseq(x):x in vecs];
	big_vec:=Vector(Rationals(),big_vec);	
	bool,part_sol,Sol_space:=IsConsistent(Transpose(Matrix(Rationals(),rows)),big_vec);
	if bool eq true then 
		return bool,A!(&+[part_sol[i]*V.i:i in [1..d]]);
	else
		return bool,_;
	end if; 
end intrinsic;

/*Utilities required by SatisfiesMonsterFusion. Implements fusion checking as per the paper Universal axial algebras and a theorem of Sakuma.*/ 
 EigsMinusOne:=[Rationals()!0,1/4,1/32];
intrinsic fmu(mu:: FldRatElt)->RngUPolElt
{
	produce the polynomial f_\{mu\}=Prod (x-lambda), lambda in \{0,1/4,1/32\},lambda ne mu.
 
} 
	 return &*[Polynomial(Rationals(),[-x,1]):x in EigsMinusOne|x ne mu]; 
end intrinsic;

/*Given a polynomial p and a matrix M, form p(M).*/
intrinsic PolynomialAtMat(p::RngUPolElt, M::AlgMatElt)-> AlgMatElt
{
	Given a polynomial p and a square matrix M, form p(M).
}
	require Nrows(M) eq Ncols(M): "The matrix must be square"; 
	 return &+[Coefficients(p)[i]*M^(i-1):i in [1..Degree(p)+1]];
end intrinsic;

/* SatisfiesMonsterFusion here. This will require a form.*/
  
/*Suppose that an algebra A has a form U. Let B be a subalgebra of A.
  This function produces the form restricted to B.*/
intrinsic RestrictedForm(U::AlgMatElt, B::ModTupFld)-> AlgMatElt
{
	Given a subpace B of an axial algebra A admitting a form U, restrict the form to B.
}
	require Nrows(U) eq Ncols(U): "The form must be a square matrix";
	require IsSymmetric(U): "The form must be symmetric";
	require Degree(B) eq Nrows(U): "B must be a subspace of the parent algebra"; 
	UU:=ChangeRing(U,BaseRing(B));
	arr:=[[(VecToMat(B.i)*UU*Transpose(VecToMat(B.j)))[1][1]:j in [1..Dimension(B)]]:i in[1..Dimension(B)]];
	return Matrix(Rationals(),[Eltseq(x):x in arr]);
end intrinsic;
/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Given an idempotent a in an axial algebra, we wish to find out if a satisfies a fusion law.       +
+                                                                                                   +
+ FindFusion AxlAlgxVectSpace-->2^X, where X:=Spec(a).                                              +
+                                                                                                   +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/
intrinsic FindFusionLaw(A::ParAxlAlg, V::ModTupFld, a::ParAxlAlgElt)->SeqEnum /*V is a subspace which could be A.*/
{
	Given an axial algebra A, a subspace V, and an axial algebra element a which lies in V as a subspace, determine if a satisfies a fusion law in V.
}
	require a ne  A!0: "a must be nonzero";	
	require Pow(a,2) eq a: "The given element is not an idempotent";
	require A`W!Eltseq(a) in V: "a must be coercible to V"; 
	eigs:=Eigenvalues(AdMatInSubAlg(A,V,a));
	fus:=[* *];
	eigs:=SetToSequence(eigs);
	evals:=[eigs[i][1]:i in [1..#eigs]];
	mults:=[eigs[i][2]:i in [1..#eigs]];
	ord_eigs:=[1/1]; 
	ord_mults:=[x[2]] where x is [y:y in eigs|y[1] eq 1][1];
	if 0 in evals then
		Append(~ord_eigs,RationalField()!0);
		ind:=Index(eigs,x) where x is [y:y in eigs|y[1] eq 0][1];
		Append(~ord_mults,mults[ind]);
	end if;
	for i:=1 to #evals do
		if evals[i] notin ord_eigs then
			Append(~ord_eigs,evals[i]);
			Append(~ord_mults,mults[i]);
		end if;
	end for;
	for j:=1 to #evals do
    		for k:=j to #evals do
        	ind:=IntegerRing()!(((j-1)/2)*(2*#evals-j+2))+k-j+1;
        	fus[ind]:=[*<ord_eigs[j],ord_eigs[k]>,[ ]*];
    		end for;
	end for;/*at this stage fus will have <<\mu,\lambda>,[]> for each fusion rule.*/
	m:=Dimension(V);
	F:=BaseField(A);
	W:=VectorSpace(F,m);
	bas_mat:=Matrix(F,[Eltseq(V.i):i in [1..m]]);
	Id:=IdentityMatrix(F,m);
	ad_mat:=AdMatInSubAlg(A,V,a);
	Projs:=[];
	for i:=1 to #ord_eigs do
		Append(~Projs,&*[(ad_mat-ord_eigs[j]*Id)/(ord_eigs[i]-ord_eigs[j]):j in [1..#eigs]|j ne i]);
	end for;
	for i:=1 to m do
		w:=W.i;
		splits:=[w*Projs[t]:t in [1..#evals]];
		for j:=1 to #evals do
			for k:=j to #evals do
				prod:=(ToBigVec(A,V,splits[j]))*(ToBigVec(A,V,splits[k]));
				prod_w:=A`W!Eltseq(prod);
				prod_short:=Solution(bas_mat,prod_w);
				for s:=1 to #Projs do
					if prod_short*Projs[s] ne W!0 then
						ind:=IntegerRing()!(((j-1)/2)*(2*#evals-j+2))+k-j+1;
						if ord_eigs[s] notin fus[ind][2] then
						       Append(~fus[ind][2],ord_eigs[s]);  
						end if;
					end if;
				end for;
			end for;
		end for;
	end for;		
	return fus;
end intrinsic;

/*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ A function to find the subalgebra generated by a sequence of axial vectors.                                    +
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/
intrinsic SubAlgebra(L::SetIndx )->ModTupFld 
{
	Given an indexed set L of axial vectors, return the subalgebra of the parent algebra that is generated by L. 
} 
	require #L gt 0: "L must be nonempty";
	A:=Parent(L[1]); 
	require Type(L[1]) eq ParAxlAlgElt: "The vectors in L must be algebra elements"; 
	n:=Dimension(A);
	W:=VectorSpace(BaseField(A),n);
	lst:=[W!Eltseq(L[i]):i in [1..#L]];/*set up the vectors in L as ordinary vectors*/
	if #L eq 1 and W!0 in lst then
		return sub<W|W!0>;
	end if;
	/* we start by finding a maximally independent set.*/ 
	max_independent_set:=[];
	non_zero:=[];
	for i:=1 to #L do
		if lst[i] ne W!0 then
			Append(~non_zero,lst[i]);
		end if;
	end for;
	V:=sub<W|non_zero[1]>;
	if #non_zero eq 1 then 
		max_independent_set:=non_zero;
	else 
		Append(~max_independent_set, non_zero[1]); 
		for i:=2 to #non_zero do
			if not non_zero[i] in V then
				Append(~max_independent_set, non_zero[i]);
				V+:=sub<W|non_zero[i]>;
			end if;
		end for;	
	end if;
	max_independent_set:=[A!x:x in max_independent_set];
	bool,VV:=ExtendMapToAlgebra(max_independent_set, max_independent_set);
	if bool eq true then 
		return W;
	else
		return VV;
	end if; 
end intrinsic;
/*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ An alternative for checking if an idempotent satisfies the Monster Fusion law if the aglgebra has form M   +
+                                                                                                            +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/ 
intrinsic SatisfiesMonsterFusion(u::ParAxlAlgElt ,M::AlgMatElt)->BoolElt
{
	Given an idempotent u in an axial algebra A and the form M, determine if u satisfies the Monster M(1/4, 1/32) fusion law.
}
	require Pow(u,2) eq u: "The given element must be an idempotent";
	require Nrows(M) eq Ncols(M): "The form must be a square matrix";
	require IsSymmetric(M): "The form must be symmetric"; 
	A:=Parent(u);/*This is the axial algebra in question. */
	d:=Dimension(A);
	require Nrows(M) eq d: "The dimension of the form must agree with the dimension of the algebra";
	F:=BaseField(A);
	X:=&join[x:x in Axes(A)];
	//admat:=Matrix(Rationals(),[Eltseq(u*A.i):i in [1..d]]);
	admat:=AdMat(u);
	Eigs:=Eigenvalues(admat);
	Evals:=[x[1]:x in Eigs];
	mults:=[x[2]:x in Eigs];
	if forall(x){x:x in Evals|x in [1,0,1/4,1/32]} eq false then
		printf "the eigenvalue %o is not in [1,0,1/4,1/32]\n",x;
		return false;
	end if;
	if &+[x:x in mults] lt d then
		print " Multiplities do not add up.\n";
		return false;
	end if;
/*In the calculation these matrices are used multiple times. Precompute them. Should surely speed things up as dimension grow.*/
	f0:=fmu(Rationals()!0);
	f0_mat:=PolynomialAtMat(f0,admat);
	f4:=fmu(1/4);
	f4_mat:=PolynomialAtMat(f4,admat);
	f32:=fmu(1/32);
	f32_mat:=PolynomialAtMat(f32,admat);
	f0_0:=Polynomial(Rationals(),[0,1]);
	f0_0_mat:=PolynomialAtMat(f0_0,admat);
	f0_4:=Polynomial(Rationals(),[-1/4,1]);
	f0_4_mat:=PolynomialAtMat(f0_4,admat);
	f0_32:=Polynomial(Rationals(),[-1/32,1]);
	f0_32_mat:=PolynomialAtMat(f0_32,admat);
	f4_4:=Polynomial(Rationals(),[0,-1,1]);
	f4_4_mat:=PolynomialAtMat(f4_4,admat);
	f4_32:=Polynomial(Rationals(),[-1/32,1]);
	f4_32_mat:=PolynomialAtMat(f4_32,admat);
	f32_32:=&*[Polynomial(Rationals(),[-x,1]):x in [1,0,1/4]];
	f32_32_mat:=PolynomialAtMat(f32_32,admat);
	bools:=[];
	Append(~bools,forall{x :x in [y:y in CartesianPower([1..#X],2)|y[1] le y[2] ]|(VecToMat((A!Eltseq((VecToMat(X[x[1]]-FrobFormAtElements(X[x[1]],u,M)*u))*f0_mat))*(A!Eltseq((VecToMat(X[x[2]]-FrobFormAtElements(X[x[2]],u,M)*u))*f0_mat))))*f0_0_mat eq VecToMat(A!0)});
	Append(~bools,forall{<x,y>:x,y in X|(VecToMat((A!Eltseq((VecToMat(x-FrobFormAtElements(x,u,M)*u))*f0_mat))*(A!Eltseq((VecToMat(y-FrobFormAtElements(y,u,M)*u))*f4_mat))))*f0_4_mat eq VecToMat(A!0)});
	Append(~bools,forall{<x,y>:x,y in X|(VecToMat((A!Eltseq((VecToMat(x-FrobFormAtElements(x,u,M)*u))*f0_mat))*(A!Eltseq((VecToMat(y-FrobFormAtElements(y,u,M)*u))*f32_mat))))*f0_32_mat eq VecToMat(A!0)});
	Append(~bools,forall{<x,y>:x,y in X|(VecToMat((A!Eltseq((VecToMat(x-FrobFormAtElements(x,u,M)*u))*f4_mat))*(A!Eltseq((VecToMat(y-FrobFormAtElements(y,u,M)*u))*f4_mat))))*f4_4_mat eq VecToMat(A!0)});
	Append(~bools,forall{<x,y>:x,y in X|(VecToMat((A!Eltseq((VecToMat(x-FrobFormAtElements(x,u,M)*u))*f4_mat))*(A!Eltseq((VecToMat(y-FrobFormAtElements(y,u,M)*u))*f32_mat))))*f4_32_mat eq VecToMat(A!0)});
	Append(~bools,forall{<x,y>:x,y in X|(VecToMat((A!Eltseq((VecToMat(x-FrobFormAtElements(x,u,M)*u))*f32_mat))*(A!Eltseq((VecToMat(y-FrobFormAtElements(y,u,M)*u))*f32_mat))))*f32_32_mat eq VecToMat(A!0)});
	return forall{x:x in bools|x eq true}; 
end intrinsic;
/*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ A function to find the structure of a subalgebra generated by a list lst, of axes of an axial algebra A. We assume that multiplication +  
+in A is known. Additional input in the form of a string ("a" say) for which the axes are to be called is required. The function returns a+  
+tensor tens of coordinates of products a_i*a_j. Imperative for the list to live in the axial category.                                  +
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/
intrinsic SubAlgStructure(lst::SetIndx: str:="a")-> SeqEnum, SeqEnum
{
	Given an indexed set of axial algebra elements, produce a tensor encoding the multiplication in the subalgebra generated by the elements.
}
	require Type(lst[1]) eq ParAxlAlgElt: "The given elements are not algebra elements";
	require Type(str) eq MonStgElt: "The input should be a string"; 
	axes:=lst;
	letter:=str;
	V:=SubAlgebra(axes);
	bas:=ExtendBasis([V!Eltseq(lst[i]):i in [1..#lst]],V);
	tens:=[];
	struct:=[Sprintf("A %o-dimensional algebra generated by axes %o_i, 1=<i =<%o ",#bas,letter,#axes)];
	A:=Parent(axes[1]);
	basmat:=Matrix(Rationals(),[Eltseq(bas[i]):i in [1..#bas]]);
	signs:=["+","-"];
	signs1:=[1,-1];
	for i in [1..#bas] do 
		for j in [1..#bas] do
		       if i le j then
		      		//st:=Sprintf("%o*%o=",strs[i],strs[j]);	       
			       	coord:=Solution(basmat,Vector(Rationals(),Eltseq((A!bas[i])*(A!bas[j]))));
			     Append(~tens,coord);
			      /*   if IsEmpty(Support(coord)) then st:=st*"0";
				elif #Support(coord) eq 1 then
				       if Abs(coord[SetToSequence(Support(coord))[1]]) eq 1 then
						if Sign(coord[(IndexedSet(Support(coord))[1])]) eq 1 then
			                       		// st:=st*Sprintf(" %o",strs[IndexedSet(Support(coord))[1]]);
						elif Sign(coord[IndexedSet(Support(coord))[1]]) eq -1 then
						      // st:=Sprintf("%o*%o= %o",strs[i],strs[j],strs[IndexedSet(Support(coord))[1]]);
						end if;
					 else
						 if Sign(coord[IndexedSet(Support(coord))[1]]) eq 1 then 
						       //st:=st*Sprintf("%o*%o",coord[IndexedSet(Support(coord))[1]],strs[IndexedSet(Support(coord))[1]]);
					         elif Sign(coord[IndexedSet(Support(coord))[1]]) eq -1 then
						       //st:=st*Sprintf("%o*%o",coord[IndexedSet(Support(coord))[1]],strs[IndexedSet(Support(coord))[1]]);
						 end if;			
					 end if;
				 elif #Support(coord) gt 1 then
					sup:=IndexedSet(Support(coord)); 
					for k:=1 to #sup do
						if k eq 1 then
						      if Abs(coord[sup[k]]) eq 1 then
							      if Sign(coord[sup[k]]) eq 1 then 
								      st *:=strs[sup[k]];
							      elif Sign(coord[sup[k]]) eq -1 then 
							      		st*:=Sprintf("-%o",strs[sup[k]]);
							      end if;
						      elif Sign(coord[sup[k]]) eq 1 then 
						     	 st*:=Sprintf("%o*%o",coord[sup[k]],strs[sup[k]]);
						      elif Sign(coord[sup[k]]) eq -1 then 
						     		st*:=Sprintf("%o*%o",coord[sup[k]],strs[sup[k]]);
						      end if; 
						elif k gt 1 then
							if Abs(coord[sup[k]]) eq 1 then
								st:=st*Sprintf("%o%o",signs[Index(signs1,Sign(coord[sup[k]]))],strs[sup[k]]);
							elif k gt 1 and Abs(coord[sup[k]]) ne 1 then 
								st:=st*Sprintf("%o %o*%o",signs[Index(signs1,Sign(coord[sup[k]]))],Abs(coord[sup[k]]),strs[sup[k]]);
							end if; 
						end if;
					end for;
				end if;	
			end if;
				Append(~struct,st); */ 
			end if;
		end for;
	end for;
	return tens, struct;
end intrinsic;

/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Suppose that A is a an algebra and suppose that pair:=[a_0,a_1] is+
+ a pair of axes. What type of dihedral agebra does it generate?    +
+ We can find the dihedral group, and the subAlg code can give us   +
+the dimension of the algebra, thereby narrowing the possibilities. +
+ We then check which is satisfied. SubAlg_v3.m must be loaded.     +
+The tau matrices t_0,t_1, of a_0,a_1 resp are required. Load       +
+ TauMapMoster                                                      +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/
intrinsic IdentifyShape(lst::SeqEnum)->MonStgElt 
{
	Given a pair of distinct axes a_0,a_1, find they type of dihedral algebra they generate.
}
	require Type(lst[1]) eq ParAxlAlgElt: "The elements of the sequence must really be axial vectors.";
	require #lst eq 2: "The input must have cardinality 2";
	require lst[1] ne lst[2]: "The input must consist of distinct axes";
	require forall{x:x in lst|Pow(x,2) eq x and HasMonsterFusion(x)}: " The elements of lst must be axes";
	/* in light of the twin axes phenomenon, we need to check that the given axes are not twins.*/ 
	A:=Parent(lst[1]);
	/*In light of the twin/multiple phenomenon, when determining the shape of dihedral algebras, it is important to check in the generating axes a_0, a_1 are twins or not. */
	/*I called the list [a_0,a_1] lst.*/
	a_0:=lst[1];
	a_1:=lst[2];
	if TauMapMonster(a_0) eq TauMapMonster(a_1) then
		if a_0*a_1 eq A!0 then
			return "2B";
		elif a_0*a_1 ne A!0 then
			return "2A";
			/*The dihedral algebra will be the span of a_0,a_1, and c where c is a_0+a_1-8*a_0*a_1*/
		end if;
	end if;
	ax:=[];
	shape:="";
	inds:=[];
	ord:=1;
	pow_id:=false;
	bas_dihed:=lst;
	t0:=TauMapMonster(bas_dihed[1]);
	t1:=TauMapMonster(bas_dihed[2]);
	rho:=t0*t1;
	rho_pow:=rho;
	W:=VectorSpace(Rationals(),Dimension(Parent(bas_dihed[1])));
	while pow_id eq false do
		if rho_pow eq Identity(Parent(rho)) then
			pow_id:=true;
		else
			rho_pow*:=rho;
			ord +:=1;
		end if;
	end while;
	/*At this stage we have n= ord in nL.*/
	dim:=Dimension(SubAlgebra(IndexedSet(bas_dihed)));
	V:=VectorSpace(Rationals(),dim);
	/*The last calculation  narrows the choice of L in nL. It remainsto check the possibilities for nL*/
	if ord eq 2 and dim eq 3 then /* the 2A case.*/
		strings:=["a_o","a_1","a_{rho}"];
		bas:=bas_dihed cat [bas_dihed[1]+bas_dihed[2]-8*(bas_dihed[1]*bas_dihed[2])];
		/*to beautify things and have the multiplication displayed nicely, we can adapt
		the code in SubAlgStructure to this setting, or we can feed bas to the function and get
		closure 1 instead of 2, a_3 for  a_rho. Future project.*/
		V:=VectorSpace(Rationals(),3);
		Expected:=[V![1,0,0],V![1/8,1/8,-1/8],V![1/8,-1/8,1/8],V![0,1,0],V![-1/8,1/8,1/8],V![0,0,1]];
		tens:=SubAlgStructure(IndexedSet(bas));
	//	tens; /*NOTE thereis a bit of an issue when MAGMA does echelonisation of bases.*/;
		if tens eq Expected then
			shape*:="2A";
		end if;
	elif ord eq 2 and dim eq 2 then /*2B case.*/
	     V:=VectorSpace(Rationals(),2);
	     Expected:=[V![1,0],V![0,0],V![0,1]];
	     bas:=bas_dihed;
	     tens:=SubAlgStructure(IndexedSet(bas));
		if tens eq Expected then
		   shape*:="2B";
		end if;
	elif ord eq 3 then /*3A and 3C here.*/
	     for i:=1 to 2 do
	     	 for j:=1 to ord-1 do
		 aa:=W!Eltseq(bas_dihed[i])*rho^j;
			if not  A!aa in bas_dihed and not A!aa in ax then
			   Append(~ax,A!aa);
			   Append(~inds, <i,j>);
			end if;
		end for;
	   end for;
	   if inds eq [<1,1>] or inds eq [<2,2>] then
	      //bas:=[bas_dihed[2],bas_dihed[1],ax[1]];
	      bas:=[ax[1],bas_dihed[1],bas_dihed[2]];
	   end if;
	   strings:=["a_{-1}","a_0","a_1"]; /*don't forget to add u_rho in the 4-dim case.*/
	   if dim eq 4 then /*3A subcase.*/
	      u_rho:=2^7/(3^3*5)*(bas[2]+bas[3]+(1/2)*bas[1]-2^4*(bas[2]*bas[3]));
	      Append(~strings,"u_{rho}");
	      bas cat:=[u_rho];
	      Expected:=[V![1/2^5,1/2^4,1/2^4,(-3^3*5)/2^11],V![-1/3^2,2/3^2,-1/3^2,5/2^5],V![0,0,0,1]];
	      tens:=SubAlgStructure(IndexedSet(bas));
	      if tens[[IntegerRing()!((x[1]-1)/2*(2*dim+2-x[1]))+x[2]-x[1]+1:x in [<2,3>,<2,4>,<4,4>]]] eq Expected then
	      	shape*:="3A";
	      end if;
	   elif dim eq 3 then
	   	tens:=SubAlgStructure(IndexedSet(bas));
		Expected:=[(1/2^6)*V![-1,1,1]];
		if tens[[5]] eq Expected then
		   shape*:="3C";
		end if;
	   end if;
	 elif  ord eq 4 then 
	   for i:=1 to 2 do
	     	 for j:=1 to ord-1 do
			 aa:=W!Eltseq(bas_dihed[i])*rho^j;
			if not  A!aa in bas_dihed and not A!aa in ax then
				 Append(~ax,A!aa);
				 Append(~inds, <i,j>);
			end if;
		end for;
	   end for;
		 bas:=[ax[2],bas_dihed[1],bas_dihed[2],ax[1]];
		/*this means a_{-1}=bas[1],a_0=bas[2],a_1=bas[3] and a_2 =bas[4].*/  
         	//if FrobFormAtElements(bas[2],bas[3],U) eq (1/(2^5)) then 
	if (bas[2])*(bas[4]) eq A!0 then	 
		v_rho:=bas[2]+bas[3]+1/3*(bas[1]+bas[4])-(2^6)/3*(bas[2]*bas[3]);
		Append(~bas,v_rho);
		strings:=["a_{-1}","a_0","a_1","a_2","v_{\rho}"];
		Expected:=[(1/2^6)*V![1,3,3,1,-3],(V!0),(1/2^4)*(V![-2,5,-2,-1,3]),V![0,0,0,0,1]];
		tens:=SubAlgStructure(IndexedSet(bas));
		if tens[[7,8,9,15]] eq Expected then 
			shape*:="4A";
		end if;
	//elif FrobFormAtElements(bas[2],bas[3],U) eq (1/(2^6)) then
	elif (bas[2])*(bas[4]) ne A!0 then 
		spec_ind:=[x:x in inds|x[2] eq 2];
		bas:=[ax[2],bas_dihed[1],bas_dihed[2],ax[1],2^6*(bas[2]*bas[3])-bas[2]-bas[3]+bas[1]+bas[4]];
		printf "%o\n",HasMonsterFusion(bas[5]) ;
		/* could have used a_{rho^2}:=a_0+a_2-8*a_0*a_2 for a_{rho^2}*/  
		strings:=["a_{-1}","a_0","a_1","a_2","a_{\rho^2 }"];
		Expected:=[(1/2^6)*V![-1,1,1,-1,1],(1/8)*(V![0,1,0,1,-1])];
		tens:=SubAlgStructure(IndexedSet(bas));
		if tens[[7,8]] eq Expected then 
			shape*:="4B";
		end if;
	end if;
	/* For the order 5 and 6, there is only one choice for each so unless we want to build the algebra, the commented parts are not relevant to finding shape.*/ 
	elif ord eq 5 then
		/*for i:=1 to 2 do 
			for j:=1 to ord-1 do 
				aa:=W!Eltseq(bas_dihed[i])*rho^j;
				if not A!aa in bas_dihed and not A!aa in ax then 
					Append(~ax,A!aa);
					Append(~inds,<i,j>);
				end if;
			end for;
		end for;
		strings:=["a_{-2}","a_{-1}","a_0","a_1","a_2","w_{\rho}"];
		bas:=[ax[Index(inds,<1,4>)],ax[Index(inds,<1,2>)],bas_dihed[1],bas_dihed[2],ax[Index(inds,<1,1>)]];
		w_rho:=bas_dihed[1]*bas_dihed[2]-(1/(2^7))*(3*bas_dihed[1]+3*bas_dihed[2]-bas[5]-bas[2]-bas[1]);
		Append(~bas,w_rho);
		tens:=SubAlgStructure(IndexedSet(bas));
		Expected:=[(1/2^7)*V![-1,-1,3,3,-1,2^7],(1/2^7)*V![-1,-1,3,-1,3,-2^7],(7/2^(12))*V![-1,1,0,1,-1,2^7],(((5^2)*7)/2^(19))*V![1,1,1,1,1,0]];
		if tens[[IntegerRing()!((x[1]-1)/2*(2*dim+2-x[1]))+x[2]-x[1]+1:x in [<3,4>,<3,5>,<3,6>,<6,6>]]] eq Expected then
			shape*:="5A";
		end if;*/
		shape*:="5A";/*we really don't need all the other checks  since order 5 is unique. I had it to just check implementation which is fine. Same
		for 6A*/
	elif ord eq 6 then 
		/*strings:=["a_{-2}","a_{-1}","a_0","a_1","a_2","a_3","a_{\rho^3}","u_{\rho^2}"];
		for i:=1 to 2 do 
			for j:=1 to ord-1 do 
				aa:=W!Eltseq(bas_dihed[i])*rho^j;
				if not A!aa in bas_dihed and not A!aa in ax then 
					Append(~ax,A!aa);
					Append(~inds,<i,j>);
				end if;
			end for;
		end for;
		bas:=[ax[2],ax[4],bas_dihed[1],bas_dihed[2],ax[1],ax[3]];
		a_rho3:=bas[3]+bas[6]-8*(bas[3]*bas[6]);
		u_rho2:=(2^6/(5*3^3))*(2*bas[3]+2*bas[5]+bas[1])-((2^11)/((3^3)*5))*(bas[3]*bas[5]); 	
		Append(~bas,a_rho3);
		Append(~bas,u_rho2);
		Expected:=[(1/2^6)*V![-1,-1,1,1,-1,-1,1,0]+((3^2)*5/(2^11))*V![0,0,0,0,0,0,0,1],(1/2^5)*V![1,0,2,0,2,0,0,0]-(5*(3^3)/(2^11))*V![0,0,0,0,0,0,0,1],(1/2^3)*V![0,0,1,0,0,1,-1,0],(1/3^2)*V![-1,0,2,0,-1,0,0,0]+(5/2^5)*V![0,0,0,0,0,0,0,1],(V!0)];
		tensSubAlgStructure(IndexedSet(bas));
		if tens[[IntegerRing()!((x[1]-1)/2*(2*dim+2-x[1]))+x[2]-x[1]+1:x in [<3,4>,<3,5>,<3,6>,<3,8>,<7,8>]]] eq Expected then
			shape*:="6A";
		end if;*/
		shape*:="6A"; 	
	end if;
	return shape; 
end intrinsic;
        
intrinsic MinimumGeneratorsMiyamotoGroup(A::ParAxlAlg)-> SeqEnum
{
	Given an axial algebra A, find a minimum generating set of Miy(G) as a matrix group. Return a sequence of matrices forming the mimnimum generating set.
} 
	dim:=Dimension(A);
	F:=BaseField(A);
	axes:=Axes(A);
	a1:=axes[1][1];
	powers:=[];
	for i:=1 to 6 do 
		Append(~powers,Sprintf("%o",i));
	end for;
	shape_len:=#Shape(A)[2];
	shape:=Shape(A)[2]; 
	shape_nums:=IntegerRing()!(shape_len/2);
	/* this means the shape is of form n_1L_1n_2L_2...n_(shape_nums)L_(shape_nums), repetitions being possible. */ 
	shape_ns:=IndexedSet([Position(powers,shape[2*i-1]):i in [1..shape_nums]]);/*the above shows that the numbers occupy the odd positions.*/
	lst:=[];
	Id:=IdentityMatrix(F,dim);
	ord:=#MiyamotoGroup(A);
	gp:=MatrixGroup<dim,F|TauMapMonster(a1)>;
	for i:=1 to #shape_ns do 
		N:=shape_ns[i];
		for j:=1 to #axes do
			for k:=1 to #axes[j] do
				if axes[j][k] ne a1 then
					prod:=TauMapMonster(a1)*TauMapMonster(axes[j][k]);
					if Minimum({l:l in [1..6]|(prod)^l eq Id}) eq N and IsCoercible(gp,prod) eq false then
						Append(~lst,prod);
					end if;
				end if;
				gp:=MatrixGroup<dim, F|lst>;
				if Order(gp) eq ord then
					break i;
				end if;
			end for;
		end for;
	end for;
	printf "A minimum set of %o generators found \n", #lst;
	return lst;
end intrinsic;

intrinsic FullAutomorphismGroupAlg(A::ParAxlAlg, L::SeqEnum)->GrpMat
{
	Given an axial algebra and a sequence L consisting of all known axes of A, (found for instance using the methods above), return the full automorphism group of A as a matrix group.
}
	/*Note that groups like A_n, L_n which have covers always have an extra automorphism class induced from the action of the cover on G. I have a routine that produces a single such automorphism which must then be added to the minimum set of generators.*/
	require #L gt 0: "The sequence must be non-empty";
	require Parent(L[1]) eq A: "The list must have elements from the algebra A";
	require forall{x:x in L|HasMonsterFusion(x)}: "The list L must consist of axes";
	min_gens:=MinimumGeneratorsMiyamotoGroup(A);
	n:=Dimension(A);
	F:=BaseField(A);
	group:=MatrixGroup<n,F|min_gens>;
	for x in L do
		if not IsJordanAxis(x) then
			if not IsCoercible(group, TauMapMonster(x)) then
				Append(~min_gens, TauMapMonster(x));
				group:=MatrixGroup<n,F|min_gens>;
			end if;
		else /*x is a Jordan axis.*/
			if not IsCoercible(group, SigmaMapMonster(x)) then
				Append(~min_gens, SigmaMapMonster(x));
				group:=MatrixGroup<n,F|min_gens>;
			end if;
		end if;
	end for;
	return MatrixGroup<n,F|min_gens>;
end intrinsic;

intrinsic IsAutomorphicSubAlgMap(A::ParAxlAlg, V::ModTupFld, phi::AlgMatElt)->BoolElt
{
	Given an axial algebra A, a subalgebra V of A as a vector space, together with a map phi: V->V, determine if phi is an automorphism of V. 
	Note here that phi must be given as a dim(V)xdim(V) matrix.
}	
	m:=Dimension(V); 
	require V subset A`W: "V must be a subspace of A";
	require forall{i:i in [1..m]|forall{j:j in [i..m]| A`W!Eltseq((A!V.i)*(A!V.j)) in V}}: "V is not closed under multiplication";
	require Nrows(phi) eq Ncols(phi): "The map phi must be in square matrix form";
	require Nrows(phi) eq m: "The matrix dimension of the square matrix phi must be equal to the dimension of V";
	require IsInvertible(phi): "The map phi must be invertible";
	BasMat:=Matrix(BaseField(A),[Eltseq(V.i):i in [1..m]]);
	tens:=[];
	for i:=1 to m do
		for j:=i to m do 
			Append(~tens,Solution(BasMat,A`W!Eltseq((A!V.i)*(A!V.j))));
		end for;
	end for;
	return forall{i:i in [1..m]|forall{j:j in [1..m]|MultTensor(tens,ToSmallVec(A,V,A!V.i),ToSmallVec(A,V,A!V.j))*phi eq MultTensor(tens,ToSmallVec(A,V,A!V.i)*phi,ToSmallVec(A,V,A!V.j)*phi)}};

end intrinsic;

intrinsic MiyamotoGroupMat(A::ParAxlAlg)->GrpMat
{
	Given an axial algebra A, return the Miyamoto group as a matrix group.
}

	return MatrixGroup<Dimension(A),BaseField(A)|MinimumGeneratorsMiyamotoGroup(A)>;
end intrinsic;
