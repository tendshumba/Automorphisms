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
	id_mat:=IdentityMatrix(BaseField(A),n);/*might now be useless.*/	
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
			end if;
		else
			M:=form;
		end if;/*at this stage we either have a form or the function has already returned a fail*/
		if one eq A!0 then
			try
				bool,one:=HasIdentityAlg(A);
				bool:=HasIdentityAlg(A);
			catch e;
				if bool eq false then
					 len_rest:=FrobFormAtElements(v,v,M)-length;
				end if;
			end try;
			_,one:=HasIdentityAlg(A);
			one:=AF!Eltseq(one);
		else 
			one:=AF!Eltseq(one);		
		end if;	
			len_rest:=FrobFormAtElements(one,v,M)-length;/* here we use (v,v)=(v,v*1)=(v*v,1)=(v,1)*/ 
		if extra_rels eq [] then  
			I:=ideal<R|Eltseq(v*v-v) cat [len_rest]>;
		/*this operation makes the calculation slow so do only as last resort.*/
		elif extra_rels ne [] and Dimension(ideal<R|Eltseq(v*v-v) cat [len_rest]>) gt 0 then  
			I:=ideal<R|Eltseq(v*v-v) cat [len_rest] cat extra_rels>; 
		end if; 
	elif length eq 0 then
		if extra_rels eq [] then  
			I:=ideal<R|Eltseq(v*v-v)>;
		elif extra_rels ne [] then  
			I:=ideal<R|Eltseq(v*v-v) cat extra_rels>;
		end if;
	end if;
		varsize:=VarietySizeOverAlgebraicClosure(I);
		if Dimension(I) le 0 then
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
		/*count:=n;prod:=v;
       		while count gt 0 do
	 		prod:=prod*a;count:=count-1;
		end while;
	      return prod;*/ /*basically that is what Pow is for.*/
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
 /*ad:=Matrix(BaseField(Parent(u)), [Eltseq(u*bas[i]): i in [1..Dimension(Parent(u))]]);*/
 ad:=AdMat(u);/* This little utility does the above.*/ 
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
				extra:=Determinant(AdMatInSubAlg(AFF,W32,uu)-(31/32)*IdentityMatrix(BaseField(A),Dimension(W32)));
				idemps:=FindAllIdempotents(A,W:length:=l,one:=one,form:=form,extra_rels:=[extra]);
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
	/*(A,l1,l2)-->bool,vector space or matrix.*/
{
	Given two indexed sets of axial algebra elements, the first with preimages and the second containing the corresponding images, 
	extend the map as far as possible. If the map extends to the whole algebra, return true and a matrix that gives a multiplicative map A->A
	where A is the axial algebra in question. If not, return false and the maximum subalgebra (as a vector space) to which the map extends.	

}
	require #input eq #images: "The lengths of the input and output lists must be  equal.";
	require Type(input[1]) eq ParAxlAlgElt and Type(images[1]) eq ParAxlAlgElt: "The elements of the given lists are not algebra elements.";
	 A:=Parent(input[1]);
	require IsIndependent({A`W!Eltseq(x):x in input}): "The input list must be independent.";
	dim:=Dimension(A);
	closed:=0;
	F:=BaseField(A);
	lst:=[A`W!Eltseq(input[i]):i in [1..#input]];
	ims:=images;
	sub:=sub<A`W|lst>;
	m:=1;
	if #lst eq dim then
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
		if #lst eq dim then
			closed:=1;
		else
			subclosed:=1;
			for i:=current_inds[1] to #lst do
				for j:=current_inds[2]+1 to #lst do
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
				for j:=current_inds[2]+1 to #lst do
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
		/*this will be multiplicative by construction, we need only check that it is invertible;*/
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
intrinsic FindAxesNaiveWithLengthRestriction(A::ParAxlAlg: id:=A!0)-> SetIndx
{
	We use the brute force approach withy the restriction that found idempotents must be of length 1. If the resultant ideal is not zero dimensional it will return fail.
}
	if id eq A!0 then
       		_,id:=HasIdentityAlg(A);
	else/* user supplied identity.*/
		require Parent(id) eq A: "The elemnt is not in A";
		require forall{i:i in [1..Dimension(A)]|id*A.i eq A.i}: "The given element is not the identity of A.";
	end if;	
	idemps:=FindAllIdempotents(A,A`W:length:=1,one:=id);
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
 	maxes:=[];
	j:=1;
	Group_Name:="";
	gp_name:=GroupName(MiyamotoGroup(A));
	while Group_Name ne gp_name do 
	for i:=1 to #shape_ns do
		N:=shape_ns[i];
		/*This loop will attempt to get two axes x_1,x_2 such that t_a*t_{x_i} has order N. If the orbit a does not have such x_i on first try immediately go to the next orbit*/ 
		while j lt #axes do
			init_num:=#maxes;
	 		for k:=1 to #axes[j] do 
		 		if Minimum({l:l in [1..6]|(TauMapMonster(a1)*TauMapMonster(axes[j][k]))^l eq IdentityMatrix(BaseField(A),Dimension(A))}) eq N then
		 			Append(~maxes,axes[j][k]);
				end if;
		 		incr:=#maxes- init_num;
		 		if incr eq 0 then
		 			j+:=1;
		 		end if;
				if #maxes ge 2 then 
		/*at this stage we check if the Miyamoto group us 2-generated, which is true for S_n, so for those groups we would be done.*/ 
					Group_Name:=GroupName(MatrixGroup<dim,F|[TauMapMonster(a1)*TauMapMonster(x):x in maxes]>);
					printf "The group name is %o\n", Group_Name; /*possibly silence this later after testing. */ 
	/* If not two-generated, we will need to continue until we get a minimum generating set.*/
					if Group_Name eq gp_name then
						break i;
					end if; 
		 			//break k;
				end if;
	 		end for;
		end while;
	end for;
	end while;
	print "A minimum set of generators found";
	lst:=[TauMapMonster(a1)*TauMapMonster(maxes[i]):i in [1..#maxes]];
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
	print "System of equations set up";
	_,sol:=Solution(Transpose(Mat),Vector(BaseField(A),[0*i:i in [1..#lst*dim]]));
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
	Given an axial algebra A and a matrix mat, over the base fielf of A, check if mat is induced from an axis. The matrix mat must be invertible. We do not check if it is automorphic. If true, the function will also produce an indexed set of axes in A which induce mat.
}
	/*we assume that the matrix is an automorphism, this will not be checked.*/
	F:=BaseField(A);
	n:=Dimension(A);
	require Nrows(mat) eq Ncols(mat) and Nrows(mat) eq n: "The matrix must be square";
	require Type(form) eq AlgMatElt: "The form must be a matrix";
	require Nrows(form) eq Ncols(form): "The form must be a square matrix";
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
