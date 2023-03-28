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
	//basmat:=Matrix(Rationals(),[Eltseq(A.i):i in [1..d]]);
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


