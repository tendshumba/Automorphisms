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
			//Append(~tens, Solution(basmat,V!Eltseq(A.i*A.j)));
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

