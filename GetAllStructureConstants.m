/*GetStructureConstants gets structure constants a_{ij}^k for i leq j and so for an n-dimensional algebra, we get 
1/2*(n(n+1)) of them (as lists or vectors, but the actual number of structure constants is 1/2*(n^2(n+1)), since axial algebras are commutative.
However, to create a general algebra, in the category GenAlg, we need all n^3 structure constants. We produce an array of length n^3 where 
a_{ij}^k is in position (i-1)*n^2+(j-1)*n+k. This is because if e_1,e_2,\ldots , e_n is a basis for the algebra in question, then 
for a fixed i and j, the array/vector (a_{ij}^k), 1\leq k\leq n comes after (i-1)*n+(j-1) such arrays, so in particular, these are 
n*[(i-1)*n+(j-1)]=(i-1)*n^2+(j-1)*n structure constants. Thus, the structure contants in the array (a_{ij}^k) occupy positions 
(i-1)*n^2+(j-1)*n+k, 1\leq k\leq n. */
intrinsic AllStructureConstants(L::SeqEnum[ModTupFldElt])->SeqEnum[FldElt]
{
	Given a sequence L of vectors (a_\{ij\}^k), i,k ranging between 1 and n, and j greater or equal to i, form the sequence of 
       length n^3 with entries a_\{ij\}^k. L above may be obtained using GetStructureConsatants. We exploit the fact that axial 
	algebras are commutative, by definition.
 }
	 length:=#L;
	 sols:=Roots(Polynomial(IntegerRing(),[-2*length,1,1]));
	 /*From the preamble if an algebra A has dimension n, then L will have length 1/2*(n(n+1)) so 2*length=n(n+1)
	or equivalently, 0=n^2+n-2*length, so n must satisfy the equation 0=x^2+x-2*length.*/
	pos_sol:=[x[1]:x in sols|Sign(x[1]) eq 1];/*positive root of the equation.*/
	require #pos_sol ne 0: "The length of L must be a positive integer";
	n:=pos_sol[1];
	require Degree(L[1]) eq n: "The degree of vectors must be n";
 	all_vecs:=[];
	for i:=1 to n do 
		for j:=1 to n do
			if i le j then
				Append(~all_vecs,L[IntegerRing()!((i-1)/2*(2*n+2-i))+j-i+1]);
			else
				Append(~all_vecs,L[IntegerRing()!((j-1)/2*(2*n+2-j))+i-j+1]);
			end if;
		end for;
	end for;
	return &cat[Eltseq(all_vecs[i]):i in [1..n^2]];
end intrinsic;

intrinsic AdMat(a::AlgGenElt)->AlgMatElt
{
	Given a general algebra element a, find the matrix of the adjoint endomorphism x:->ax, relative to the 
	standard basis. 
}
	A:=Parent(a);
	return Matrix([Coordinates(A,a*A.i):i in [1..Dimension(A)]]);
end intrinsic;

/*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Frind the Frobenius form at (u,v)                                                                          +
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/

intrinsic FrobFormAtElements(u::AlgGenElt, v::AlgGenElt, U::AlgMatElt)->FldElt 
{
 
Given an algebra A with a form U, compute the number (u,v) for given elements u,v in A.
}
	require Nrows(U) eq Ncols(U): "Form must be a square matrix";
	A:=Parent(u);
	F:=BaseField(A);
	/*Because we work over function fields sometimes, we may need to change the base ring of U.*/ 
	UQ:=ChangeRing(U,F);
	//return (Matrix(F,[Eltseq(u)])*UQ*Transpose(Matrix(F,[Eltseq(v)])))[1][1];
	return InnerProduct(u*UQ,v);
end intrinsic;

intrinsic LengthOfElement(u:: AlgGenElt,form::AlgMatElt)->FldElt
{
Given an element u of an axial algebra A which admits a Frobenius form "form", find the length of u wrt to the form, i.e., (u,u).
}

return FrobFormAtElements(u,u,form);
end intrinsic;

/*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ This function takes an axial algebra A, a subspace V (not necessarily a subalgebra) and attempts to find all the +
+ idempotents in V. This takes optional parameters (length, form,one) so that we can determine idempotents of a    +
+ prescribed length. In such a case it will be advantageous to input a form and identity if A has.                 +
+                                                                                                                  +
+ ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/
intrinsic FindAllIdempotents(A::AlgGen, U::ModTupFld: length:=false, form :=false, one:=false, extra_rels:=[]) -> SetIndx
  {
  Given an algebra A and a subspace (not necessarily a subalgebra) U, find all the idempotents of A contained in U.
  
  Optional arguments:
    length - requires the length of the idempotents to be as given
    form - the Frobenius form
    one- the identity of A. 
    extra_rels - require the idempotent to satisfy extra relation(s).  These are given by multivariate polynomials in dim(U) variables corresponding to the basis of U.
  }
 	if Type(form) ne BoolElt then	
		require Type(form) eq AlgMatElt: "form must be a matrix";
		require Nrows(form) eq Ncols(form): "Form must be a square matrix";
	end if;
	if Type(one) ne BoolElt then
		require Type(one) eq AlgGenElt: " one must be an axial algebra element";
		require forall{i:i in [1..Dimension(A)]|one*(A.i) eq A.i}: "one must be algebra identity";
	end if;	
	n:=Dimension(A);
	m:=Dimension(U);
	F:=BaseField(A);
	if Type(length) ne BoolElt then
		require IsCoercible(F,length): "The length must be a field element";
	end if;
	R:=PolynomialRing(F,m);/*Set up F[x_1,x_2,...,x_m].*/
	FF:=FieldOfFractions(R);
	AF:=ChangeRing(A,FF);
	bas:=Basis(U);
	v:=&+[R.i*AF!bas[i]:i in [1..m]];/*Set up $\sum_{i=1}^m x_iv_i. where v_1,v_2,...,v_m is a basis. */
	if not Type(length) eq BoolElt then
		if Type(form) eq BoolElt then
			bool,M:=HasFrobeniusForm(A);
			if bool eq false then
				return "fail, the concept of length is not defined";
			end if;
		elif Type(form) ne BoolElt then
			M:=form;
		end if;/*at this stage we either have a form or the function has already returned a fail*/
		if Type(one) eq BoolElt then
			bool,one:=HasOne(A);
			if bool eq false then
				 len_rest:=FrobFormAtElements(v,v,M)-length;
			elif bool eq true then
				one:=AF!Eltseq(one);
				len_rest:=FrobFormAtElements(one,v,M)-length;/* here we use (v,v)=(v,v*1)=(v*v,1)=(v,1)*/ 
			end if;
		elif Type(one) ne BoolElt then
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
	elif Type(length) eq BoolElt then
		if extra_rels eq [] then  
			I:=ideal<R|Eltseq(v*v-v)>;
		elif extra_rels ne [] then 
			I:=ideal<R|Eltseq(v*v-v) cat extra_rels>;
		end if;
	end if;
		t:=Cputime();
		dim_I:=Dimension(I); 
		if dim_I lt 0 then
			return {@ @};
		elif dim_I eq 0 then 
			varsize:=VarietySizeOverAlgebraicClosure(I);
			var:=Variety(I);
			if #var eq varsize then
				idemps:=[];
				for x in var do
					ide:=&+[x[i]*A!U.i:i in [1..m]];
					Append(~idemps,ide);
				end for;
				return IndexedSet(idemps);
			elif #var lt varsize then
				FClos:=AlgebraicClosure(Rationals());
				varF:=Variety(ChangeRing(I,FClos));
				AClos:=ChangeRing(A,FClos);
				idemps:=[];
				for x in varF do
					ide:=&+[x[i]*AClos!U.i:i in [1..m]];
					Append(~idemps,ide);
				end for;
				return IndexedSet(idemps), FClos;
			end if;
		elif dim_I eq 1 then
			print "ideal not zero-dimensional";
			return "fail";
		end if;
end intrinsic;
/*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ This function takes an axial algebra A, a subspace V (not necessarily a subalgebra) and attempts to find all the +
+ idempotents in V. This takes optional parameters (length, form,one) so that we can determine idempotents of a    +
+ prescribed length. In such a case it will be advantageous to input a form and identity if A has.                 +
+                                                                                                                  +
+ ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/
intrinsic GetIdempotentIdeal(A::AlgGen, U::ModTupFld: length:=false, form :=false, one:=false, extra_rels:=[]) -> SetIndx
  {
  Given an algebra A and a subspace (not necessarily a subalgebra) U, find all the idempotents of A contained in U.
  
  Optional arguments:
    length - requires the length of the idempotents to be as given
    form - the Frobenius form
    one- the identity of A. 
    extra_rels - require the idempotent to satisfy extra relation(s).  These are given by multivariate polynomials in dim(U) variables corresponding to the basis of U.
    }
        n:=Dimension(A);
	m:=Dimension(U);
	F:=BaseField(A);
        R:=PolynomialRing(F,m);/*Set up F[x_1,x_2,...,x_m].*/
	FF:=FieldOfFractions(R);
	AF:=ChangeRing(A,FF);
	bas:=Basis(U);
	v:=&+[R.i*AF!bas[i]:i in [1..m]];/*Set up $\sum_{i=1}^m x_iv_i. where v_1,v_2,...,v_m is a basis. */
        if Type(length) eq BoolElt then
	    I:=ideal<R|Eltseq(v*v-v)>; 
            return I;
         end if;
/* At this stage length is given.*/
       if Type(length) ne BoolElt then
		require IsCoercible(F,length): "The length must be a field element";
	   if Type(form) ne BoolElt then	
		require Type(form) eq AlgMatElt: "form must be a matrix";
		require Nrows(form) eq Ncols(form): "Form must be a square matrix";
           end if;
/* For now we do not have a way of getting the Frobenius form for algebras in AlgGen form.*/
           if Type(form) eq BoolElt then 
                        bool,form:=HasFrobeniusForm(A);
			if bool eq false then
				return "fail, the concept of length is not defined";
			end if;
	    end if;
	    if Type(one) ne BoolElt then
		require Type(one) eq AlgGenElt: " one must be an axial algebra element";
		require forall{i:i in [1..Dimension(A)]|one*(A.i) eq A.i}: "one must be algebra identity";
I:=ideal<R|Eltseq(v*v-v) cat [FrobFormAtElements(v,AF!Eltseq(one),form)-length]>;
		return I;
	    end if;	
/*Here one is not given. Try and find it.*/
            if Type(one) eq BoolElt then
                bool,one:=HasOne(A);
                if bool eq false then
		I:=ideal<R|Eltseq(v*v-v) cat [FrobFormAtElements(v,v,form)-length]>;
		else
		I:=ideal<R|Eltseq(v*v-v) cat [FrobFormAtElements(v,AF!Eltseq(one),form)-length]>;
                end if;
                return I;
             end if;
     end if;

end intrinsic;

intrinsic TauMap( a::AlgGenElt, T::Tup)->AlgMatElt
{
	Given an axis a in an algebra A,  and a tuple T with two lists of eigenvalues of ad_a restricted to U, 
	one being positive and the second being negative in a C_2-grading, produce the tau map t_a as a dim(A)xdim(A) matrix.
}
        A:=Parent(a);
	m:=Dimension(A);
        require a*a eq a: "a must be an idempotent.";
	ad_a:=AdMat(a);
	Eigs:=Eigenvalues(ad_a);
	vals:=[x[1]:x in Eigs];
	multiplicities:=[x[2]:x in Eigs];
	require forall{x:x in T[1] cat T[2]|x in vals}: "Every element in the tuple components must be an eigenvalue of a";
	require &+[x:x in multiplicities] eq m: "a must be semi-simple.";
	I_m:=IdentityMatrix(BaseField(A),m);
	eigs:=T[1] cat T[2];
	P:=(&+[&*[(ad_a-x*I_m)/(T[1][j]-x):x in eigs| x ne T[1][j]]:j in [1..#T[1]]])-(&+[&*[(ad_a-x*I_m)/(T[2][j]-x):x in eigs|x ne T[2][j]]:j in [1..#T[2]]]);
	/* This matrix (v_+)-(v_-), where v_- is the positive part of v, v_- is the negative part of v.*/
	return P;
	//return Matrix([Eltseq((ToSmallVec(A,U,A!U.i))*P):i in [1..m]]);
end intrinsic;

/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ This function takes an axial algebra A, and two lists, input, and images, of axial vectors which must be of the same length and ouputs    +
+ a boolean value as well as either a map in matrix form or a subalgebra if the map does not extend to the full space.                      +
+                                                                                                                                           +
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/

intrinsic ExtendMapToAlgebra(input::SeqEnum[AlgGenElt],images::SeqEnum[AlgGenElt])->BoolElt,AlgMatElt
{
	Given two indexed sets of axial algebra elements, the first with preimages and the second containing the corresponding images, 
	extend the map as far as possible. If the map extends to the whole algebra, return true and a matrix that gives a multiplicative map A->A
	where A is the axial algebra in question. If not, return false and the maximum subalgebra (as a vector space) to which the map extends.	
}
	require #input eq #images: "The lengths of the input and output lists must be  equal.";
	//require Type(input[1]) eq ParAxlAlgElt and Type(images[1]) eq ParAxlAlgElt: "The elements of the given lists are not algebra elements.";
	 A:=Parent(input[1]);
        W:=VectorSpace(A);
	require IsIndependent({W!Eltseq(x):x in input}): "The input list must be independent.";
	require IsIndependent({W!Eltseq(x):x in images}): "The images list must be independent.";
	dim:=Dimension(A);
	closed:=0;
	F:=BaseField(A);
	sub_alg_mode:="off";
	lst:=[W!Eltseq(input[i]):i in [1..#input]];
	if input eq images then
		sub_alg_mode:="on";
	end if;
	ims:=images;
	sub:=sub<W|lst>;
	m_s:=[1^i:i in [1..#lst]];
	structs:=[Sprintf("x%o",i):i in [1..#lst]];
	current:=[1,#lst];
	new:=[1,#lst];
	while closed eq 0 do
		for i:=current[1] to current[2] do
			for j:=new[1] to new[2] do
				if not i gt j then/*idea here is that multiplication is commutative for axial algebras so v_i*v_j=v_j*v_i.*/
				w:=W!Eltseq((A!lst[i])*(A!lst[j]));
					if not w in sub then
						Append(~lst,w);
						sub+:=sub<W|w>;
						Append(~m_s,m_s[i]+m_s[j]);
						Append(~structs,Sprintf("(%o)(%o)",structs[i],structs[j]));
						if not sub_alg_mode eq "on" then
							Append(~ims,ims[i]*ims[j]);
						end if;
					end if;
				end if;
			end for;
		end for;
                if #lst eq current[2] or #lst eq dim then
			closed+:=1;
			printf("multiplication is now closed with minimum %o-closure \n"),Maximum(m_s);
		else
			/*update new and current.*/
			new:=[current[2]+1,#lst];
			current:=[1,#lst];
			printf("current dimension is %o\n"),#lst;
                        bas:=Basis(sub);
                        if sub_alg_mode eq "on" then
                           ims:=[A!bas[i]:i in [1..#lst]];
                        end if;
                        change_of_basis:=Matrix([Coordinates(sub,lst[i]):i in [1..#lst]]);
                        V_ugly:=VectorSpaceWithBasis(lst);
                        current_map:=change_of_basis^(-1)*Matrix([Coordinates(V_ugly,Vector(ims[i])):i in [1..#lst]])*change_of_basis;
                	lst:=bas;
                	V:=sub<W|bas>;
                	Bas_V:=Matrix([Eltseq(bas[i]):i in [1..#lst]]);
                	ims:=[(Solution(Bas_V,Vector(ims[i]))*current_map):i in [1..#ims]];
                	ims:=[A!(&+[ims[i][j]*bas[j]:j in [1..#bas]]):i in [1..#ims]];
		end if;
	end while;
	//return sub,structs,m_s;
	if #lst lt dim then
		return false,sub;
	end if;;

	if sub_alg_mode eq "on" then
		return true, MatrixAlgebra(F,dim)!1;
	end if;
	bas_mat:=Matrix(F,[Eltseq(lst[i]):i in [1..#lst]]);
	phi:=Matrix(F,[Eltseq(Solution(bas_mat,W!Eltseq(ims[i]))):i in [1..#ims]]);
	std_phi:=bas_mat^(-1)*phi*bas_mat;
	if std_phi eq IdentityMatrix(F,#lst) then
		return true, std_phi;
	else
		return true,std_phi;
	end if;
end intrinsic;

intrinsic JointEigenspaceDecomposition(L::SetIndx[AlgGenElt]) -> Assoc
  {
  Given an indexed set of axes L = \{ a_1, ..., a_n\}, decompose the algebra into joint eigenspaces for these axes.  Returns an associative array where the element A_lm_1(a_1) \cap ... \cap A_lm_n(a_n) has keys give by the set of eigenvalues \{ lm_1, ..., lm_n \}.
  }
  
//require forall{x:x in L|Type(x) eq ParAxlAlgElt} : "The elements are not axial algebra elements.";
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

intrinsic ProjectVectorToJointSpace(u::AlgGenElt,Y::SetIndx[AlgGenElt],Q::SeqEnum)->AlgGenElt
{
	Given an algebra element u, an indexed set Y= \{@a_1,a_2,...,a_k@\} of axes (or idempotents), as well as a sequence [lm_1,lm_2,...,lm_k], of
	       	eigenvalues whose length equals the cardinality of axes, find the projection of u to the joint space A_\{lm_1,lm_2,...,lm_k\}(Y). Note that we do not check that Y consists of axes.
																				  }
	require #Y gt 0: "The set Y must be non-empty";
	require #Y eq #Q: "The cardinalities of the sets of axes and eigenvalues must be equal.";
	A:=Parent(u);
	require IsCoercible(A,Eltseq(Y[1])): "The axes must be coercible to the parent algebra of u"; 
	require forall{x:x in Q| x in BaseField(A)}:" The eigenvalues must be in the base field of the parent algebra.";
	ads:=[AdMat(Y[i]):i in [1..#Y]];/*The adjoints.*/
	eigs:=[x[1]:x in Eigenvalues(ads[1])];
	id:=IdentityMatrix(BaseField(A), Dimension(A)); 
	projs:=[&*[(ads[i]-x*id)/(Q[i]-x): x in eigs|x ne Q[i]]:i in [1..#Y]];
	return u*(&*[x: x in projs]);
end intrinsic;
/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Function to check if an idempotent satisfies the Monster M(alpha,beta) fusion law. 						          +
+           	                                                                                                                          +
+ We implement ideas from Hall, Rehren and Shpectorov's 'Universal axial algebras and a theorem of Sakuma.                                +
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/


/*check if the eigenvalues are in eigens, if so, check if dimensions add up.*/
intrinsic HasMonsterFusion(u::AlgGenElt:arbitrary_parameters:=false)-> BoolElt
{
	Check if the algebra element u satisfies the Monster M(alpha,beta) fusion law.
	The switch for arbitrary alpha and beta is off by default, when we assume (alpha,beta)
	is (1/4,1/32). Parameters:
	-arbitrary_parameters a tuple <alpha,beta>, set to false by default. 
}
	require u*u eq u: "u must be an idempotent"; 
	A:=Parent(u);
	bas:=Basis(A);
	n:=#bas;
	F:=BaseField(A);
	zero:=A!0;
	if Type(arbitrary_parameters) eq BoolElt then
		alpha:=1/4;
		beta:=1/32;
	else
		require Type(arbitrary_parameters) eq Tup: "The parameter must be in tuple form.";
		require arbitrary_parameters[1] in F and arbitrary_parameters[2] in F: 
		"The values alpha and beta must lie in the base field of underlying algebra.";
		alpha:=arbitrary_parameters[1];
		beta:=arbitrary_parameters[2];
		require <alpha,beta> notin {<0,1>,<1,0>} and alpha ne beta: "alpha and beta must be distinct and different from 1 and 0.";
	end if;
	eigens:=[1,0,alpha,beta];
	I_n:=IdentityMatrix(F,n);
	ad:=AdMat(u);
	eigs:=IndexedSet(Eigenvalues(ad));
	if exists(ev){eigs[i][1]:i in [1..#eigs]|not (eigs[i][1]  in eigens)} then
		printf("Eigenvalue %o not in [1,0,alpha,beta]\n"),ev;
		return false; 
	elif &+[eigs[i][2]:i in [1..#eigs]] ne #bas then /*semisimplicity check.*/
		print("Dimensions do not add up\n");
		return false;
 	end if;
 	/*At this point all failures with regards to the correct eigenvalues and simplicity 
 	have been tested.*/ 
 	E0:=[A!Eltseq(u):u in Basis(Eigenspace(ad,0))];
 	E1:=[A!Eltseq(u):u in Basis(Eigenspace(ad,1))];
 	E4:=[A!Eltseq(u):u in Basis(Eigenspace(ad,alpha))];
 	E32:=[A!Eltseq(u):u in Basis(Eigenspace(ad,beta))];
	/*We set up the matrices f_{mu,\lamba} and apply Lemma 5.4 of the universal axial algebra paper.*/
	P1:=ad-I_n;/*we evaluate t-mu_i for mu_i different from 1.*/
	P2:=ad-alpha*I_n;
	P3:=ad-beta*I_n;
 	/*1* everything else, not necessary, obvious by definition of eigenvalues .*/
 	/*for a space E_i, we cut the number of multiplication in E_i using commutativity of axial alegebras.*/ 
	/*we now check multiplication by 0 here.*/
	bools:=[];
	bool2:=[forall{x:x in {y:y in CartesianPower([1..#E0],2)|y[1] le y[2]}|(E0[x[1]]*E0[x[2]])*ad eq zero },
	forall{<i,j>:i in [1..#E4],j in [1..#E0]|(E4[i]*E0[j])*P2 eq zero},   
	forall{<i,j> :i in [1..#E32],j in [1..#E0]|(E32[i]*E0[j])*P3 eq zero}];
	Append(~bools,forall{bool:bool in bool2|bool eq true});

	/*we check multiplication by alpha now.*/
	bool3:=[
	forall{x:x in {y:y in CartesianPower([1..#E4],2)|y[1] le y[2]}|(E4[x[1]]*E4[x[2]])*(P1*ad)  eq zero },
	forall{<i,j>:i in [1..#E32],j in [1..#E4]|(E32[i]*E4[j])*P3 eq zero }];
	Append(~bools,forall{bool:bool in bool3|bool eq true});
	/*multiplication is commutative so if <x,y> in EixEi, we need not check <y,x>*/
	/*finally multipliction by beta.*/
	bool4:=[
	forall{x:x in {y:y in CartesianPower([1..#E32],2)|y[1] le y[2]}|(E32[x[1]]*E32[x[2]])*(P1*P2*ad) eq zero}];
	Append(~bools,forall{bool:bool in bool4|bool eq true});
	if false in bools then
		return false;
	else 
		return true;
	end if;
end intrinsic;

/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Function to check if an idempotent satisfies the Monster M(alpha,beta) fusion law. 						          +
+           	                                                                                                                          +
+ We implement ideas from Hall, Rehren and Shpectorov's 'Universal axial algebras and a theorem of Sakuma.                                +
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/


/*check if the eigenvalues are in eigens, if so, check if dimensions add up.*/
intrinsic SatisfiesMonsterFusionLaw(u::AlgGenElt:arbitrary_parameters:=false)-> BoolElt
{
	Check if the algebra element u satisfies the Monster M(alpha,beta) fusion law.
	The switch for arbitrary alpha and beta is off by default, when we assume (alpha,beta)
	is (1/4,1/32). Parameters:
	-arbitrary_parameters a tuple <alpha,beta>, set to false by default. 
}
	require u*u eq u: "u must be an idempotent"; 
	A:=Parent(u);
        n:=Dimension(A);
	F:=BaseField(A);
	ad_u:=AdMat(u);
	if Type(arbitrary_parameters) eq BoolElt then
		alpha:=1/4;
		beta:=1/32;
	else
		require Type(arbitrary_parameters) eq Tup: "The parameter must be in tuple form.";
		require arbitrary_parameters[1] in F and arbitrary_parameters[2] in F: 
		"The values alpha and beta must lie in the base field of underlying algebra.";
		alpha:=arbitrary_parameters[1];
		beta:=arbitrary_parameters[2];
		require <alpha,beta> notin {<0,1>,<1,0>} and alpha ne beta: "alpha and beta must be distinct and different from 1 and 0.";
	end if;
	eigens:=[1,0,alpha,beta];
	eigs:=IndexedSet(Eigenvalues(ad_u));
	evalues:=[eigs[i][1]:i in [1..#eigs]];
	if exists(ev){x:x in evalues|x notin eigens} then
		printf("Eigenvalue %o not in [1,0,alpha,beta]\n"),ev;
		return false; 
	elif &+[eigs[i][2]:i in [1..#eigs]] ne n then /*semisimplicity check.*/
		print("Dimensions do not add up\n");
		return false;
 	end if;
 	/*At this point all failures with regards to the correct eigenvalues and simplicity 
 	have been tested.*/ 
	R:=PolynomialRing(F,n);
        FR:=FieldOfFractions(R);
        AFR:=ChangeRing(A,FR);
        x:=&*[R.i*AFR.i:i in [1..n]]; /* set up a general algebra element.*/
        parts:=AssociativeArray();
        for evalue in evalues do
        	proj:=ProjectVectorToJointSpace(x,{@u@},[evalue]);
        	parts[evalue]:=proj;
        end for;
	zero:=AFR!0;/*push this down so that we have 0_FR.*/
        I_n:=IdentityMatrix(FR,n);
	ad_u:=ChangeRing(ad_u,FR);
	fusion_law:=[<<1,1>,{1}>,<<1,0>,{}>,<<1,alpha>,{alpha}>,<<1,beta>,{beta}>,
		<<0,0>,{0}>,<<0,alpha>,{alpha}>,<<0,beta>,{beta}>,
		<<alpha,alpha>,{1,0}>,<<alpha, beta>,{beta}>,<<beta,beta>,{1,0,alpha}>];
	booleans:=[];
	/* we do not need to check 1*lm_i for all lm_i.*/ 
	for law in fusion_law[[5..#fusion_law]] do
		if forall{i:i in [1,2]|law[1][i] in Keys(parts)} then/*loop necessary should one value be missing, eg in J(1/4) case.*/
			bool:=(&*[parts[law[1][i]]:i in [1,2]])*(&*[ad_u-y*I_n:y in law[2]]) eq zero;
			printf(" law %o done\n"),law;
			Append(~booleans,bool);
		end if;
	end for;
	if exists{bool:bool in booleans|bool eq false} then
		return false;
 	else
  		 return true;
	end if;
end intrinsic;
intrinsic FindStructureConstantsSubAlgebra(A:: AlgGen, U::ModTupFld)->SeqEnum[ModTupFld]
{	
	Given An axial algebra A and a subalgebra U, find the structure constants c_\{i,j\}^k, where 
	u_i*u_j=Sum_\{i=1\}^m c_\{i,j\}^ku_k, with u_1, u_2,...,u_m a basis for U. Here m:=dim(U). 
	The function resturns a sequence of m-long vectors with structure constants corresposing to 
	product u_i*u_j for j ge i.
}
        W:=VectorSpace(A);
        require U subset W : "U must be a subspace of A.";
	m:=Dimension(U);
	require forall{i:i in [1..m]|forall{j:j in [i..m]|W!Eltseq((A!U.i)*(A!U.j)) in U}}: "U must be a subalgebra";
	bas:=Basis(U);/*in the case of a subalgebra of a subalgebra generated by some vectors use of U.i is problematic.*/
	tens:=[];
	for i:=1 to m do
       		for j:=i to m do
			Append(~tens,ToSmallVec(A,U, (A!bas[i])*(A!bas[j])));
		end for;
	end for;
	return tens;	
end intrinsic;
/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+This function takes an alebra/vector space A and a subspace V and a vector v in A to produce a dimV-long +
+ relative to a basis of V. The opposite of ToBigVec.                                                     +
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/
intrinsic ToSmallVec(A::AlgGen, V::ModTupFld, v::AlgGenElt)-> ModTupFldElt 
{ 
	Given an algebra A, a subspace V and a vector v of a which is coercible to V, find a dim(V)-long vector which is an expression of v in terms of some b		asis of V. 
}

	F:=BaseField(A);
	n:=Dimension(A);
	m:=Dimension(V);
	AA:=VectorSpace(A);
	require V subset AA: "V must be a subspace of A";
	bas:=Basis(V);
	mat:=Matrix(F,[Eltseq(bas[i]):i in [1..m]]);
	v,_:= Solution(mat,AA!Eltseq(v));
	return v;
end intrinsic;
/*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ We present a routine for finding all the idempotents in a subalgebra of an algebra.                                +
+														     +
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/

intrinsic FindAllIdempotentsInSubAlgebra(A::AlgGen,U::ModTupFld:length:=false,form:=false)-> SetIndx
{	
	Given an algebra A, a subalgebra U, as a subspace, find all the idempotents in U. We go and work in the 
	subalgebra. Parameters:
	1. length -the length of idempotents,
	2. form -the Frobenius form if it exists, this is restricted to U; and 
}
	require U subset VectorSpace(A): "U must be a subspace of A.";
	dim_U:=Dimension(U);
	bas_U:=Basis(U);
        U:=VectorSpaceWithBasis(bas_U);/*force the use of the nicer basis.*/
	L:=FindStructureConstantsSubAlgebra(A,U);/*checks if U is a subalgebra.*/
	LL:=AllStructureConstants(L);
	B:=Algebra<BaseField(A),dim_U|LL>;
	f:=hom<B->A|[<B.i,A!U.i>:i in [1..dim_U]]>;/*embedding B into A.*/
	/*we've proved that all algebras are unital.*/
	_,one:=HasOne(B);
	if Type(form) eq BoolElt then
		bool,form:=HasFrobeniusForm(A);
		if bool eq false then 
			idemps:=FindAllIdempotents(B,VectorSpace(B):one:=one);
		end if;
	end if;
	form_U:=RestrictedForm(form,U);
        //form_U:=form;
	if Type(length) eq BoolElt then
		idemps:=FindAllIdempotents(B,VectorSpace(B));
	else
		idemps:=FindAllIdempotents(B,VectorSpace(B):length:=length,form:=form_U,one:=one);
	end if;
	if Type(idemps) eq MonStgElt then
		return "fail";
	end if;
	if #idemps eq 0 then
		return {@ @};
	end if;
	if exists(x){y:y in idemps|IsCoercible(A,y) eq false} then
		BB:=Parent(x);
		FF:=BaseField(BB);
		AA:=ChangeRing(A,FF);
		ff:=hom<BB->AA|[<BB.i,AA!U.i>:i in [1..dim_U]]>;
		return ff(idemps);
	else
		return f(idemps);
	end if;
end intrinsic;

/*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ A function to find the subalgebra generated by a sequence of axial vectors.                                    +
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/
intrinsic SubAlgebra(L::SetIndx[AlgGenElt] )->ModTupFld 
{
	Given an indexed set L of axial vectors, return the subalgebra of the parent algebra that is generated by L. 
} 
	require #L gt 0: "L must be nonempty";
	A:=Parent(L[1]); 
	n:=Dimension(A);
	W:=VectorSpace(A);
	lst:=[Vector(L[i]):i in [1..#L]];/*set up the vectors in L as ordinary vectors*/
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

/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Given an idempotent a in an axial algebra, we wish to find out if a satisfies a fusion law.       +
+                                                                                                   +
+ FindFusion AxlAlgxVectSpace-->2^X, where X:=Spec(a).                                              +
+                                                                                                   +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/
intrinsic FindFusionLaw(a::AlgGenElt)->SeqEnum /*V is a subspace which could be A.*/
{
	Given an algebra A, and an algebra element a, determine if a satisfies a fusion law in A.
}
        A:=Parent(a);
	require a ne  A!0: "a must be nonzero";	
	require a*a eq a: "The given element is not an idempotent";
        m:=Dimension(A);
	F:=BaseField(A);
	W:=VectorSpace(F,m);
        eigs:=Eigenvalues(AdMat(a));
	fus:=[* *];
	eigs:=SetToSequence(eigs);
	evals:=[eigs[i][1]:i in [1..#eigs]];
	mults:=[eigs[i][2]:i in [1..#eigs]];
        require &+[x:x in mults] eq m: "The given element is not  semisimple";
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
	//bas_mat:=Matrix(F,[Eltseq(V.i):i in [1..m]]);
	Id:=IdentityMatrix(F,m);
	ad_mat:=AdMat(a);
	Projs:=[];
	for i:=1 to #ord_eigs do
		Append(~Projs,&*[(ad_mat-ord_eigs[j]*Id)/(ord_eigs[i]-ord_eigs[j]):j in [1..#eigs]|j ne i]);
	end for;
	for i:=1 to m do
		w:=W.i;
		splits:=[w*Projs[t]:t in [1..#evals]];
		for j:=1 to #evals do
			for k:=j to #evals do
				prod:=(A!splits[j])*(A!splits[k]);
				prod_w:=W!Eltseq(prod);
				for s:=1 to #Projs do
					if prod*Projs[s] ne W!0 then
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
