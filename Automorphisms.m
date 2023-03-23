/*

Automorphisms of axial algebras


*/

/*

Functions to retrieve the algebra and properties from a ParAxlAlg

Eventually, this can be removed and replaced with a DecAlg

*/
intrinsic Algebra(A::ParAxlAlg) -> Alg
  {
  Returns the algebra of a ParAxlAlg.
  }
  
end intrinsic;

intrinsic Axes(A::ParAxlAlg) -> Alg
  {
  Returns the algebra of a ParAxlAlg.
  }
  
end intrinsic;

// Add some more here as needed

/*




*/
types := ["2A","2B","3A","3C","4A","4B","5A","6A"];
identities_lengths := [(2^2*3)/5,2,(2^2*29)/(5*7),(2^5/11),4, 19/5,(2^5)/7,(3*17)/(2*5)];



// FindAutNuanced
intrinsic FindNewAxes(A::Alg, axes::SetIndx, decomp::SetIndx, form::AlgMatElt) -> SetIndx
  {
  The inputs are an axial algebra A with a set axes of (orbit representatives) of the axes and corresponding eigenspace decompositions together with a Frobenius form.
  
  We perform the nuanced algorithm to find all axes.  
  }
  
end intrinsic;




// What about field extensions - do we need this??  I don't think so...
intrinsic FindAllIdempotents(A::Alg, U::ModTupFld: length:=false, form := false, extra_rels:=[]) -> SetIndx
  {
  Given an algebra A and a subspace (not necessarily a subalgebra) U, find all the idempotents of A contained in U.
  
  Optional arguments:
    length - requires the length of the idempotents to be as given
    form - the Frobenius form
    extra_rels - require the idempotent to satisfy extra relation(s).  These are given by multivariate polynomials in dim(U) variables corresponding to the basis of U.
  }
  
end intrinsic;


// FindTwin
intrinsic FindMultiples(a::AlgElt: eigenspace:=false, form := false) -> SetIndx
  {
  Given an axis, find the set of all other axes which have the same Miyamoto automorphism as a.
  }
  
end intrinsic;

intrinsic AnnihilatorOfSpace(A::Alg, U::ModTupFld) -> ModTupFld
  {
  Given an algebra A and a subspace U of A, return the subspace (not a subalgebra) of A which annihilates U.
  }
  
  
end intrinsic;


// DecomposeToJointEigenspaces 
intrinsic JointEigenspaceDecomposition(L::SetIndx) -> Assoc
  {
  Given an indexed set of axes L = \{ a_1, ..., a_n\}, decompose the algebra into joint eigenspaces for these axes.  Returns an associative array where the element A_lm_1(a_1) \cap ... \cap A_lm_n(a_n) has keys give by the set of eigenvalues \{ lm_1, ..., lm_n \}.
  }
  

	decomps:=AssociativeArray();
	A:=Parent(lst[1]); /* why this must be really axial*/ 
	eigs:=[1,0,1/4,1/32];
	n:=#lst;
	dims:=[];
	ads:=[AdMat(lst[i]):i in [1..n]];
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

/*

Functions to extend an automorphism of a subalgebra to an automorphism of the whole algebra.

*/
// ExtendMapToAut
// Do we need A?? Can't this just be the overalgebra of the domain of phi?
intrinsic ExtendMapToAlgebra(A::Alg, phi::Map) -> BoolElt, .
  {
  Given a map phi on a subspace of A, extend this multiplicatively as far as possible.  We return true and the map if it does extend to the whole of A.  If not, we return false and the largest subalgebra to which it extends.
  }
  
end intrinsic;

intrinsic ExtendMapToAlgebra(A::Alg, M::AlgMatElt) -> BoolElt, .
  {
  Given a matrix M on a subspace of A, extend this multiplicatively as far as possible.  We return true and the matrix if it does extend to the whole of A.  If not, we return false and the largest subalgebra to which it extends.
  }
  
end intrinsic;

// ExtendAutToMod
// Do we need the algebra here?? Can't this just be the overalgebra of the domain of phi?
intrinsic HasInducedMap(M::ModTupFld, phi::Map) -> BoolElt, .
  {
  Given a module M for an algebra A and an automorphism phi of A.  Try to construct the induced map psi: M --> M such that psi(ma) = psi(m)phi(a), for all a in A and m in M.
  }
  
end intrinsic;
