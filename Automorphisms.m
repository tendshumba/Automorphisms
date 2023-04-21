/*

Automorphisms of axial algebras


*/

/*

Functions to retrieve the algebra and properties from a ParAxlAlg

Eventually, this can be removed and replaced with a DecAlg

*/
intrinsic Algebra(A::ParAxlAlg) -> AlgGen
  {
  Returns the algebra of a ParAxlAlg.
  }
  require Dimension(A`W) eq Dimension(A`V): "The partial axial algebra has not completed.";
  
  return Algebra<BaseRing(A), Dimension(A) | A`mult>;
end intrinsic;

intrinsic AxesOrbitRepresentatives(A::ParAxlAlg) -> SetIndx
  {
  Returns a set of orbit representatives of axes of a ParAxlAlg coerced into an algebra.
  }
  // This will check it is a complete algebra.
  AA := Algebra(A);
  
  return {@ AA!A`axes[i]`id`elt : i in [1..#A`axes] @};
end intrinsic;


intrinsic Axes(A::ParAxlAlg) -> SetIndx
  {
  Returns the set of axes of a ParAxlAlg coerced into an algebra.
  }
  // This will check it is a complete algebra.
  AA := Algebra(A);
  
  G := Group(A);
  
  axes := {@@};
  
  for i in [1..#A`axes] do
    H := A`axes[i]`stab;
    trans := Transversal(G, H);
    
    orbit := {@ AA!(A`axes[i]`id*g)`elt : g in trans @};
  end for;

  return &join axes;
end intrinsic;

// Add some more here as needed

/*




*/
IdentityLength := AssociativeArray();
types := ["2A","2B","3A","3C","4A","4B","5A","6A"];
identities_lengths := [(2^2*3)/5,2,(2^2*29)/(5*7),(2^5/11),4, 19/5,(2^5)/7,(3*17)/(2*5)];

for i in [1..#types] do
  IdentityLength[types[i]] := identities_lengths[i];
end for;


// FindAutNuanced
intrinsic FindNewAxes(A::Alg, axes::SetIndx, decomp::SetIndx, form::AlgMatElt) -> SetIndx
  {
  The inputs are an axial algebra A with a set axes of (orbit representatives) of the axes and corresponding eigenspace decompositions together with a Frobenius form.
  
  We perform the nuanced algorithm to find all axes.  
  }
  require Parent(axes) eq A: "The axes are not in the algebra";
  F := BaseField(A);
  
  require Nrows(form) eq Ncols(form): "The form must be a square matrix.";
  require Nrows(form) eq Dimension(A): "The form is not the same dimension as the algebra";
  require #axes eq #decomp: "There are not the same number of decompositions as axis representatives.";
  // Can change this later
  // What about other characteristics
  require Type(decomp[1]) eq Assoc and forall{ d : d in decomp | Keys(d) subset {1,0,1/4,1/32}}: "The decompositions are not in the correct form.";
  
  found := [];
  for i in [1..#axes] do
    a := axes[i];
    dec := decomp[i];
    
    /*
    For one of our known axes a, we want to find a new axis b
    So B = < a,b > is a 2-generated axial algebra.  These all have identity.
    We search for z = 1-a is an idempotent in the 0-eigenspace for a.
    
    We use this to identify 1 and then the subalgebra.
    */
    // Change when decomposition algebra
    A0 := decomp[0];
    
    for k in Keys(IdentityLength) do
      // Get the length of z
      len := IdentityLength[k] - 1;
      
      // if the type is 4A, then there are infinitely many such idempotents
      // Hence we need to add some extra relations
      if k = "4A" then
        A32 := decomp[1/32];
        R := PolynomialRing(F, Dimension(A0));
				FF := FieldOfFractions(R);
				AFF := ChangeRing(A, FF);
				z := &+[R.i*AFF!A0.i : i in [1..Dimension(A0)]];
				// Since z is in A0 and the fusion law is Seress, z A32 subset A32
				// So we can restrict the action of the adjoint of z to A32
				bas := Basis(A32)
				A32_vectorspace := VectorSpaceWithBasis(bas);
				adz := Matrix([ Coordinates(A32_vectorspace, Vector((AFF!b)*z)) : b in bas]);
				
				extra := [ Determinant(adz - (31/32)*IdentityMatrix(F, Dimension(A32))) ];
			else
			  extra = [];
			end if;
			
  		idemps := FindAllIdempotents(A, A0: length:=len, form:=form, extra_rels:=extra);
  		
      // Need to complete
  
  
  
  
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
