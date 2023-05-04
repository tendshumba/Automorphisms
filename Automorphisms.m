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

intrinsic AxesOrbitRepresentatives(A::ParAxlAlg) -> SetIndx, List
  {
  Returns a set of orbit representatives of axes of a ParAxlAlg coerced into an algebra and a List of associative arrays giving the decompositions for each axis.
  }
  // This will check it is a complete algebra.
  AA := Algebra(A);
  
  axes := {@ AA!A`axes[i]`id`elt : i in [1..#A`axes] @};
  
  eigs := A`fusion_table`eigenvalues;
  Gr, gr := Grading(A`fusion_table);
  require Order(Gr) eq 2: "The grading group must be of order 2";
  
  deccomps := {@@};
  
  keys := AssociativeArray();
  keys["even"] := {@ e : e in eigs | e@gr eq Gr!1@};
  keys["odd"] := {@ e : e in eigs | e@gr ne Gr!1@};

  V := A`W;
  
  // We use a sequence, so there could be duplicate decompositions
  decs := [* *];
  for i in [1..#A`axes] do
    D := AssociativeArray([* <k, sub<V | Basis(A`axes[i]``attr[{@k@}])> >
                : k in keys[attr], attr in ["even", "odd"] *]);
    Append(~decs, D);
  end for;
    
  return axes, decs;
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

Some additional data


*/
types := ["2A","2B","3A","3C","4A","4B","5A","6A"];
IdentityLength := AssociativeArray([* <"2A", (2^2*3)/5>,
                                      <"2B", 2>,
                                      <"3A", (2^2*29)/(5*7)>,
                                      <"3C", (2^5/11)>,
                                      <"4A", 4>,
                                      <"4B", 19/5>,
                                      <"5A", (2^5)/7>,
                                      <"6A", (3*17)/(2*5)> *]);

/*

===============  The main algorithms ====================

*/
// FindAutNuanced
intrinsic FindNewAxes(axes::SetIndx, decomp::List, form::AlgMatElt) -> SetIndx
  {
  The inputs are a set axes of (orbit representatives) of the axes and corresponding eigenspace decompositions together with a Frobenius form.
  
  We perform the nuanced algorithm to find all axes.  
  }
  A := Universe(axes);
  F := BaseField(A);
  
  require Nrows(form) eq Ncols(form): "The form must be a square matrix.";
  require Nrows(form) eq Dimension(A): "The form is not the same dimension as the algebra";
  require #axes eq #decomp: "There are not the same number of decompositions as axis representatives.";
  // Can change this later
  // What about other characteristics
  require forall{ d : d in decomp | Type(d) eq Assoc and Keys(d) subset {1,0,1/4,1/32} and &+[Dimension(d[k]) : k in Keys(d)] eq Dimension(A)}: "The decompositions are not in the correct form.";
  

  found := {@ @};
  for i in [1..#axes] do
    a := axes[i];
    dec := decomp[i];
    
    printf "Orbit number %o of %o\n", i, #axes;
    
    /*
    For one of our known axes a, we want to find a new axis b
    So B = < a,b > is a 2-generated axial algebra.  These all have identity.
    We search for z = 1-a is an idempotent in the 0-eigenspace for a.
    
    We use this to identify 1 and then the subalgebra.
    */
    // Change when decomposition algebra
    A0 := dec[0];
    
    for k in Keys(IdentityLength) do
      // Get the length of z
      printf "  Eigenvalue is %o\n", k;
      len := IdentityLength[k] - 1;
      
      // if the type is 4A, then there are infinitely many such idempotents
      // Hence we need to add some extra relations
      if k eq "4A" then
        A32 := dec[1/32];
        R := PolynomialRing(F, Dimension(A0));
				FF := FieldOfFractions(R);
				AFF := ChangeRing(A, FF);
				z := &+[R.i*AFF!A0.i : i in [1..Dimension(A0)]];
				// Since z is in A0 and the fusion law is Seress, z A32 subset A32
				// So we can restrict the action of the adjoint of z to A32
				bas := Basis(A32);
				A32_vectorspace := VectorSpaceWithBasis(bas);
				A32_vectorspace := ChangeRing(A32_vectorspace, FF);
				adz := Matrix([ Coordinates(A32_vectorspace, Vector((AFF!b)*z)) : b in bas]);
				
				extra := [ Determinant(adz - (31/32)*IdentityMatrix(FF, Dimension(A32))) ];
			else
			  extra := [];
			end if;
			
			t := Cputime();
			print "  Finding idempotents";
  		idems := FindAllIdempotents(A, A0: length:=len, form:=form, extra_rels:=extra);
  		printf "  Found %o idempotents in %o secs\n", #idems, Cputime()-t;
  		
  		// From the idempotents found, find the algebra B = <<a,b>> and sift for Monster type axes.
  		for z in idems do
  		  // Since z = 1-a, we can find 1
  		  one := a+z;
  		  // The subalgebra B must be contained in the 1-eigenspace of one.
  		  BB := Eigenspace(AdjointMatrix(one), 1);
  		  
  		  t := Cputime();
  			print "  Finding idempotents";
  		  possibles := FindAllIdempotents(A, BB: length:=1, form:=form);
  		  printf "  Found %o idempotents in %o secs\n", #possibles, Cputime()-t;
  		  
  		  // check for the Monster fusion law
  		  for y in possibles do
  		    if HasMonsterFusionLaw(y) then
    		    Include(~found, y);
    		  end if;
  		  end for;
  		end for;
    end for;
  end for;
  
  return found;
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
  F := BaseRing(A);
  n := Dimension(A);
	m := Dimension(U);
	
  require m le n: "U must be a subspace of A";
  if Type(form) ne BoolElt then
    require ISA(Type(form), Mtrx): "The Frobenius form if given must be a matrix";
    require Nrows(form) eq Ncols(form) and Nrows(form) eq n: "The matrix given for the Frobenius form must be a square matrix with dim(A) rows and columns";
  end if;  
  if Type(length) ne BoolElt then
    // We have already checked it has the correct form.
    require Type(form) ne BoolElt: "You need to provide a Frobenius form";
    require IsCoercible(F, length): "The length of an axis must belong to the field of the algebra";
  end if;
  
  P := PolynomialRing(F, m);
	FF := FieldOfFractions(P);
	
  if extra_rels ne [] then
    require forall{ x : x in extra_rels | IsCoercible(FF, x)}: "The extra relations do not lie in the correct field";
  end if;
  
	// FF_to_P := hom<FF->P | [ P.i : i in [1..m]]>;
	AF := ChangeRing(A, FF);
	
	// We set up a general element x
	bas := Basis(U);
	x := &+[ P.i*AF!bas[i] : i in [1..m]];
	
	// We add any extra relations coming from a length restriction
	if Type(length) ne BoolElt then
	  formF := ChangeRing(form, FF);
	  extra_rels cat:= [ InnerProduct(Vector(x)*formF, Vector(x)) - length];
	end if;
  
  // form the ideal
  I := ideal<P | Eltseq(x*x - x) cat extra_rels>;
  
  if Dimension(I) ge 1 then
    print "The variety of idempotents is not zero-dimensional.  Try adding extra relations.";
		return false;
	end if;
  
  // Form the variety and check to see if we have all the solutions
  var := Variety(I);
  varsize := VarietySizeOverAlgebraicClosure(I);
  if #var ne varsize then
    print "Warning: there are additional idempotents over a field extension";
  end if;
  
  // We need to coerce the variety elements back into the algebra
  // We form a matrix whose rows are the elements of the variety (each row is the coefficients of the basis elements)
  // and multiply by the matrix of basis elements
  // idems := {@ A | r : r in Rows(Matrix([[v[i] : i in [1..m]]: v in var])*Matrix(bas)) @};
  
  // Do the simple coercion
  idems := {@ A | &+[ v[i]*bas[i] : i in [1..m]]: v in var @};
  
  return idems;
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
  
  /*
	decomps:=AssociativeArray();
	A:=Parent(lst[1]); // why this must be really axial
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
	*/
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

/*

============ Checking axes and fusion laws ==================

*/
intrinsic HasMonsterFusionLaw(u::AlgGenElt: fusion_values := {@1/4, 1/32@})-> BoolElt
  {
  Check if an algebra element u satisfies the Monster fusion law.  Defaults to M(1/4,1/32) fusion law.
  }
  require Type(fusion_values) eq SetIndx and #fusion_values eq 2 and 1 notin fusion_values and 0 notin fusion_values: "You must provide two distinct non-zero, non-one ring or field elements for the fusion law.";
  
  if not IsIdempotent(u) then
    print("Element is not an idempotent");
    return false;
  end if;
  
  F := Universe(fusion_values);
  fusion_set := {@ F | 1, 0 @} join fusion_values;
  
  A := Parent(u);
  adu := AdjointMatrix(u);
  
  eigs := {@ t[1] : t in Eigenvalues(adu) @};
  
  // Check we don't have extra eigenvalues
  if exists(ev){ ev : ev in eigs | ev notin fusion_set } then
    printf("Eigenvalue %o not in %o\n"), ev, fusion_set;
    return false;
  end if;
  
  // Find the eigenspaces
  espace := AssociativeArray([* <ev, Eigenspace(adu, ev)> : ev in fusion_set *]);
  
  // The multiplicities attached are sometimes not reliable
  if Dimension(A) ne &+[ Dimension(espace[k]) : k in fusion_set] then
    print("The element is not semisimple.");
    return false;
  end if;
  
  // Check the fusion law
  ebas := AssociativeArray([* <ev, Basis(espace[ev])> : ev in fusion_set *]);

  al := fusion_set[3];
  bt := fusion_set[4];

  // these are the tuples <a,b,S> representing a*b = S in the fusion law
  fus_law := [ <0, 0, {0}>, <0, al, {al}>, <0, bt, {bt}>, <al, al, {1,0}>, <al, bt, {bt}>, <bt, bt, {1,0,al}> ]; 

  for t in fus_law do
    a,b,S := Explode(t);
    if not forall{ p : p in [ (A!v)*(A!w) : v in ebas[a], w in ebas[b]] | p in &+[espace[s] : s in S]} then
      return false;
    end if;
  end for;

  return true;
end intrinsic;
