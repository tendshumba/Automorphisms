/*

Automorphisms of axial algebras


*/
// Define an verbose setting for printing
declare verbose Axes_verb, 2;
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
intrinsic FindAllAxes(A::AxlAlg) -> SetIndx
  {
  Finds all axes in an axial algebra. 
  }
  FL := FusionLaw(A);
  require FL eq MonsterFusionLaw(1/4,1/32): "The axial algebra must be of Monster type (1/4, 1/32)";
  
  so, form := HasFrobeniusForm(A);
  require so: "The axial algebra has no Frobenius form.";
  
  ev := Evaluation(FL);
  // this should just be [1,2,3,4]
  index := [ i where so := exists(i){i : i in [1..4] | i@ev eq lm} : lm in [1,0,1/4,1/32]];
  
  F := BaseField(A);
  G := MiyamotoGroup(A);
  axes := Axes(A);
  // get the orbits
  axes_reps := AxisOrbitRepresentatives(A);
  
  found := {@ @};
  for a in axes_reps do
    dec := Decomposition(a);
    
    vprintf Axes_verb, 1: "Orbit number %o of %o\n", Position(axes_reps, a), #axes_reps;
    /*
    For one of our known axes a, we want to find a new axis b
    So B = < a,b > is a 2-generated axial algebra.  These all have identity.
    We search for z = 1-a is an idempotent in the 0-eigenspace for a.
    
    We use this to identify 1 and then the subalgebra.
    */
    A0 := Part(dec, FL!2);
    
    for k in Keys(IdentityLength) do
      // Get the length of z
      vprintf Axes_verb, 1: "  Assumed subalgebra is %o\n", k;
      len := IdentityLength[k] - 1;
      
      // if the type is 4A, then there are infinitely many such idempotents
      // Hence we need to add some extra relations
      if k eq "4A" then
        // All Monster type algebras have an identity
        so, one := HasOne(A);
        assert so;
        
        A32 := Part(dec, FL!4);
        R := PolynomialRing(F, Dimension(A0));
				FF := FieldOfFractions(R);
				AFF := ChangeRing(A, FF);
				z := &+[R.i*AFF!Eltseq(A0.i) : i in [1..Dimension(A0)]];
				
				len_rest := [ Frobenius(z, AFF!Eltseq(one)) - len ];
				
				// Taking the determinant is still is slow, so avoid if possible.
				if Dimension(ideal<R | Eltseq(z*z-z) cat len_rest>) gt 0 then
					t := Cputime();
					// Since z is in A0 and the fusion law is Seress, z A32 subset A32
				  // So we can restrict the action of the adjoint of z to A32
				  bas := Basis(A32);
				  A32_vectorspace := VectorSpaceWithBasis(bas);
				  A32_vectorspace := ChangeRing(A32_vectorspace, FF);
				  adz := Matrix([ Coordinates(A32_vectorspace, Vector((AFF!b)*z)) : b in bas]);
				  
				  extra_rels := [ Determinant(adz - (31/32)*IdentityMatrix(FF, Dimension(A32))) ];
				  
					vprintf Axes_verb, 2: "    Extra 4A relation found in %o seconds\n", t;
				end if;
			else
			  extra_rels := [];
			end if;
			
			t := Cputime();
  		idems := FindAllIdempotents(A, A0: length:=len, extra_rels:=extra_rels);
  		vprintf Axes_verb, 2: "    Found %o possible identities in %o secs\n", #idems, Cputime()-t;
  		
  		// From the idempotents found, find the algebra B = <<a,b>> and sift for Monster type axes.
  		for z in idems do
  		  // Since z = 1-a, we can find 1
  		  one := a+z;
  		  // The subalgebra B must be contained in the 1-eigenspace of one.
  		  ad := AdjointMatrix(one);
  		  BB := Eigenspace(ad, 1);
  		  
  		  t := Cputime();
  			vprintf Axes_verb, 1: "      Finding idempotents for identity %o of %o\n", Position(idems, z), #idems;
  		  possibles := FindAllIdempotents(A, BB: length:=1);
  		  vprintf Axes_verb, 2: "        Found %o idempotents in %o secs\n", #possibles, Cputime()-t;
  		  
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

intrinsic FindAllIdempotents(A::AlgGen, U::ModTupFld: extra_rels:=[], extend_field:=false) -> SetIndx
  {
  Given an algebra A and a subspace (not necessarily a subalgebra) U, find all the idempotents of A contained in U.
  
  Optional arguments:
    extra_rels - require the idempotent to satisfy extra relation(s).  These are given by multivariate polynomials in dim(U) variables corresponding to the basis of U.
    extend_field - if true, then if necessary extend the field to an algebraically closed field to find additional solutions.
  }
  F := BaseRing(A);
  n := Dimension(A);
	m := Dimension(U);
	
  require m le n: "U must be a subspace of A"; 
  
  P := PolynomialRing(F, m);
	FF := FieldOfFractions(P);
	
  if extra_rels ne [] then
    require forall{ x : x in extra_rels | IsCoercible(FF, x)}: "The extra relations do not lie in the correct field";
  end if;
  
	AF := ChangeRing(A, FF);
	
	// We set up a general element x
	bas := Basis(U);
  x := &+[ P.i*AF!Eltseq(bas[i]) : i in [1..m]];
	
  // form the ideal
  I := ideal<P | Eltseq(x*x - x) cat extra_rels>;
  
  if Dimension(I) ge 1 then
    print "The variety of idempotents is not zero-dimensional.  Try adding extra relations.";
		return false;
	end if;
  
  // Form the variety and check to see if we have all the solutions
  var := Variety(I);
  varsize := VarietySizeOverAlgebraicClosure(I);
  
  // We need to coerce the variety elements back into the algebra
  // We form a matrix whose rows are the elements of the variety (each row is the coefficients of the basis elements)
  // and multiply by the matrix of basis elements
  // idems := {@ A | r : r in Rows(Matrix([[v[i] : i in [1..m]]: v in var])*Matrix(bas)) @};
  
  
  if #var eq varsize then
    // Do the simple coercion
    idems := {@ A | &+[ v[i]*bas[i] : i in [1..m]]: v in var @};
    return idems;
  end if;
  if not extend_field then
    print "Warning: there are additional idempotents over a field extension";
    // Do the simple coercion
    idems := {@ A | &+[ v[i]*bas[i] : i in [1..m]]: v in var @};
    return idems;
  end if;
  
  // so we need to extend the field and resolve
  FClos := AlgebraicClosure(FF);
  varCl := Variety(I, FClos);
	ACl := ChangeRing(A, FClos);
	
	// Do the simple coercion
  idems := {@ ACl | &+[ v[i]*ACl!bas[i] : i in [1..m]]: v in varCl @};
  return idems;
end intrinsic;

intrinsic FindAllIdempotents(A::DecAlg, U::ModTupFld: length:=false, extra_rels:=[], extend_field:=false) -> SetIndx
  {
  Given a decomposition algebra A and a subspace (not necessarily a subalgebra) U, find all the idempotents of A contained in U.
  
  Optional arguments:
    length - requires the length of the idempotents to be as given
    extra_rels - require the idempotent to satisfy extra relation(s).  These are given by multivariate polynomials in dim(U) variables corresponding to the basis of U.
    extend_field - if true, then if necessary extend the field to an algebraically closed field to find additional solutions.
  }
  F := BaseRing(A);
  n := Dimension(A);
	m := Dimension(U);
	
  require m le n: "U must be a subspace of A"; 
  if Type(length) ne BoolElt then
    // We have already checked it has the correct form.
    require IsCoercible(F, length): "The length of an axis must belong to the field of the algebra";
  end if;
  
  P := PolynomialRing(F, m);
	FF := FieldOfFractions(P);
	
  if extra_rels ne [] then
    require forall{ x : x in extra_rels | IsCoercible(FF, x)}: "The extra relations do not lie in the correct field";
  end if;
  
	// We work in the algebra as changing ring is quicker here.
  Aalg := Algebra(A);
	AalgF := ChangeRing(Aalg, FF);
	
	// We set up a general element x
	bas := Basis(U);
  x := &+[ P.i*AalgF!Eltseq(bas[i]) : i in [1..m]];
	
	// We add any extra relations coming from a length restriction
	if Type(length) ne BoolElt then
	  // An axial algebra of Monster type always has an identity
	  so, one := HasOne(A);
	  assert so;
	  
    so, frob := HasFrobeniusForm(A);
	  assert so;
	  frob := ChangeRing(frob, FF);
	  // Since we assume that x is a idempotent, (x,x) = (x,x*id) = (x^2, id) = (x, id)
	  extra_rels cat:= [ InnerProduct(x*frob, AalgF!Eltseq(one)) - length];
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
  
  // We need to coerce the variety elements back into the algebra
  // We form a matrix whose rows are the elements of the variety (each row is the coefficients of the basis elements)
  // and multiply by the matrix of basis elements
  // idems := {@ A | r : r in Rows(Matrix([[v[i] : i in [1..m]]: v in var])*Matrix(bas)) @};
  
  
  if #var eq varsize then
    // Do the simple coercion
    idems := {@ A | &+[ v[i]*bas[i] : i in [1..m]]: v in var @};
    return idems;
  end if;
  if not extend_field then
    vprint Axes_verb, 1: "Warning: there are additional idempotents over a field extension";
    // Do the simple coercion
    idems := {@ A | &+[ v[i]*bas[i] : i in [1..m]]: v in var @};
    return idems;
  end if;
  
  // so we need to extend the field and resolve
  FClos := AlgebraicClosure(FF);
  varCl := Variety(I, FClos);
	ACl := ChangeRing(A, FClos);
	
	// Do the simple coercion
  idems := {@ ACl | &+[ v[i]*ACl!bas[i] : i in [1..m]]: v in varCl @};
  return idems;
end intrinsic;
/*

============ Functions to find twins/multiples ===============

*/
// First we need this useful function
intrinsic AnnihilatorOfSpace(A::DecAlg, U::ModTupFld) -> ModTupFld
  {
  Given a decomposition algebra A and a subspace U of A, return the subspace (not a subalgebra) of A which annihilates U.
  }
  require U subset VectorSpace(A): "U must be a subspace of the algebra.";
  
  // create the matrix which is the horizontal join of the matrices ad_a|_U for each a in a basis of A.
  M := HorizontalJoin([Matrix([ Eltseq(A.i*(A!u)) : i in [1..Dimension(A)]]) : u in Basis(U)]);
  
  return Nullspace(M);
end intrinsic;

intrinsic FindMultiples(a::AxlAlgElt) -> SetIndx
  {
  Given an axis, find the set of all other axes which have the same Miyamoto automorphism as a.  The axis supplied must be of Monster, or Jordan type.
  }
  require HasMonsterFusionLaw(a): "The element is not of Monster or Jordan type.";
  A := Parent(a);

  ada := AdjointMatrix(a);
  
	eigenspace := Eigenspace(ada, 1/32);
	if Dimension(eigenspace) eq 0 then
	  eiegnspace := Eigenspace(ada, 1/4);
	  require Dimension(eigenspace) ne 0: "The element given has only eigenvalues 1, or 0";
	end if;
	
	// We now find any twins/multiples b.
	// If b has the same Miyamoto automorphism as a, then their 1/32-eigenspaces (resp 1/4-) U are equal.
	// This implies that b-a \in Ann(U)
	
	ann := AnnihilatorOfSpace(A, eigenspace);
	
	// If such a b does exist, then b is in the coset a + U
	// We search for idempotents in the subspace <a,U>
	
	idems := FindAllIdempotents(A, sub<VectorSpace(A)|Vector(a), ann>: length := 1);
	
	return idems;
end intrinsic;
/*

========== Functions to find Jordan axes =============

*/
// First we need the Fixed subalgebra of A
intrinsic FixedSubalgebra(A::DecAlg, G::GrpMat) -> AlgGen
  {
  Find the subalgebra of A which is fixed under the action of G, where G must be a subgroup of automorphisms of A.
  }
  require Dimension(G) eq Dimension(A): "The matrix group G must be in the same dimension as A.";
  // We should really check whether G is a subgroup of automorphisms of A
  
  V := GModule(G);
  fix := Fix(V);
  
  return Subalgebra(A, [Eltseq(V!v) : v in Basis(fix)]);
end intrinsic;

intrinsic FixedSubalgebra(A::DecAlg, G::GrpPerm) -> AlgGen
  {
  Find the subalgebra of A which is fixed under the action of G, where G must be a subgroup of automorphisms of A.
  }
  if G subset MiyamotoGroup(A) then
    return FixedSubalgebra(A, G@MiyamotoActionMap(A));
  elif G subset UniversalMiyamotoGroup(A) then
    _, phi := UniversalMiyamotoGroup(A);
    return FixedSubalgebra(A, (G@phi)@MiyamotoActionMap(A));
  else
    error "The permutation group must be a subgroup of the (universal) Miyamoto group.";
  end if;
end intrinsic;

intrinsic JordanAxes(A::AxlAlg: G:= MiyamotoGroup(A), form := false) -> Alg
  {
  Find all Jordan type 1/4 axes contained in the axis algebra A of Monster type (1/4,1/32) with Miyamoto group G.  
  }
  /*
  If b is a Jordan type 1/4 axis and a is one of the (known generating) axes in A,
  then B = <<a, b>> is a 2-gen axial algebra of Monster type.
  Since \tau_b = 1, it fixes a and hence \tau_a must fix b.
  This is true for all axes a, so we can search for b in the fixed subalgebra.
  */
  
  // This will also check that the dimensions of G and A or compatible.
  B := FixedSubalgebra(A, G);
  
  /*
  B = <<a, b>> must be either 2B, or 2A
  If B is a 2A, then, as a is Monster type (1/4, 1/32) and b is Jordan type 1/4, a and b must be the standard generators for 2A
  Hence the length of b is also 1
  If B = 2B, then b could have length 1, or length 2 (be the identity in the 2B).
  */
  V := VectorSpace(A);
  U := sub<V | [Vector(A!b) : b in Basis(B)]>;
  idems := FindAllIdempotents(A, U:length := 1) join FindAllIdempotents(A, U:length := 2);

  // We remove the zero and id from the list
  so, id := HasOne(A);
  if not so then
    id := A!0;
  end if;
  
  return {@ b : b in idems | HasJordanFusionLaw(b) @} diff {@ A!0, id@};
end intrinsic;

// DecomposeToJointEigenspaces 
intrinsic JointPartDecomposition(L::{@Dec@}: non_trivial := true) -> Assoc
  {
  Given an indexed set of decompositions L = \{ D_1, ..., D_n\}, find the intersections of all these decompositions.  Returns an associative array of where the element D_1(x_1) \cap ... \cap D_n(x_n) has keys give by the set of eigenvalues \{ x_1, ..., x_n \}.
  If the optional argument non_trivial is true, then we only return the non-trivial subspaces.
  }
  if IsEmpty(L) then
    return AssociativeArray();
  end if;
  require Type(non_trivial) eq BoolElt: "The optional parameter non_trivial must be a boolean.";
  // Now L is not empty
  require forall{ D : D in L | IsAttached(D)}: "The decompositions must be attached to an algebra.";
  A := Algebra(L[1]);
  require forall{ D : D in L | Algebra(D) eq A}: "The decompositions must all be for the same algebra.";
  
  FL := FusionLaw(A);
  elts := Elements(FL);
  cart := CartesianPower(elts, #L);
  
  decomps := AssociativeArray();
  for c in cart do
    U := &meet [ Part(L[i], c[i]) : i in [1..#L]];
    
    // the only case when we don't add is if non-trivial eq true and the dim is 0
    if non_trivial and Dimension(U) eq 0 then
      continue c;
    end if;
    // otherwise we add the associative array
    decomps[c] := U;
  end for;
  return decomps;
end intrinsic;
/*

Given a basis of a subspace and some extra vectors sieve the extra vectors to form a basis of the space spanned by all vectors.  Returns the indices of the required extra vectors for the basis.

*/
function CompleteToBasis(bas, extra)
  // note from before suggest working in a quotient is quicker.
  V := Universe(bas);
  U := sub<V | bas >;
  Q, quo := quo<V | bas>;
  
  extra_Q := extra@quo;
  dim := Dimension(sub<Q | extra_Q>);
  extra_bas := [];
  index := [];
  
  i := 0;
  while #extra_bas ne dim do
    i +:= 1;
    if IsIndependent(extra_bas cat [extra_Q[i]]) then
      Append(~extra_bas, extra_Q[i]);
      Append(~index, i);
    end if;
  end while;
  
  return index;
end function;
/*

Functions to extend an automorphism of a subalgebra to an automorphism of the whole algebra.

*/
// ExtendMapToAlgebra
intrinsic ExtendMapToAlgebraAutomorphism(A::DecAlg, phi::Map) -> BoolElt, .
  {
  Given a bijective map phi:B -> A on a subspace B of A, try to extend this to an automorphism of the algebra, by using the algebra multiplication.  We return true and the map if it does extend to the whole of A.  If not, we return false and the largest subalgebra to which it extends.
  }
  B := Domain(phi);
  require ISA(Type(B), ModTupFld): "The domain of the map must be a subspace of A";
  require B subset VectorSpace(A): "B must be a subspace of A.";
  require Codomain(phi) eq VectorSpace(A): "The image of the map must be in A.";
  require Dimension(Image(phi)) eq Dimension(B): "The map must be bijective.";
  
  // should check for any contradiction to being an automorphism in phi already.
  // Maybe 
  
  V := VectorSpace(A);
  old_bas := [V|];
  new_bas := Basis(B);
  old_im := [V|];
  new_im := [ phi(b) : b in new_bas];
  psi := phi;
  
  closed := false;
  
  // we will extend our map phi to psi in stages
  // at each stage, we will take a,b in the domain of the current map psi
  // define psi(ab) to be psi(a)*psi(b)
  // if ab is in the domain of psi already, then this must agree, or we have a contradiction.
  // otherwise this terminates when the domain is closed.
  while not closed do
    // we only need to take products we haven't seen before
    // ie products old_bas with new_bas and new_bas with new_bas
    map_dom := Domain(psi);
    
    newprods := [];
    im_newprods := [];
    
    for i -> a in (old_bas cat new_bas), j -> b in new_bas do
      ab := Vector(A!a*A!b);
      im_ab := Vector(A!((old_im cat new_im)[i])*A!new_im[j]);
      
      if ab in map_dom and ab@psi ne im_ab then
        print("The map cannot be extended to an automorphism.");
        return false, _;
      end if;
      // hence it is ok.
      
      Append(~newprods, ab);
      Append(~im_newprods, im_ab);
    end for;
    
    // Now need to pick a basis for the new space of new products
    old_bas cat:= new_bas;
    old_im cat:= new_im;
    index := CompleteToBasis(old_bas, newprods);
    new_bas := newprods[index];
    new_im := im_newprods[index];
    
    bas := old_bas cat new_bas;
    im := old_im cat new_im;
    assert #bas eq #im;
    
    psi := hom<sub<V|bas> -> V | [<bas[i], im[i]> : i in [1..#bas]]>;
    
    // if there no new products, then the domain is closed.
    closed := #index eq 0;
  end while;
  
  return true, psi;
end intrinsic;

// Do We need this version??
intrinsic ExtendMapToAlgebra(A::Alg, M::AlgMatElt) -> BoolElt, .
  {
  Given a matrix M on a subspace of A, extend this multiplicatively as far as possible.  We return true and the matrix if it does extend to the whole of A.  If not, we return false and the largest subalgebra to which it extends.
  }
  
end intrinsic;

// ExtendAutToMod
// How do we give the map phi??? as a map to a matrix?
intrinsic HasInducedMap(A::DecAlg, M::ModTupFld, phi::Map) -> BoolElt, .
  {
  Suppose phi is an automorphism of a (AlgGen) subalgebra B of A and M is a module of B.  Try to construct the induced map psi: M --> M such that psi(ma) = psi(m)phi(a), for all a in B and m in M.
  }
  B := Domain(phi);
  require ISA(Type(B), AlgGen): "The domain of the map must be an algebra";
  require B subset Algebra(A): "B must be a subalgebra of A.";
  require Codomain(phi) eq B: "The map must be an automorphism of a subalgebra B of A.";
  // Could check for being an automorphism here, but might be costly.
  
  require BaseRing(M) eq BaseRing(A) and OverDimension(M) eq Dimension(A): "M must be a subspace of A";
  
  // Replace once coercion for subalgebras works properly
  Aalg := Algebra(A);
  Balg := B;
  function coerce(b)
    return A!Vector(Aalg!(Balg!Vector(b)));
  end function;
  
  require forall{ <m,b> : m in Basis(M), b in Basis(B) | Vector((A!m)*coerce(b)) in M}: "M must be a submodule for B.";
  
  /*
  We want to find a map psi such that
  
  psi(ma) = psi(m)phi(a)
  
  Let X = (x_{ij}) be the matrix representing the unknown map psi.
  P(a) = (p_{ij}) represent phi(a).  Then, we have:
  
  m ad_a X = m X P(a)
  
  Since this is true for all m in M, we have
    
  ad_a X - X P(a) = 0
  
  This is a special case of Sylvester's equation AX + XB = C.  We solve this using vectorisation and the Kronecker product.  The vectorisation of a matrix is vec(X) = Rows(X).  Then, we have vec(AXB) = vec(X)(A^t \otimes B), where \otimes is the Kronecker product.  So the above is equivalent to
  
  ad_a X I - I X P(a) = 0
  
  and hence
  
  vec(X) (ad_a^t \otimes I - I \otimes P(a)) = 0
  
  So we form the Horizontal join over generators a of
  
  ad_a^t \otimes I - I \otimes P(a)
  
  and find the nullspace.
  */
  F := BaseRing(M);
  m := Dimension(M);
  b := Dimension(B);
  I := IdentityMatrix(F, m);
  ad_as := [ Matrix( [Coordinates(M, Vector((A!m)*coerce(B.i))) : m in Basis(M)]) : i in [1..b]];
  phis := [ Matrix( [Coordinates(M, Vector((A!m)*coerce(B.i@phi))) : m in Basis(M)]) : i in [1..b]];
  
  M := HorizontalJoin([ KroneckerProduct(Transpose(ad_as[i]), I) - KroneckerProduct(I, phis[i]) 
                           : i in [1..b]]);
  
  null := NullSpace(M);
  
  if Dimension(null) eq 0 then
		return false,_;
	else
		return true, null;
	end if;
end intrinsic;





/*

============ Checking axes and fusion laws ==================

*/
// Monster type
intrinsic HasMonsterFusionLaw(u::AxlAlgElt: fusion_values := {@1/4, 1/32@})-> BoolElt
  {
  Check if a axial algebra element u satisfies the Monster fusion law.  Defaults to M(1/4,1/32) fusion law.
  }
  Aalg := Algebra(Parent(u));
  
  return HasMonsterFusionLaw(Aalg!Eltseq(u): fusion_values := fusion_values);
end intrinsic;

intrinsic HasMonsterFusionLaw(u::AlgGenElt: fusion_values := {@1/4, 1/32@})-> BoolElt
  {
  Check if an algebra element u satisfies the Monster fusion law.  Defaults to M(1/4,1/32) fusion law.
  }
  require Type(fusion_values) eq SetIndx and #fusion_values eq 2 and 1 notin fusion_values and 0 notin fusion_values: "You must provide two distinct non-zero, non-one ring or field elements for the fusion law.";
  
  if not IsIdempotent(u) then
    vprint Axes_verb, 1: "Element is not an idempotent";
    return false;
  end if;
  
  F := Universe(fusion_values);
  fusion_set := {@ F | 1, 0 @} join fusion_values;
  
  A := Parent(u);
  adu := Matrix([A.i*u : i in [1..Dimension(A)]]);
  
  eigs := {@ t[1] : t in Eigenvalues(adu) @};
  
  // Check we don't have extra eigenvalues
  if exists(ev){ ev : ev in eigs | ev notin fusion_set } then
    vprintf Axes_verb, 1: "Eigenvalue %o not in %o\n", ev, fusion_set;
    return false;
  end if;
  
  // Find the eigenspaces
  espace := AssociativeArray([* <ev, Eigenspace(adu, ev)> : ev in fusion_set *]);
  
  // The multiplicities attached are sometimes not reliable
  if Dimension(A) ne &+[ Dimension(espace[k]) : k in fusion_set] then
    vprint Axes_verb, 1: "The element is not semisimple.";
    return false;
  end if;
  
  // Check the fusion law
  // first precompute the adjoints for each element in the eigenspace
  adjs := AssociativeArray([* <lm, [ AdjointMatrix(A!v) : v in Basis(espace[lm])]>
                                 : lm in fusion_set*]);
  
  al := fusion_set[3];
  bt := fusion_set[4];

  // these are the tuples <a,b,S> representing a*b = S in the fusion law
  // NB don't need to check 1*a
  fus_law := [ <0, 0, {0}>, <0, al, {al}>, <0, bt, {bt}>, <al, al, {1,0}>, <al, bt, {bt}>, <bt, bt, {1,0,al}> ]; 
  
  V := VectorSpace(A);
  // I := IdentityMatrix(F, Dimension(A));
  for t in fus_law do
    a,b,S := Explode(t);
    // slightly slower to do this
    // if not forall{ ad : ad in adjs[b] | BasisMatrix(espace[a])*ad*(&*[adu-s*I : s in S]) eq 0} then
    // Quicker to take the rows of a matrix than join several subspaces.
    U := sub<V | Rows(VerticalJoin([ BasisMatrix(espace[a])*ad : ad in adjs[b]]))>;
    if not U subset &+[espace[s] : s in S] then
      return false;
    end if;
  end for;

  return true;
end intrinsic;

intrinsic HasJordanFusionLaw(u::AxlAlgElt: fusion_value := 1/4)-> BoolElt
  {
  Check if a axial algebra element u satisfies the Jordan fusion law.  Defaults to J(1/4) fusion law.
  }
  Aalg := Algebra(Parent(u));
  
  return HasJordanFusionLaw(Aalg!Eltseq(u): fusion_value := fusion_value);
end intrinsic;

intrinsic HasJordanFusionLaw(u::AlgGenElt: fusion_value := 1/4)-> BoolElt
  {
  Check if an algebra element u satisfies the Jordan fusion law.  Defaults to J(1/4) fusion law.
  }
  
  require fusion_value notin {0,1}: "The fusion_value cannot be 0, or 1";
  
  if not IsIdempotent(u) then
    vprint Axes_verb, 1: "Element is not an idempotent";
    return false;
  end if;
  
  F := Parent(fusion_value);
  fusion_set := {@ F | 1, 0, fusion_value @};
  
  A := Parent(u);
  adu := Matrix([A.i*u : i in [1..Dimension(A)]]);
  
  eigs := {@ t[1] : t in Eigenvalues(adu) @};
  
  // Check we don't have extra eigenvalues
  if exists(ev){ ev : ev in eigs | ev notin fusion_set } then
    vprintf Axes_verb, 1: "Eigenvalue %o not in %o\n", ev, fusion_set;
    return false;
  end if;
  
  // Find the eigenspaces
  espace := AssociativeArray([* <ev, Eigenspace(adu, ev)> : ev in fusion_set *]);
  
  // The multiplicities attached are sometimes not reliable
  if Dimension(A) ne &+[ Dimension(espace[k]) : k in fusion_set] then
    vprint Axes_verb, 1: "The element is not semisimple.";
    return false;
  end if;
  
  // Check the fusion law
  // first precompute the adjoints for each element in the eigenspace
  adjs := AssociativeArray([* <lm, [ AdjointMatrix(A!v) : v in Basis(espace[lm])]>
                                 : lm in fusion_set*]);
  
  eta := fusion_set[3];

  // these are the tuples <a,b,S> representing a*b = S in the fusion law
  // NB don't need to check 1*a
  fus_law := [ <0, 0, {0}>, <0, eta, {eta}>, <eta, eta, {1,0}> ]; 
  
  V := VectorSpace(A);
  for t in fus_law do
    a,b,S := Explode(t);
    U := sub<V | Rows(VerticalJoin([ BasisMatrix(espace[a])*ad : ad in adjs[b]]))>;
    if not U subset &+[espace[s] : s in S] then
      return false;
    end if;
  end for;

  return true;
end intrinsic;
