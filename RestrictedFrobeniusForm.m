/*Suppose that an algebra A has a form U. Let B be a subalgebra of A with a basis "basis".
  This function produces the form restricted to B.*/
RestrictedForm:=function(basis)
  UU:=U;
  /*At this point it takes basis as a set ofvectors, not necessarily axial algebra elements*/
 // UU:=Matrix(BaseRing(Parent(basis[1])),[Eltseq(UU[i]):i in [1..Nrows(UU)]]);/*converting the matrix to a matrix over the rationals.
						//	     For some reason ChangeField does not always work.*/
						//
UU:=ChangeRing(UU,BaseRing(Parent(basis[1])));
arr:=[[(VecToMat(basis[i])*UU*Transpose(VecToMat(basis[j])))[1][1]:j in [1..#basis]]:i in[1..#basis]];
return Matrix(Rationals(),[Eltseq(x):x in arr]);
end function;
