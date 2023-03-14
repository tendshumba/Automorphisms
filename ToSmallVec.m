/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+This function takes an alebra/vector space A and a subspace V and a vector v in A to produce a dimV-long +
+ relative to a basis of V. The opposite of ToBigVec.                                                     +
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/
ToSmallVec:=function(A,V,v)
	F:=BaseField(A);n:=Dimension(A); m:=Dimension(V);
	AA:=VectorSpace(F,n);
	mat:=Matrix(F,[Eltseq(V.i):i in [1..m]]);
	v,_:= Solution(mat,AA!Eltseq(v));
	return v;
end function;
