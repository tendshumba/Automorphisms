/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Suppose that V is a subalgebra of an axial algebra A of known multiplication. Determine the ad_a matrix of a in V.    +
+
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/

AdMatInSubAlg:=function(A,V,a)
	n:=Dimension(A);
	d:=Dimension(V);
	basV:=Basis(V);
	basmat:=Matrix(BaseField(A),[Eltseq(basV[i]):i in [1..d]]);
	sols:=[Eltseq(Solution(basmat,Vector(BaseField(A),Eltseq(a*(A!V.i))))):i in [1..d]];
	return Matrix(BaseField(A),sols);
end function;
