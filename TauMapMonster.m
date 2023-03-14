/*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Must load MonsterFusionProjection.m . Require that a be an axial vector. (length n, dimension n).                          +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/

TauMapMonster:=function(a)
	A:=Parent(a);
	W:=VectorSpace(Rationals(),Dimension(A));
	P1:=ProjMat(a,1);
	P0:=ProjMat(a,0);
	P4:=ProjMat(a,1/4);
	P32:=ProjMat(a,1/32);
	P:=P1+P0+P4;
	return Matrix(Rationals(),[Eltseq((W!Eltseq(A.i))*P-(W!Eltseq(A.i))*P32): i in [1..Dimension(A)]]);
end function;
