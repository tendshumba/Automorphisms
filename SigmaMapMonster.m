/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Given an axis a which is known to be J(1/4), find the sigma map which inverts the 1/4-space.            +
+                                                                                                         +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++=+++++*/

/*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Must load MonsterFusionProjection.m . Require that a be an axial vector. (length n, dimension n).                          +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/

SigmaMapMonster:=function(a)
	A:=Parent(a);
	W:=VectorSpace(Rationals(),Dimension(A));
	P1:=ProjMat(a,1);
	P0:=ProjMat(a,0);
	P4:=ProjMat(a,1/4);
	P:=P1+P0; 
	return Matrix(Rationals(),[Eltseq((W!Eltseq(A.i))*P-(W!Eltseq(A.i))*P4): i in [1..Dimension(A)]]);
end function;
