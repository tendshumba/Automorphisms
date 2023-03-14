/*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Let A be an n-dim algebra and suppose that a is an axis in A. Asumme Monster fusion. Find the          +
+  projections to the 1,0,1/4 and 1/32 spaces. To avoid too many arguments, make sure that a is in cat   +
+  axial. Take as input the axes and the eigenvalue.                                                     +
+                                                                                                        +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/
ProjMat:=function(a,ev)
	A:=Parent(a);d:=Dimension(A);
	evals:=[1,0,1/4,1/32];
	I:=IdentityMatrix(Rationals(),d);
	ad:=Matrix(Rationals(),[Eltseq(a*A.i): i in [1..d]]);
	return &*[(ad-x*I)/(ev-x):x in evals|x ne ev];

end function;
