/*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Given an axial vector w and a subspae V of an axial algebra containing w, project w to V.                                                  +
+                                                                                                                                            +
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/
ProjectVecToSubspace:=function(w,V,U)
	A:=Parent(w); /*w must be axial.*/
	if A`W!Eltseq(w) in V then 
		return A`W!Eltseq(w);
	end if; 
	bas:=Basis(V);
	bas:=[A!x:x in bas];
	orth:=OrthogonalizeBasis(A,bas,U); 
	proj:=&+[Proj_aTo_b(w,A!orth[i],U):i in [1..#bas]];
	return A`W!Eltseq(proj);
end function; 

