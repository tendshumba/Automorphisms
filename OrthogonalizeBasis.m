/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Function to othorgonalize a basis of a subspace of an axial algebra with a form                                                   =
+                                                                                                                                   +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/
OrthogonalizeBasis:=function(A,basis,U)
	m:=#basis;
	orth_bas:=[basis[1]];
	for i:=2 to m do
		v:=basis[i];
		w:=v-(&+[Proj_aTo_b(A!v,A!orth_bas[j],U):j in [1..i-1]]);
		Append(~orth_bas,w);
	end for;
	return orth_bas;
end function; 
