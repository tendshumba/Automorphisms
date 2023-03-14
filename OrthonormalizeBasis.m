/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Function to othorgonalize a basis of a subspace of an axial algebra with a form                                                   =
+                                                                                                                                   +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/
OrthonormalizeBasis:=function(A,basis,U)
	orth_bas:=OrthogonalizeBasis(A,basis,U);
	norm_bas:=[];
	for i:=1 to # orth_bas do
		v:=A!orth_bas[i];
		norm:=FrobFormAtElements(v,v,U);
		Append(~norm_bas,v/norm);
	end for;
	return norm_bas;   
end function; 
