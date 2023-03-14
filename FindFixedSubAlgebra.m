
/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ This function determines the fixed subalgebra of a given matrix group for a particular algebra A. For efficiency, give the              +
+ fewest possible number of generators of the group. The function will return the fixed subalgebra in vector space form.                  +
+                                                                                                                                         +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/ 
FindFixedSubAlgebra:=function(A,lst)
        dim:=Dimension(A);
	Mat:=ZeroMatrix(BaseField(A),#lst*dim,dim); 		 
	for l:=1 to #lst do
		for i:=1 to dim do
			for j:=1 to dim do
				Mat[(l-1)*dim+i,j]:=lst[l][j,i];
			end for;
		end for;
		for j:=1 to dim  do
			Mat[(l-1)*dim+j,j]-:=1;
		end for;
	end for;
	_,sol:=Solution(Transpose(Mat),Vector(BaseField(A),[0*i:i in [1..#lst*dim]]));
	return sol;
end function; 
 
 

